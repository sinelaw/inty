//! Run inference work on a worker thread with a generous stack.
//!
//! Inty's substitution / unification walks recurse over the structural
//! depth of a type. The depth-cap in `Type::apply_subst`
//! (`crates/inty/src/types/subst.rs`) converts the *logical*
//! divergent-recursion cases into a `Type::Error` diagnostic instead
//! of a runaway, but the *native* per-frame cost is not the
//! `~200 B / frame` the cap was originally calibrated against:
//! debug-build frames with closure environments and iterator-adapter
//! chains routinely run 4-20 KB, which on the default 8 MB Linux
//! main-thread stack puts the depth-cap's 256 frames at ~5 MB and
//! leaves no headroom for the surrounding inference call chain.
//! See `docs/scaling.md` for the full analysis.
//!
//! The fix is twofold:
//!   - the depth-cap (in place; converts SIGSEGV into a clean
//!     diagnostic when the *logical* recursion runs away), and
//!   - a worker thread with a 64 MB stack (this module), so the
//!     depth-cap fires before the OS guard page on legitimate-but-deep
//!     types. `RUST_MIN_STACK` only affects spawned threads, not
//!     `main`, which is why every inty entry point (`inty <file>`,
//!     `inty declarations`, `inty bundle`, the LSP `update_document`)
//!     needs to route inference through here rather than running it
//!     on whatever thread happens to call in.
//!
//! 64 MB matches the budget documented in `docs/scaling.md`. It is
//! generous for every input the existing test suite exercises;
//! adversarial input like `bigskysoftware/htmx@master/src/htmx.js`
//! still hits the underlying O(N·S·K) substitution cost (it returns
//! type errors after ~25 s rather than crashing — that is the
//! contract here, not full htmx support).

/// Stack size handed to the inference worker thread. Public so the
/// integration tests can match the production budget exactly without
/// hard-coding the number.
pub const INFERENCE_STACK_SIZE: usize = 64 * 1024 * 1024;

/// Run `f` on a freshly-spawned worker thread with
/// [`INFERENCE_STACK_SIZE`] of stack, returning the closure's value.
///
/// Panics in `f` propagate via `join().expect(...)`; a panic-in-the-
/// inference-pipeline aborts the calling process with the worker's
/// payload rather than swallowing it. The thread is named so a
/// debugger or `gdb` trace shows the inference frames sitting on the
/// worker rather than `<unnamed>`.
///
/// `label` is the thread name (shows up in `ps -L`, `top -H`, and
/// debugger thread lists). Pick something specific per call site
/// (`"inty-cli-infer"`, `"inty-lsp-infer"`, ...) so a stuck inference
/// is attributable.
///
/// This call is *blocking*: it spawns, runs to completion, joins.
/// It's a stack-size band-aid, not a parallelism primitive — the
/// caller's thread sits idle waiting for the worker.
pub fn run_with_inference_stack<F, R>(label: &'static str, f: F) -> R
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
{
    std::thread::Builder::new()
        .name(label.to_string())
        .stack_size(INFERENCE_STACK_SIZE)
        .spawn(f)
        .expect("spawn inference worker")
        .join()
        .expect("inference worker panicked")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The helper's whole point is that it provides materially more
    /// stack than the default main-thread budget (8 MB on Linux, 1 MB
    /// on Windows, 512 KB on most macOS builds). Verify by consuming
    /// ~20 MB of stack inside a closure run via the helper: if the
    /// helper ever silently dropped its `stack_size(...)` call, this
    /// recursion would SIGSEGV the test process on any tier-1 host
    /// instead of returning the count.
    ///
    /// 20 MB > every default tier-1 stack size, < 64 MB. 4 KB per
    /// frame is debug-build conservative; release builds use less.
    #[test]
    fn worker_stack_exceeds_default_main_stack() {
        const FRAME_BYTES: usize = 4 * 1024;
        const TOTAL_BYTES: usize = 20 * 1024 * 1024;
        const DEPTH: usize = TOTAL_BYTES / FRAME_BYTES;

        // `#[inline(never)]` so the compiler doesn't tail-call this
        // away into an iterative loop. The whole test is about
        // stack usage; the optimiser eliminating it would silently
        // void the assertion.
        #[inline(never)]
        fn eat(depth: usize, acc: u8) -> u8 {
            // Each call pushes a 4 KB block on the stack. Touch it
            // so a smart compiler can't elide it.
            let buf: [u8; FRAME_BYTES] = [acc; FRAME_BYTES];
            if depth == 0 {
                return buf[FRAME_BYTES - 1];
            }
            // Use the buffer in the recursive call so it can't be
            // hoisted above the call.
            eat(depth - 1, buf[0].wrapping_add(1))
        }

        let last = run_with_inference_stack("inty-stack-test", || eat(DEPTH, 0));
        // Sanity: the recursion ran to depth and returned a real
        // value rather than crashing. The exact byte depends on
        // wrapping arithmetic; we just need that it returned.
        let _ = last;
    }

    /// The helper must return the closure's value verbatim — it's a
    /// stack band-aid, not a transformer. Trivial but pins the
    /// signature so a future refactor that, e.g., changed the helper
    /// to return `Result<R, JoinError>` would break this test.
    #[test]
    fn worker_returns_closure_value() {
        let v = run_with_inference_stack("inty-return-test", || 42_u64);
        assert_eq!(v, 42);
    }

    /// A panic in the closure must propagate, not be silently
    /// swallowed. The CLI relies on this: if inference panics on
    /// adversarial input, the user must see the panic — not a clean
    /// exit-zero that hides a logic bug.
    #[test]
    #[should_panic(expected = "inference worker panicked")]
    fn worker_propagates_panic() {
        run_with_inference_stack("inty-panic-test", || -> () {
            panic!("boom from inference");
        });
    }
}
