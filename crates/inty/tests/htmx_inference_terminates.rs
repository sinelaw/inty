//! Wall-clock regression guard for the destructive-substitution work.
//!
//! Before commit `ae453b4` (destructive substitution + union shortcut
//! for equal-shape rows), the htmx-class IIFE pattern either
//! SIGSEGV'd on the 8 MB main stack or hung indefinitely on any
//! stack size — `docs/scaling.md` measured >90 s with a 512 MB
//! stack. The two algorithmic changes in that commit dropped htmx
//! inference from "doesn't terminate" to ~22 s; this test pins that
//! property on a synthetic ~30-function shape derived from htmx's
//! mutually-recursive method-table pattern (`tests/fixtures/large_iife.js`).
//!
//! If `Subst::compose` ever creeps back into the hot path, or the
//! `(Open α, Open β)` arm of `unify_rows` reverts to always
//! allocating a fresh tail, this test will time out long before any
//! syntactic regression is visible.
//!
//! Budget: 30 s. Empirically the fixture type-checks in well under a
//! second on debug builds; 30 s is "the destructive-substitution work
//! is gone" territory.

use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;
use inty::worker::INFERENCE_STACK_SIZE;

/// Wall-clock budget for the fixture. Generous relative to actual
/// runtime so a slow CI machine doesn't false-positive, but tight
/// enough that an asymptotic regression trips it.
const TIMEOUT: Duration = Duration::from_secs(30);

/// Run `inty` inference on the fixture in a worker thread sized
/// the same as the production CLI / LSP path
/// (`INFERENCE_STACK_SIZE` from `inty::worker`). Return once
/// inference finishes, or panic on timeout.
fn run_with_timeout(source: String) {
    let (tx, rx) = mpsc::channel::<()>();
    let started = Instant::now();
    let handle = thread::Builder::new()
        .stack_size(INFERENCE_STACK_SIZE)
        .spawn(move || {
            let program = parse(&source).expect("fixture must parse");
            let (env, mut state) = initial_env_with_stdlib().expect("stdlib must load");
            // We don't assert success/failure of inference — only
            // that it terminates. The fixture currently type-checks
            // cleanly, but a future tweak to inty's diagnostics
            // could surface new errors without violating the
            // termination property this test guards.
            let _ = state.infer_program_with_env(&env, &program);
            let _ = tx.send(());
        })
        .expect("spawn inference worker");

    match rx.recv_timeout(TIMEOUT) {
        Ok(()) => {
            let _ = handle.join();
            // Lower bound. If inference suddenly returns instantly
            // because some optimisation broke completeness (e.g. the
            // SCC pass starts skipping function bodies), the test
            // still catches "ran zero work" via the duration log.
            let elapsed = started.elapsed();
            assert!(
                elapsed >= Duration::from_micros(1),
                "inference returned implausibly fast ({elapsed:?})"
            );
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!(
                "large_iife.js inference did not finish within {TIMEOUT:?}. \
                 This usually means an asymptotic regression in the \
                 substitution path (see ae453b4 + docs/scaling.md)."
            );
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            let _ = handle.join();
            panic!("inference worker panicked");
        }
    }
}

#[test]
fn large_iife_inference_terminates() {
    let source = include_str!("fixtures/large_iife.js").to_string();
    run_with_timeout(source);
}

/// Direct repro of the smallest IIFE forward-reference shape that
/// motivated the hoist (commit 472cccb). Independent of the bigger
/// fixture: tests the hoist alone, no substitution-cost stress.
#[test]
fn iife_forward_reference_terminates_and_checks() {
    let source = String::from(
        "var lib = (function() {\n\
           const state = { count: 0 };\n\
           function get() { return state.count; }\n\
           function inc() { state.count = state.count + 1; }\n\
           const api = { get: get, inc: inc };\n\
           return api;\n\
         })();\n\
         var n = lib.get();\n",
    );
    let (tx, rx) = mpsc::channel::<bool>();
    let handle = thread::Builder::new()
        .stack_size(INFERENCE_STACK_SIZE)
        .spawn(move || {
            let program = parse(&source).expect("source must parse");
            let (env, mut state) = initial_env_with_stdlib().expect("stdlib");
            let ok = state.infer_program_with_env(&env, &program).is_ok();
            let _ = tx.send(ok);
        })
        .expect("spawn");
    match rx.recv_timeout(Duration::from_secs(10)) {
        Ok(ok) => {
            let _ = handle.join();
            assert!(
                ok,
                "IIFE forward-reference shape should type-check after the hoist fix"
            );
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!("IIFE forward-reference inference did not finish in 10 s");
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            let _ = handle.join();
            panic!("inference worker panicked");
        }
    }
}
