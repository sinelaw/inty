# Regression checks over the example and test programs

Two tests in `crates/inty-cli/tests/` run the `inty` binary over every
JavaScript program in the repository that is a program: the files under
`examples/`, `crates/inty/tests/*.js` and `crates/inty/tests/fixtures/`,
`crates/inty-go/tests/programs/` and `crates/inty-go/tests/io/`, and the
probes in `crates/inty-cli/tests/soundness/` (the list is `DIRS` in
`tests/corpus/mod.rs`; a new `.js` file in one of these directories joins
both checks). `cargo test` runs them, and so does CI (`.github/workflows/rust.yml`).

## Accepted means it runs (`tests/soundness.rs`)

For each program inty accepts, the test runs it under Node
(`tests/soundness/run.mjs`: strict mode, as inty assumes; a file with
`import`/`export` as a module) and fails if Node exits with an error: a
`TypeError` or `ReferenceError` in a program inty accepted is a hole in
the checker.

```text
cargo test -p inty-cli --test soundness -- --nocapture
INTY_SOUNDNESS_FILTER=soundness/ cargo test -p inty-cli --test soundness -- --nocapture
```

What a program expects is said by directives, `// inty: DIRECTIVE` lines in
a probe, or `PATH DIRECTIVE` lines in `tests/soundness/corpus.txt` for the
other programs (so they stay as they are):

| Directive | Meaning |
| --- | --- |
| `reject` | inty must reject it (a probe of a hole: it would fail under Node) |
| `accept` | inty must accept it, and Node run it |
| `no-run: REASON` | don't run it: it needs a browser's DOM, command-line arguments, ... |
| `throws: REASON` | it ends in an error of its own on purpose; a native error still fails |
| `known-failing: REASON` | fails today for the bug REASON names: reported, not failing the test; a pass fails it, so the marker goes with the bug |

Nothing is left out silently: each program that isn't run is listed with
its reason in the test's output. To probe a bug, add a small program to
`tests/soundness/` with `// inty: reject` (or `accept`) and, until it is
fixed, `// inty: known-failing: WHAT IS WRONG`.

Without Node (`node`, or `INTY_NODE`) the runs are skipped, but on CI the
test fails instead.

## Output snapshots: no unexplained change (`tests/output_snapshots.rs`)

`crates/inty-cli/tests/snapshots/PATH.out` holds what inty prints for the
program at PATH: the exit status, stdout (the program printed back with
the inferred types as annotations) and stderr (the diagnostics) of `inty
PATH`, and for a module that exports something, of `inty declarations PATH`
(the run time and the workspace's path are normalised). The test fails on
any difference, on a program with no snapshot and on a snapshot of no
program.

This is the before/after comparison of a pull request: the snapshots on
its base are the old binary's output over every program, so a change in
what inty infers or reports for any of them fails CI, unless the pull
request updates the snapshots, and then the change is in its diff for
review. After a change meant to affect the output:

```text
INTY_BLESS=1 cargo test -p inty-cli --test output_snapshots
git diff crates/inty-cli/tests/snapshots    # review, then commit with the change
```

(`INTY_BLESS` adds and removes snapshot files as programs come and go, as
it rewrites `tests/golden/*/expected.txt` in `tests/diagnostics_golden.rs`.)

Why snapshots rather than a CI job that builds the base and the head and
diffs their output: the comparison is then an ordinary test, run locally
the same way as on CI, with no second build; the expected change is
reviewed as a diff of the files it changes, in the pull request itself,
rather than as a separate expected-diff file that has to be kept in step;
and merging two pull requests that both change the output shows up as a
conflict (or a failing test) instead of passing unnoticed.
