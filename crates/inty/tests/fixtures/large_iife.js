// Synthetic htmx-class IIFE shape.
//
// Stress test for the substitution system: a single large const
// holding several fields, repeatedly accessed and mutated by ~30
// mutually-recursive functions. Mirrors the shape that overflowed
// inty's main-thread stack before the destructive-substitution work
// (commit ae453b4) and hung at any stack size before the union-find
// shortcut in `unify_rows`'s (Open, Open) arm.
//
// Avoids `Array.push` and related row-vs-array unification because
// inty doesn't yet bridge those (`tests/metamorphic.rs` and
// `examples/modules/store.js` exercise that gap separately).
// `tests/htmx_inference_terminates.rs` runs inty on this file with a
// wall-clock budget; an asymptotic regression in `extend_subst` or
// `unify_rows` will time it out.

const state = {
  count: 0,
  total: 0,
  last: 0,
  label: "",
  active: false,
};

function inc() {
  state.count = state.count + 1;
  state.total = state.total + 1;
  state.last = state.count;
}

function dec() {
  state.count = state.count - 1;
  state.total = state.total - 1;
  state.last = state.count;
}

function reset() {
  state.count = 0;
  state.total = 0;
  state.last = 0;
  state.active = false;
}

function activate() {
  state.active = true;
  state.label = "active";
  touch();
}

function deactivate() {
  state.active = false;
  state.label = "inactive";
  touch();
}

function touch() {
  state.total = state.total + 1;
  state.last = state.count;
}

function snapshot() {
  return {
    count: state.count,
    total: state.total,
    active: state.active,
    label: state.label,
  };
}

function summary() {
  return `${state.label}:${state.count}`;
}

function label_of(prefix) {
  return `${prefix}:${state.label}`;
}

function bump_count(n) {
  state.count = state.count + n;
  state.last = state.count;
}

function bump_total(n) {
  state.total = state.total + n;
}

function set_label(s) {
  state.label = s;
}

function double_count() {
  state.count = state.count * 2;
  state.total = state.total * 2;
  state.last = state.count;
}

function halve_count() {
  state.count = state.count - state.count / 2;
  state.last = state.count;
}

function is_active() {
  return state.active;
}

function toggle() {
  if (state.active) {
    deactivate();
  } else {
    activate();
  }
}

function combined() {
  return state.count + state.total;
}

function describe() {
  return `${summary()} ${label_of("@")}`;
}

function with_prefix(p) {
  return `${label_of(p)} count=${state.count}`;
}

function reset_and_set(n, lbl) {
  reset();
  bump_count(n);
  set_label(lbl);
}

function increment_to(n) {
  while (state.count < n) {
    inc();
  }
}

function decrement_to(n) {
  while (state.count > n) {
    dec();
  }
}

function step(n) {
  if (n > 0) {
    bump_count(n);
  } else {
    bump_count(-n);
  }
}

function copy_into(other) {
  other.count = state.count;
  other.total = state.total;
  other.last = state.last;
  other.label = state.label;
  other.active = state.active;
}

function restore_from(other) {
  state.count = other.count;
  state.total = other.total;
  state.last = other.last;
  state.label = other.label;
  state.active = other.active;
}

function diff_from(other) {
  return state.count - other.count;
}

function sum_with(other) {
  return state.count + other.count + state.total + other.total;
}

function eq_to(other) {
  return state.count === other.count && state.total === other.total;
}

function near(other) {
  const a = state.count - other.count;
  const b = state.total - other.total;
  return a * a + b * b;
}

inc();
inc();
activate();
const final_snapshot = snapshot();
