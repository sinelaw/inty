# Coverage: the model's typing rules and inty's

Ground rule 3 of the [roadmap](ROADMAP.md): every rule of the typing
judgement (`HasTypeS`, `Inty/Typing.lean`) names the inty functions it
models, and every function of inty's inference is either named here or
listed as not modelled, with why. `crates/inty/tests/lean_coverage.rs`
checks the tables against both sources: a rule missing here, a function
named here that inty hasn't, or an inference function of inty's
(`infer_…` and `check_…` in `src/infer/features`, `src/infer/mod.rs` and
`src/infer/state.rs`) in neither table fails it.

## The rules

| Lean rule | inty |
|---|---|
| `HasTypeS.lit` | `infer_literal` |
| `HasTypeS.var` | `infer_expr`, `instantiate` |
| `HasTypeS.func` | `infer_function`, `infer_function_with_this`, `infer_body_return_type` |
| `HasTypeS.funcCheck` | `check_function_literal`, `infer_function_expecting`, `infer_body_return_type_expecting` |
| `HasTypeS.app` | `infer_call` |
| `HasTypeS.let_` | `infer_stmt_var`, `infer_stmt_function_decl`, `generalize` |
| `HasTypeS.letPoly` | `check_polymorphic_annotation`, `skolemize` |
| `HasTypeS.assign` | `infer_assign`, `infer_store_target` |
| `HasTypeS.assignCheck` | `infer_assign`, `subsume` (the value subsumed into the variable's type; a rule of the system Sys.inty, not of HasType) |
| `HasTypeS.cond` | `infer_conditional`, `infer_stmt_if` |
| `HasTypeS.unop` | `infer_unary` |
| `HasTypeS.binop` | `infer_binary`, `infer_add` |
| `HasTypeS.ret` | `infer_stmt` |
| `HasTypeS.throw_` | `infer_stmt` |
| `HasTypeS.seq` | `infer_stmt_list`, `infer_stmt_list_inner`, `infer_sequence` |
| `HasTypeS.while_` | `infer_stmt_while` |
| `HasTypeS.break_` | `infer_stmt` |
| `HasTypeS.continue_` | `infer_stmt` |
| `HasTypeS.tryCatch` | `infer_stmt_try` |
| `HasTypeS.tryFinally` | `infer_stmt_try` |
| `HasTypeS.obj` | `infer_object` |
| `HasTypeS.objCheck` | `try_check_object` |
| `HasTypeS.cls` | `infer_function` (a class lowers to a factory function) |
| `HasTypeS.ctor` | `infer_function` |
| `HasTypeS.new_` | `infer_new` |
| `HasTypeS.get` | `infer_member`, `infer_member_on_type` |
| `HasTypeS.set` | `infer_assign`, `infer_store_target` |
| `HasTypeS.spread` | `infer_object`, `merge_spread` |
| `HasTypeS.arr` | `infer_array` |
| `HasTypeS.arrCheck` | `check_expr` |
| `HasTypeS.index` | `infer_computed_member` |
| `HasTypeS.setIndex` | `infer_assign`, `infer_store_target` |
| `HasTypeS.mcall` | `infer_call` |
| `HasTypeS.unwrap` | `infer_nullish_coalesce`, `infer_branching_test`, `apply_narrowing`, `resolve_strip` |
| `HasTypeS.litStr` | `check_expr` |
| `HasTypeS.litBool` | `check_expr` |
| `HasTypeS.caseTag` | `infer_branching_test`, `apply_narrowing`, `test_facts` |
| `HasTypeS.conv` | `unify`, `unroll_named` |
| `HasTypeS.inj` | `check_expr`, `subsume` |
| `HasTypeS.drop` | `infer_discarded` |

Beside the rules: `Expr.assignsMutable` is `check_assignment_target`;
`infer`/`inferProgram` are `infer_expr`, `infer_expr_inner`, `infer_stmt`,
`infer_program` and `infer_program_with_env`.

## inty's functions the model doesn't have

| inty | Why |
|---|---|
| `infer_function_group` | mutually recursive functions (phase 7, strongly connected components) |
| `infer_group_with_deps` | the same |
| `infer_ready_groups` | the same |
| `infer_keyword_call` | Python's keyword arguments |
| `infer_optional_chain` | `?.` (phase 5) |
| `infer_rest_array` | destructuring (remaining syntax) |
| `infer_rest_row` | the same |
| `infer_stmt_do_while` | `do … while` (remaining syntax) |
| `infer_stmt_for` | `for` (remaining syntax) |
| `infer_stmt_for_in` | `for … in` (remaining syntax) |
| `infer_stmt_for_of` | `for … of` (remaining syntax) |
| `infer_stmt_switch` | `switch` (phase 5) |
| `infer_template_literal` | template literals (remaining syntax) |
| `infer_tuple` | tuples (remaining syntax) |
