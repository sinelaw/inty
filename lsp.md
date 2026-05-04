# Inty LSP — design

Status: design doc, work-in-progress.

## Goals

Ship a Language Server Protocol implementation for mquickjs source files
that delegates all type reasoning to the existing `inty` library. Expose
it as a sub-command of the project's CLI binary so editors can launch it
with a single command (e.g. `inty lsp`).

## Feature set

v1 (already shipped, hand-rolled JSON):

1. **Diagnostics** (`textDocument/publishDiagnostics`) — surface lex,
   parse, and type errors as red squigglies.
2. **Hover** (`textDocument/hover`) — show the inferred type of the
   identifier under the cursor.
3. **Document lifecycle** (`textDocument/didOpen`, `didChange`, `didSave`,
   `didClose`) — keep an in-memory mirror of every open file and
   re-check on every change.

v2 (current):

4. **Go to definition** (`textDocument/definition`) — jump from an
   identifier reference to its binding site.
5. **Rename** (`textDocument/rename`) — rename a binding and every
   reference to it. Also propagates across open files via imports
   (see "Cross-file rename" below).
6. **Completions** (`textDocument/completion`) — list identifiers in
   scope (and properties of an object after a `.`).
7. **Signature help** (`textDocument/signatureHelp`) — show the
   parameter list of the function being called, with the cursor's
   active parameter highlighted. Supports both bare-identifier
   callees (`foo(...)`) and member chains (`obj.method(...)`,
   `a.b.c.method(...)`).
8. **Inlay hints** (`textDocument/inlayHint`) — render `: <Type>`
   ghost labels after each binding's name (var / let / const /
   function declaration / function parameter), pulled from the
   inferred type.

## Block scoping

The parser distinguishes `var` from `let` (since v2). Inference treats
them identically; the resolver gives each block its own scope so that
`let x` and `const x` declarations bind only inside the enclosing block,
while `var x` continues to hoist to the enclosing function/module
scope. Strict TDZ (rejecting use-before-`let`-declaration) is **not**
modelled — that's a control-flow analysis we don't need for go-to-def
/ rename / completion correctness.

## Per-position type lookup

Hover and inlay hints used to look every binding up by name in the
program's *final* env. That broke shadowing: an inner `let x = "hi"`
hidden by an outer `var x = 1` would surface the outer's type. v2:

- The AST's function/method/arrow `params` field is now
  `Vec<Param>` where `Param { name, span }` — every parameter has a
  unique source span.
- Inference records `binding span -> Type` in `InferState.decl_types`
  at every binding site (var declarators, function declarations,
  function parameters). The key for function declarations is the
  *name* offset (not the `function` keyword), matching the
  resolver's go-to-def target.
- The hover handler resolves `cursor → def_span` via the resolver
  (which is scope-aware and picks the innermost shadow), then looks
  the type up by `def_span` in `decl_types`. Falls back to env
  lookup for binding kinds we don't yet record per-span (catch
  params, named function expressions).

## Cross-file rename

The server holds a `documents: HashMap<Uri, Document>`. When the user
renames a top-level binding `foo` exported from file A:

1. Build same-file edits as before (def site + every use).
2. For each other open document B:
   - Walk its imports via `Analysis::imports()`.
   - For each import where:
     - the resolved module URI of the import equals A's URI, AND
     - `import.imported == "foo"`,
   - emit a `TextEdit` for the imported-name span.
   - If the import is *not* aliased (the local equals the imported),
     also emit edits for every use of the local binding (via B's
     resolver's `uses_of`).
   - If aliased (`{ foo as bar }`), only the `foo` portion is
     rewritten; `bar` and its uses stay — the alias is B's local
     choice.

Module path resolution is a small `file://`-only helper in
`server.rs` that joins relative paths against the importer's
directory and normalises `.` / `..` segments. Limitation: only
currently-open files are scanned; we don't crawl the filesystem for
unopened importers.

Still out of scope: filesystem-crawling cross-file refactors (we
only see open files), find-references across files, document symbols,
code actions, semantic tokens, formatting, strict TDZ for `let`.

## Dependency change: switch to `lsp-server` + `lsp-types`

v1 hand-rolled the protocol on top of `serde_json::Value`. Adding the
v2 features makes that increasingly painful: each new method needs
hand-written request extraction, each new response needs hand-shaped
JSON, and a typo silently breaks clients.

v2 replaces `protocol.rs` and most of `server.rs`'s message dispatch
with the rust-analyzer-team-maintained pair:

- **`lsp-server`** — sync, stdio-based message loop. `Connection::stdio()`
  + `connection.handle_shutdown(&req)` covers the lifecycle. No async
  runtime, no Tokio, fits the existing CPU-bound checker.
- **`lsp-types`** — `serde`-derived structs for every LSP request,
  notification, and parameter. Typos become compile errors.

Net dep delta: `lsp-server`, `lsp-types`, `crossbeam-channel`, `serde`,
plus the existing `serde_json`. No async runtime added.

## Name resolution

The four new features all need scope-aware identifier resolution, which
inty itself doesn't expose (its `TypeEnv` knows what each name's type
is, but not what `Span` originally bound it). v2 adds a separate pass
in `crates/inty-lsp/src/resolver.rs`:

```rust
pub struct Resolution {
    /// Identifier-use span -> binding-site span.
    refs: HashMap<Span, Span>,
    /// Binding-site span -> info about the binding.
    defs: HashMap<Span, DefInfo>,
    /// Binding-site span -> all use spans (for rename, find-refs).
    uses: HashMap<Span, Vec<Span>>,
    /// For completion: scope chain at every position. Stored as a flat
    /// list of (span, scope_id), sorted by inclusion; for a query we
    /// pick the smallest containing entry.
    scopes: Vec<(Span, ScopeId)>,
    scope_chain: HashMap<ScopeId, Vec<ScopeId>>,
    scope_bindings: HashMap<ScopeId, Vec<(String, Span)>>,
}

pub enum DefInfo {
    Var,       // var x
    Const,     // const x
    Param,     // function parameter
    Function,  // function declaration
    Catch,     // catch (e)
}
```

The pass walks the AST top-down with a scope stack:

- **Function entry** opens a new scope. Pre-scan the body for `var X`
  (anywhere except inside nested functions) and `function X` (any
  block) and add them to the function scope. Then add params. Then
  walk.
- **Block entry** opens a new scope only if the block contains any
  `const` declarations (inty's mquickjs subset doesn't fully
  distinguish `let`; treat `var`/`const` as the two relevant kinds).
- **Catch clause** opens a one-binding scope for the caught name.
- **`Expr::Ident { name, span }`** in non-target position resolves
  against the scope chain, innermost first; record an entry in
  `refs` and `uses`.

Limitations for v1 of the resolver:

- No real let/TDZ semantics; same-named `var` shadowing across blocks
  resolves to the function-scope binding.
- We don't follow imports; cross-file rename / definition is out of
  scope for now.

## Per-feature wiring

### Go to definition

```
textDocument/definition (params: TextDocumentPositionParams)
  -> Option<Location>
```

1. Convert `(line, character)` to a byte offset.
2. Find the smallest `Expr::Ident` whose span contains the offset.
3. Look up `resolution.refs[span]` for the def span.
4. Return `Location { uri, range: span_to_range(def_span) }`.

If the cursor is on the binding site itself, return that same site
(so VS Code's "Go to definition" doesn't no-op silently).

### Rename

```
textDocument/rename (params: RenameParams { new_name, position })
  -> WorkspaceEdit
```

1. Resolve the cursor to a definition span (either the cursor is on
   the def, or `resolution.refs[use_span]` gives the def).
2. Validate the new name is a legal mquickjs identifier (regex
   `[a-zA-Z_$][a-zA-Z0-9_$]*` and not a reserved word).
3. Build a `WorkspaceEdit` with one `TextEdit` per use span and one for
   the def span itself, all replacing the old text with `new_name`.
4. Return the edit; the editor applies it atomically.

We also implement `textDocument/prepareRename` returning the range of
the identifier under the cursor (or `null` if it isn't an identifier),
so editors can show the rename UI inline.

### Completions

```
textDocument/completion (params: CompletionParams { position, context })
  -> Vec<CompletionItem>
```

Two cases:

1. **Member completion** — if the position is right after a `.` on a
   `Member` or stalled-parser member access, look up the type of the
   object expression. If it's a row type, return the row's labels as
   completion items, each with its field type as `detail`.
2. **Identifier completion** — otherwise, return every binding visible
   in the resolver's scope chain at that position. `kind` is mapped
   from `DefInfo` (Function -> `Function`, Param -> `Variable`, …).

For v1 we won't filter by prefix; the editor does that fuzzy match.

### Signature help

```
textDocument/signatureHelp (params: TextDocumentPositionParams)
  -> Option<SignatureHelp>
```

1. Walk the AST and find the innermost `Expr::Call { callee, arguments, span }`
   whose span contains the cursor *and* whose argument list (the part
   between `(` and the matching `)`) brackets the cursor.
2. Resolve the type of `callee`:
   - If `callee` is `Expr::Ident { name }`, look up `name` in the env
     active at the call's position.
   - If it's a member access we punt for v1.
3. Apply the substitution, instantiate, and read parameter and return
   types from the resulting function type.
4. Build `SignatureInformation` with one `ParameterInformation` per
   parameter.
5. Determine `activeParameter` by counting top-level commas in the
   argument list source between `(` and the cursor.

If the call's callee type isn't a function (or isn't resolvable),
return `null`.

## Capability negotiation update

The `initialize` reply now advertises:

```json
{
  "textDocumentSync": 1,
  "hoverProvider": true,
  "definitionProvider": true,
  "renameProvider": { "prepareProvider": true },
  "completionProvider": { "triggerCharacters": ["."] },
  "signatureHelpProvider": { "triggerCharacters": ["(", ","] }
}
```

## Testing strategy update

v1's `tests/handshake.rs` already covers diagnostics + hover via JSON
round-trips. After the migration to `lsp-types` we keep the round-trip
shape but use the typed structs to build messages. New tests cover:

- definition: open file, request definition on a use, assert location
  matches the binding's span.
- rename: open file with two uses + one def, request rename, assert
  the resulting `WorkspaceEdit` has three text edits with correct
  ranges.
- completion: open file with several bindings, request completion,
  assert all visible names appear in the result.
- signature help: open file with a function, request signature help
  inside a call, assert the parameter list and active index.



## Workspace layout

The repository becomes a Cargo workspace with three sub-crates. Until
this change the library and binary lived together at the workspace root;
now nothing builds at the root.

```
typed-js/
├── Cargo.toml                  # [workspace] only — no [package]
├── Cargo.lock
├── crates/
│   ├── inty/                # library: type inference / checking
│   │   ├── Cargo.toml
│   │   ├── stdlib/             # core.d.js, dom.d.js (include_str! targets)
│   │   ├── tests/              # integration + metamorphic tests
│   │   └── src/                # everything that was in src/ (minus main.rs)
│   ├── inty-lsp/            # library: LSP server
│   │   ├── Cargo.toml
│   │   └── src/lib.rs
│   └── inty-cli/            # binary: top-level entry point
│       ├── Cargo.toml
│       └── src/main.rs         # dispatches to either inference or `lsp`
└── ... (docs, examples, web)
```

Why three crates and not two:

- `inty` is reused by tests, the WASM build, downstream consumers, and
  the LSP. It must not pull in any LSP/JSON-RPC dependencies.
- `inty-lsp` depends on `inty` and on `serde_json` for protocol
  framing. Other tools (e.g. an editor that embeds the server in-process)
  can depend on it directly without going through the binary.
- `inty-cli` is the user-facing entry point. It owns argument parsing,
  stdin/stdout wiring, and the `lsp` sub-command dispatch. Keeping it
  separate means the library crates compile and ship without the CLI's
  argument layer.

The WASM `cdylib` lives on the `inty` crate (the `wasm` feature already
gates it). The web build script's `wasm-pack build` invocation will need
to point at `crates/inty` instead of the workspace root — a one-line
fix in `web/build.sh`.

## CLI surface

Today the CLI takes a file (or `-`) and runs inference. After the
sub-crate split, the binary keeps that default behaviour and adds one
new sub-command:

```
inty <file.js>          # unchanged: type-check a file
inty -                  # unchanged: type-check stdin
inty lsp                # NEW: speak LSP on stdin/stdout
inty lsp --stdio        # explicit form, same as above
```

Detection: if the first positional argument is `lsp`, dispatch to the LSP
server; otherwise the existing argument parser runs unchanged. The `lsp`
sub-command takes its own option set (currently just `--stdio`, which is
the default and only transport for v1).

## LSP server design

### Transport

Stdio only. LSP framing is the standard HTTP-style header block:

```
Content-Length: <n>\r\n
\r\n
<n bytes of UTF-8 JSON>
```

A small reader (`read_message`) parses headers, reads the exact byte
count, and returns a `serde_json::Value`. A small writer (`write_message`)
serialises a `Value`, prefixes the header, and flushes. No async runtime,
no `tower`, no `lsp-server` crate — just `std::io::stdin().lock()` and
`std::io::stdout().lock()` plus `serde_json`.

### State

```rust
struct Server {
    documents: HashMap<Url, Document>,
    shutdown_requested: bool,
}

struct Document {
    text: String,
    version: i64,
    /// Cached inference result for hover / future requests.
    analysis: Option<Analysis>,
}

struct Analysis {
    /// Decorated AST, so we can map a (line, character) cursor position
    /// to an inferred type for hover.
    decorated: Program,
    /// Errors collected during the last check. Translated to LSP
    /// diagnostics on demand.
    errors: Vec<IntyError>,
}
```

`documents` is keyed by URI so `didChange` can locate the doc. Versions
are echoed back in `publishDiagnostics` so the client can drop stale
results.

### Message handling

A single-threaded loop reads one message at a time. Each request maps to
one handler; notifications return `()` and may publish diagnostics as a
side effect. v1 doesn't need cancellation — checks are fast enough that
running them synchronously is fine.

| Method                          | Kind         | Action                                                |
| ------------------------------- | ------------ | ----------------------------------------------------- |
| `initialize`                    | request      | Respond with server capabilities (see below).         |
| `initialized`                   | notification | No-op.                                                |
| `shutdown`                      | request      | Set `shutdown_requested`, respond `null`.             |
| `exit`                          | notification | Exit 0 if shutdown was requested, else 1.             |
| `textDocument/didOpen`          | notification | Insert document, run inference, publish diagnostics.  |
| `textDocument/didChange`        | notification | Replace text (full sync), re-check, publish.          |
| `textDocument/didSave`          | notification | No-op (already checked on change).                    |
| `textDocument/didClose`         | notification | Drop document, publish empty diagnostics for it.      |
| `textDocument/hover`            | request      | Look up type at position, respond `Hover \| null`.    |
| anything else                   | request      | Respond with `MethodNotFound` (-32601).               |
| anything else                   | notification | Ignore.                                               |

### Server capabilities

```json
{
  "capabilities": {
    "textDocumentSync": 1,        // full sync — simplest, fast enough
    "hoverProvider": true,
    "positionEncoding": "utf-16"  // LSP default; UTF-8 needs negotiation
  },
  "serverInfo": { "name": "inty-lsp", "version": "<crate version>" }
}
```

Full document sync (mode `1`) avoids implementing incremental edit
application in v1. The cost is re-sending the whole file on each
keystroke, which is fine for the file sizes inty targets.

### Position encoding

LSP positions are `(line, character)` — zero-based — where `character`
counts UTF-16 code units by default. Inty stores byte offsets in
`Span`. The LSP layer therefore needs two conversions:

- `byte_to_position(text, offset) -> Position` (for diagnostics)
- `position_to_byte(text, position) -> Option<usize>` (for hover)

Both walk the document text once per call and count UTF-16 code units per
char. We can advertise UTF-8 once a wider client base supports it via
`positionEncoding`; until then UTF-16 is the only safe default.

### Diagnostics

For each `IntyError` collected during inference:

- Map the error's `Span` to an LSP `Range`.
- Severity is always `Error` (1) for v1; warnings can be added once
  `InferState::warnings` is plumbed through.
- `source` is `"inty"`. `code` is the error variant name (e.g.
  `"UndefinedVariable"`), useful for filtering in the editor.
- `message` is the same human-readable string the CLI prints, sans
  ariadne formatting — the editor draws its own underline.

`publishDiagnostics` is sent unconditionally on every check, including
when the error list is empty (so previous diagnostics get cleared).

### Hover

Two pieces:

1. **Position lookup.** Convert the LSP `(line, character)` to a byte
   offset. Walk the decorated AST and find the smallest expression whose
   span contains that offset. (For v1, "smallest containing identifier
   or expression" is good enough; we don't need a binding-aware
   resolution.)
2. **Type extraction.** The decorator already attaches inferred types to
   AST nodes via `decorate_with_types`. Read the type, format it with
   `PrettyContext`, return as a Markdown code block:

   ```
   ```ts
   <pretty-printed type>
   ```
   ```

If no expression contains the cursor (whitespace, comment, etc.) respond
with `null`.

## Dependencies

`inty-lsp` adds:

- `serde_json = "1"` — JSON parsing/encoding via `Value`. We don't
  derive any structs in v1; the protocol surface is small enough to
  read/write fields by name.

`inty-cli` adds:

- a path dep on `inty-lsp`
- a path dep on `inty`

The existing `inty` crate keeps its current dependency set
(`thiserror`, `ariadne`, plus the optional WASM trio).

## Testing strategy

The LSP crate gets a small `tests/` directory with synchronous
round-trip tests:

- Spawn an in-process `Server`, feed it a sequence of LSP messages via
  in-memory channels, assert on the responses.
- Cover: initialize handshake, didOpen → publishDiagnostics on a known
  bad file, hover on a known identifier in a known good file, shutdown
  → exit.

No editor-integration tests in v1; those can live downstream.

## Migration notes

- `src/main.rs`'s argument parser moves into `crates/inty-cli/src/`.
  Its `--lib`, `--no-stdlib`, `--no-color` options stay untouched.
- The `tests/` directory at the workspace root moves into
  `crates/inty/tests/` so it can `use inty::...` against the
  relocated library.
- `web/build.sh` learns the new path: `wasm-pack build crates/inty
  --target web --out-dir ../../web/pkg --features wasm`.
- The CI workflow (`.github/workflows/rust.yml`) does not need to
  change: `cargo build` and `cargo test` at the workspace root build
  and test all members.
