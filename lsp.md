# Minfern LSP — design

Status: design doc, work-in-progress.

## Goals

Ship a Language Server Protocol implementation for mquickjs source files
that delegates all type reasoning to the existing `minfern` library. Expose
it as a sub-command of the project's CLI binary so editors can launch it
with a single command (e.g. `minfern lsp`).

The first cut targets the most common LSP features programmers expect from
a typed language:

1. **Diagnostics** (`textDocument/publishDiagnostics`) — surface lex,
   parse, and type errors as red squigglies.
2. **Hover** (`textDocument/hover`) — show the inferred type of the
   identifier or expression under the cursor.
3. **Document lifecycle** (`textDocument/didOpen`, `didChange`, `didSave`,
   `didClose`) — keep an in-memory mirror of every open file and re-check
   on every change.

Out of scope for v1 (but the architecture is designed to allow them
later): completions, go-to-definition, find-references, document
symbols, rename, code actions, semantic tokens, signature help.

## Workspace layout

The repository becomes a Cargo workspace with three sub-crates. Until
this change the library and binary lived together at the workspace root;
now nothing builds at the root.

```
typed-js/
├── Cargo.toml                  # [workspace] only — no [package]
├── Cargo.lock
├── crates/
│   ├── minfern/                # library: type inference / checking
│   │   ├── Cargo.toml
│   │   ├── stdlib/             # core.d.js, dom.d.js (include_str! targets)
│   │   ├── tests/              # integration + metamorphic tests
│   │   └── src/                # everything that was in src/ (minus main.rs)
│   ├── minfern-lsp/            # library: LSP server
│   │   ├── Cargo.toml
│   │   └── src/lib.rs
│   └── minfern-cli/            # binary: top-level entry point
│       ├── Cargo.toml
│       └── src/main.rs         # dispatches to either inference or `lsp`
└── ... (docs, examples, web)
```

Why three crates and not two:

- `minfern` is reused by tests, the WASM build, downstream consumers, and
  the LSP. It must not pull in any LSP/JSON-RPC dependencies.
- `minfern-lsp` depends on `minfern` and on `serde_json` for protocol
  framing. Other tools (e.g. an editor that embeds the server in-process)
  can depend on it directly without going through the binary.
- `minfern-cli` is the user-facing entry point. It owns argument parsing,
  stdin/stdout wiring, and the `lsp` sub-command dispatch. Keeping it
  separate means the library crates compile and ship without the CLI's
  argument layer.

The WASM `cdylib` lives on the `minfern` crate (the `wasm` feature already
gates it). The web build script's `wasm-pack build` invocation will need
to point at `crates/minfern` instead of the workspace root — a one-line
fix in `web/build.sh`.

## CLI surface

Today the CLI takes a file (or `-`) and runs inference. After the
sub-crate split, the binary keeps that default behaviour and adds one
new sub-command:

```
minfern <file.js>          # unchanged: type-check a file
minfern -                  # unchanged: type-check stdin
minfern lsp                # NEW: speak LSP on stdin/stdout
minfern lsp --stdio        # explicit form, same as above
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
    errors: Vec<MinfernError>,
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
  "serverInfo": { "name": "minfern-lsp", "version": "<crate version>" }
}
```

Full document sync (mode `1`) avoids implementing incremental edit
application in v1. The cost is re-sending the whole file on each
keystroke, which is fine for the file sizes minfern targets.

### Position encoding

LSP positions are `(line, character)` — zero-based — where `character`
counts UTF-16 code units by default. Minfern stores byte offsets in
`Span`. The LSP layer therefore needs two conversions:

- `byte_to_position(text, offset) -> Position` (for diagnostics)
- `position_to_byte(text, position) -> Option<usize>` (for hover)

Both walk the document text once per call and count UTF-16 code units per
char. We can advertise UTF-8 once a wider client base supports it via
`positionEncoding`; until then UTF-16 is the only safe default.

### Diagnostics

For each `MinfernError` collected during inference:

- Map the error's `Span` to an LSP `Range`.
- Severity is always `Error` (1) for v1; warnings can be added once
  `InferState::warnings` is plumbed through.
- `source` is `"minfern"`. `code` is the error variant name (e.g.
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

`minfern-lsp` adds:

- `serde_json = "1"` — JSON parsing/encoding via `Value`. We don't
  derive any structs in v1; the protocol surface is small enough to
  read/write fields by name.

`minfern-cli` adds:

- a path dep on `minfern-lsp`
- a path dep on `minfern`

The existing `minfern` crate keeps its current dependency set
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

- `src/main.rs`'s argument parser moves into `crates/minfern-cli/src/`.
  Its `--lib`, `--no-stdlib`, `--no-color` options stay untouched.
- The `tests/` directory at the workspace root moves into
  `crates/minfern/tests/` so it can `use minfern::...` against the
  relocated library.
- `web/build.sh` learns the new path: `wasm-pack build crates/minfern
  --target web --out-dir ../../web/pkg --features wasm`.
- The CI workflow (`.github/workflows/rust.yml`) does not need to
  change: `cargo build` and `cargo test` at the workspace root build
  and test all members.
