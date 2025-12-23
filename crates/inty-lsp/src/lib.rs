//! Language Server Protocol implementation backed by [`inty`].
//!
//! The crate ships two front-ends over a single [`Analysis`] core:
//!
//! - With the `stdio` feature (on by default), [`run_stdio`] runs an
//!   LSP server over stdin/stdout using `lsp-server` and `lsp-types`.
//!   Supported protocol features:
//!   - `initialize` / `shutdown` / `exit`
//!   - `textDocument/didOpen`, `didChange`, `didSave`, `didClose`
//!   - `textDocument/publishDiagnostics`
//!   - `textDocument/hover`
//!   - `textDocument/definition`
//!   - `textDocument/rename` (with `textDocument/prepareRename`)
//!   - `textDocument/completion`
//!   - `textDocument/signatureHelp`
//!   - `textDocument/inlayHint`
//!
//! - With the `wasm` feature, the same [`Analysis`] is exposed via
//!   `wasm-bindgen` so the web playground can ask hover and inlay-hint
//!   queries directly — no JSON-RPC, but the same answers an editor sees.

mod analysis;
mod resolver;

#[cfg(feature = "stdio")]
mod convert;
#[cfg(feature = "stdio")]
mod server;

#[cfg(feature = "wasm")]
mod wasm;

pub use analysis::Analysis;

#[cfg(feature = "stdio")]
pub use server::{run_stdio, Server};
