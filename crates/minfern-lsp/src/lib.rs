//! Language Server Protocol implementation backed by [`minfern`].
//!
//! Built on `lsp-server` (sync stdio transport) and `lsp-types` (typed
//! protocol structs). Supported features:
//!
//! - `initialize` / `shutdown` / `exit`
//! - `textDocument/didOpen`, `didChange`, `didSave`, `didClose`
//! - `textDocument/publishDiagnostics`
//! - `textDocument/hover`
//! - `textDocument/definition`
//! - `textDocument/rename` (with `textDocument/prepareRename`)
//! - `textDocument/completion`
//! - `textDocument/signatureHelp`

mod analysis;
mod convert;
mod resolver;
mod server;

pub use analysis::Analysis;
pub use server::{run_stdio, Server};
