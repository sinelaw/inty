//! Language Server Protocol implementation backed by [`minfern`].
//!
//! The server speaks LSP over stdio. Supported features in this version:
//!
//! - `initialize` / `shutdown` / `exit`
//! - `textDocument/didOpen`, `didChange`, `didSave`, `didClose`
//! - `textDocument/publishDiagnostics` (lex / parse / type errors)
//! - `textDocument/hover` (inferred type for the identifier under the cursor)
//!
//! Embed the server with [`Server::new`] for tests, or call [`run_stdio`]
//! to wire it to actual stdin/stdout.

use std::io::{self, BufReader};

mod analysis;
mod convert;
mod protocol;
mod server;

pub use analysis::Analysis;
pub use server::Server;

/// Run the LSP server on stdin/stdout. Returns the exit code the binary
/// should propagate (0 on clean shutdown, 1 if the client exited without
/// the proper handshake).
pub fn run_stdio() -> io::Result<i32> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let reader = BufReader::new(stdin.lock());
    let writer = stdout.lock();
    Server::new(reader, writer).run()
}
