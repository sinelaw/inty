//! Regression guard: the LSP `update_document` path must route
//! inference through the 64 MB worker helper, not run inline on
//! the LSP server thread.
//!
//! Why: the LSP server is spawned via `thread::spawn`
//! (`crates/inty-lsp/tests/handshake.rs:27`), which uses the
//! default 2 MB stack — even smaller than the 8 MB main-thread
//! stack the CLI used to overflow on. Inside `update_document`,
//! `Analysis::check` runs lex → parse → infer; recursive-descent
//! parsing of a moderately-nested expression alone consumes the 2
//! MB budget. A depth-100 nested-array literal (~200 bytes of
//! source) was empirically measured to SIGSEGV on a 2 MB stack and
//! to complete cleanly on a 64 MB stack — exactly the boundary the
//! worker helper enforces.
//!
//! Without the worker wrap in `update_document`, this test aborts
//! the test binary with `fatal runtime error: stack overflow`
//! before any `publishDiagnostics` message reaches the client. With
//! the wrap, the deep input is checked inside a 64 MB worker, the
//! parse error (the depth itself is benign JS but produces no
//! useful program for inference) is published, and the test ends
//! cleanly.
//!
//! Lives in its own integration-test file so a regression that
//! reintroduces the SIGSEGV crashes only this binary, not the rest
//! of the inty-lsp test suite.

use std::thread;
use std::time::{Duration, Instant};

use inty_lsp::Server;
use lsp_server::{Connection, Message, Notification, Request, RequestId};
use lsp_types::notification::{
    DidOpenTextDocument, Initialized, Notification as LspNotification, PublishDiagnostics,
};
use lsp_types::request::{Initialize, Request as LspRequest, Shutdown};
use lsp_types::{
    ClientCapabilities, DidOpenTextDocumentParams, InitializeParams, PublishDiagnosticsParams,
    TextDocumentItem, Uri,
};
use serde::{de::DeserializeOwned, Serialize};

fn boot() -> (Connection, thread::JoinHandle<()>) {
    // Default `thread::spawn` stack — 2 MB on Linux, smaller on
    // some other targets. The point of this test is that
    // `update_document` survives input that would otherwise
    // overflow whatever stack happens to be here.
    let (server_conn, client_conn) = Connection::memory();
    let handle = thread::spawn(move || {
        Server::new(server_conn).run().unwrap();
    });
    (client_conn, handle)
}

fn req<R: LspRequest>(id: i32, params: R::Params) -> Request
where
    R::Params: Serialize,
{
    Request::new(RequestId::from(id), R::METHOD.to_string(), params)
}

fn not<N: LspNotification>(params: N::Params) -> Notification
where
    N::Params: Serialize,
{
    Notification::new(N::METHOD.to_string(), params)
}

fn expect_response<R: DeserializeOwned>(client: &Connection, id: i32) -> R {
    loop {
        let msg = client.receiver.recv().expect("recv");
        if let Message::Response(resp) = msg {
            if resp.id == RequestId::from(id) {
                let value = resp.result.expect("response result");
                return serde_json::from_value(value).expect("parse response");
            }
        }
    }
}

fn handshake(client: &Connection) {
    client
        .sender
        .send(Message::Request(req::<Initialize>(
            1,
            InitializeParams {
                capabilities: ClientCapabilities::default(),
                ..Default::default()
            },
        )))
        .unwrap();
    let _ = expect_response::<lsp_types::InitializeResult>(client, 1);
    client
        .sender
        .send(Message::Notification(not::<Initialized>(
            lsp_types::InitializedParams {},
        )))
        .unwrap();
}

fn shutdown(client: Connection, handle: thread::JoinHandle<()>) {
    client
        .sender
        .send(Message::Request(req::<Shutdown>(99, ())))
        .unwrap();
    let _ = expect_response::<serde_json::Value>(&client, 99);
    client
        .sender
        .send(Message::Notification(Notification::new(
            "exit".to_string(),
            (),
        )))
        .unwrap();
    drop(client);
    handle.join().unwrap();
}

fn open_doc(client: &Connection, uri: &Uri, text: String) {
    client
        .sender
        .send(Message::Notification(not::<DidOpenTextDocument>(
            DidOpenTextDocumentParams {
                text_document: TextDocumentItem {
                    uri: uri.clone(),
                    language_id: "javascript".to_string(),
                    version: 1,
                    text,
                },
            },
        )))
        .unwrap();
}

/// Wait for a `publishDiagnostics` message for `uri` with a wall-
/// clock budget. The default LSP server thread has a 2 MB stack;
/// without the worker wrap in `update_document`, a deep input
/// SIGSEGVs and no notification ever arrives — the wait would
/// hang. The budget surfaces that as a test failure instead.
fn wait_for_diagnostics(
    client: &Connection,
    uri: &Uri,
    budget: Duration,
) -> Option<Vec<lsp_types::Diagnostic>> {
    let deadline = Instant::now() + budget;
    loop {
        let remaining = deadline.checked_duration_since(Instant::now())?;
        let msg = match client.receiver.recv_timeout(remaining) {
            Ok(m) => m,
            Err(_) => return None,
        };
        if let Message::Notification(n) = msg {
            if n.method == PublishDiagnostics::METHOD {
                let params: PublishDiagnosticsParams = serde_json::from_value(n.params).unwrap();
                if &params.uri == uri {
                    return Some(params.diagnostics);
                }
            }
        }
    }
}

/// Build a JS source of the shape `[[[...1...]]];` nested `depth`
/// times. Recursive-descent parsing recurses one frame per `[`.
/// At depth 100 this overflows a 2 MB stack on Linux debug builds
/// (gdb-confirmed: the top of the trace is `Parser::parse_primary
/// -> Parser::parse_array_literal -> Parser::parse_primary`).
fn deeply_nested_array(depth: usize) -> String {
    let mut s = String::with_capacity(depth * 2 + 4);
    for _ in 0..depth {
        s.push('[');
    }
    s.push('1');
    for _ in 0..depth {
        s.push(']');
    }
    s.push(';');
    s.push('\n');
    s
}

#[test]
fn lsp_survives_deeply_nested_input() {
    // Depth chosen against the empirical 2 MB-stack threshold on
    // Linux debug builds. Doubling it stays well inside the 64 MB
    // worker budget. If this assertion ever needs raising, the
    // recursion shape it guards (parser/inference combined) has
    // grown materially more expensive per-level — file that, don't
    // bump the depth blindly.
    const DEPTH: usize = 100;

    let (client, handle) = boot();
    handshake(&client);

    let u: Uri = "file:///deep.js".parse().unwrap();
    open_doc(&client, &u, deeply_nested_array(DEPTH));

    // Generous budget. Depth-100 takes well under 100 ms in
    // practice; the 30 s ceiling is for slow CI hosts. A genuine
    // hang manifests as `None` here.
    let diags = wait_for_diagnostics(&client, &u, Duration::from_secs(30))
        .expect("publishDiagnostics never arrived — the LSP likely SIGSEGV'd");

    // The exact diagnostics aren't the contract — termination is.
    // We do sanity-check that the LSP produced *some* response
    // (either parse-failed cleanly or inferred-and-found-nothing).
    let _ = diags;

    shutdown(client, handle);
}
