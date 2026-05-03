//! End-to-end LSP server tests: feed messages on stdin, assert on
//! stdout. Uses in-memory channels so no real process is spawned.

use std::io::{BufReader, Cursor, Write};

use minfern_lsp::Server;
use serde_json::{json, Value};

/// Pack one or more LSP messages into a single byte buffer with proper
/// `Content-Length` headers.
fn frame(msgs: &[Value]) -> Vec<u8> {
    let mut buf = Vec::new();
    for msg in msgs {
        let body = serde_json::to_vec(msg).unwrap();
        write!(buf, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
        buf.extend_from_slice(&body);
    }
    buf
}

/// Parse all framed LSP messages out of `bytes`.
fn parse_messages(bytes: &[u8]) -> Vec<Value> {
    let mut reader = BufReader::new(bytes);
    let mut out = Vec::new();
    loop {
        match minfern_lsp_test_support::read_one(&mut reader) {
            Some(v) => out.push(v),
            None => break,
        }
    }
    out
}

mod minfern_lsp_test_support {
    use serde_json::Value;
    use std::io::BufRead;

    pub fn read_one<R: BufRead>(reader: &mut R) -> Option<Value> {
        let mut content_length: Option<usize> = None;
        loop {
            let mut line = String::new();
            let n = reader.read_line(&mut line).ok()?;
            if n == 0 {
                return None;
            }
            let trimmed = line.trim_end_matches(['\r', '\n']);
            if trimmed.is_empty() {
                break;
            }
            if let Some(rest) = trimmed.strip_prefix("Content-Length:") {
                content_length = rest.trim().parse().ok();
            }
        }
        let len = content_length?;
        let mut buf = vec![0u8; len];
        reader.read_exact(&mut buf).ok()?;
        serde_json::from_slice(&buf).ok()
    }
}

fn run_server(input: Vec<u8>) -> (Vec<Value>, i32) {
    let reader = BufReader::new(Cursor::new(input));
    let mut output: Vec<u8> = Vec::new();
    let exit = Server::new(reader, &mut output).run().unwrap();
    (parse_messages(&output), exit)
}

#[test]
fn initialize_then_shutdown_exit() {
    let init = json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {"capabilities": {}}
    });
    let initialized = json!({"jsonrpc": "2.0", "method": "initialized", "params": {}});
    let shutdown = json!({"jsonrpc": "2.0", "id": 2, "method": "shutdown"});
    let exit = json!({"jsonrpc": "2.0", "method": "exit"});

    let (replies, code) = run_server(frame(&[init, initialized, shutdown, exit]));
    assert_eq!(code, 0, "clean shutdown should exit 0");

    // First reply: initialize response.
    assert_eq!(replies[0]["id"], 1);
    assert_eq!(replies[0]["result"]["capabilities"]["hoverProvider"], true);
    assert_eq!(replies[0]["result"]["capabilities"]["textDocumentSync"], 1);

    // Second reply: shutdown response (null result).
    assert_eq!(replies[1]["id"], 2);
    assert!(replies[1]["result"].is_null());
}

#[test]
fn did_open_publishes_diagnostics_for_bad_program() {
    let init = json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}});
    // `var x: number = "hello";` would need an annotation; use undefined
    // variable instead — definitely a type error, span well-defined.
    let did_open = json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": "file:///bad.js",
                "languageId": "javascript",
                "version": 1,
                "text": "y;\n",
            }
        }
    });
    let exit = json!({"jsonrpc": "2.0", "method": "exit"});

    let (replies, _) = run_server(frame(&[init, did_open, exit]));

    let diag_msg = replies
        .iter()
        .find(|m| m["method"] == "textDocument/publishDiagnostics")
        .expect("expected a diagnostics notification");
    assert_eq!(diag_msg["params"]["uri"], "file:///bad.js");
    let diags = diag_msg["params"]["diagnostics"].as_array().unwrap();
    assert!(!diags.is_empty(), "should have at least one diagnostic");
    assert_eq!(diags[0]["source"], "minfern");
    assert_eq!(diags[0]["code"], "UndefinedVariable");
    // Severity 1 == Error.
    assert_eq!(diags[0]["severity"], 1);
}

#[test]
fn did_open_publishes_empty_diagnostics_for_good_program() {
    let init = json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}});
    let did_open = json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": "file:///ok.js",
                "languageId": "javascript",
                "version": 1,
                "text": "var x = 1;\n",
            }
        }
    });
    let exit = json!({"jsonrpc": "2.0", "method": "exit"});

    let (replies, _) = run_server(frame(&[init, did_open, exit]));

    let diag_msg = replies
        .iter()
        .find(|m| m["method"] == "textDocument/publishDiagnostics")
        .expect("expected a diagnostics notification");
    let diags = diag_msg["params"]["diagnostics"].as_array().unwrap();
    assert!(diags.is_empty(), "expected no diagnostics, got: {:?}", diags);
}

#[test]
fn hover_returns_inferred_type() {
    let init = json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}});
    let did_open = json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": "file:///hover.js",
                "languageId": "javascript",
                "version": 1,
                "text": "var x = 42;\n",
            }
        }
    });
    // `x` is at line 0, char 4 (after `var `).
    let hover = json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/hover",
        "params": {
            "textDocument": {"uri": "file:///hover.js"},
            "position": {"line": 0, "character": 4},
        }
    });
    let exit = json!({"jsonrpc": "2.0", "method": "exit"});

    let (replies, _) = run_server(frame(&[init, did_open, hover, exit]));

    let hover_reply = replies
        .iter()
        .find(|m| m["id"] == 2)
        .expect("expected a reply to the hover request");
    let value = &hover_reply["result"]["contents"]["value"];
    let s = value.as_str().expect("hover contents should be a string");
    assert!(s.contains("x"), "hover should mention `x`: {}", s);
    // Number is the inferred type for the literal 42.
    assert!(
        s.to_lowercase().contains("number"),
        "hover should mention Number: {}",
        s
    );
}

#[test]
fn hover_off_identifier_returns_null() {
    let init = json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}});
    let did_open = json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": "file:///hover.js",
                "languageId": "javascript",
                "version": 1,
                "text": "var x = 1;\n",
            }
        }
    });
    // Position past end of file.
    let hover = json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/hover",
        "params": {
            "textDocument": {"uri": "file:///hover.js"},
            "position": {"line": 99, "character": 0},
        }
    });
    let exit = json!({"jsonrpc": "2.0", "method": "exit"});

    let (replies, _) = run_server(frame(&[init, did_open, hover, exit]));

    let hover_reply = replies.iter().find(|m| m["id"] == 2).unwrap();
    assert!(hover_reply["result"].is_null());
}

#[test]
fn unknown_request_returns_method_not_found() {
    let init = json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}});
    let bogus = json!({"jsonrpc": "2.0", "id": 7, "method": "textDocument/wave"});
    let exit = json!({"jsonrpc": "2.0", "method": "exit"});

    let (replies, _) = run_server(frame(&[init, bogus, exit]));
    let err = replies.iter().find(|m| m["id"] == 7).unwrap();
    assert_eq!(err["error"]["code"], -32601);
}
