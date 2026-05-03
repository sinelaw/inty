//! LSP server state and message dispatch.

use std::collections::HashMap;
use std::io::{self, BufRead, Write};

use serde_json::{json, Value};

use crate::analysis::Analysis;
use crate::convert::{error_to_diagnostic, position_to_byte, span_to_range, Position};
use crate::protocol::{read_message, write_message};

/// One in-memory document, keyed by its LSP URI.
struct Document {
    text: String,
    analysis: Analysis,
}

/// Top-level LSP server. Owns the open-document map and runs the
/// read-dispatch-write loop until the client sends `exit`.
pub struct Server<R: BufRead, W: Write> {
    reader: R,
    writer: W,
    documents: HashMap<String, Document>,
    initialized: bool,
    shutdown_requested: bool,
}

impl<R: BufRead, W: Write> Server<R, W> {
    pub fn new(reader: R, writer: W) -> Self {
        Server {
            reader,
            writer,
            documents: HashMap::new(),
            initialized: false,
            shutdown_requested: false,
        }
    }

    /// Run the LSP message loop. Returns `Ok(0)` if the client sent the
    /// proper `shutdown` then `exit` sequence, `Ok(1)` if the client
    /// sent `exit` without `shutdown` first, and any IO error otherwise.
    pub fn run(mut self) -> io::Result<i32> {
        loop {
            let msg = match read_message(&mut self.reader)? {
                Some(m) => m,
                None => {
                    // Client closed stdin without `exit`.
                    return Ok(if self.shutdown_requested { 0 } else { 1 });
                }
            };

            // Distinguish requests (have an `id`) from notifications.
            let id = msg.get("id").cloned();
            let method = msg
                .get("method")
                .and_then(Value::as_str)
                .unwrap_or("")
                .to_string();
            let params = msg.get("params").cloned().unwrap_or(Value::Null);

            if method == "exit" {
                return Ok(if self.shutdown_requested { 0 } else { 1 });
            }

            match (id.is_some(), method.as_str()) {
                (true, "initialize") => {
                    let resp = self.on_initialize(params);
                    self.respond(id.unwrap(), resp)?;
                }
                (true, "shutdown") => {
                    self.shutdown_requested = true;
                    self.respond(id.unwrap(), Ok(Value::Null))?;
                }
                (true, "textDocument/hover") => {
                    let resp = self.on_hover(params);
                    self.respond(id.unwrap(), resp)?;
                }
                (true, _) => {
                    // Unknown request — answer with MethodNotFound so the
                    // client doesn't hang on its `id`.
                    self.respond_error(id.unwrap(), -32601, format!("Method not found: {}", method))?;
                }
                (false, "initialized") => {
                    self.initialized = true;
                }
                (false, "textDocument/didOpen") => {
                    self.on_did_open(params)?;
                }
                (false, "textDocument/didChange") => {
                    self.on_did_change(params)?;
                }
                (false, "textDocument/didSave") => {
                    // No-op: we re-check on every change.
                }
                (false, "textDocument/didClose") => {
                    self.on_did_close(params)?;
                }
                (false, _) => {
                    // Unknown notification — silently ignore per LSP spec.
                }
            }
        }
    }

    fn respond(&mut self, id: Value, result: Result<Value, (i64, String)>) -> io::Result<()> {
        let msg = match result {
            Ok(value) => json!({"jsonrpc": "2.0", "id": id, "result": value}),
            Err((code, message)) => json!({
                "jsonrpc": "2.0",
                "id": id,
                "error": {"code": code, "message": message},
            }),
        };
        write_message(&mut self.writer, &msg)
    }

    fn respond_error(&mut self, id: Value, code: i64, message: String) -> io::Result<()> {
        self.respond(id, Err((code, message)))
    }

    fn on_initialize(&mut self, _params: Value) -> Result<Value, (i64, String)> {
        Ok(json!({
            "capabilities": {
                // Full document sync (TextDocumentSyncKind.Full).
                "textDocumentSync": 1,
                "hoverProvider": true,
                "positionEncoding": "utf-16",
            },
            "serverInfo": {
                "name": "minfern-lsp",
                "version": env!("CARGO_PKG_VERSION"),
            },
        }))
    }

    fn on_did_open(&mut self, params: Value) -> io::Result<()> {
        let doc = match params.get("textDocument") {
            Some(d) => d,
            None => return Ok(()),
        };
        let uri = doc
            .get("uri")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();
        let text = doc
            .get("text")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();
        let version = doc.get("version").and_then(Value::as_i64).unwrap_or(0);
        self.update_document(uri, text, version)
    }

    fn on_did_change(&mut self, params: Value) -> io::Result<()> {
        let doc = match params.get("textDocument") {
            Some(d) => d,
            None => return Ok(()),
        };
        let uri = doc
            .get("uri")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();
        let version = doc.get("version").and_then(Value::as_i64).unwrap_or(0);

        // We advertise full sync, so the client sends a single change
        // event whose `text` is the whole document.
        let new_text = params
            .get("contentChanges")
            .and_then(Value::as_array)
            .and_then(|arr| arr.last())
            .and_then(|c| c.get("text"))
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();

        self.update_document(uri, new_text, version)
    }

    fn on_did_close(&mut self, params: Value) -> io::Result<()> {
        let uri = match params
            .get("textDocument")
            .and_then(|d| d.get("uri"))
            .and_then(Value::as_str)
        {
            Some(u) => u.to_string(),
            None => return Ok(()),
        };
        self.documents.remove(&uri);
        // Clear any diagnostics we previously published for this doc.
        self.publish_diagnostics(&uri, None, &[])
    }

    fn update_document(&mut self, uri: String, text: String, version: i64) -> io::Result<()> {
        let analysis = Analysis::check(&text);
        let diagnostics: Vec<Value> = analysis
            .errors
            .iter()
            .map(|e| error_to_diagnostic(&text, e))
            .collect();

        self.publish_diagnostics(&uri, Some(version), &diagnostics)?;

        let _ = version;
        self.documents.insert(uri, Document { text, analysis });
        Ok(())
    }

    fn publish_diagnostics(
        &mut self,
        uri: &str,
        version: Option<i64>,
        diagnostics: &[Value],
    ) -> io::Result<()> {
        let mut params = json!({
            "uri": uri,
            "diagnostics": diagnostics,
        });
        if let Some(v) = version {
            params["version"] = json!(v);
        }
        let msg = json!({
            "jsonrpc": "2.0",
            "method": "textDocument/publishDiagnostics",
            "params": params,
        });
        write_message(&mut self.writer, &msg)
    }

    fn on_hover(&mut self, params: Value) -> Result<Value, (i64, String)> {
        let uri = params
            .get("textDocument")
            .and_then(|d| d.get("uri"))
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();
        let position = match parse_position(params.get("position")) {
            Some(p) => p,
            None => return Ok(Value::Null),
        };

        let doc = match self.documents.get(&uri) {
            Some(d) => d,
            None => return Ok(Value::Null),
        };

        let byte_offset = match position_to_byte(&doc.text, position) {
            Some(o) => o,
            None => return Ok(Value::Null),
        };

        let hover = match doc.analysis.hover_at(byte_offset) {
            Some(h) => h,
            None => return Ok(Value::Null),
        };

        // Render as a fenced TypeScript-ish block. Editors that show
        // hover use Markdown, and `ts` is the closest highlighter for
        // minfern's type syntax.
        let markdown = format!("```ts\n{}: {}\n```", hover.name, hover.type_str);
        Ok(json!({
            "contents": {"kind": "markdown", "value": markdown},
            "range": span_to_range(&doc.text, hover.span),
        }))
    }
}

fn parse_position(v: Option<&Value>) -> Option<Position> {
    let v = v?;
    let line = v.get("line")?.as_u64()? as u32;
    let character = v.get("character")?.as_u64()? as u32;
    Some(Position { line, character })
}

