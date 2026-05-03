//! End-to-end LSP server tests using `lsp_server::Connection::memory()`
//! to drive the server in the same process.

use std::thread;

use lsp_server::{Connection, Message, Notification, Request, RequestId};
use lsp_types::notification::{
    DidOpenTextDocument, Initialized, Notification as LspNotification, PublishDiagnostics,
};
use lsp_types::request::{
    Completion, GotoDefinition, HoverRequest, Initialize, InlayHintRequest, PrepareRenameRequest,
    Rename, Request as LspRequest, Shutdown, SignatureHelpRequest,
};
use lsp_types::{
    ClientCapabilities, CompletionParams, CompletionResponse, DidOpenTextDocumentParams,
    GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverParams, InitializeParams, InlayHint,
    InlayHintParams, PartialResultParams, Position, PrepareRenameResponse,
    PublishDiagnosticsParams, Range, RenameParams, SignatureHelp, SignatureHelpContext,
    SignatureHelpParams, SignatureHelpTriggerKind, TextDocumentIdentifier, TextDocumentItem,
    TextDocumentPositionParams, Uri, WorkDoneProgressParams, WorkspaceEdit,
};
use minfern_lsp::Server;
use serde::{de::DeserializeOwned, Serialize};

fn boot() -> (Connection, thread::JoinHandle<()>) {
    let (server_conn, client_conn) = Connection::memory();
    let handle = thread::spawn(move || {
        Server::new(server_conn).run().unwrap();
    });
    (client_conn, handle)
}

fn next_request_id(n: i32) -> RequestId {
    RequestId::from(n)
}

fn req<R: LspRequest>(id: i32, params: R::Params) -> Request
where
    R::Params: Serialize,
{
    Request::new(next_request_id(id), R::METHOD.to_string(), params)
}

fn not<N: LspNotification>(params: N::Params) -> Notification
where
    N::Params: Serialize,
{
    Notification::new(N::METHOD.to_string(), params)
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

fn expect_response<R: DeserializeOwned>(client: &Connection, id: i32) -> R {
    loop {
        let msg = client.receiver.recv().expect("recv");
        if let Message::Response(resp) = msg {
            if resp.id == next_request_id(id) {
                let value = resp.result.expect("response result");
                return serde_json::from_value(value).expect("parse response");
            }
        }
    }
}

fn drain_diagnostics(client: &Connection, uri: &Uri) -> Vec<lsp_types::Diagnostic> {
    loop {
        let msg = client.receiver.recv().expect("recv");
        if let Message::Notification(n) = msg {
            if n.method == PublishDiagnostics::METHOD {
                let params: PublishDiagnosticsParams = serde_json::from_value(n.params).unwrap();
                if &params.uri == uri {
                    return params.diagnostics;
                }
            }
        }
    }
}

fn open_doc(client: &Connection, uri: &Uri, text: &str) {
    client
        .sender
        .send(Message::Notification(not::<DidOpenTextDocument>(
            DidOpenTextDocumentParams {
                text_document: TextDocumentItem {
                    uri: uri.clone(),
                    language_id: "javascript".to_string(),
                    version: 1,
                    text: text.to_string(),
                },
            },
        )))
        .unwrap();
}

fn uri(u: &str) -> Uri {
    u.parse().unwrap()
}

#[test]
fn diagnostics_for_undefined_variable() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///bad.js");
    open_doc(&client, &u, "y;\n");
    let diags = drain_diagnostics(&client, &u);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].source.as_deref(), Some("minfern"));
    assert!(diags[0].message.contains("Undefined variable"));

    shutdown(client, handle);
}

#[test]
fn empty_diagnostics_for_clean_program() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///ok.js");
    open_doc(&client, &u, "var x = 1;\n");
    let diags = drain_diagnostics(&client, &u);
    assert!(diags.is_empty(), "expected no diagnostics, got {:?}", diags);

    shutdown(client, handle);
}

#[test]
fn hover_returns_inferred_type() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///hover.js");
    open_doc(&client, &u, "var x = 42;\n");
    let _ = drain_diagnostics(&client, &u);

    client
        .sender
        .send(Message::Request(req::<HoverRequest>(
            10,
            HoverParams {
                text_document_position_params: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 0, character: 4 },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
            },
        )))
        .unwrap();
    let hover: Option<Hover> = expect_response(&client, 10);
    let hover = hover.expect("hover present");
    let value = match hover.contents {
        lsp_types::HoverContents::Markup(m) => m.value,
        _ => panic!("expected markdown contents"),
    };
    assert!(value.contains("x"), "hover mentions x: {}", value);
    assert!(
        value.to_lowercase().contains("number"),
        "hover mentions Number: {}",
        value
    );

    shutdown(client, handle);
}

#[test]
fn hover_picks_shadowing_binding() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///shadow.js");
    // Outer x is Number, inner is String. Hovering on the inner-block
    // `x;` use should report String, not Number.
    let src = "var x = 1;\n{ let x = \"hi\"; x; }\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    // The inner `x;` use is on line 1, somewhere after `let x = "hi"; `.
    // We pick the column of the trailing `x` by scanning the line.
    let line = "{ let x = \"hi\"; x; }";
    let col = line.rfind("x;").unwrap() as u32;

    client
        .sender
        .send(Message::Request(req::<HoverRequest>(
            11,
            HoverParams {
                text_document_position_params: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 1, character: col },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
            },
        )))
        .unwrap();
    let hover: Option<Hover> = expect_response(&client, 11);
    let value = match hover.unwrap().contents {
        lsp_types::HoverContents::Markup(m) => m.value,
        _ => panic!("expected markdown contents"),
    };
    assert!(
        value.to_lowercase().contains("string"),
        "inner x should be String: {}",
        value
    );
    assert!(
        !value.to_lowercase().contains("number"),
        "inner x should NOT be Number (that's the outer): {}",
        value
    );

    shutdown(client, handle);
}

#[test]
fn hover_on_parameter_returns_param_type() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///param.js");
    // Pin the param type concretely with a function-level annotation so
    // the hover answer is unambiguous (otherwise `add` is polymorphic).
    let src = "/** function add (Number, Number) => Number */\nfunction add(a, b) { return a + b; }\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    // The first occurrence of `a` is in the parameter list of the
    // function declaration on line 1, column 13.
    client
        .sender
        .send(Message::Request(req::<HoverRequest>(
            12,
            HoverParams {
                text_document_position_params: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 1, character: 13 },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
            },
        )))
        .unwrap();
    let hover: Option<Hover> = expect_response(&client, 12);
    let value = match hover.unwrap().contents {
        lsp_types::HoverContents::Markup(m) => m.value,
        _ => panic!("expected markdown contents"),
    };
    assert!(
        value.contains("a"),
        "hover should mention the parameter name: {}",
        value
    );
    assert!(
        value.to_lowercase().contains("number"),
        "param should be Number after add(1, 2): {}",
        value
    );

    shutdown(client, handle);
}

#[test]
fn definition_returns_binding_site() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///def.js");
    let src = "var x = 1;\nx;\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    // The use of `x` is at line 1, character 0.
    client
        .sender
        .send(Message::Request(req::<GotoDefinition>(
            20,
            GotoDefinitionParams {
                text_document_position_params: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 1, character: 0 },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
                partial_result_params: PartialResultParams::default(),
            },
        )))
        .unwrap();
    let resp: Option<GotoDefinitionResponse> = expect_response(&client, 20);
    let resp = resp.expect("definition present");
    let loc = match resp {
        GotoDefinitionResponse::Scalar(l) => l,
        _ => panic!("expected scalar location"),
    };
    assert_eq!(loc.uri, u);
    // The definition's `x` is at line 0, char 4.
    assert_eq!(loc.range.start.line, 0);
    assert_eq!(loc.range.start.character, 4);

    shutdown(client, handle);
}

#[test]
fn rename_produces_workspace_edit_with_all_uses() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///rename.js");
    let src = "var x = 1;\nx + x;\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    // Rename `x` (the def) -> `y`. Cursor on line 0, character 4.
    client
        .sender
        .send(Message::Request(req::<Rename>(
            30,
            RenameParams {
                text_document_position: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 0, character: 4 },
                },
                new_name: "y".to_string(),
                work_done_progress_params: WorkDoneProgressParams::default(),
            },
        )))
        .unwrap();
    let edit: Option<WorkspaceEdit> = expect_response(&client, 30);
    let edit = edit.expect("workspace edit present");
    let edits = edit.changes.unwrap().remove(&u).unwrap();
    // 1 def + 2 uses.
    assert_eq!(edits.len(), 3, "edits: {:?}", edits);
    for e in &edits {
        assert_eq!(e.new_text, "y");
    }

    shutdown(client, handle);
}

#[test]
fn prepare_rename_returns_identifier_range() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///prep.js");
    open_doc(&client, &u, "var foo = 1;\n");
    let _ = drain_diagnostics(&client, &u);

    client
        .sender
        .send(Message::Request(req::<PrepareRenameRequest>(
            40,
            TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: u.clone() },
                position: Position { line: 0, character: 5 }, // inside `foo`
            },
        )))
        .unwrap();
    let resp: Option<PrepareRenameResponse> = expect_response(&client, 40);
    let resp = resp.expect("prepare-rename present");
    match resp {
        PrepareRenameResponse::Range(_) => {}
        other => panic!("expected Range, got {:?}", other),
    }

    shutdown(client, handle);
}

#[test]
fn completion_lists_visible_identifiers() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///comp.js");
    let src = "var apple = 1; var banana = 2;\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    client
        .sender
        .send(Message::Request(req::<Completion>(
            50,
            CompletionParams {
                text_document_position: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 0, character: 30 },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
                partial_result_params: PartialResultParams::default(),
                context: None,
            },
        )))
        .unwrap();
    let resp: Option<CompletionResponse> = expect_response(&client, 50);
    let items = match resp.expect("completion") {
        CompletionResponse::Array(items) => items,
        CompletionResponse::List(list) => list.items,
    };
    let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
    assert!(
        labels.iter().any(|l| *l == "apple"),
        "apple in {:?}",
        labels
    );
    assert!(
        labels.iter().any(|l| *l == "banana"),
        "banana in {:?}",
        labels
    );

    shutdown(client, handle);
}

#[test]
fn completion_after_dot_lists_object_fields() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///mem.js");
    // `obj.x` and `obj.y` give obj a row type with x: Number and y: Number.
    let src = "var obj = { x: 1, y: 2 };\nobj.\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    // Cursor sits right after the `.` on line 1.
    client
        .sender
        .send(Message::Request(req::<Completion>(
            60,
            CompletionParams {
                text_document_position: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 1, character: 4 },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
                partial_result_params: PartialResultParams::default(),
                context: None,
            },
        )))
        .unwrap();
    let resp: Option<CompletionResponse> = expect_response(&client, 60);
    let items = match resp.expect("completion") {
        CompletionResponse::Array(items) => items,
        CompletionResponse::List(list) => list.items,
    };
    let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
    assert!(labels.iter().any(|l| *l == "x"), "x in {:?}", labels);
    assert!(labels.iter().any(|l| *l == "y"), "y in {:?}", labels);

    shutdown(client, handle);
}

#[test]
fn signature_help_inside_function_call() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///sig.js");
    // A function with a known param list.
    let src = "function add(a, b) { return a + b; }\nadd(1, 2);\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    // Cursor on the `2` argument: line 1, column 7. That's the second
    // arg, so signature help should highlight active parameter index 1.
    client
        .sender
        .send(Message::Request(req::<SignatureHelpRequest>(
            70,
            SignatureHelpParams {
                text_document_position_params: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 1, character: 7 },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
                context: Some(SignatureHelpContext {
                    trigger_kind: SignatureHelpTriggerKind::CONTENT_CHANGE,
                    trigger_character: None,
                    is_retrigger: false,
                    active_signature_help: None,
                }),
            },
        )))
        .unwrap();
    let resp: Option<SignatureHelp> = expect_response(&client, 70);
    let help = resp.expect("signature help present");
    assert_eq!(help.signatures.len(), 1);
    let sig = &help.signatures[0];
    assert!(sig.label.contains("add"));
    let params = sig.parameters.as_ref().unwrap();
    assert_eq!(params.len(), 2);
    // Active parameter should be index 1 (the second arg).
    assert_eq!(help.active_parameter, Some(1));

    shutdown(client, handle);
}

#[test]
fn inlay_hints_show_inferred_types() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///hints.js");
    // Three bindings: var x = 1; (Number), const s = "hi"; (String),
    // function f(n) { return n; } (a polymorphic function).
    let src = "var x = 1;\nconst s = \"hi\";\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    client
        .sender
        .send(Message::Request(req::<InlayHintRequest>(
            80,
            InlayHintParams {
                work_done_progress_params: WorkDoneProgressParams::default(),
                text_document: TextDocumentIdentifier { uri: u.clone() },
                range: Range {
                    start: Position { line: 0, character: 0 },
                    end: Position { line: 10, character: 0 },
                },
            },
        )))
        .unwrap();
    let hints: Option<Vec<InlayHint>> = expect_response(&client, 80);
    let hints = hints.expect("inlay hints present");

    // We expect at least two hints: one for x, one for s.
    let labels: Vec<String> = hints
        .iter()
        .map(|h| match &h.label {
            lsp_types::InlayHintLabel::String(s) => s.clone(),
            lsp_types::InlayHintLabel::LabelParts(parts) => {
                parts.iter().map(|p| p.value.clone()).collect::<String>()
            }
        })
        .collect();
    let any_number = labels.iter().any(|l| l.to_lowercase().contains("number"));
    let any_string = labels.iter().any(|l| l.to_lowercase().contains("string"));
    assert!(any_number, "expected a Number hint among {:?}", labels);
    assert!(any_string, "expected a String hint among {:?}", labels);

    shutdown(client, handle);
}

#[test]
fn signature_help_on_member_call() {
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///mc.js");
    // `Math.pow` is in stdlib at type (Number, Number) => Number.
    let src = "Math.pow(2, 3);\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    // Cursor on the second arg, line 0 col 12 (the `3`).
    client
        .sender
        .send(Message::Request(req::<SignatureHelpRequest>(
            71,
            SignatureHelpParams {
                text_document_position_params: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 0, character: 12 },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
                context: Some(SignatureHelpContext {
                    trigger_kind: SignatureHelpTriggerKind::CONTENT_CHANGE,
                    trigger_character: None,
                    is_retrigger: false,
                    active_signature_help: None,
                }),
            },
        )))
        .unwrap();
    let resp: Option<SignatureHelp> = expect_response(&client, 71);
    let help = resp.expect("signature help present for member call");
    assert_eq!(help.signatures.len(), 1);
    let sig = &help.signatures[0];
    assert!(
        sig.label.contains("Math.pow"),
        "label should mention Math.pow: {}",
        sig.label
    );
    let params = sig.parameters.as_ref().unwrap();
    assert_eq!(params.len(), 2);
    assert_eq!(help.active_parameter, Some(1));

    shutdown(client, handle);
}

#[test]
fn rename_propagates_to_importing_files() {
    let (client, handle) = boot();
    handshake(&client);

    // `lib.js` exports `foo`. `app.js` imports it (no alias) and
    // uses it. Renaming `foo` in `lib.js` should produce edits in
    // both files: lib.js (the export decl + uses) and app.js (the
    // import specifier + every use).
    let lib_uri = uri("file:///proj/lib.js");
    let app_uri = uri("file:///proj/app.js");

    let lib_src = "export var foo = 1;\n";
    open_doc(&client, &lib_uri, lib_src);
    let _ = drain_diagnostics(&client, &lib_uri);

    let app_src = "import { foo } from \"./lib.js\";\nfoo;\n";
    open_doc(&client, &app_uri, app_src);
    let _ = drain_diagnostics(&client, &app_uri);

    // Position of `foo` in lib.js: column 11 ("export var ").
    client
        .sender
        .send(Message::Request(req::<Rename>(
            81,
            RenameParams {
                text_document_position: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: lib_uri.clone() },
                    position: Position { line: 0, character: 11 },
                },
                new_name: "bar".to_string(),
                work_done_progress_params: WorkDoneProgressParams::default(),
            },
        )))
        .unwrap();
    let edit: Option<WorkspaceEdit> = expect_response(&client, 81);
    let edit = edit.expect("workspace edit present");
    let mut changes = edit.changes.unwrap();

    // Both files should have edits.
    assert!(
        changes.contains_key(&lib_uri),
        "edits expected for lib.js: {:?}",
        changes.keys().collect::<Vec<_>>()
    );
    assert!(
        changes.contains_key(&app_uri),
        "edits expected for app.js: {:?}",
        changes.keys().collect::<Vec<_>>()
    );

    // Every edit replaces with `bar`.
    let lib_edits = changes.remove(&lib_uri).unwrap();
    for e in &lib_edits {
        assert_eq!(e.new_text, "bar", "lib edit: {:?}", e);
    }
    let app_edits = changes.remove(&app_uri).unwrap();
    for e in &app_edits {
        assert_eq!(e.new_text, "bar", "app edit: {:?}", e);
    }
    // app.js should have at least 2 edits: the import specifier and
    // the use of `foo`.
    assert!(
        app_edits.len() >= 2,
        "app.js should have >= 2 edits, got {}: {:?}",
        app_edits.len(),
        app_edits
    );

    shutdown(client, handle);
}

#[test]
fn hover_inside_function_body_picks_inner_expr() {
    // Hovering on an identifier inside a function body must report the
    // type of *that* expression, not the enclosing function. Named
    // function expressions store the function's def with a span that
    // covers the entire body, so without the smallest-span tie-breaker
    // in `binding_at`, this hover used to return the function type.
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///fbody.js");
    let src = "var g = function f(x) { var y = x; y; };\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    // Hover on the inner `y;` use: line 0, at the column of the last `y`.
    let col = src.rfind("y;").unwrap() as u32;

    client
        .sender
        .send(Message::Request(req::<HoverRequest>(
            50,
            HoverParams {
                text_document_position_params: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 0, character: col },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
            },
        )))
        .unwrap();
    let hover: Option<Hover> = expect_response(&client, 50);
    let value = match hover.expect("hover present").contents {
        lsp_types::HoverContents::Markup(m) => m.value,
        _ => panic!("expected markdown contents"),
    };
    assert!(
        value.contains("y"),
        "hover should mention the inner identifier `y`: {}",
        value
    );
    assert!(
        !value.contains("=>"),
        "hover on inner `y` should NOT show the function type: {}",
        value
    );

    shutdown(client, handle);
}

#[test]
fn hover_on_function_name_still_works() {
    // Hovering on the literal `f` in a function declaration's header
    // should still return the function type (smallest-span tie-breaker
    // shouldn't cause the name lookup to disappear).
    let (client, handle) = boot();
    handshake(&client);

    let u = uri("file:///fname.js");
    let src = "function f(x) { return x + 1; }\nf(1);\n";
    open_doc(&client, &u, src);
    let _ = drain_diagnostics(&client, &u);

    // Position on the literal `f` in `function f(x)` — column 9.
    let col = src.find("function f").unwrap() as u32 + "function ".len() as u32;

    client
        .sender
        .send(Message::Request(req::<HoverRequest>(
            51,
            HoverParams {
                text_document_position_params: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: u.clone() },
                    position: Position { line: 0, character: col },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
            },
        )))
        .unwrap();
    let hover: Option<Hover> = expect_response(&client, 51);
    let value = match hover.expect("hover present").contents {
        lsp_types::HoverContents::Markup(m) => m.value,
        _ => panic!("expected markdown contents"),
    };
    assert!(
        value.contains("f"),
        "hover should mention the function name `f`: {}",
        value
    );
    assert!(
        value.contains("=>"),
        "hover on function name should show a function type: {}",
        value
    );

    shutdown(client, handle);
}
