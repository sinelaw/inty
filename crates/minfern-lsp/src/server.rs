//! LSP server: glues `lsp-server`'s sync stdio loop to minfern.

use std::collections::HashMap;
use std::error::Error;

use lsp_server::{Connection, ExtractError, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{
    DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, DidSaveTextDocument,
    Notification as LspNotification, PublishDiagnostics,
};
use lsp_types::request::{
    Completion, GotoDefinition, HoverRequest, PrepareRenameRequest, Rename, Request as LspRequest,
    SignatureHelpRequest,
};
use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionOptions, CompletionParams, CompletionResponse,
    Diagnostic, GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverContents, HoverParams,
    HoverProviderCapability, Location, MarkupContent, MarkupKind, OneOf, ParameterInformation,
    ParameterLabel, PrepareRenameResponse, PublishDiagnosticsParams, RenameOptions, RenameParams,
    ServerCapabilities, SignatureHelp, SignatureHelpOptions, SignatureHelpParams,
    SignatureInformation, TextDocumentPositionParams, TextDocumentSyncKind, TextEdit, Uri,
    WorkDoneProgressOptions, WorkspaceEdit,
};
use serde::{de::DeserializeOwned, Serialize};

use crate::analysis::Analysis;
use crate::convert::{error_to_diagnostic, position_to_byte, span_to_range};

/// One in-memory document.
struct Document {
    text: String,
    analysis: Analysis,
}

/// Owns the connection and document map; its `run` method is the
/// message loop.
pub struct Server {
    connection: Connection,
    documents: HashMap<Uri, Document>,
}

impl Server {
    /// Create a server bound to the given `Connection`. For production
    /// use prefer [`run_stdio`]; this constructor is exposed so tests
    /// can pair the server with `Connection::memory()`.
    pub fn new(connection: Connection) -> Self {
        Server {
            connection,
            documents: HashMap::new(),
        }
    }

    /// Drive the server until the client sends `shutdown` + `exit`.
    pub fn run(mut self) -> Result<(), Box<dyn Error + Sync + Send>> {
        // Initialize handshake.
        let (id, _params_json) = self.connection.initialize_start()?;
        let init_result = serde_json::json!({
            "capabilities": server_capabilities(),
            "serverInfo": {
                "name": "minfern-lsp",
                "version": env!("CARGO_PKG_VERSION"),
            },
        });
        self.connection.initialize_finish(id, init_result)?;

        // Main loop.
        for msg in &self.connection.receiver.clone() {
            match msg {
                Message::Request(req) => {
                    if self.connection.handle_shutdown(&req)? {
                        return Ok(());
                    }
                    self.handle_request(req)?;
                }
                Message::Response(_) => {
                    // We don't issue server-to-client requests yet, so
                    // any response is ignored.
                }
                Message::Notification(not) => {
                    self.handle_notification(not)?;
                }
            }
        }
        Ok(())
    }

    fn handle_request(&mut self, req: Request) -> Result<(), Box<dyn Error + Sync + Send>> {
        let id = req.id.clone();
        let method = req.method.clone();

        if let Some(params) = cast_req::<HoverRequest>(&req)? {
            let result = self.on_hover(params);
            self.respond_ok(id, &result)?;
            return Ok(());
        }
        if let Some(params) = cast_req::<GotoDefinition>(&req)? {
            let result = self.on_definition(params);
            self.respond_ok(id, &result)?;
            return Ok(());
        }
        if let Some(params) = cast_req::<PrepareRenameRequest>(&req)? {
            let result = self.on_prepare_rename(params);
            self.respond_ok(id, &result)?;
            return Ok(());
        }
        if let Some(params) = cast_req::<Rename>(&req)? {
            let result = self.on_rename(params);
            self.respond_ok(id, &result)?;
            return Ok(());
        }
        if let Some(params) = cast_req::<Completion>(&req)? {
            let result = self.on_completion(params);
            self.respond_ok(id, &result)?;
            return Ok(());
        }
        if let Some(params) = cast_req::<SignatureHelpRequest>(&req)? {
            let result = self.on_signature_help(params);
            self.respond_ok(id, &result)?;
            return Ok(());
        }

        // Unknown request — answer with MethodNotFound so the client
        // doesn't hang on the id.
        self.connection.sender.send(Message::Response(Response {
            id,
            result: None,
            error: Some(lsp_server::ResponseError {
                code: lsp_server::ErrorCode::MethodNotFound as i32,
                message: format!("Method not found: {}", method),
                data: None,
            }),
        }))?;
        Ok(())
    }

    fn handle_notification(&mut self, not: Notification) -> Result<(), Box<dyn Error + Sync + Send>> {
        let method = not.method.clone();
        if let Some(params) = cast_not::<DidOpenTextDocument>(&not)? {
            let uri = params.text_document.uri.clone();
            self.update_document(uri, params.text_document.text)?;
            return Ok(());
        }
        if let Some(params) = cast_not::<DidChangeTextDocument>(&not)? {
            let uri = params.text_document.uri.clone();
            // We advertise full sync, so the last change has the whole
            // new text.
            if let Some(change) = params.content_changes.into_iter().last() {
                self.update_document(uri, change.text)?;
            }
            return Ok(());
        }
        if cast_not::<DidSaveTextDocument>(&not)?.is_some() {
            // No-op: we re-check on every change.
            return Ok(());
        }
        if let Some(params) = cast_not::<DidCloseTextDocument>(&not)? {
            self.documents.remove(&params.text_document.uri);
            self.publish_diagnostics(&params.text_document.uri, &[])?;
            return Ok(());
        }
        let _ = method; // unknown notifications are silently ignored
        Ok(())
    }

    fn update_document(
        &mut self,
        uri: Uri,
        text: String,
    ) -> Result<(), Box<dyn Error + Sync + Send>> {
        let analysis = Analysis::check(&text);
        let diagnostics: Vec<Diagnostic> = analysis
            .errors
            .iter()
            .map(|e| error_to_diagnostic(&text, e))
            .collect();
        self.publish_diagnostics(&uri, &diagnostics)?;
        self.documents.insert(uri, Document { text, analysis });
        Ok(())
    }

    fn publish_diagnostics(
        &self,
        uri: &Uri,
        diagnostics: &[Diagnostic],
    ) -> Result<(), Box<dyn Error + Sync + Send>> {
        let params = PublishDiagnosticsParams {
            uri: uri.clone(),
            diagnostics: diagnostics.to_vec(),
            version: None,
        };
        let not = Notification {
            method: PublishDiagnostics::METHOD.to_string(),
            params: serde_json::to_value(params)?,
        };
        self.connection.sender.send(Message::Notification(not))?;
        Ok(())
    }

    fn respond_ok<R: Serialize>(
        &self,
        id: RequestId,
        result: &R,
    ) -> Result<(), Box<dyn Error + Sync + Send>> {
        let resp = Response {
            id,
            result: Some(serde_json::to_value(result)?),
            error: None,
        };
        self.connection.sender.send(Message::Response(resp))?;
        Ok(())
    }

    // ---------- Per-feature handlers ----------

    fn on_hover(&self, params: HoverParams) -> Option<Hover> {
        let pos = params.text_document_position_params;
        let doc = self.documents.get(&pos.text_document.uri)?;
        let offset = position_to_byte(&doc.text, pos.position)?;
        let hover = doc.analysis.hover_at(offset)?;
        let value = format!("```ts\n{}: {}\n```", hover.name, hover.type_str);
        Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value,
            }),
            range: Some(span_to_range(&doc.text, hover.span)),
        })
    }

    fn on_definition(&self, params: GotoDefinitionParams) -> Option<GotoDefinitionResponse> {
        let pos = params.text_document_position_params;
        let doc = self.documents.get(&pos.text_document.uri)?;
        let offset = position_to_byte(&doc.text, pos.position)?;
        let (def_span, _) = doc.analysis.resolution.binding_at(offset)?;
        Some(GotoDefinitionResponse::Scalar(Location {
            uri: pos.text_document.uri,
            range: span_to_range(&doc.text, def_span),
        }))
    }

    fn on_prepare_rename(&self, params: TextDocumentPositionParams) -> Option<PrepareRenameResponse> {
        let doc = self.documents.get(&params.text_document.uri)?;
        let offset = position_to_byte(&doc.text, params.position)?;
        let (_, hit_span) = doc.analysis.resolution.binding_at(offset)?;
        Some(PrepareRenameResponse::Range(span_to_range(&doc.text, hit_span)))
    }

    fn on_rename(&self, params: RenameParams) -> Option<WorkspaceEdit> {
        let pos = params.text_document_position;
        let doc = self.documents.get(&pos.text_document.uri)?;
        let offset = position_to_byte(&doc.text, pos.position)?;
        let new_name = params.new_name;
        if !is_valid_identifier(&new_name) {
            return None;
        }

        let (def_span, _) = doc.analysis.resolution.binding_at(offset)?;
        let mut edits: Vec<TextEdit> = Vec::new();

        // The def site itself.
        edits.push(TextEdit {
            range: span_to_range(&doc.text, def_span),
            new_text: new_name.clone(),
        });
        // Every use.
        for &use_span in doc.analysis.resolution.uses_of(def_span) {
            edits.push(TextEdit {
                range: span_to_range(&doc.text, use_span),
                new_text: new_name.clone(),
            });
        }

        let mut changes = HashMap::new();
        changes.insert(pos.text_document.uri, edits);
        Some(WorkspaceEdit {
            changes: Some(changes),
            document_changes: None,
            change_annotations: None,
        })
    }

    fn on_completion(&self, params: CompletionParams) -> Option<CompletionResponse> {
        let pos = params.text_document_position;
        let doc = self.documents.get(&pos.text_document.uri)?;
        let offset = position_to_byte(&doc.text, pos.position)?;

        // Member completion: cursor immediately after a `.`.
        if let Some(items) = doc
            .analysis
            .member_completions_before_with(&doc.text, offset)
        {
            return Some(CompletionResponse::Array(items));
        }

        // Identifier completion: list everything visible.
        let visible = doc.analysis.resolution.visible_at(offset);
        let items: Vec<CompletionItem> = visible
            .into_iter()
            .map(|def| {
                let kind = match def.kind {
                    crate::resolver::DefKind::Function => CompletionItemKind::FUNCTION,
                    crate::resolver::DefKind::Param => CompletionItemKind::VARIABLE,
                    crate::resolver::DefKind::Const => CompletionItemKind::CONSTANT,
                    crate::resolver::DefKind::Var => CompletionItemKind::VARIABLE,
                    crate::resolver::DefKind::Catch => CompletionItemKind::VARIABLE,
                    crate::resolver::DefKind::Import => CompletionItemKind::MODULE,
                };
                let detail = doc.analysis.type_of_name(&def.name);
                CompletionItem {
                    label: def.name.clone(),
                    kind: Some(kind),
                    detail,
                    ..Default::default()
                }
            })
            .collect();
        Some(CompletionResponse::Array(items))
    }

    fn on_signature_help(&self, params: SignatureHelpParams) -> Option<SignatureHelp> {
        let pos = params.text_document_position_params;
        let doc = self.documents.get(&pos.text_document.uri)?;
        let offset = position_to_byte(&doc.text, pos.position)?;
        let info = doc.analysis.signature_help_at(&doc.text, offset)?;

        let label = info.signature_label.clone();
        let parameters: Vec<ParameterInformation> = info
            .parameters
            .iter()
            .map(|p: &String| ParameterInformation {
                label: ParameterLabel::Simple(p.clone()),
                documentation: None,
            })
            .collect();
        Some(SignatureHelp {
            signatures: vec![SignatureInformation {
                label,
                documentation: None,
                parameters: Some(parameters),
                active_parameter: Some(info.active_parameter),
            }],
            active_signature: Some(0),
            active_parameter: Some(info.active_parameter),
        })
    }
}

fn server_capabilities() -> ServerCapabilities {
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncKind::FULL.into()),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        rename_provider: Some(OneOf::Right(RenameOptions {
            prepare_provider: Some(true),
            work_done_progress_options: WorkDoneProgressOptions::default(),
        })),
        completion_provider: Some(CompletionOptions {
            trigger_characters: Some(vec![".".to_string()]),
            ..Default::default()
        }),
        signature_help_provider: Some(SignatureHelpOptions {
            trigger_characters: Some(vec!["(".to_string(), ",".to_string()]),
            retrigger_characters: None,
            work_done_progress_options: WorkDoneProgressOptions::default(),
        }),
        ..Default::default()
    }
}

fn cast_req<R: LspRequest>(req: &Request) -> Result<Option<R::Params>, ExtractError<Request>>
where
    R::Params: DeserializeOwned,
{
    if req.method == R::METHOD {
        let req = req.clone();
        let (_, params) = req.extract::<R::Params>(R::METHOD)?;
        Ok(Some(params))
    } else {
        Ok(None)
    }
}

fn cast_not<N: LspNotification>(
    not: &Notification,
) -> Result<Option<N::Params>, ExtractError<Notification>>
where
    N::Params: DeserializeOwned,
{
    if not.method == N::METHOD {
        let not = not.clone();
        let params = not.extract::<N::Params>(N::METHOD)?;
        Ok(Some(params))
    } else {
        Ok(None)
    }
}

fn is_valid_identifier(s: &str) -> bool {
    let mut chars = s.chars();
    let first = match chars.next() {
        Some(c) => c,
        None => return false,
    };
    if !(first.is_ascii_alphabetic() || first == '_' || first == '$') {
        return false;
    }
    for c in chars {
        if !(c.is_ascii_alphanumeric() || c == '_' || c == '$') {
            return false;
        }
    }
    !is_reserved_word(s)
}

fn is_reserved_word(s: &str) -> bool {
    matches!(
        s,
        "break" | "case" | "catch" | "class" | "const" | "continue" | "debugger" | "default"
            | "delete" | "do" | "else" | "export" | "extends" | "finally" | "for" | "function"
            | "if" | "import" | "in" | "instanceof" | "new" | "null" | "return" | "super"
            | "switch" | "this" | "throw" | "true" | "false" | "try" | "typeof" | "var"
            | "void" | "while" | "with" | "yield" | "let" | "static" | "enum" | "await"
            | "implements" | "interface" | "package" | "private" | "protected" | "public"
    )
}

/// Run the LSP server on stdin/stdout. Returns when the client cleanly
/// shuts down.
pub fn run_stdio() -> Result<(), Box<dyn Error + Sync + Send>> {
    let (connection, threads) = Connection::stdio();
    let server = Server::new(connection);
    server.run()?;
    threads.join()?;
    Ok(())
}

