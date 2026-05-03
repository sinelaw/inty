// Thin VS Code adapter that launches the minfern LSP server over stdio.
//
// The extension itself adds no editor logic — the server speaks LSP and
// drives hovers, diagnostics, completions, go-to-def, rename, signature
// help, and inlay hints directly. This file only locates the binary and
// configures the language-client.

const path = require("path");
const vscode = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

let client;

function resolveServerPath() {
  const cfg = vscode.workspace.getConfiguration("minfern");
  const fromSetting = cfg.get("serverPath", "").trim();
  if (fromSetting) return fromSetting;
  if (process.env.MINFERN_BIN) return process.env.MINFERN_BIN;
  return "minfern"; // Fall back to PATH lookup.
}

function activate(context) {
  const command = resolveServerPath();
  const args = ["lsp", "--stdio"];

  const serverOptions = {
    run:   { command, args, transport: TransportKind.stdio },
    debug: { command, args, transport: TransportKind.stdio },
  };

  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "javascript" }],
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher("**/*.js"),
    },
    outputChannelName: "minfern",
  };

  client = new LanguageClient("minfern", "minfern", serverOptions, clientOptions);
  client.start();
  context.subscriptions.push({ dispose: () => client && client.stop() });
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
