// Thin VS Code adapter that launches the minfern LSP server over stdio.
//
// The extension itself adds no editor logic — the server speaks LSP and
// drives hovers, diagnostics, completions, go-to-def, rename, signature
// help, and inlay hints directly. This file only locates the binary and
// configures the language-client.

const fs = require("fs");
const vscode = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

let client;
let log;
let status;

function resolveServerPath() {
  const cfg = vscode.workspace.getConfiguration("minfern");
  const fromSetting = cfg.get("serverPath", "").trim();
  if (fromSetting) return { path: fromSetting, source: "minfern.serverPath" };
  if (process.env.MINFERN_BIN) {
    return { path: process.env.MINFERN_BIN, source: "MINFERN_BIN env" };
  }
  return { path: "minfern", source: "PATH lookup" };
}

function activate(context) {
  // Create the Output channel up front so even early failures (binary
  // missing, wrong path, etc.) surface in View -> Output -> "minfern".
  log = vscode.window.createOutputChannel("minfern");
  context.subscriptions.push(log);

  // Status-bar item gives a visible signal that the extension activated.
  status = vscode.window.createStatusBarItem(
    vscode.StatusBarAlignment.Right,
    100
  );
  status.text = "$(loading~spin) minfern";
  status.tooltip = "minfern language server";
  status.command = "minfern.showLog";
  status.show();
  context.subscriptions.push(status);

  context.subscriptions.push(
    vscode.commands.registerCommand("minfern.showLog", () => log.show(true)),
    vscode.commands.registerCommand("minfern.restart", async () => {
      if (client) {
        log.appendLine(">> restarting client...");
        await client.stop();
      }
      startClient(context);
    })
  );

  startClient(context);
}

function startClient(context) {
  const { path, source } = resolveServerPath();
  log.appendLine(`minfern extension activated`);
  log.appendLine(`server path: ${path}  (from ${source})`);

  // If the path is absolute, sanity-check it exists. A "spawn ENOENT"
  // from VS Code's process layer is opaque, so catching it here gives a
  // clearer error.
  if (path.startsWith("/") && !fs.existsSync(path)) {
    const msg = `minfern binary not found at: ${path}`;
    log.appendLine(`ERROR: ${msg}`);
    vscode.window.showErrorMessage(
      `${msg}. Set "minfern.serverPath" or build with: cargo build --release -p minfern-cli`,
      "Show Log"
    ).then(pick => { if (pick === "Show Log") log.show(true); });
    status.text = "$(error) minfern";
    status.backgroundColor = new vscode.ThemeColor("statusBarItem.errorBackground");
    return;
  }

  const args = ["lsp", "--stdio"];
  log.appendLine(`spawning: ${path} ${args.join(" ")}`);

  const serverOptions = {
    run:   { command: path, args, transport: TransportKind.stdio },
    debug: { command: path, args, transport: TransportKind.stdio },
  };

  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "javascript" }],
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher("**/*.js"),
    },
    outputChannel: log,
    traceOutputChannel: log,
  };

  client = new LanguageClient("minfern", "minfern", serverOptions, clientOptions);

  client.start().then(
    () => {
      log.appendLine("client started");
      status.text = "$(check) minfern";
      status.backgroundColor = undefined;
    },
    err => {
      log.appendLine(`ERROR starting client: ${err && err.stack ? err.stack : err}`);
      status.text = "$(error) minfern";
      status.backgroundColor = new vscode.ThemeColor("statusBarItem.errorBackground");
      vscode.window.showErrorMessage(
        `minfern failed to start: ${err && err.message ? err.message : err}`,
        "Show Log"
      ).then(pick => { if (pick === "Show Log") log.show(true); });
    }
  );
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
