# inty VS Code extension

Minimal VS Code adapter for the [inty](../../README.md) LSP server.
Adds no editor logic of its own — it just launches `inty lsp --stdio`
and routes traffic through `vscode-languageclient`.

## Quick start

```sh
cd editors/vscode

./install.sh             # build server, package extension, install into VS Code
./install.sh dev         # OR: launch an Extension Development Host (no install)
./install.sh uninstall   # remove the installed extension
```

After `install.sh` finishes, set `inty.serverPath` in VS Code settings
to the printed binary path, then reload the window. (`dev` mode wires
the path automatically via `inty_BIN`.)

The script honours `$CODE` if you use a non-default channel
(`CODE=code-insiders ./install.sh`).

## Manual setup

If you'd rather drive it yourself:

1. **Build the server.** From the repo root:

   ```sh
   cargo build --release -p inty-cli
   # binary lands at <repo>/target/release/inty
   ```

2. **Install extension dependencies.** From this directory:

   ```sh
   npm install
   ```

3. **Run it.** Either:

   ```sh
   # Dev host (no install):
   code --extensionDevelopmentPath=$PWD .

   # Permanent install:
   npx @vscode/vsce package
   code --install-extension inty-lsp-0.0.1.vsix
   ```

4. **Tell the extension where the binary is.** Set `inty.serverPath`
   in VS Code settings to an absolute path, or export `inty_BIN`,
   or put `inty` on `PATH`.

## Settings

| Setting                  | Default | Notes                                                                |
| ------------------------ | ------- | -------------------------------------------------------------------- |
| `inty.serverPath`     | `""`    | Absolute path to the `inty` binary. Falls back to `inty_BIN`, then `PATH`. |
| `inty.trace.server`   | `"off"` | `"messages"` or `"verbose"` to log LSP traffic to the Output channel. |

## Verifying it's running

After install + reload, you should see:

1. **A "inty" item in the status bar (bottom-right of the window)**.
   - `$(check) inty` → server started.
   - `$(error) inty` (red background) → startup failed; click it to
     open the log.
   - No item at all → the extension didn't activate. Run **Developer:
     Show Running Extensions** from the Command Palette to confirm
     `local.inty-lsp` is in the list.

2. **An Output channel called "inty"**. View it via:
   - the status bar item (it's clickable), or
   - **View → Output**, then pick **inty** in the dropdown, or
   - Command Palette → **inty: Show Server Log**.

3. The log starts with something like:

   ```
   inty extension activated
   server path: /…/target/release/inty  (from inty.serverPath)
   spawning: /…/target/release/inty lsp --stdio
   client started
   ```

## Troubleshooting

- **Status item is red / log says "binary not found".** Build the
  server (`cargo build --release -p inty-cli`), then set
  `inty.serverPath` to the absolute path printed by `install.sh`,
  or run **inty: Restart Server**.
- **No status item, no Output channel.** The extension didn't activate.
  Confirm install with `code --list-extensions | grep inty`. If
  missing, re-run `./install.sh`. If present, open **Output → Extension
  Host** for activation errors.
- **Diagnostics appear but hover does nothing.** A type-check error
  early in the file makes inference bail out, which suppresses hovers
  for the whole document. Fix the diagnostic first.
- **Want to see the LSP traffic.** Set `inty.trace.server` to
  `"verbose"` in settings; messages stream to the same Output channel.
