# minfern VS Code extension

Minimal VS Code adapter for the [minfern](../../README.md) LSP server.
Adds no editor logic of its own — it just launches `minfern lsp --stdio`
and routes traffic through `vscode-languageclient`.

## Quick start

```sh
cd editors/vscode

./install.sh             # build server, package extension, install into VS Code
./install.sh dev         # OR: launch an Extension Development Host (no install)
./install.sh uninstall   # remove the installed extension
```

After `install.sh` finishes, set `minfern.serverPath` in VS Code settings
to the printed binary path, then reload the window. (`dev` mode wires
the path automatically via `MINFERN_BIN`.)

The script honours `$CODE` if you use a non-default channel
(`CODE=code-insiders ./install.sh`).

## Manual setup

If you'd rather drive it yourself:

1. **Build the server.** From the repo root:

   ```sh
   cargo build --release -p minfern-cli
   # binary lands at <repo>/target/release/minfern
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
   code --install-extension minfern-lsp-0.0.1.vsix
   ```

4. **Tell the extension where the binary is.** Set `minfern.serverPath`
   in VS Code settings to an absolute path, or export `MINFERN_BIN`,
   or put `minfern` on `PATH`.

## Settings

| Setting                  | Default | Notes                                                                |
| ------------------------ | ------- | -------------------------------------------------------------------- |
| `minfern.serverPath`     | `""`    | Absolute path to the `minfern` binary. Falls back to `MINFERN_BIN`, then `PATH`. |
| `minfern.trace.server`   | `"off"` | `"messages"` or `"verbose"` to log LSP traffic to the Output channel. |

## Verifying it's running

After install + reload, you should see:

1. **A "minfern" item in the status bar (bottom-right of the window)**.
   - `$(check) minfern` → server started.
   - `$(error) minfern` (red background) → startup failed; click it to
     open the log.
   - No item at all → the extension didn't activate. Run **Developer:
     Show Running Extensions** from the Command Palette to confirm
     `local.minfern-lsp` is in the list.

2. **An Output channel called "minfern"**. View it via:
   - the status bar item (it's clickable), or
   - **View → Output**, then pick **minfern** in the dropdown, or
   - Command Palette → **minfern: Show Server Log**.

3. The log starts with something like:

   ```
   minfern extension activated
   server path: /…/target/release/minfern  (from minfern.serverPath)
   spawning: /…/target/release/minfern lsp --stdio
   client started
   ```

## Troubleshooting

- **Status item is red / log says "binary not found".** Build the
  server (`cargo build --release -p minfern-cli`), then set
  `minfern.serverPath` to the absolute path printed by `install.sh`,
  or run **minfern: Restart Server**.
- **No status item, no Output channel.** The extension didn't activate.
  Confirm install with `code --list-extensions | grep minfern`. If
  missing, re-run `./install.sh`. If present, open **Output → Extension
  Host** for activation errors.
- **Diagnostics appear but hover does nothing.** A type-check error
  early in the file makes inference bail out, which suppresses hovers
  for the whole document. Fix the diagnostic first.
- **Want to see the LSP traffic.** Set `minfern.trace.server` to
  `"verbose"` in settings; messages stream to the same Output channel.
