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

## Troubleshooting

- **No diagnostics appear.** Check **View → Output → "minfern"**. If the
  channel doesn't exist the extension didn't activate (open a `.js`
  file). If it shows `spawn ... ENOENT`, fix `minfern.serverPath`.
- **Diagnostics appear but hover does nothing.** A type-check error
  early in the file makes inference bail out, which suppresses hovers
  for the whole document. Fix the diagnostic first.
- **Want to see the LSP traffic.** Set `minfern.trace.server` to
  `"verbose"` in settings.
