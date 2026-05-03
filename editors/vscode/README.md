# minfern VS Code extension

Minimal VS Code adapter for the [minfern](../../README.md) LSP server.
Adds no editor logic of its own — it just launches `minfern lsp --stdio`
and routes traffic through `vscode-languageclient`.

## Setup

1. **Build the server.** From the repo root:

   ```sh
   cargo build --release -p minfern-cli
   # binary lands at <repo>/target/release/minfern
   ```

2. **Install extension dependencies.** From this directory:

   ```sh
   cd editors/vscode
   npm install
   ```

3. **Tell the extension where the binary is.** Either set
   `minfern.serverPath` in VS Code settings to an absolute path, set
   the `MINFERN_BIN` environment variable, or put `minfern` on `PATH`.

## Run it

### As an Extension Development Host (no install)

```sh
code --extensionDevelopmentPath=$PWD .
```

A new VS Code window opens with the extension loaded. Open any `.js`
file: hovers, diagnostics, completions, go-to-def, rename, signature
help, and inlay hints come from minfern.

### Install permanently

```sh
npm install -g @vscode/vsce
vsce package          # produces minfern-lsp-<version>.vsix
code --install-extension minfern-lsp-0.0.1.vsix
```

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
