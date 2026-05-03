#!/usr/bin/env bash
# Build the minfern server, then install / dev-run the VS Code extension.
#
# Usage:
#   ./install.sh               # build server + install extension into VS Code
#   ./install.sh dev [path]    # launch Extension Development Host on `path`
#                              # (defaults to the current working directory)
#   ./install.sh uninstall     # remove the installed extension
#   ./install.sh -h | --help

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
BIN_PATH="$REPO_ROOT/target/release/minfern"
EXT_ID="local.minfern-lsp"
VSIX_PATH="$SCRIPT_DIR/minfern-lsp.vsix"

# Match VS Code's installation channel via $CODE if set; default to `code`.
CODE="${CODE:-code}"

usage() {
  sed -n '2,9p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "error: '$1' not found on PATH" >&2
    exit 1
  }
}

build_server() {
  require_cmd cargo
  echo ">> building minfern (release)…"
  (cd "$REPO_ROOT" && cargo build --release -p minfern-cli)
  [ -x "$BIN_PATH" ] || {
    echo "error: build did not produce $BIN_PATH" >&2
    exit 1
  }
  echo ">> server binary: $BIN_PATH"
}

ensure_node_modules() {
  require_cmd npm
  if [ ! -d "$SCRIPT_DIR/node_modules" ]; then
    echo ">> npm install…"
    (cd "$SCRIPT_DIR" && npm install --no-audit --no-fund)
  fi
}

print_setting_hint() {
  cat <<EOF

Next:
  1. Set this in VS Code user settings (Cmd/Ctrl+Shift+P -> "Open User Settings (JSON)"):

         "minfern.serverPath": "$BIN_PATH"

     Or export MINFERN_BIN in the shell you launch VS Code from.

  2. Reload the window (Cmd/Ctrl+Shift+P -> "Reload Window") and open a .js file.
EOF
}

cmd="${1:-install}"

case "$cmd" in
  install)
    build_server
    ensure_node_modules
    require_cmd "$CODE"
    echo ">> packaging .vsix via npx @vscode/vsce…"
    (cd "$SCRIPT_DIR" && npx --yes @vscode/vsce package --out "$VSIX_PATH")
    # Force a clean replace: --force alone occasionally keeps the old
    # manifest cached in VS Code's extension index, so commands /
    # activation events from the new build don't appear.
    echo ">> uninstalling previous version (if any)…"
    "$CODE" --uninstall-extension "$EXT_ID" >/dev/null 2>&1 || true
    echo ">> installing extension into $CODE…"
    "$CODE" --install-extension "$VSIX_PATH" --force
    print_setting_hint
    cat <<EOF

  3. *** Reload the VS Code window *** (Cmd/Ctrl+Shift+P -> "Developer:
     Reload Window"). New commands and contributions only register on
     reload — without it you'll see "command not found" errors.
EOF
    ;;

  dev)
    build_server
    ensure_node_modules
    require_cmd "$CODE"
    workspace="${2:-$PWD}"
    echo ">> launching Extension Development Host on: $workspace"
    MINFERN_BIN="$BIN_PATH" exec "$CODE" \
      --extensionDevelopmentPath="$SCRIPT_DIR" \
      "$workspace"
    ;;

  uninstall)
    require_cmd "$CODE"
    "$CODE" --uninstall-extension "$EXT_ID" || true
    rm -f "$VSIX_PATH"
    echo ">> uninstalled $EXT_ID"
    ;;

  -h|--help|help)
    usage
    ;;

  *)
    echo "unknown subcommand: $cmd" >&2
    usage >&2
    exit 2
    ;;
esac
