#!/bin/bash
# Build script for Inty WebAssembly module

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

echo "Generating web/examples.js from examples/playground/..."
python3 "$PROJECT_ROOT/scripts/gen-examples.py"

echo "Building Inty WASM module..."

# Check if wasm-pack is installed
if ! command -v wasm-pack &> /dev/null; then
    echo "wasm-pack not found. Installing..."
    cargo install wasm-pack
fi

# The web playground hits the same Analysis API the editor LSP uses,
# so we build the inty-lsp crate (without the stdio server feature).
# `--out-name inty` keeps the JS module path stable at web/pkg/inty.js.
cd "$PROJECT_ROOT"
wasm-pack build crates/inty-lsp \
    --target web \
    --out-dir ../../web/pkg \
    --out-name inty \
    --no-default-features \
    --features wasm

echo ""
echo "Build complete!"
echo ""
echo "To run the web app:"
echo "  cd web"
echo "  python3 -m http.server 8080"
echo "  # Then open http://localhost:8080"
echo ""
echo "Or use any static file server of your choice."
