#!/bin/bash
# Build script for Minfern WebAssembly module

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

echo "Building Minfern WASM module..."

# Check if wasm-pack is installed
if ! command -v wasm-pack &> /dev/null; then
    echo "wasm-pack not found. Installing..."
    cargo install wasm-pack
fi

# Build the WASM module. The minfern library now lives in
# crates/minfern/, so wasm-pack must point at that crate explicitly.
cd "$PROJECT_ROOT"
wasm-pack build crates/minfern --target web --out-dir ../../web/pkg --features wasm

echo ""
echo "Build complete!"
echo ""
echo "To run the web app:"
echo "  cd web"
echo "  python3 -m http.server 8080"
echo "  # Then open http://localhost:8080"
echo ""
echo "Or use any static file server of your choice."
