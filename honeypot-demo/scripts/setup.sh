#!/bin/bash
# Setup script for Ma-Dai-Shi Honeypot Demo
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

echo "[1/5] Compiling Noir circuit..."
cd "$PROJECT_DIR/circuits"
nargo compile

echo "[2/5] Generating verification key..."
bb write_vk -b target/honeypot_verifier.json -o target/vk

echo "[3/5] Building WASM module..."
cd "$PROJECT_DIR/wasm"
if command -v wasm-pack &> /dev/null; then
    wasm-pack build --target web --release
else
    echo "  [!] wasm-pack not found, skipping WASM build"
    echo "  Install with: cargo install wasm-pack"
fi

echo "[4/5] Copying artifacts..."
mkdir -p "$PROJECT_DIR/web/pkg"
if [ -d "$PROJECT_DIR/wasm/pkg" ]; then
    cp -r "$PROJECT_DIR/wasm/pkg/"* "$PROJECT_DIR/web/pkg/"
fi

echo "[5/5] Done!"
echo ""
echo "To run the demo:"
echo "  cd $PROJECT_DIR/web"
echo "  python -m http.server 8080"
echo "  open http://localhost:8080"
