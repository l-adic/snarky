#!/usr/bin/env bash
# Build the kimchi-napi crate for wasm32-wasip1-threads (rayon over wasi
# threads) from the in-tree proof-systems submodule, patch the generated
# browser loader, and optimize the module. Output lands in ./wasm.
#
# Counterpart to build.sh (the native build), and uses the same
# toolchain-pinning discipline: build with exactly the version
# proof-systems pins in its rust-toolchain.toml, so the wasm artifact
# matches the native one and the OCaml reference. Idempotent; re-run any
# time. Expects napi + wasm-opt on PATH (npm provides them via
# node_modules/.bin when invoked through `npm run build:wasm`).

set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
HERE="$(pwd)"

PS_DIR="../../mina/src/lib/crypto/proof-systems"
OUT="$HERE/wasm"
WASM="$OUT/kimchi-napi.wasm32-wasi.wasm"

# Pin the toolchain proof-systems declares (currently 1.92) explicitly so
# neither a stray RUSTUP_TOOLCHAIN nor an older cargo on PATH can win, and
# make sure that toolchain has the wasm target (napi does not add it).
TOOLCHAIN="$(sed -n 's/^channel *= *"\(.*\)"/\1/p' "$PS_DIR/rust-toolchain.toml")"
if [ -n "$TOOLCHAIN" ] && command -v rustup >/dev/null 2>&1; then
  rustup toolchain list 2>/dev/null | grep -q "^${TOOLCHAIN}-" \
    || rustup toolchain install "$TOOLCHAIN" --profile minimal --no-self-update
  export RUSTUP_TOOLCHAIN="$TOOLCHAIN"
  rustup target add wasm32-wasip1-threads
fi

echo "==> napi build --target wasm32-wasip1-threads --profile release-wasm (in $PS_DIR)"
( cd "$PS_DIR" && napi build \
    --package kimchi-napi \
    --package-json-path "$HERE/package.json" \
    --target wasm32-wasip1-threads \
    --profile release-wasm \
    --platform \
    -o "$OUT" )

echo "==> patch browser loader (async instantiate + pre-spawned worker pool)"
node patch-wasi-browser.mjs

echo "==> wasm-opt -O3"
wasm-opt -O3 \
  --enable-threads --enable-bulk-memory --enable-mutable-globals \
  --enable-sign-ext --enable-nontrapping-float-to-int \
  "$WASM" -o "$WASM"

echo "==> wrote $WASM"
