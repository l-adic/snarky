#!/usr/bin/env bash
# Build the kimchi-napi crate from the in-tree proof-systems submodule
# and copy the resulting cdylib here under the platform-suffixed .node
# name that index.js expects. Idempotent: re-runs cargo (which is itself
# incremental) and re-copies the artifact on every invocation.

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)  NODE_NAME=kimchi-napi.linux-x64-gnu.node;   LIB=libkimchi_napi.so   ;;
  Linux-aarch64) NODE_NAME=kimchi-napi.linux-arm64-gnu.node; LIB=libkimchi_napi.so   ;;
  Darwin-x86_64) NODE_NAME=kimchi-napi.darwin-x64.node;      LIB=libkimchi_napi.dylib ;;
  Darwin-arm64)  NODE_NAME=kimchi-napi.darwin-arm64.node;    LIB=libkimchi_napi.dylib ;;
  *)
    echo "kimchi-napi/build.sh: unsupported host $(uname -s) $(uname -m)" >&2
    exit 1
    ;;
esac

PS_DIR="../../mina/src/lib/crypto/proof-systems"

# Build with exactly the toolchain proof-systems pins in its rust-toolchain.toml
# (currently 1.92) in EVERY environment. Go through `rustup run <pinned>` so
# that neither a stray RUSTUP_TOOLCHAIN (CI's dtolnay/rust-toolchain action
# exports one) nor an older cargo first on PATH (the mina nix dev shell ships
# 1.82, too old for napi-derive's convert_case 0.8.0) can win. A pinned version
# installs with the minimal profile -- no channel sync, no rust-src component
# download (that download races across cargo's parallel rustc jobs and fails on
# CI runners). If rustup is unavailable we fall back to bare cargo.
TOOLCHAIN="$(sed -n 's/^channel *= *"\(.*\)"/\1/p' "$PS_DIR/rust-toolchain.toml")"

if [ -n "$TOOLCHAIN" ] && command -v rustup >/dev/null 2>&1; then
  rustup toolchain list 2>/dev/null | grep -q "^${TOOLCHAIN}-" \
    || rustup toolchain install "$TOOLCHAIN" --profile minimal --no-self-update
  CARGO=(rustup run "$TOOLCHAIN" cargo)
else
  CARGO=(cargo)
fi

echo "==> ${CARGO[*]} build -p kimchi-napi --release (in $PS_DIR)"
( cd "$PS_DIR" && "${CARGO[@]}" build -p kimchi-napi --release )

SRC="$PS_DIR/target/release/$LIB"
[ -f "$SRC" ] || { echo "expected artifact missing: $SRC" >&2; exit 1; }

cp "$SRC" "$NODE_NAME"
echo "==> wrote $(pwd)/$NODE_NAME"
