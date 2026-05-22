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

# Build with the rustc that proof-systems/rust-toolchain.toml pins (currently
# 1.92), not whatever `cargo` is first on PATH. Some environments (notably the
# mina nix dev shell) put an older cargo ahead of the rustup shim; napi-derive
# pulls convert_case 0.8.0, which fails to compile on the nix 1.82 cargo
# (E0599: no method `graphemes` on &str). `rustup which cargo`, run from
# PS_DIR, reads the toolchain file and hands back the matching cargo.
if command -v rustup >/dev/null 2>&1; then
  CARGO="$(cd "$PS_DIR" && rustup which cargo)"
else
  CARGO="cargo"
fi

echo "==> $CARGO build -p kimchi-napi --release (in $PS_DIR)"
( cd "$PS_DIR" && "$CARGO" build -p kimchi-napi --release )

SRC="$PS_DIR/target/release/$LIB"
[ -f "$SRC" ] || { echo "expected artifact missing: $SRC" >&2; exit 1; }

cp "$SRC" "$NODE_NAME"
echo "==> wrote $(pwd)/$NODE_NAME"
