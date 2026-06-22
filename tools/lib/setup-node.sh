#!/usr/bin/env bash
# tools/lib/setup-node.sh — pin node version for reproducible runs.
# Source after setting REPO_ROOT. Respects PINNED_NODE_VERSION env override.

: "${PINNED_NODE_VERSION:=v23.11.1}"
PINNED_NODE="$HOME/.nvm/versions/node/${PINNED_NODE_VERSION}/bin"
if [ -x "$PINNED_NODE/node" ]; then
  export PATH="$PINNED_NODE:$PATH"
else
  warn "pinned node ${PINNED_NODE_VERSION} not at $PINNED_NODE — using $(command -v node) ($(node --version 2>/dev/null)). Install ${PINNED_NODE_VERSION} (nvm install ${PINNED_NODE_VERSION#v}) or set PINNED_NODE_VERSION."
fi
echo "==> node: $(node --version) ($(command -v node))"
