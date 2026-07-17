#!/usr/bin/env bash
# Emit a Graphviz DOT graph of the module-level import dependencies across every
# workspace package (one cluster per package; edges between our own modules only —
# Mathlib / CompElliptic / core-Lean imports are omitted). Library sources only:
# each package's scripts/ drivers and .lake/ build dirs are excluded.
#
# Usage:  scripts/module-deps.sh [out.dot]     (default: docs/module-deps.dot)
# Render: dot -Tsvg docs/module-deps.dot -o docs/module-deps.svg
set -euo pipefail
cd "$(dirname "$0")/.."
out="${1:-docs/module-deps.dot}"

pkgs=(pasta poseidon bulletproof-pcs kimchi snarky)

srcs() { # $1 = package dir
  find "$1" -name '*.lean' -not -path '*/.lake/*' -not -path '*/scripts/*' | sort
}

mod_of() { # $1 = package dir, $2 = file path -> module name
  local m="${2#"$1"/}"
  m="${m%.lean}"
  printf '%s' "${m//\//.}"
}

{
  echo 'digraph "formal-modules" {'
  echo '  rankdir=LR;'
  echo '  node [shape=box, fontsize=10, fontname="Helvetica"];'
  echo '  edge [color=gray40, arrowsize=0.6];'
  for p in "${pkgs[@]}"; do
    echo "  subgraph \"cluster_${p}\" {"
    echo "    label=\"${p}\"; color=gray60; fontsize=12; fontname=\"Helvetica-Bold\";"
    while IFS= read -r f; do
      echo "    \"$(mod_of "$p" "$f")\";"
    done < <(srcs "$p")
    echo '  }'
  done
  for p in "${pkgs[@]}"; do
    while IFS= read -r f; do
      m="$(mod_of "$p" "$f")"
      { grep -hE '^import (Kimchi|Snarky|Pasta|Poseidon|FixtureKit|Bulletproof)(\.[A-Za-z0-9_.]+)?[[:space:]]*$' "$f" || true; } \
        | sed 's/^import //; s/[[:space:]]*$//' \
        | while IFS= read -r dep; do
            echo "  \"${m}\" -> \"${dep}\";"
          done
    done < <(srcs "$p")
  done
  echo '}'
} > "$out"

echo "wrote ${out}: $(grep -c '^    "' "$out") module node(s), $(grep -c ' -> ' "$out") edge(s)"
