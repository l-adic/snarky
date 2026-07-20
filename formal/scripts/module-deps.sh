#!/usr/bin/env bash
# Emit a Graphviz DOT graph of the module-level import dependencies across every
# workspace package (one cluster per package; edges between our own modules only —
# Mathlib / CompElliptic / core-Lean imports are omitted). Library sources only:
# each package's scripts/ drivers and .lake/ build dirs are excluded.
#
# Usage:  scripts/module-deps.sh [out.dot]     (default: docs/module-deps.dot)
# Render: dot -Tsvg docs/module-deps.dot -o docs/module-deps.svg  (or `make lean-dep-graph`)
set -euo pipefail
cd "$(dirname "$0")/.."
out="${1:-docs/module-deps.dot}"

pkgs=(pasta poseidon bulletproof-pcs kimchi snarky)

# Per-package fill colour (light tint; nodes stay white for readable text).
declare -A pkg_color=(
  [pasta]="#cfe8ff"          # blue
  [poseidon]="#d5f0d0"       # green
  [bulletproof-pcs]="#ffe0c2" # orange
  [kimchi]="#e6d5f0"         # purple
  [snarky]="#ffd6d6"         # red
)

srcs() { # $1 = package dir
  find "$1" -name '*.lean' -not -path '*/.lake/*' -not -path '*/scripts/*' | sort
}

mod_of() { # $1 = package dir, $2 = file path -> module name
  local m="${2#"$1"/}"
  m="${m%.lean}"
  printf '%s' "${m//\//.}"
}

# Second-level namespace group of a module: the first two dotted segments when the
# module lies at least three deep (`Kimchi.Gate.AddComplete` -> `Kimchi.Gate`,
# `Kimchi.Gate.Semantics.X` -> `Kimchi.Gate`). Shallower modules (`Kimchi.Domain`)
# get no group and float free in the package cluster.
group_of() { # $1 = module name -> "Prefix.Second" (one per line) or nothing
  local m="$1" dots="${1//[^.]/}"
  if [ "${#dots}" -ge 2 ]; then printf '%s\n' "$(printf '%s' "$m" | cut -d. -f1-2)"; fi
}

# Emit the module nodes of a package cluster, boxing each 2nd-level namespace group
# (modules >= 3 deep) into a nested subcluster and leaving shallower modules free.
emit_grouped_nodes() { # $1 = package dir
  local m g mods=() groups
  while IFS= read -r f; do mods+=("$(mod_of "$1" "$f")"); done < <(srcs "$1")
  for m in "${mods[@]}"; do
    if [ -z "$(group_of "$m")" ]; then echo "    \"$m\";"; fi
  done
  groups="$(for m in "${mods[@]}"; do group_of "$m"; done | grep -v '^$' | sort -u || true)"
  for g in $groups; do
    echo "    subgraph \"cluster_${1}_${g//./_}\" {"
    echo "      label=\"${g}\"; style=\"filled,dashed\"; fillcolor=white;"
    echo "      color=gray55; fontsize=11; fontname=\"Helvetica-Oblique\";"
    for m in "${mods[@]}"; do
      if [ "$(group_of "$m")" = "$g" ]; then echo "      \"$m\";"; fi
    done
    echo '    }'
  done
}

{
  echo 'digraph "formal-modules" {'
  # Top-to-bottom: an edge `A -> B` (module A imports B) points downward, so an
  # arrow pointing down reads "depends on" — dependencies sink toward the bottom.
  echo '  rankdir=TB;'
  # Wide, shallow DAG: give each dependency level generous vertical separation so the
  # layers read clearly, and keep nodes horizontally tight so it does not sprawl wider.
  echo '  ranksep=1.6; nodesep=0.25;'
  echo '  node [shape=box, style=filled, fillcolor=white, fontsize=10, fontname="Helvetica"];'
  echo '  edge [color=gray40, arrowsize=0.6];'
  for p in "${pkgs[@]}"; do
    echo "  subgraph \"cluster_${p}\" {"
    echo "    label=\"${p}\"; style=filled; fillcolor=\"${pkg_color[$p]}\";"
    echo "    color=gray50; fontsize=12; fontname=\"Helvetica-Bold\";"
    if [ "$p" = kimchi ]; then
      emit_grouped_nodes "$p"
    else
      while IFS= read -r f; do
        echo "    \"$(mod_of "$p" "$f")\";"
      done < <(srcs "$p")
    fi
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

echo "wrote ${out}: $(grep -cE '^ +"[^"]+";$' "$out") module node(s), $(grep -c ' -> ' "$out") edge(s)"
