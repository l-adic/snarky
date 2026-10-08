#!/usr/bin/env bash
# The import boundaries, read from the sources' import lines.
#
# The compiler-proof isolation: the ordinary compiler, the definitions the checker and the
# index constructor share, and those two executables reach no module of the lowering's proof
# development (`Snarky.Kimchi.Backend.Internal.*`) and no check module, directly or
# transitively. The checked-compilation facade imports the proof of its lifting theorem, so it
# reaches the internal tree, but no check module.
#
# The check-module boundary: no library root reaches a check module (`Kimchi.Index.CompareChecks`,
# `Snarky.Kimchi.Backend.Checks.*`, `Pickles.Application.Checks.*`), and no library module outside
# those trees imports one. The decided checks are built by the libraries' globs and imported by
# the audit drivers under scripts/, never exposed through `import <Library>`. A violation is
# reported with its import chain from the root.
#
# The closure is computed over every package's library sources (scripts/ drivers and .lake/
# excluded); imports of Mathlib and the git dependencies end the walk, since none of them
# imports back into the workspace. The library roots are read from the packages' lakefiles.
#
# Usage: scripts/check-import-boundaries.sh   (from anywhere; no build needed)
set -euo pipefail
cd "$(dirname "$0")/.."

declare -A imports
for pkg in pasta poseidon bulletproof-pcs kimchi snarky pickles; do
  while IFS= read -r f; do
    m="${f#"$pkg"/}"
    m="${m%.lean}"
    m="${m//\//.}"
    imports[$m]="$({ grep -E '^import ' "$f" || true; } | awk '{print $2}' | tr '\n' ' ')"
  done < <(find "$pkg" -name '*.lean' -not -path '*/.lake/*' -not -path '*/scripts/*' | sort)
done

declare -A parent
walk() { # $1 = root: parent[] gets a shortest import chain to every workspace module reached
  parent=()
  local queue=("$1") m d
  parent[$1]="."
  while ((${#queue[@]})); do
    m="${queue[0]}"
    queue=("${queue[@]:1}")
    for d in ${imports[$m]:-}; do
      [[ -n "${imports[$d]+x}" && -z "${parent[$d]+x}" ]] || continue
      parent[$d]="$m"
      queue+=("$d")
    done
  done
}

chain() { # $1 = a module reached by the last walk: its import chain from the root
  local c="$1" p="${parent[$1]}"
  while [[ "$p" != "." ]]; do
    c="$p -> $c"
    p="${parent[$p]}"
  done
  echo "$c"
}

fail=0

forbid() { # $1 = module, $2 = regex of forbidden modules, $3 = what they are
  [[ -n "${imports[$1]+x}" ]] || { echo "✗ $1: no such module"; fail=1; return; }
  walk "$1"
  local bad=() m
  for m in "${!parent[@]}"; do
    [[ "$m" != "$1" && "$m" =~ $2 ]] && bad+=("$m")
  done
  if ((${#bad[@]})); then
    echo "✗ $1 reaches $3:"
    for m in $(printf '%s\n' "${bad[@]}" | sort); do
      echo "    $(chain "$m")"
    done
    fail=1
  else
    echo "✓ $1 reaches no $3"
  fi
}

B=Snarky.Kimchi.Backend
CHECKS='(^Kimchi\.Index\.CompareChecks$|\.Checks\.)'

for m in Compile Admissibility IndexSpec ScopedCheck CompiledIndex; do
  forbid "$B.$m" "^$B\.(Internal|Checks)\." "proof or check module"
done
forbid "$B.CheckedCompile" "^$B\.Checks\." "check module"

roots=$(awk '/^\[\[lean_lib\]\]/ { want = 1; next }
  want && /^name = / { gsub(/"/, "", $3); print $3; want = 0 }' */lakefile.toml | sort)
for root in $roots; do
  forbid "$root" "$CHECKS" "check module"
done

leaks=""
for m in "${!imports[@]}"; do
  [[ "$m" =~ $CHECKS ]] && continue
  for d in ${imports[$m]}; do
    [[ "$d" =~ $CHECKS ]] && leaks+="$m imports $d"$'\n'
  done
done
if [[ -n "$leaks" ]]; then
  echo "✗ library modules outside the check trees import check modules:"
  printf '%s' "$leaks" | sort | sed 's/^/    /'
  fail=1
else
  echo "✓ no library module outside the check trees imports a check module"
fi

if ((fail)); then
  echo "── import boundaries FAILED ──"
  exit 1
fi
echo "── import boundaries OK ──"
