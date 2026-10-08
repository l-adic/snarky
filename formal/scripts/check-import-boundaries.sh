#!/usr/bin/env bash
# The compiler-proof isolation boundaries, read from the sources' import lines.
#
# The ordinary compiler, the definitions the checker and the index constructor share, and
# those two executables reach no module of the lowering's proof development
# (`Snarky.Kimchi.Backend.Internal.*`) and no check module (`Snarky.Kimchi.Backend.Checks.*`),
# directly or transitively. The checked-compilation facade imports the proof of its lifting
# theorem, so it reaches the internal tree, but no check module. No library module outside
# the checks tree imports a check module.
#
# The closure is computed over the snarky and pickles library sources (scripts/ drivers and
# .lake/ excluded); imports of other packages and of Mathlib end the walk, since none of them
# imports back into snarky.
#
# Usage: scripts/check-import-boundaries.sh   (from anywhere; no build needed)
set -euo pipefail
cd "$(dirname "$0")/.."

declare -A imports
for pkg in snarky pickles; do
  while IFS= read -r f; do
    m="${f#"$pkg"/}"
    m="${m%.lean}"
    m="${m//\//.}"
    imports[$m]="$({ grep -E '^import ' "$f" || true; } | awk '{print $2}' | tr '\n' ' ')"
  done < <(find "$pkg" -name '*.lean' -not -path '*/.lake/*' -not -path '*/scripts/*' | sort)
done

closure() { # $1 = module -> every workspace module it imports, transitively
  local -A seen=()
  local queue=("$1") m d
  while ((${#queue[@]})); do
    m="${queue[0]}"
    queue=("${queue[@]:1}")
    for d in ${imports[$m]:-}; do
      [[ -n "${imports[$d]+x}" && -z "${seen[$d]+x}" ]] || continue
      seen[$d]=1
      queue+=("$d")
    done
  done
  ((${#seen[@]})) && printf '%s\n' "${!seen[@]}"
  return 0
}

B=Snarky.Kimchi.Backend
fail=0

forbid() { # $1 = module, $2 = regex of forbidden modules, $3 = what they are
  [[ -n "${imports[$1]+x}" ]] || { echo "✗ $1: no such module"; fail=1; return; }
  local bad
  bad=$(closure "$1" | grep -E "$2" | sort || true)
  if [[ -n "$bad" ]]; then
    echo "✗ $1 reaches $3:"
    printf '    %s\n' $bad
    fail=1
  else
    echo "✓ $1 reaches no $3"
  fi
}

for m in Compile Admissibility IndexSpec ScopedCheck CompiledIndex; do
  forbid "$B.$m" "^$B\.(Internal|Checks)\." "proof or check module"
done
forbid "$B.CheckedCompile" "^$B\.Checks\." "check module"

leaks=""
for m in "${!imports[@]}"; do
  [[ "$m" == "$B.Checks."* ]] && continue
  for d in ${imports[$m]}; do
    [[ "$d" == "$B.Checks."* ]] && leaks+="$m imports $d"$'\n'
  done
done
if [[ -n "$leaks" ]]; then
  echo "✗ library modules outside the checks tree import check modules:"
  printf '%s' "$leaks" | sort | sed 's/^/    /'
  fail=1
else
  echo "✓ no library module outside the checks tree imports a check module"
fi

if ((fail)); then
  echo "── import boundaries FAILED ──"
  exit 1
fi
echo "── import boundaries OK ──"
