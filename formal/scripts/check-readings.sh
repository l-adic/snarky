#!/usr/bin/env bash
# Every domain `CircuitType` instance owes its reading lemmas.
#
# `CircuitType.ofEquiv`/`ofShape` hand you an instance whose `Reads`/`Scoped` are true
# by `Iff.rfl` but syntactically opaque: their characterizations (`CircuitType.reads_ofEquiv`
# and friends) match on the instance TERM being literally `CircuitType.ofEquiv ev ew`, and
# `simp` will not unfold a named instance to discover that. So nothing derives the
# characterization — not the former, not Lean's `Generic`-style machinery, not the PureScript
# original's generic derivation, which produces the FUNCTION and never a theorem about it.
#
# Left unwritten, every consumer re-derives the unfolding inline. This gate makes the
# obligation explicit: declaring `instance … : CircuitType F (X …) (X …)` for a domain type
# obliges either a `reads_x` and a `scoped_x` in the same module, or — for an `ofEquiv`
# instance — an `@[simps apply]` decomposition, whose projection lemma lets the
# `reads_simps` set (Snarky.Encoding.Simps) decompose the reading generically.
#
# The formers themselves (`F`, `Bool`, `Unit`, `Prod`, `Vector`, `UnChecked`) are exempt:
# their lemmas live in Snarky/Prover.lean, keyed on the former rather than on a type.
#
# Usage:
#   check-readings.sh   # check only; non-zero exit on any violation
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2   # -> formal/

# Modules that DEFINE the formers and their lemmas, not domain types.
exempt_modules=(
  "./snarky/Snarky/Encoding.lean"
  "./snarky/Snarky/Prover.lean"
)

files=()
while IFS= read -r f; do files+=("$f"); done \
  < <(find . -name '*.lean' \
        -not -path '*/.lake/*' -not -path './vendor/*' -not -path './.archon-seed/*' \
        -not -path './.archon/*' | sort)

violations=0
checked=0

for f in "${files[@]}"; do
  skip=0
  for e in "${exempt_modules[@]}"; do [ "$f" = "$e" ] && skip=1; done
  [ "$skip" -eq 1 ] && continue

  # An instance whose declared class is `CircuitType` — matched after the bracketed
  # binders are stripped, so `[CircuitType F a va] => …` (an instance ARGUMENT of some
  # other class) does not count.
  while IFS= read -r decl; do
    line="${decl%%:*}"
    body="${decl#*:}"
    stripped=$(printf '%s' "$body" | sed 's/\[[^][]*\]//g')
    printf '%s' "$stripped" | grep -q ': *CircuitType' || continue
    # `CircuitType F (Val …) (Var …)` — the lemmas are named for the VAR head, which is
    # what a proof holds (`SpongeState` for the `Triple` value, `AffinePoint` for both).
    head=$(printf '%s' "$stripped" \
      | sed -n 's/.*: *CircuitType [^ ]* *(\{0,1\}\([A-Za-z_][A-Za-z0-9_.]*\).*/\1/p')
    var=$(printf '%s' "$stripped" \
      | sed -n 's/.*: *CircuitType [^ ]* *([^)]*) *(\{0,1\}\([A-Za-z_][A-Za-z0-9_.]*\).*/\1/p')
    [ -n "$var" ] && head="$var"
    [ -z "$head" ] && continue
    short="${head##*.}"
    lemma="$(printf '%s' "${short:0:1}" | tr '[:upper:]' '[:lower:]')${short:1}"
    checked=$((checked + 1))
    # Either style discharges the obligation: the two reading lemmas by hand, or an
    # `ofEquiv` instance whose decomposition carries `@[simps apply]` — its projection lemma
    # is what `simp [reads_simps]` (Snarky.Encoding.Simps) decomposes the reading with.
    if grep -q "theorem reads_${lemma}\b" "$f" && grep -q "theorem scoped_${lemma}\b" "$f"; then
      continue
    fi
    equiv=$(printf '%s' "$body" \
      | sed -n 's/.*CircuitType\.ofEquiv (\{0,1\}\([A-Za-z_][A-Za-z0-9_.]*\).*/\1/p')
    if [ -n "$equiv" ] \
        && grep -Eq "@\[simps[^]]*\][[:space:]]+def[[:space:]]+(_root_\.)?([A-Za-z0-9_]+\.)*${equiv//./\\.}([[:space:]]|$)" "$f"; then
      continue
    fi
    echo "$f:$line: CircuitType instance for '$short' has neither 'reads_${lemma}'/'scoped_${lemma}' nor an '@[simps apply]' decomposition"
    violations=$((violations + 1))
  done < <(awk '
    /^instance/ { buf = $0; ln = NR; depth = 1; next }
    depth == 1 { buf = buf " " $0 }
    depth == 1 && /:=|where[ \t]*$/ { depth = 2; tail = 0; next }
    depth == 2 { buf = buf " " $0; tail++; if (tail == 2) { print ln ":" buf; depth = 0 } }
  ' "$f" | grep "CircuitType")
done

if [ "$violations" -ne 0 ]; then
  echo
  echo "reading-lemma gate FAILED: $violations missing ($checked instances checked)"
  exit 1
fi

echo "✓ reading lemmas present ($checked CircuitType instances)"
