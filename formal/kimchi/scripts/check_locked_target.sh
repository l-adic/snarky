#!/usr/bin/env bash
# The kimchi knowledge-soundness endpoints are LOCKED — the kimchi-side twin of
# bulletproof-pcs/scripts/check_locked_target.sh, closing the external audit's A-3 (the
# lock protected the IPA rung only; the Tier-1 kimchi statements had no pin).
#
# Five texts are pinned, modulo indentation and internal spacing:
#   TARGET-VESTA / TARGET-PALLAS — the two endpoint statements: binders, hypotheses,
#                      measured event, and the four-summand bound (PROOFS are free to change)
#   WINS             — the measured win predicate: the challenge-generic verifier fed the
#                      table's own reads at every named squeeze, at the WARM base
#   EXTRACTS-WITNESS — the failure predicate: a `PSum.inl` payload whose assembled table
#                      SATISFIES the circuit the key corresponds to (branch + semantics —
#                      weakening either direction keeps every other gate green)
#   RELATION-FINDER  — the break projection the DL reduction consumes, including the
#                      `U`-coefficient split (the `else none` branch is the residual)
#
# plus grep guards: the faithfulness bundle (`FSFaithful`), the pointwise bridge
# (`wins_iff_kimchiVerify`), and both honest-family exhibits still exist.
#
# NOTE on computability, documented here because the IPA gate forbids the same thing:
# kimchi's `relationFinder` IS `noncomputable` — deliberately. Its key gate reads
# Lagrange-interpolated honest windows, and the data-valued/computability guard lives one
# layer down, on the IPA `deployedExtract` underneath (which the IPA lock enforces plain
# `def`) and on `check_extractor_computes.sh`, which `#eval`s the extraction pipeline.
#
# Changing a pinned text is a decision about what is being proved, not a proof step.
#   check_locked_target.sh            check
#   check_locked_target.sh --regen    re-pin (a statement change; needs sign-off)
set -euo pipefail
cd "$(dirname "$0")/.."

expected="scripts/locked_target.expected"
ks="Kimchi/Verifier/KnowledgeSoundness.lean"
bridge="Kimchi/Verifier/Forking/Bridge.lean"
honest="Kimchi/Verifier/Forking/Honest.lean"

render() {
  python3 - "$ks" <<'PY'
import re, sys, pathlib
ks, = (pathlib.Path(p).read_text().splitlines() for p in sys.argv[1:2])

def block(lines, start, end, what):
    i = next((n for n, l in enumerate(lines) if re.match(start, l)), None)
    if i is None:
        return [f'### MISSING-START {what}: no line matches {start}']
    j = next((n for n, l in enumerate(lines[i:], i) if re.search(end, l)), None)
    if j is None:
        return [f'### MISSING-END {what}: no line matches {end} after {start}']
    return lines[i:j + 1]

out = ['### TARGET-VESTA']
out += block(ks, r'^theorem vesta_kimchi_knowledge_sound',
             r'szBudget nc n fam\.idx\.zkRows', 'TARGET-VESTA')
out += ['### TARGET-PALLAS']
out += block(ks, r'^theorem pallas_kimchi_knowledge_sound',
             r'szBudget nc n fam\.idx\.zkRows', 'TARGET-PALLAS')
out += ['### WINS']
out += block(ks, r'^def Wins ', r'^    = true', 'WINS')
out += ['### EXTRACTS-WITNESS']
out += block(ks, r'^def ExtractsWitness ', r'fam\.idx a\)', 'EXTRACTS-WITNESS')
out += ['### RELATION-FINDER']
out += block(ks, r'^noncomputable def relationFinder', r'^        else none', 'RELATION-FINDER')
print('\n'.join(out))
PY
}

norm() { sed 's/^[[:space:]]*//; s/[[:space:]]*$//; s/[[:space:]]\+/ /g' | grep -v '^$'; }

if [[ "${1:-}" == "--regen" ]]; then
  { echo '-- LOCKED: the kimchi knowledge-soundness endpoints. Frozen text.'
    echo '-- Regenerating this file is a STATEMENT CHANGE and requires explicit sign-off.'
    render; } > "$expected"
  echo "re-pinned $expected — this is a statement change; record why"
  exit 0
fi

if ! diff -q <(grep -v '^--' "$expected" | norm) <(render | norm) >/dev/null; then
  echo "✗ a LOCKED kimchi endpoint text has changed"
  diff <(grep -v '^--' "$expected" | norm) <(render | norm) || true
  echo
  echo "This is a change to WHAT is being proved. See docs/locked-target.md."
  exit 1
fi

# The faithfulness layer and the anti-vacuity companions must still exist: without them the
# endpoints are about an unrelated game (an existential-challenge verifier, or an empty win
# set an always-`none` extractor satisfies).
if ! grep -qE '^structure FSFaithful' "$bridge"; then
  echo "✗ faithfulness bundle missing: FSFaithful"; exit 1
fi
if ! grep -qE '^theorem wins_iff_kimchiVerify' "$bridge"; then
  echo "✗ pointwise bridge missing: wins_iff_kimchiVerify"; exit 1
fi
if ! grep -qE '^theorem honestKimchiFamily_wins' "$honest"; then
  echo "✗ anti-vacuity companion missing: honestKimchiFamily_wins"; exit 1
fi
if ! grep -qE '^theorem honestKimchiFamily_failure_set' "$honest"; then
  echo "✗ anti-vacuity companion missing: honestKimchiFamily_failure_set"; exit 1
fi

# THE EXHIBIT SET (see the bulletproof-pcs gate's note): certificates consumed by nothing
# are indistinguishable from dead code once they leave roots.txt, so their existence is
# pinned here instead of relying on review.
for n in exists_ne_zero_kernel_scalarBasis kimchiVerify_eq_verifyWith \
         exists_complete_reductionEfficient; do
  if ! grep -qE "^(theorem|def) $n\b" "$ks"; then
    echo "✗ EXHIBIT MISSING: $n (expected in $ks)"; exit 1
  fi
done
for n in vesta_honest_extraction_failure_measure_le \
         pallas_honest_extraction_failure_measure_le; do
  if ! grep -qE "^theorem $n\b" "$honest"; then
    echo "✗ EXHIBIT MISSING: $n (the per-curve honest-family corollary, in $honest)"
    exit 1
  fi
done

echo "✓ kimchi locked target intact: both endpoint statements, Wins, ExtractsWitness,"
echo "  relationFinder, the faithfulness bundle, and the seven exhibits"
