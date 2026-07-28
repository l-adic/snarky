#!/usr/bin/env bash
# The target statement is LOCKED (docs/locked-target.md). This gate is what makes that mechanical.
#
# A prover — human or autonomous — closing a hard bound is under constant pressure to adjust the
# statement instead: add a hypothesis, widen the error, weaken a disjunct, restate acceptance away
# from the wire verifier. Every one of those keeps the build green and the sorry count falling while
# proving something else. Nothing else in the gate set can see it.
#
# Seven texts are pinned, modulo indentation and internal spacing:
#   TARGET           — the query-loss rung's binders and conclusion (its PROOF is free to change)
#   EXTRACTOR        — `deployedExtract`'s signature and return type
#   CONCLUSION-TYPE  — `OpeningOrBreak`, so the disjunction cannot lose a side
#   TERMINAL         — the DL-charged endpoint's binders and conclusion
#   HAS-OPENING      — the failure predicate, which must inspect the `PSum.inl` BRANCH
#   RELATION-FINDER  — the break projection the DL reduction consumes, including the split on the
#                      `U` coefficient (the `else none` branch is the residual being filtered out)
#   RESIDUAL-ASSUMPTION — `DerivedUDLAdvantageLE`, the price of the `U`-touching breaks
#
# plus: the extractor is a plain `def`, and both anti-vacuity companions still exist.
#
# RESIDUAL-ASSUMPTION is pinned because it is the one hypothesis with no upstream counterpart:
# kimchi's `U` is transcript derived, so no DL challenge can be planted there and the event is
# NOT reducible to textbook DL. `derivedUDL_iff_residual_measure` proves it is the residual
# event's own measure. Widening it — or quietly folding it into `ε` — would hide the one place
# this development assumes more than ironwood does.
#
# HAS-OPENING is the one that matters most. `deployedExtract` returns `opening ⊕' DL-relation`,
# and at a prime-order group a nontrivial relation among the generators ALWAYS exists
# (Soundness.lean:104-108). So a failure predicate reading `= none` — mere absence of an
# instance — is satisfied by an extractor that returns a break on every accepting run, and
# proves nothing. Upstream inspects the branch for exactly this reason
# (`ComputedAlgebraicFSFamily.hasCleanOpening`, Algebraic.lean:1164). Weakening `HasOpening`
# back to `= none` would keep the build, the axiom census and the sorry census all green.
#
# Changing a pinned text is a decision about what is being proved, not a proof step.
#   check_locked_target.sh            check
#   check_locked_target.sh --regen    re-pin (a statement change; needs sign-off)
set -euo pipefail
cd "$(dirname "$0")/.."

expected="scripts/locked_target.expected"
dep="Bulletproof/Forking/Deployed.lean"
game="Bulletproof/Forking/Game.lean"
ks="Bulletproof/Forking/KnowledgeSoundness.lean"

render() {
  python3 - "$dep" "$game" "$ks" <<'PY'
import re, sys, pathlib
dep, game, ks = (pathlib.Path(p).read_text().splitlines() for p in sys.argv[1:4])

def block(lines, start, end, what):
    # A missing anchor is itself a statement change (the usual cause: the pinned bound was edited,
    # so the end marker no longer matches). Report it as data, never as a traceback — a confusing
    # failure invites fixing this script instead of the statement.
    i = next((n for n, l in enumerate(lines) if re.match(start, l)), None)
    if i is None:
        return [f'### MISSING-START {what}: no line matches {start}']
    j = next((n for n, l in enumerate(lines[i:], i) if re.search(end, l)), None)
    if j is None:
        return [f'### MISSING-END {what}: no line matches {end} after {start}']
    return lines[i:j + 1]

out = ['### TARGET']
out += block(dep, r'^theorem deployedExtract_failure_measure_le', r'2 \^ 128 : ℕ', 'TARGET')
out += ['### EXTRACTOR']
out += block(dep, r'^def deployedExtract ', r'^    Option \(OpeningOrBreak', 'EXTRACTOR')
out += ['### CONCLUSION-TYPE']
out += block(game, r'^abbrev OpeningOrBreak ', r'augmentedBasis', 'CONCLUSION-TYPE')
out += ['### TERMINAL']
out += block(ks, r'^theorem deployedExtract_noOpening_measure_le_of_textbookDL',
             r'Fintype\.card \(SetupIndex', 'TERMINAL')
out += ['### HAS-OPENING']
out += block(ks, r'^def HasOpening ', r'PSum\.inl', 'HAS-OPENING')
out += ['### RELATION-FINDER']
out += block(ks, r'^def relationFinder', r'^        else none', 'RELATION-FINDER')
out += ['### RESIDUAL-ASSUMPTION']
out += block(ks, r'^def DerivedUDLAdvantageLE ', r'isSome\} ≤ bound', 'RESIDUAL-ASSUMPTION')
print('\n'.join(out))
PY
}

# Compare modulo leading/trailing whitespace and runs of spaces: reindentation is allowed, any
# change of term, binder or bound is not.
norm() { sed 's/^[[:space:]]*//; s/[[:space:]]*$//; s/[[:space:]]\+/ /g' | grep -v '^$'; }

if [[ "${1:-}" == "--regen" ]]; then
  { echo '-- LOCKED: the target statement (docs/locked-target.md). Frozen text.'
    echo '-- Regenerating this file is a STATEMENT CHANGE and requires explicit sign-off.'
    render; } > "$expected"
  echo "re-pinned $expected — this is a statement change; record why"
  exit 0
fi

if ! diff -q <(grep -v '^--' "$expected" | norm) <(render | norm) >/dev/null; then
  echo "✗ the LOCKED target has changed"
  diff <(grep -v '^--' "$expected" | norm) <(render | norm) || true
  echo
  echo "This is a change to WHAT is being proved. See docs/locked-target.md."
  exit 1
fi

# `noncomputable` would void the anti-vacuity guard: the return type is data, and computability is
# what separates a reduction that computes the break from one asserting a relation exists.
if grep -qE '^noncomputable def deployedExtract' "$dep"; then
  echo "✗ deployedExtract is marked noncomputable — that voids the data-valued guard"; exit 1
fi

# Without these the bound is free: an extractor that always answers `none` satisfies it whenever
# the win set is empty.
if ! grep -qE '^theorem verifyWith_of_deferred_delta' "$dep"; then
  echo "✗ anti-vacuity companion missing: verifyWith_of_deferred_delta"; exit 1
fi
if ! grep -qE '^theorem honestNode_wireWins_everywhere' Bulletproof/Forking/Honest.lean; then
  echo "✗ anti-vacuity companion missing: honestNode_wireWins_everywhere"; exit 1
fi

# THE EXHIBIT SET. Every self-audit certificate — the results whose whole job is to say what
# the endpoints do NOT claim — pinned by existence here, because nothing else can protect
# them: an exhibit is by construction consumed by nothing, so under the dead=0 gate it is
# indistinguishable from dead code the moment it leaves roots.txt. (That is not
# hypothetical: the dead-code sweep at e7c431b2 deleted kimchi's concrete-index exhibits for
# exactly this reason, which the external audit found and generalized in its addendum.)
# Deleting one now fails a LOCK — a statement-level decision needing sign-off — rather than
# passing silently.
exhibits_dep='sg_determined_of_verifyWith wireWins_pinTable pinTable_factors chainAt_sg
              nodeTranscript_nodes uBaseOf_eq_transcript identityTape exists_complete_coins'
exhibits_ks='wireWins_U_irrelevant deployedExtract_U_irrelevant uRepresentationOfBreak
             reductionEfficient_exists derivedUDL_iff_residual_measure honestFamily_failure_set'
exhibits_tr='verifyOracle_spongeFS verifyOracleFrom_spongeFSFrom spongeFS_eq_from
             toGroup_spongeOBase_preT'
exhibits_hon='winsAtBase_uBaseOf honestNode_wins_everywhere'
for pair in "$dep:$exhibits_dep" "$ks:$exhibits_ks" \
            "Bulletproof/Forking/Transcript.lean:$exhibits_tr" \
            "Bulletproof/Forking/Honest.lean:$exhibits_hon"; do
  file="${pair%%:*}"; names="${pair#*:}"
  for n in $names; do
    if ! grep -qE "^(theorem|def|noncomputable def) ([A-Za-z_.]*\.)?$n\b" "$file"; then
      echo "✗ EXHIBIT MISSING: $n (expected in $file)"
      echo "  Exhibits are the anti-vacuity layer. Removing one is a decision about what"
      echo "  the endpoints claim, not a cleanup — see docs/locked-target.md."
      exit 1
    fi
  done
done

echo "✓ locked target intact: statement, extractor type, conclusion type,"
echo "  plain-def extractor, both anti-vacuity companions, and the 20 exhibits"
