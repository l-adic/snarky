#!/usr/bin/env bash
# The sorry census, pinned as a literal.
#
# The axiom gates cannot see this: `roots.txt` names no `Forking.*` declaration, so a sorried
# theorem under `Forking/` passes `check_axioms.sh` untouched. During a refactor that both deletes
# and restates proofs, an accidental `sorry` is exactly how a step "passes" while proving nothing —
# and a sorry that silently DISAPPEARS is equally suspect, because it means a statement changed.
# So this pins the set in both directions: any addition or removal fails, and closing a sorry means
# editing the expected list in the same commit.
set -euo pipefail
cd "$(dirname "$0")/.."

# The kimchi knowledge-soundness module is a STATEMENT: its three open proofs are the
# deliverable's boundary, not work in progress that slipped through.
#   178 — kimchiVerify_eq_verifyWith: Fiat-Shamir faithfulness. KNOWN TOO WEAK to be worth
#         closing as stated: the existential does not pin its witnesses, and the one-liner
#         that closes it also closes the same statement for a verifier with Fiat-Shamir
#         deleted. Restate it at a named sponge source before discharging.
#  1664 — vesta_kimchi_knowledge_sound
#  1681 — pallas_kimchi_knowledge_sound
expected='kimchi/Kimchi/Verifier/KnowledgeSoundness.lean:1664
kimchi/Kimchi/Verifier/KnowledgeSoundness.lean:1681
kimchi/Kimchi/Verifier/KnowledgeSoundness.lean:178'

actual=$(grep -rn '\bsorry\b' \
  bulletproof-pcs/Bulletproof kimchi/Kimchi pasta poseidon snarky \
  --include='*.lean' | cut -d: -f1,2 | sort || true)

if [[ "$actual" != "$expected" ]]; then
  echo "✗ sorry census changed"
  echo "--- expected ---"; echo "$expected"
  echo "--- actual ---";   echo "${actual:-(none)}"
  echo
  echo "If you closed a sorry, delete its line from \$expected in this script, same commit."
  exit 1
fi

if [[ -z "$expected" ]]; then
  echo "✓ sorry census unchanged: the tree is sorry-free"
else
  echo "✓ sorry census unchanged: $(echo "$expected" | wc -l) known sorry/sorries"
  echo "$expected" | sed 's/^/  /'
fi
