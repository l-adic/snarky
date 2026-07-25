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

expected=$'bulletproof-pcs/Bulletproof/Forking/Deployed.lean:812'

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

echo "✓ sorry census unchanged: 1 known sorry"
echo "  bulletproof-pcs/Bulletproof/Forking/Deployed.lean:812 — deployedExtract_failure_measure_le"
