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

# The tree is sorry-free. Both knowledge-soundness endpoints and the Fiat-Shamir
# faithfulness theorem are proved; the residual modelling assumption is carried as the
# `FSFaithful` hypothesis in Verifier/Forking/Bridge.lean, not as an open proof.
expected=''

# Scope includes the fixture-decoding libraries and every scripts/ driver (external-audit
# A-1: the artifact checks run through exactly that code, so a sorry there voids them).
# Prose mentions are filtered: a real `sorry` is never backticked and never sits after
# a line-comment marker.
actual=$(grep -rn '\bsorry\b' \
  bulletproof-pcs/Bulletproof bulletproof-pcs/BulletproofFixture.lean \
  bulletproof-pcs/scripts kimchi/Kimchi kimchi/KimchiFixture kimchi/KimchiFixture.lean \
  kimchi/Main.lean kimchi/scripts pasta pickles poseidon snarky scripts/deadcode.lean \
  --include='*.lean' \
  | grep -Fv -- '`sorry`' | grep -vE -- '--.*\bsorry\b' \
  | cut -d: -f1,2 | sort || true)

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
