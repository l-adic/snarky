/-
Environment linters for the Kimchi formalization.

Runs Batteries' standard `@[env_linter]` suite (docBlame, unusedArguments, simpNF,
checkType, etc.) over **only** the `Kimchi.*` declarations — not Mathlib's — via the
`#lint in <pkg>` scoping. On any finding it `logError`s (so `lean` exits non-zero, which
gates CI); otherwise it prints "All linting checks passed!".

Run it with:  lake env lean scripts/lint.lean      (or: scripts/lint.sh)
-/
import Kimchi
import Batteries.Tactic.Lint

#lint in Kimchi
