import Pasta.Basic
import Pasta.Endo
import Pasta.Shifted

/-!
# Pasta — the Pasta curves' trust base

Root module of the `Pasta` library:

- `Pasta/Basic.lean` — the group orders and their primality, the bridge to Mathlib's point
  group, and the module structure over each scalar field.
- `Pasta/Endo.lean` — the GLV endomorphisms: constants, eigenvalue relations, and the
  lattice short-basis bounds.
- `Pasta/Shifted.lean` — the wire scalar-shift algebra.

The package declares no axioms. Its curve facts rest on `native_decide` certificates:
CompElliptic's primality and point-count witnesses, plus the two eigenvalue anchors declared
in `Pasta/Endo.lean`. Every consumer — the bulletproof PCS, the kimchi formalization —
inherits that trust surface from here.
-/
