import Pasta.Basic
import Pasta.Endo
import Pasta.Shifted

/-!
# Pasta — the Pasta curves' trust base

Root module of the `Pasta` library: the group orders, primality, and the point-group
module structure (`Pasta/Basic.lean`); the GLV endomorphisms — constants, eigenvalue
relations, and short-basis bounds (`Pasta/Endo.lean`); and the wire scalar-shift algebra
(`Pasta/Shifted.lean`).

This package declares no axioms; the curve trust is `native_decide` certificates. Every
consumer (the bulletproof PCS, the kimchi formalization) inherits its trust surface from
here.
-/
