import Pasta.Curve
import Pasta.Constants
import Pasta.Basic
import Pasta.Endo
import Pasta.Module
import Pasta.Shifted

/-!
# Pasta — the Pasta curves' trust base

Root module of the `Pasta` library: the generic elliptic-curve order/shape sugar over
Mathlib's `WeierstrassCurve.Affine` (`Pasta/Curve.lean`), the concrete Pasta GLV constants
(`Pasta/Constants.lean`), the curve trust base — the Hasse-bound and CM-eigenvalue axioms
and everything derived from them: group orders, primality, the GLV short-basis bounds
(`Pasta/Basic.lean`), the GLV eigenvalue relations PROVED from the endomorphism's
homomorphism property + prime-order cyclicity + `native_decide` anchors at the generators
(`Pasta/Endo.lean`), and the scalar-field module structure on the point groups
(`Pasta/Module.lean`).

This package is the single home of the Pasta curve axioms — now ONLY the Hasse bounds
(`Pasta.{pallas,vesta}_hasse`); the CM eigenvalue relations are theorems; every consumer
(the bulletproof PCS, the kimchi formalization) inherits its trust surface from here.
-/
