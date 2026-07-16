import Pasta.Curve
import Pasta.Constants
import Pasta.Basic
import Pasta.Module

/-!
# Pasta — the Pasta curves' trust base

Root module of the `Pasta` library: the generic elliptic-curve order/shape sugar over
Mathlib's `WeierstrassCurve.Affine` (`Pasta/Curve.lean`), the concrete Pasta GLV constants
(`Pasta/Constants.lean`), the curve trust base — the Hasse-bound and CM-eigenvalue axioms
and everything derived from them: group orders, primality, the GLV short-basis bounds
(`Pasta/Basic.lean`) — and the scalar-field module structure on the point groups
(`Pasta/Module.lean`).

This package is the single home of the Pasta curve axioms
(`Pasta.{pallas,vesta}_hasse`, `Pasta.{pallas,vesta}_eigen`); every consumer
(the bulletproof PCS, the kimchi formalization) inherits its trust surface from here.
-/
