import Kimchi.Cycle.Soundness
import Kimchi.Cycle.Pasta

/-!
# VarBaseMul soundness at the real Pasta curve

`varBaseMul_deployed_correct` is proved abstractly over any `WeierstrassCurve.Affine` carrying
the short-shape and prime-order `Fact`s, and is `#print axioms`-clean. Here we instantiate it at
the concrete Pallas curve: the two `Fact`s are discharged from `Cycle/Pasta.lean` — the
prime-order one through the trusted point count `pallas_card`. So this theorem (and only this
theorem) depends on the point-count axiom; the abstract development stays axiom-free.
-/

namespace Kimchi.Cycle

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine Kimchi.Circuit.VarBaseMul

/-- **The deployed VarBaseMul circuit is correct on the real Pallas curve.** Same statement as
    `varBaseMul_deployed_correct`, with the curve fixed to `Pallas.curve.toAffine`; the
    short-shape and prime-order hypotheses are supplied by the `Fact` instances in
    `Cycle/Pasta.lean`, and `2 ≠ 0` by computation in the Pallas base field. -/
theorem varBaseMul_pallas_correct
    (m : ℕ) (g : ℕ → Witness PallasBaseField) (circuitMod : ℕ)
    (T : Pallas.curve.toAffine.Point) (P : ℕ → Pallas.curve.toAffine.Point) (s : ℤ)
    (hTne : T ≠ 0)
    (hd : ∀ i, i < m → GateData Pallas.curve.toAffine (g i))
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (hd i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (hd i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (hd i hi).a5)
    (hP0 : P 0 = (2 : ℤ) • T)
    (horder : 3 < Pallas.curve.toAffine.order)
    (hreg₁ : 2 ^ (5 * m - 1) < Pallas.curve.toAffine.order)
    (hreg₂ : Pallas.curve.toAffine.order < 2 ^ (5 * m))
    (hbound : circuitMod + 2 ^ (5 * m - 1) + 2 ≤ 2 * Pallas.curve.toAffine.order)
    (hs : s = gateLadder g (5 * m))
    (hreg : s < 2 * (circuitMod : ℤ) + 2 ^ (5 * m)) :
    P m = s • T ∧ ∀ i, i < m → NonDegen (g i) :=
  varBaseMul_deployed_correct Pallas.curve.toAffine m g circuitMod T P s hTne hd hT hin hout hP0
    (by decide) horder hreg₁ hreg₂ hbound hs hreg

end Kimchi.Cycle
