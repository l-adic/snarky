import Kimchi.Circuit.VarBaseMul.Basic
import Kimchi.Circuit.VarBaseMul.Ladder
import Kimchi.Circuit.VarBaseMul.NonDegen
import Kimchi.Circuit.VarBaseMul.Soundness
import Kimchi.Pasta

/-!
# The `VarBaseMul` circuit

The public module for variable-base scalar multiplication: it aggregates the circuit
definitions (`.Basic`), the number-theoretic ladder kernel (`.Ladder`), the group-order
non-degeneracy toolkit (`.NonDegen`), and the abstract soundness (`.Soundness`), and then
instantiates the soundness at the real Pasta curve.

`varBaseMul_deployed_correct` is proved abstractly over any `WeierstrassCurve.Affine` carrying
the short-shape and prime-order `Fact`s, and is `#print axioms`-clean. Here we fix the curve to
the concrete Pallas curve: the two `Fact`s are discharged from `Kimchi.Pasta` — the prime-order
one through the trusted point count `pallas_card`. So this corollary (and only this corollary)
depends on the point-count axiom; the abstract development stays axiom-free.
-/

namespace Kimchi.Circuit.VarBaseMul

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine

/-- **The deployed VarBaseMul circuit is correct on the real Pallas curve.** Same statement as
    `varBaseMul_deployed_correct`, with the curve fixed to `Pallas.curve.toAffine`; the
    short-shape and prime-order hypotheses are supplied by the `Fact` instances in
    `Kimchi.Pasta`, and `2 ≠ 0` by computation in the Pallas base field. -/
theorem varBaseMul_pallas_correct
    (m : ℕ) (g : ℕ → Witness PallasBaseField) (baseFieldOrder : ℕ)
    (T : Pallas.curve.toAffine.Point) (P : ℕ → Pallas.curve.toAffine.Point) (s : ℤ)
    (hTne : T ≠ 0)
    (hd : ∀ i, i < m → GateData Pallas.curve.toAffine (g i))
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (hd i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (hd i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (hd i hi).a5)
    (hP0 : P 0 = (2 : ℤ) • T)
    (horder : 3 < Pallas.curve.toAffine.order)
    (hreg₁ : 2 ^ (5 * m - 1) < Pallas.curve.toAffine.order)
    (hbound : baseFieldOrder + 2 ^ (5 * m - 1) + 2 ≤ 2 * Pallas.curve.toAffine.order)
    (hs : s = gateLadder g (5 * m))
    (hreg : s < 2 * (baseFieldOrder : ℤ) + 2 ^ (5 * m)) :
    P m = s • T ∧ ∀ i, i < m → NonDegen (g i) :=
  varBaseMul_deployed_correct Pallas.curve.toAffine m g baseFieldOrder T P s hTne hd hT hin hout hP0
    (by decide) horder hreg₁ hbound hs hreg

end Kimchi.Circuit.VarBaseMul
