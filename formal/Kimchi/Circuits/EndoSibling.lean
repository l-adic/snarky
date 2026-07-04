import Kimchi.Circuits.EndoMulStep
import Kimchi.Circuits.EndoScalarStep

/-!
# Rung 3b: EndoScalar ↔ EndoMul sibling consistency

The two endo gates are *siblings*, not producer/consumer: `EndoMulScalar` decodes a challenge's
crumbs into the effective scalar `a·λ + b` **in the field**, while `EndoMul` consumes the same
crumbs to multiply them **onto a point**. There is no wire between them — the shared challenge is
the interface. The consistency theorem is the verifier fact this encodes:

> if an `EndoMulScalar` run and an `EndoMul` chain process the **same crumb stream**, then the
> point the chain produced is `[s]·T` for exactly the field element the scalar run computed:
> `(s : F) = a₈·λ + b₈`.

Both circuit-level soundness results already speak `EndoScalar.toField`, so the join is their
composition at a shared crumb list — instantiating the scalar run's `λ` at the concrete Pallas
eigenvalue. The crumb-stream equality is the honest interface hypothesis: in a joint dumped
circuit it would be discharged by the bit/crumb decomposition rows that derive both streams from
one squeezed challenge (the Fiat–Shamir rung's job).
-/

namespace Kimchi.Circuit.EndoSibling

open Kimchi.Circuit (Satisfies)
open WeierstrassCurve.Affine
open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Kimchi.Pasta

/-- **Sibling consistency at Pallas.** An `EndoMulScalar` run (rows `wES`, canonical init) and an
    `EndoMul` chain (rows `wEM`, base/init as in `pallas_endoMul_circuit`) whose crumb streams
    agree produce a point `[s]·T` whose scalar's field image is the run's effective scalar
    `a₈·λ + b₈` — "the scalar used on points is the scalar computed in-field". -/
theorem pallas_sibling_consistency
    -- the EndoMulScalar run
    (mES : ℕ) (wES : Kimchi.Circuit.Witness PallasBaseField) (pubES : Array PallasBaseField)
    (hsatES : Satisfies (Kimchi.Circuit.EndoScalar.esCircuit mES) wES pubES)
    (ha0 : (Kimchi.Circuit.EndoScalar.gwit wES 0).a0 = 2)
    (hb0 : (Kimchi.Circuit.EndoScalar.gwit wES 0).b0 = 2)
    (hn0 : (Kimchi.Circuit.EndoScalar.gwit wES 0).n0 = 0)
    -- the EndoMul chain
    (mEM : ℕ) (hbits : 4 * mEM ≤ 244) (wEM : Kimchi.Circuit.Witness PallasBaseField)
    (pubEM : Array PallasBaseField)
    (hsatEM : Satisfies (Kimchi.Circuit.EndoMul.emCircuit mEM) wEM pubEM)
    (hdist : ∀ i, i < mEM →
        ((Kimchi.Circuit.EndoMul.gwit wEM i).xP - (Kimchi.Circuit.EndoMul.gwit wEM i).xR)
          * ((Kimchi.Circuit.EndoMul.gwit wEM i).xR - (Kimchi.Circuit.EndoMul.gwit wEM i).xS) ≠ 0)
    (T φT : Pallas.curve.toAffine.Point)
    (hTns : Pallas.curve.toAffine.Nonsingular (Kimchi.Circuit.EndoMul.gwit wEM 0).xT
      (Kimchi.Circuit.EndoMul.gwit wEM 0).yT)
    (hTeq : T = Point.some _ _ hTns)
    (hφTns : Pallas.curve.toAffine.Nonsingular
      (pallas_endo * (Kimchi.Circuit.EndoMul.gwit wEM 0).xT) (Kimchi.Circuit.EndoMul.gwit wEM 0).yT)
    (hφTeq : φT = Point.some _ _ hφTns)
    (hP0ns : Pallas.curve.toAffine.Nonsingular (Kimchi.Circuit.EndoMul.gwit wEM 0).xP
      (Kimchi.Circuit.EndoMul.gwit wEM 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT)
    -- the interface: both consume the same crumb stream
    (hcrumbs : Kimchi.Circuit.EndoMul.crumbList (Kimchi.Circuit.EndoMul.gwit wEM) mEM
      = Kimchi.Circuit.EndoScalar.chainCrumbs (Kimchi.Circuit.EndoScalar.gwit wES) (mES + 1)) :
    ∃ (hfin : Pallas.curve.toAffine.Nonsingular
        (Kimchi.Circuit.EndoMul.accX (Kimchi.Circuit.EndoMul.gwit wEM) mEM)
        (Kimchi.Circuit.EndoMul.accY (Kimchi.Circuit.EndoMul.gwit wEM) mEM)) (s : ℤ),
      Point.some _ _ hfin = s • T
        ∧ (s : PallasBaseField)
            = (Kimchi.Circuit.EndoScalar.gwit wES mES).a8 * (pallas_lam : PallasBaseField)
              + (Kimchi.Circuit.EndoScalar.gwit wES mES).b8 := by
  obtain ⟨hfin, s, hpt, hsF⟩ := Kimchi.Circuit.EndoMul.pallas_endoMul_circuit mEM hbits wEM pubEM
    hsatEM hdist T φT hTns hTeq hφTns hφTeq hP0ns hP0
  obtain ⟨hES, -⟩ := Kimchi.Circuit.EndoScalar.pallas_circuit_sound
    (pallas_lam : PallasBaseField) mES wES pubES hsatES ha0 hb0 hn0
  exact ⟨hfin, s, hpt, by rw [hsF, hcrumbs, ← hES]⟩

end Kimchi.Circuit.EndoSibling
