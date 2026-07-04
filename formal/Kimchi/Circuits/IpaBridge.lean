import Kimchi.Circuits.Msm
import Kimchi.Commitment.IPA.Soundness

/-!
# Rungs 5–6: the circuit ↔ commitment-layer IPA bridge

The capstone of the sub-circuit direction: connect the *circuit* layer (a satisfying witness of a
reconstructed gate circuit) to the *commitment* layer's proven IPA soundness
(`Kimchi.Commitment.IPA.ipa_soundness`).

The meeting point is `recombine` — the verifier's recombined commitment
`Q = P + v•U + ∑ⱼ (uⱼ⁻¹•Lⱼ + uⱼ•Rⱼ)` — which is *exactly* an `n`-term MSM: the accumulator is
`P + v•U` and the terms pair up as `(uⱼ⁻¹, Lⱼ), (uⱼ, Rⱼ)`. So the in-circuit final check's heart
is `msm_sound` with `2k` blocks, and **Rung 5** (`msm_recombine`) lands its output on `recombine`
verbatim. Two pieces of glue make the layers meet:

* the point group becomes a **module over the scalar field**: `ZMod W.order` acts on `W.Point`
  (`AddCommGroup.zmodModule` from `order_smul`) — this is where the 2-cycle lives, since
  `ZMod (Vesta.order) = PallasBaseField`;
* the circuit's ℤ-scalars cross into that field by `Int.cast_smul_eq_zsmul` — the per-block cast
  hypotheses pin each block's ladder scalar to the corresponding challenge (or its inverse).

**Rung 6** (`circuit_ipa_soundness`) composes: the circuit-derived `Q`, the asserted Schnorr
equation (the outer `c•Q + δ = z1•sg + (z1·b)•U + z2•h` — its sides are further scale-and-combine
blocks of the same shape, taken here in point form over the circuit's output cells), and the
`sg`-check give `VerifierAccepts`; then `ipa_soundness` — under the commitment layer's own stated
Fiat–Shamir rewinding hypothesis — yields the **opening relation**. Circuit satisfaction has
become cryptographic knowledge soundness, over the four Pasta postulates.
-/

namespace Kimchi.Circuit.IpaBridge

open Kimchi.Circuit (Satisfies)
open Kimchi.Circuit.VarBaseMul
open Kimchi.Commitment.IPA
open WeierstrassCurve.Affine
open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Kimchi.Pasta

/-- The Vesta point group. -/
abbrev VPoint := Vesta.curve.toAffine.Point

/-- The Vesta scalar field — by the 2-cycle, `ZMod PALLAS_BASE_CARD` (= Pallas's base field). -/
abbrev VScalar := ZMod Vesta.curve.toAffine.order

noncomputable instance : Module VScalar VPoint :=
  AddCommGroup.zmodModule (fun P => by
    have h := Vesta.curve.toAffine.order_smul P
    rwa [natCast_zsmul] at h)

instance : Fact (Nat.Prime Vesta.curve.toAffine.order) := inferInstance

/-- Pair-and-reindex: a `2k`-range sum as a `Fin k` sum of consecutive pairs. -/
theorem sum_range_two_mul_fin {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ → M) :
    ∑ i ∈ Finset.range (2 * k), f i
      = ∑ j : Fin k, (f (2 * j.val) + f (2 * j.val + 1)) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Fin.sum_univ_castSucc, add_assoc]
    rfl

/-- **Rung 5: the circuit-level `recombine`.** A satisfying witness of the `2k`-block MSM circuit
    whose accumulator carries `P + v•U`, whose block bases are the cross-commitments
    `L₀, R₀, …, L_{k−1}, R_{k−1}`, and whose block scalars cast to `u₀⁻¹, u₀, …` produces — in its
    final combine's output cells — the verifier's recombined commitment
    `recombine σ P v u lr`. -/
theorem msm_recombine (μ : ℕ) (w : Kimchi.Circuit.Witness VestaBaseField)
    (pub : Array VestaBaseField) (σ : SRS VPoint) (hk : 0 < σ.k)
    (P : VPoint) (v : VScalar) (u : Fin σ.k → VScalar) (lr : Fin σ.k → VPoint × VPoint)
    (T : ℕ → VPoint)
    (hT : ∀ i (hns : Vesta.curve.toAffine.Nonsingular
        (gwit (w.shift (chainOff (μ + 1) i)) 0).xT (gwit (w.shift (chainOff (μ + 1) i)) 0).yT),
      T i = Point.some _ _ hns)
    (hbits : 5 * (μ + 1) ≤ pastaFieldBits)
    (hAccNs : Vesta.curve.toAffine.Nonsingular
      (w.cell (cbRow (μ + 1) 0, 0)) (w.cell (cbRow (μ + 1) 0, 1)))
    (hsat : Satisfies (msmCircuit (μ + 1) (2 * σ.k) (F := VestaBaseField)) w pub)
    (hTnsAll : ∀ i, i < 2 * σ.k → Vesta.curve.toAffine.Nonsingular
        (gwit (w.shift (chainOff (μ + 1) i)) 0).xT
        (gwit (w.shift (chainOff (μ + 1) i)) 0).yT)
    (hnfAll : ∀ i, i < 2 * σ.k → 5 * (μ + 1) = pastaFieldBits →
        msmScalar (μ + 1) w i ∉ forbiddenValues Vesta.curve.toAffine.order)
    (hinfsAll : ∀ i, i < 2 * σ.k →
        (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) i))).inf = 0)
    (hAccPt : Point.some _ _ hAccNs = P + v • σ.U)
    (hlr1 : ∀ j : Fin σ.k, T (2 * j.val) = (lr j).1)
    (hlr2 : ∀ j : Fin σ.k, T (2 * j.val + 1) = (lr j).2)
    (hu1 : ∀ j : Fin σ.k, ((msmScalar (μ + 1) w (2 * j.val) : ℤ) : VScalar) = (u j)⁻¹)
    (hu2 : ∀ j : Fin σ.k, ((msmScalar (μ + 1) w (2 * j.val + 1) : ℤ) : VScalar) = u j) :
    ∃ hOut : Vesta.curve.toAffine.Nonsingular
        (w.cell (cbRow (μ + 1) (2 * σ.k - 1), 4)) (w.cell (cbRow (μ + 1) (2 * σ.k - 1), 5)),
      Point.some _ _ hOut = recombine σ P v u lr := by
  have h2k : 2 * σ.k - 1 + 1 = 2 * σ.k := by omega
  rw [show 2 * σ.k = 2 * σ.k - 1 + 1 from h2k.symm] at hsat
  obtain ⟨hOut, hout⟩ := msm_sound μ w pub T hT hbits hAccNs (2 * σ.k - 1) hsat
    (fun i hi => hTnsAll i (by omega)) (fun i hi => hnfAll i (by omega))
    (fun i hi => hinfsAll i (by omega))
  refine ⟨hOut, ?_⟩
  rw [hout, hAccPt, h2k, recombine]
  congr 1
  -- the 2k-term ℤ-scalar sum is the paired challenge sum
  rw [sum_range_two_mul_fin σ.k (fun i => msmScalar (μ + 1) w i • T i)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Int.cast_smul_eq_zsmul VScalar (msmScalar (μ + 1) w (2 * j.val)),
    ← Int.cast_smul_eq_zsmul VScalar (msmScalar (μ + 1) w (2 * j.val + 1)),
    hu1 j, hu2 j, hlr1 j, hlr2 j]

/-- **Rung 6: the capstone.** Circuit satisfaction becomes IPA knowledge soundness. Given

    * the `2k`-block MSM circuit facts of `msm_recombine` (the witness computes `Q = recombine`),
    * the asserted **Schnorr equation** over the circuit's output cells — for any nonsingularity
      proof of those cells, `c•Q' + δ = z1•sg + (z1·bPoly(u,x))•U + z2•h` where `Q'` is the point
      they carry (its two sides are further scale-and-combine blocks of the shapes proven in
      Rungs 0–4; stated here in point form),
    * the `sg`-correctness check, and
    * the commitment layer's own Fiat–Shamir rewinding hypothesis,

    the prover **knows an opening**: `∃ a r, openingRelation σ P x v a r`. -/
theorem circuit_ipa_soundness (μ : ℕ) (w : Kimchi.Circuit.Witness VestaBaseField)
    (pub : Array VestaBaseField) (σ : SRS VPoint) (hk : 0 < σ.k)
    (proof : OpeningProof VScalar VPoint σ.k)
    (P : VPoint) (x v c : VScalar) (u : Fin σ.k → VScalar)
    (T : ℕ → VPoint)
    (hT : ∀ i (hns : Vesta.curve.toAffine.Nonsingular
        (gwit (w.shift (chainOff (μ + 1) i)) 0).xT (gwit (w.shift (chainOff (μ + 1) i)) 0).yT),
      T i = Point.some _ _ hns)
    (hbits : 5 * (μ + 1) ≤ pastaFieldBits)
    (hAccNs : Vesta.curve.toAffine.Nonsingular
      (w.cell (cbRow (μ + 1) 0, 0)) (w.cell (cbRow (μ + 1) 0, 1)))
    (hsat : Satisfies (msmCircuit (μ + 1) (2 * σ.k) (F := VestaBaseField)) w pub)
    (hTnsAll : ∀ i, i < 2 * σ.k → Vesta.curve.toAffine.Nonsingular
        (gwit (w.shift (chainOff (μ + 1) i)) 0).xT
        (gwit (w.shift (chainOff (μ + 1) i)) 0).yT)
    (hnfAll : ∀ i, i < 2 * σ.k → 5 * (μ + 1) = pastaFieldBits →
        msmScalar (μ + 1) w i ∉ forbiddenValues Vesta.curve.toAffine.order)
    (hinfsAll : ∀ i, i < 2 * σ.k →
        (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) i))).inf = 0)
    (hAccPt : Point.some _ _ hAccNs = P + v • σ.U)
    (hlr1 : ∀ j : Fin σ.k, T (2 * j.val) = (proof.lr j).1)
    (hlr2 : ∀ j : Fin σ.k, T (2 * j.val + 1) = (proof.lr j).2)
    (hu1 : ∀ j : Fin σ.k, ((msmScalar (μ + 1) w (2 * j.val) : ℤ) : VScalar) = (u j)⁻¹)
    (hu2 : ∀ j : Fin σ.k, ((msmScalar (μ + 1) w (2 * j.val + 1) : ℤ) : VScalar) = u j)
    (hSchnorr : ∀ hOut : Vesta.curve.toAffine.Nonsingular
        (w.cell (cbRow (μ + 1) (2 * σ.k - 1), 4)) (w.cell (cbRow (μ + 1) (2 * σ.k - 1), 5)),
      c • Point.some _ _ hOut + proof.delta
        = proof.z1 • proof.sg + (proof.z1 * bPoly u x) • σ.U + proof.z2 • σ.h)
    (hsg : proof.sg = commitGen σ.g (bPolyCoefficients u))
    (hFS : FiatShamirTree σ P x v (VerifierAccepts σ proof P x v c u)) :
    ∃ (a : Fin (2 ^ σ.k) → VScalar) (r : VScalar), openingRelation σ P x v a r := by
  obtain ⟨hOut, hQ⟩ := msm_recombine μ w pub σ hk P v u proof.lr T hT hbits hAccNs hsat
    hTnsAll hnfAll hinfsAll hAccPt hlr1 hlr2 hu1 hu2
  have hacc : VerifierAccepts σ proof P x v c u := by
    refine ⟨?_, hsg⟩
    rw [← hQ]
    exact hSchnorr hOut
  exact ipa_soundness σ proof P x v c u hFS hacc

end Kimchi.Circuit.IpaBridge
