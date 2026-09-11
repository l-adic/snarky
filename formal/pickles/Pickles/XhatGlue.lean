import Pickles.PublicInputCommit
import Bulletproof.Wire
import Pasta.Basic

/-!
# The `x_hat` wire crossing (glue G2, second half)

`PublicInputCommit`'s `publicInputCommitFull_net` reads the gadget output as `-(Σ netDelta) + h`
over Mathlib's Vesta point group (`d.W.Point`). This module crosses that to the wire verifier's
own `Kimchi.Verifier.publicCommitment` on the commitment curve (`SWPoint Vesta.curve`), via
`SWPoint.equivPoint` and the integer→scalar reduction `vesta_zsmul_eq` (exact — the group's
characteristic is the scalar order, so there is no `lowest_128_bits` slack here).

Curve-specific (wrap side, Vesta / `IpaVesta`), unlike the generic `PublicInputCommit`. The two
short reduction lemmas are private in `CheckBulletproof`, so restated here.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass

/-- The Vesta commitment-curve scalar field, `ZMod PALLAS_BASE_CARD`. -/
abbrev XhatFp := Bulletproof.IpaVesta.curve.ScalarField

section Crossing

variable {G : Type} [AddCommGroup G]

/-- In a group killed by `n`, an integer acts as its residue's canonical representative.
(Restated from `CheckBulletproof`, where it is private.) -/
private theorem zsmul_eq_val_nsmul (n : ℕ) [NeZero n] (hn : ∀ x : G, n • x = 0) (z : ℤ) (x : G) :
    z • x = ((z : ZMod n).val : ℕ) • x := by
  have hv : (((z : ZMod n).val : ℕ) : ℤ) = z % n := ZMod.val_intCast z
  rw [← natCast_zsmul, hv]
  conv_lhs => rw [← Int.emod_add_mul_ediv z n]
  rw [add_zsmul, mul_zsmul, natCast_zsmul, hn, _root_.add_zero]

end Crossing

/-- The Vesta point group is killed by its order. -/
private theorem vesta_card_nsmul (X : Vesta.curve.toAffine.Point) : PALLAS_BASE_CARD • X = 0 :=
  ZModModule.char_nsmul_eq_zero (n := PALLAS_BASE_CARD) X

/-- An integer acts on Vesta points as its residue's representative in the scalar field. -/
private theorem vesta_zsmul_eq (z : ℤ) (X : Vesta.curve.toAffine.Point) :
    z • X = ((z : XhatFp).val : ℕ) • X :=
  zsmul_eq_val_nsmul PALLAS_BASE_CARD vesta_card_nsmul z X

/-- **Negating an `ℕ`-scaling on a Vesta point is the `Fp`-negated scalar's scaling.** The MSM's
`-(n·X)` is `((-n : Fp)).val · X` — the group's characteristic is the scalar order, so the
`ℕ → Fp` reduction and the negation commute exactly. -/
private theorem neg_nsmul_eq (n : ℕ) (X : Vesta.curve.toAffine.Point) :
    -((n : ℕ) • X) = ((-(n : XhatFp)).val : ℕ) • X := by
  rw [← natCast_zsmul, ← neg_zsmul, vesta_zsmul_eq]
  simp only [Int.cast_neg, Int.cast_natCast]

/-- **The negated `publicMsm` term list is the wire's negated-scalar term list.** Termwise
`-((f aₗ) · Tₗ) = ((-↑(f aₗ)).val · Tₗ)` over `neg_nsmul_eq`, lifted over the (leaf, base) list —
the shape `equivPoint_publicCommitment` produces once the scalars line up. -/
private theorem neg_publicMsm_sum {A : Type} (f : A → ℕ)
    (l : List (A × Vesta.curve.toAffine.Point)) :
    -(l.map (fun p => f p.1 • p.2)).sum
      = (l.map (fun p => ((-(↑(f p.1) : XhatFp)).val : ℕ) • p.2)).sum := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons, neg_add]
      rw [neg_nsmul_eq, ih]

/-- **`publicCommitment`'s chunk, transported through an additive equivalence on the point
group.** The wire's negated-scalar MSM with each Lagrange base mapped over, plus `h`. Pure
additive-equiv algebra over `publicCommitment_eq_sum` (G1); the wire crossing instantiates it
at `SWPoint.equivPoint`. -/
theorem equivPoint_publicCommitment {C : Bulletproof.Ipa.CommitmentCurve} {nc : ℕ} {G : Type}
    [AddCommGroup G] (e : C.Point ≃+ G) (σ : Bulletproof.SRS C.Point)
    (cvk : Kimchi.Verifier.KimchiVK C nc)
    (pub : Array C.ScalarField) (ci : Fin nc) (hne : pub.size ≠ 0) :
    e ((Kimchi.Verifier.publicCommitment C σ cvk pub)[ci])
      = (((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList.map
          (fun Pp => (-Pp.2).val • e (Pp.1[ci]))).sum + e σ.h := by
  rw [Kimchi.Verifier.publicCommitment_eq_sum C σ cvk pub hne]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, map_add, map_list_sum, List.map_map,
    Function.comp_def, map_nsmul]

/-! ## The x_hat target: the gadget reads as `publicCommitment` (glue G2, piece 5) -/

/-- The public input the leaves commit to, as the wire verifier's `Fp` scalar array: each
scalar leaf contributes its `Fq` scalar's value cast to `Fp` — the group-order reduction the
MSM performs on the in-circuit scalar — and each `condAdd` its bit. The `ℕ → Fp` cast IS the
reduction, so no slack predicate is needed. -/
def pubOf {nc : ℕ} (V : Valuation Fq) (leaves : List (Leaf Fq nc)) : Array XhatFp :=
  (leaves.map (fun leaf => ((leaf.scalarVar.val V).val : XhatFp))).toArray

/-- One leaf's chunk base at `ci`. -/
def leafBaseAt {nc : ℕ} (ci : Fin nc) : Leaf Fq nc → AffinePoint (FVar Fq)
  | .full _ base _ => base[ci]
  | .b128 _ base _ => base[ci]
  | .b10 _ base _ => base[ci]
  | .condAdd _ base => base[ci]

/-- `pubOf` has one entry per leaf. -/
theorem pubOf_size {nc : ℕ} (V : Valuation Fq) (leaves : List (Leaf Fq nc)) :
    (pubOf V leaves).size = leaves.length := by simp [pubOf]

/-- A leaf's `LeafPre` reading names its base cell on the curve at that point — the on-curve
half of `LeafPre` for every leaf shape (`condAdd` also carries a bit clause). -/
private theorem leafPre_onCurve {nc : ℕ} (ci : Fin nc) (V : Valuation Fq)
    (leaf : Leaf Fq nc) (T : HasCurve.vesta.W.Point) (h : LeafPre ci V leaf T) :
    OnCurveAt HasCurve.vesta.W V (leafBaseAt ci leaf) T := by
  cases leaf <;> first | exact h | exact h.1

/-- **The wire's negated-scalar MSM term list equals the crossed `publicMsm` term list.** The
walk-order correspondence: at each `i`, the wire pairs Lagrange base `i` with `pubOf`'s `i`-th
scalar, and the gadget pairs leaf `i`'s base — read as that same Lagrange base by `htie` — with
its own scalar. The `Fq → Fp` reduction (`ZMod.natCast_val`) makes the scalars agree. -/
private theorem crossing_list {nc : ℕ} (ci : Fin nc) (V : Valuation Fq)
    (cvk : Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc)
    (leaves : List (Leaf Fq nc)) (Ts : List HasCurve.vesta.W.Point)
    (hlen : Ts.length = leaves.length)
    (hsize : leaves.length ≤ cvk.lagrangeBasis.size)
    (htie : ∀ (i : ℕ) (hi : i < leaves.length),
      Ts[i]'(hlen ▸ hi)
        = (SWPoint.equivPoint Vesta.curve) ((cvk.lagrangeBasis[i]'(lt_of_lt_of_le hi hsize))[ci])) :
    ((cvk.lagrangeBasis.extract 0 (pubOf V leaves).size).zip (pubOf V leaves)).toList.map
        (fun Pp => (-Pp.2).val • (SWPoint.equivPoint Vesta.curve) (Pp.1[ci]))
      = (leaves.zip Ts).map
          (fun p => ((-(↑(ToNat.toNat (p.1.scalarVar.val V)) : XhatFp)).val : ℕ) • p.2) := by
  simp only [pubOf]
  apply List.ext_getElem
  · simp only [List.length_map, Array.length_toList, Array.size_zip, Array.size_extract,
      List.size_toArray, List.length_zip, Nat.sub_zero, hlen, Nat.min_self,
      Nat.min_eq_left hsize]
  · intro i h1 h2
    have hil : i < leaves.length := by
      simp only [List.length_map, List.length_zip, hlen, Nat.min_self] at h2; exact h2
    simp only [List.getElem_map, Array.getElem_toList, Array.getElem_zip, Array.getElem_extract,
      List.getElem_zip, List.getElem_toArray, Nat.zero_add]
    rw [htie i hil]
    rfl

/-- The binding the deferred packing item discharges — everything the faithfulness read needs
of the outside world, in public terms (no `LeafInfo`/`LeafReads`). The scalar-side alias
(`Fq → Fp`) is absorbed into `pubOf`; `canon` reflects `scale_fast2`'s top-bit pin, and the
fold premises (`pre`/`corr`/`scalar`/`hon`/`regime`) are exactly `publicInputCommitFull_reads`'s.
`Ts` are the leaves' base points, `cps` their correction points. -/
structure XhatBinding {nc : ℕ} (ci : Fin nc) (V : Valuation Fq)
    (σ : Bulletproof.SRS Bulletproof.IpaVesta.curve.Point)
    (cvk : Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc)
    (blindingH : AffinePoint (FVar Fq)) (leaves : List (Leaf Fq nc))
    (Ts cps : List HasCurve.vesta.W.Point) : Prop where
  /-- The blinding cell reads as the verifier's SRS blinding `σ.h`, crossed to the Vesta group. -/
  blinding : OnCurveAt HasCurve.vesta.W V blindingH ((SWPoint.equivPoint Vesta.curve) σ.h)
  /-- Each leaf reads its base cell as a curve point `Ts[i]` (and its bit, for `condAdd`). -/
  pre : List.Forall₂ (LeafPre ci V) leaves Ts
  /-- Each leaf's correction cell reads as `cps[i]`. -/
  corr : List.Forall₂ (CorrPre ci V) leaves cps
  /-- The leaves reach a scalar leaf (so the corrections fold has a seed). -/
  scalar : leafHasScalar leaves
  /-- Each leaf's correction is the honest shift `-(2^L)·base`. -/
  hon : ∀ leaf ∈ leaves, CorrHonest HasCurve.vesta ci V leaf
  /-- Each full leaf's scalar has its top bit zero — the `With_top_bit0` assumption. -/
  canon : ∀ leaf ∈ leaves, Leaf.canonFull V leaf
  /-- Each full leaf's ladder decode is in regime (the forbidden-band exclusion). -/
  regime : ∀ leaf ∈ leaves, Leaf.regimeFull HasCurve.vesta V leaf
  /-- There are at least as many Lagrange bases as public-input leaves. -/
  hsize : leaves.length ≤ cvk.lagrangeBasis.size
  /-- Each leaf's chunk base reads as the verifier's Lagrange base at that index — the walk-order
  tie the packing item owns. -/
  bases : ∀ (i : ℕ) (hi : i < leaves.length),
    OnCurveAt HasCurve.vesta.W V (leafBaseAt ci leaves[i])
      ((SWPoint.equivPoint Vesta.curve) ((cvk.lagrangeBasis[i]'(lt_of_lt_of_le hi hsize))[ci]))

/-- **The x_hat commitment gadget reads as the wire verifier's `publicCommitment`.** The
in-circuit public-input obligation of the group half (`incrementally_verify_proof`):
`publicInputCommitFull` commits to `pubOf leaves`, crossed to Mathlib's Vesta group by
`SWPoint.equivPoint`. The subtle half (the canonical `Fq` decode, `-(Σ [scalarₗ]·baseₗ) + h`) is
`publicInputCommitFull_reads`; this crosses that to the wire's `publicCommitment` — the `Fq → Fp`
reduction is exact (`vesta_zsmul_eq`), so the read carries no slack. -/
theorem xHat_reads_publicCommitment {nc : ℕ} (ci : Fin nc) {V : Valuation Fq}
    (σ : Bulletproof.SRS Bulletproof.IpaVesta.curve.Point)
    (cvk : Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc)
    (blindingH : AffinePoint (FVar Fq)) (leaves : List (Leaf Fq nc))
    (Ts cps : List HasCurve.vesta.W.Point)
    (hbind : XhatBinding ci V σ cvk blindingH leaves Ts cps) :
    ⦃⌜True⌝⦄
    publicInputCommitFull (S := Builder V (KimchiConstraint Fq)) ci blindingH leaves
    ⦃⇓ r _ => ⌜OnCurveAt HasCurve.vesta.W V r
      ((SWPoint.equivPoint Vesta.curve)
        (Kimchi.Verifier.publicCommitment Bulletproof.IpaVesta.curve σ cvk
          (pubOf V leaves))[ci])⌝⦄ := by
  have hcast : ∀ m : ℤ, 0 ≤ m → m < 2 ^ 254 → (ToNat.toNat ((m : Fq)) : ℤ) = m := by
    intro m hm0 hmlt
    have hp : (2 : ℤ) ^ 254 ≤ (PALLAS_SCALAR_CARD : ℤ) := by norm_num [PALLAS_SCALAR_CARD]
    show ((ZMod.val ((m : Fq))) : ℤ) = m
    rw [ZMod.val_intCast]; exact Int.emod_eq_of_lt hm0 (by push_cast; linarith)
  have hbit : ∀ b : Bool, ToNat.toNat (bit b : Fq) = if b then 1 else 0 := by
    haveI : Fact (1 < PALLAS_SCALAR_CARD) := ⟨by norm_num [PALLAS_SCALAR_CARD]⟩
    intro b
    cases b
    · show ZMod.val (bit false : Fq) = 0; simp [bit]
    · show ZMod.val (bit true : Fq) = 1; simp [bit, ZMod.val_one]
  have h130 : 3 * 2 ^ 130 ≤ HasCurve.vesta.W.order := by
    rw [Pasta.vesta_card]; norm_num [PALLAS_BASE_CARD]
  have h10 : 3 * 2 ^ 10 ≤ HasCurve.vesta.W.order := by
    rw [Pasta.vesta_card]; norm_num [PALLAS_BASE_CARD]
  have hlen : Ts.length = leaves.length := (List.Forall₂.length_eq hbind.pre).symm
  have htie : ∀ (i : ℕ) (hi : i < leaves.length),
      Ts[i]'(hlen ▸ hi)
        = (SWPoint.equivPoint Vesta.curve)
            ((cvk.lagrangeBasis[i]'(lt_of_lt_of_le hi hbind.hsize))[ci]) := by
    intro i hi
    have hpre_i : LeafPre ci V leaves[i] (Ts[i]'(hlen ▸ hi)) :=
      hbind.pre.get hi (hlen ▸ hi)
    exact OnCurveAt.eq (leafPre_onCurve ci V _ _ hpre_i) (hbind.bases i hi) rfl rfl
  have hne : (pubOf V leaves).size ≠ 0 := by
    rw [pubOf_size]
    intro h0
    rw [List.length_eq_zero_iff.mp h0] at hbind
    simpa [leafHasScalar] using hbind.scalar
  have hpm : -(publicMsm V leaves Ts)
      = ((leaves.zip Ts).map
          (fun p => ((-(↑(ToNat.toNat (p.1.scalarVar.val V)) : XhatFp)).val : ℕ) • p.2)).sum := by
    rw [publicMsm]
    exact neg_publicMsm_sum (fun leaf => ToNat.toNat (leaf.scalarVar.val V)) (leaves.zip Ts)
  have hcross : (SWPoint.equivPoint Vesta.curve)
        (Kimchi.Verifier.publicCommitment Bulletproof.IpaVesta.curve σ cvk (pubOf V leaves))[ci]
      = -(publicMsm V leaves Ts) + (SWPoint.equivPoint Vesta.curve) σ.h := by
    rw [equivPoint_publicCommitment (SWPoint.equivPoint Vesta.curve) σ cvk (pubOf V leaves) ci hne,
      crossing_list ci V cvk leaves Ts hlen hbind.hsize htie, hpm]
  refine builder_spec_imp _ _ _
    (publicInputCommitFull_reads (d := HasCurve.vesta) ci blindingH leaves Ts cps
      ((SWPoint.equivPoint Vesta.curve) σ.h) hcast hbit h130 h10 hbind.regime hbind.canon
      hbind.blinding hbind.pre hbind.corr hbind.scalar hbind.hon) fun r hr => ?_
  rw [hcross]; exact hr

end Pickles
