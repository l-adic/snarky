import Pickles.CheckBulletproof
import Pickles.PublicInputCommit
import Snarky.Traverse
import Snarky.Witness

/-!
# The ladder's forbidden band, asserted on the cells that are scaled

`VarBaseMul` adds incompletely, so a ladder run is the scalar multiplication it names only off
the forbidden band `Kimchi.Gate.VarBaseMul.forbiddenValues`: eleven residues of the ladder's
top modulo the group order, exact at the Pasta primes (`varBaseMul_forbidden_correct`). The
band is a property of a cell together with the ladder it feeds. This module asserts it on
exactly those cells: the shifted scalars a group half scales by, and the full leaves of the
`x_hat` commitment.

The deployed circuits check something of this kind where `step_main` / `wrap_main` allocate
the shifted-scalar type (`forbidden_shifted_values`, `impls.ml`), at two residues on the step
side and none on the wrap side; upstream marks its list incomplete. The assertions here are
the complete list. They are for the harness circuits around the shared gadgets
(`StepProof.groupCircuit`, `WrapProof.groupCircuit`), which the deployed mains are not ported
to; the gadgets themselves, and their CS-equality with the PureScript, are untouched.

## Main definitions

* `assertNotIn`: a cell is none of the listed constants;
* `bandInputs`: the ladder inputs below `2²⁵⁴` whose top meets the band of a group of a Pasta
  order — eleven integers;
* `assertClaimsOffBandWrap`, `assertClaimsOffBandStep`: the assertion on a side's shifted
  scalars (the step side's also makes each parity cell boolean);
* `assertLeavesOffBand`: the assertion on the full leaves of an `x_hat` leaf list.

## Main results

* `not_forbidden_of_not_bandInputs`: off `bandInputs`, the ladder's top is off the band;
* `assertClaimsOffBandWrap_spec`, `assertClaimsOffBandStep_spec`: the asserted scalars are
  claims the ladder read speaks about (`IvpSide.ClaimOk`);
* `assertLeavesOffBand_spec`: the asserted leaves are off the `x_hat` window (`Leaf.offBand`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Gate.VarBaseMul Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta

/-! ## A cell outside a list of constants -/

section NotIn

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- Assert that a cell is none of the listed constants: one `assertNotEqual` each. -/
def assertNotIn (x : FVar F) (cs : List F) : CircuitM F c PUnit :=
  cs.forM fun v => assertNotEqual x (.const v)

/-- `assertNotIn` forces the cell to read as none of the constants. -/
theorem assertNotIn_spec {V : Valuation F} [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x : FVar F) (cs : List F) :
    ⦃⌜True⌝⦄ assertNotIn (c := Builder V c) x cs ⦃⇓ _ _ => ⌜∀ v ∈ cs, x.val V ≠ v⌝⦄ :=
  forM_spec (V := V) (c := c)
    (fun v : F => assertNotEqual (c := Builder V c) x (.const v)) (fun v => x.val V ≠ v)
    (fun v => assertNotEqual_spec (V := V) x (.const v)) cs

end NotIn

/-! ## The ladder inputs on the band -/

/-- The ladder inputs `0 ≤ z < 2²⁵⁴` whose one-wrap top `2z + 2²⁵⁵ + 1` meets the forbidden band
of a group of order `q`: with `δ = q − 2²⁵⁴`, the eight `δ − 2 … δ + 5` (the odd residues, two
orders up) and the three around `2²⁵³ + (3δ − 1)/2` (the even ones, three orders up). -/
def bandInputs (q : ℕ) : List ℤ :=
  let δ : ℤ := q - 2 ^ 254
  let m : ℤ := 2 ^ 253 + (3 * δ - 1) / 2
  [δ - 2, δ - 1, δ, δ + 1, δ + 2, δ + 3, δ + 4, δ + 5, m - 1, m, m + 1]

/-- The arithmetic behind `bandInputs`, with `H = 2²⁵³` opaque so that every step is linear: a
ladder input whose top is a forbidden residue modulo an odd `q` between `2H + 12` and `3H` is
one of the eleven. -/
private theorem band_arith (H q z t k : ℤ) (h0 : 0 ≤ z) (hlt : z < 2 * H) (hq : 2 * H + 12 < q)
    (hq' : q < 3 * H) (hodd : q % 2 = 1)
    (ht : t = 0 ∨ t = 1 ∨ t = -1 ∨ t = 2 ∨ t = -2 ∨ t = 3 ∨ t = -3 ∨ t = 5 ∨ t = 7 ∨ t = 9 ∨
      t = 11)
    (hk : 2 * z + 4 * H + 1 - t = q * k) :
    z = q - 2 * H - 2 ∨ z = q - 2 * H - 1 ∨ z = q - 2 * H ∨ z = q - 2 * H + 1 ∨
      z = q - 2 * H + 2 ∨ z = q - 2 * H + 3 ∨ z = q - 2 * H + 4 ∨ z = q - 2 * H + 5 ∨
      z = H + (3 * (q - 2 * H) - 1) / 2 - 1 ∨ z = H + (3 * (q - 2 * H) - 1) / 2 ∨
      z = H + (3 * (q - 2 * H) - 1) / 2 + 1 := by
  have hk2 : 2 ≤ k := by
    by_contra hc
    have : k ≤ 1 := by omega
    have : q * k ≤ q := by nlinarith
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hk3 : k ≤ 3 := by
    by_contra hc
    have : 4 ≤ k := by omega
    have : 4 * q ≤ q * k := by nlinarith
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain rfl | rfl : k = 2 ∨ k = 3 := by omega
  all_goals
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Off `bandInputs`, a ladder input's top is off the forbidden band, at any odd order between
`2²⁵⁴ + 12` and `3·2²⁵³` — both Pasta orders. -/
theorem not_forbidden_of_not_bandInputs (q : ℕ) (hq : 2 ^ 254 + 12 < q) (hq' : q < 3 * 2 ^ 253)
    (hodd : q % 2 = 1) (z : ℤ) (h0 : 0 ≤ z) (hlt : z < 2 ^ 254) (hz : z ∉ bandInputs q) :
    (2 * z + 2 ^ 255 + 1) ∉ forbiddenValues q := by
  rintro ⟨t, ht, k, hk⟩
  apply hz
  simp only [Ladder.forbiddenResidues, List.mem_cons, List.not_mem_nil, or_false] at ht
  have key := band_arith (2 ^ 253) q z t k h0 (by linarith [hlt]) (by
    have : ((2 : ℤ) ^ 254 + 12 : ℤ) < q := by exact_mod_cast hq
    linarith) (by exact_mod_cast hq') (by exact_mod_cast hodd) ht (by linarith [hk])
  simp only [bandInputs, List.mem_cons, List.not_mem_nil, or_false]
  have e : (2 : ℤ) * 2 ^ 253 = 2 ^ 254 := by norm_num
  rw [e] at key
  exact key

/-! ## The shifted scalars a group half scales by -/

section Claims

variable {c : Type}

/-- The wrap side's band cells: `bandInputs` of Vesta's order, as `Type1` cell values. -/
def wrapBandCells : List Fq := List.map (Int.cast : ℤ → Fq) (bandInputs PALLAS_BASE_CARD)

/-- The step side's band cells: `bandInputs` of Pallas's order, as halved-limb values. -/
def stepBandCells : List Fp := List.map (Int.cast : ℤ → Fp) (bandInputs PALLAS_SCALAR_CARD)

/-- The wrap side's assertion: each `Type1` scalar's cell is off the band. -/
def assertClaimsOffBandWrap [BasicSystem Fq c] (xs : List (Type1 (FVar Fq))) :
    CircuitM Fq c PUnit :=
  xs.forM fun x => assertNotIn x.val wrapBandCells

/-- The step side's assertion: each split scalar's parity cell is boolean and its halved limb is
off the band. -/
def assertClaimsOffBandStep [BasicSystem Fp c]
    (xs : List (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) : CircuitM Fp c PUnit :=
  xs.forM fun x => do
    CheckedType.check (F := Fp) (val := Bool) x.val.sOdd
    assertNotIn x.val.sDiv2 stepBandCells

/-- The asserted wrap-side scalars are claims the ladder read speaks about. -/
theorem assertClaimsOffBandWrap_spec {V : Valuation Fq} (xs : List (Type1 (FVar Fq))) :
    ⦃⌜True⌝⦄ assertClaimsOffBandWrap (c := Builder V (KimchiConstraint Fq)) xs
    ⦃⇓ _ _ => ⌜∀ x ∈ xs, (wrapSide V).ClaimOk x⌝⦄ := by
  refine forM_spec (V := V) (c := KimchiConstraint Fq) _ (fun x => (wrapSide V).ClaimOk x)
    (fun x => ?_) xs
  refine builder_spec_imp _ _ _ (assertNotIn_spec (V := V) x.val wrapBandCells) fun _ hne => ?_
  change True ∧ ∀ z : ℤ, WrapLadderPre V x z → WrapLadderReg z
  refine ⟨trivial, fun z hpre => ?_⟩
  obtain ⟨h0, hlt, hz⟩ := hpre
  refine HasCurve.vesta_ladderRegime _ (not_forbidden_of_not_bandInputs PALLAS_BASE_CARD
    (by norm_num [PALLAS_BASE_CARD]) (by norm_num [PALLAS_BASE_CARD]) (by decide) z h0 hlt
    fun hmem => ?_)
  have hcell : ((z : ℤ) : Fq) ∈ wrapBandCells :=
    List.mem_map_of_mem (f := (Int.cast : ℤ → Fq)) hmem
  exact hne _ hcell hz.symm

/-- The asserted step-side scalars are claims the ladder read speaks about. -/
theorem assertClaimsOffBandStep_spec {V : Valuation Fp}
    (xs : List (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    ⦃⌜True⌝⦄ assertClaimsOffBandStep (c := Builder V (KimchiConstraint Fp)) xs
    ⦃⇓ _ _ => ⌜∀ x ∈ xs, (stepSide V).ClaimOk x⌝⦄ := by
  refine forM_spec (V := V) (c := KimchiConstraint Fp) _ (fun x => (stepSide V).ClaimOk x)
    (fun x => ?_) xs
  have hbool : ⦃⌜True⌝⦄
      CheckedType.check (F := Fp) (c := Builder V (KimchiConstraint Fp)) (val := Bool) x.val.sOdd
      ⦃⇓ _ _ => ⌜∃ bb : Bool, (↑x.val.sOdd : CVar Fp).val V = bit bb⌝⦄ := by
    rw [builder_spec_iff]
    intro nv hsat
    exact CheckedType.check_sound (F := Fp) (val := Bool) V x.val.sOdd nv hsat
  have hnot := assertNotIn_spec (V := V) (c := KimchiConstraint Fp) x.val.sDiv2 stepBandCells
  mvcgen [hbool, hnot]
  intro hne
  have hb : ∃ bb : Bool, (↑x.val.sOdd : CVar Fp).val V = bit bb := by assumption
  change (∃ bb : Bool, (↑x.val.sOdd : CVar Fp).val V = bit bb) ∧
    ∀ w : ℤ × Bool, StepLadderPre V x w → StepLadderReg w
  refine ⟨hb, fun w hpre => ?_⟩
  obtain ⟨-, h0, hlt, hz⟩ := hpre
  refine HasCurve.pallas_ladderRegime _ (not_forbidden_of_not_bandInputs PALLAS_SCALAR_CARD
    (by norm_num [PALLAS_SCALAR_CARD]) (by norm_num [PALLAS_SCALAR_CARD]) (by decide) w.1 h0
    hlt fun hmem => ?_)
  have hcell : ((w.1 : ℤ) : Fp) ∈ stepBandCells :=
    List.mem_map_of_mem (f := (Int.cast : ℤ → Fp)) hmem
  exact hne _ hcell hz.symm

end Claims

/-! ## The full leaves of an `x_hat` commitment -/

section Leaves

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] {nc : ℕ}

/-- The sixteen cell values of the `x_hat` band window `[2δ − 4, 2δ + 11]`, `δ = p − 2²⁵⁴`. -/
def xhatBandCells (p : ℕ) : List F :=
  (List.range 16).map fun i => ((2 * xhatBandDelta p - 4 + i : ℕ) : F)

/-- A leaf's full scalar cell, if it is a full leaf. -/
def Leaf.fullScalar? : Leaf F nc → Option (FVar F)
  | .full s _ _ => some s
  | _ => none

/-- The assertion on a leaf list: each full leaf's scalar cell is off the `x_hat` window. -/
def assertLeavesOffBand (p : ℕ) (leaves : List (Leaf F nc)) : CircuitM F c PUnit :=
  (leaves.filterMap Leaf.fullScalar?).forM fun s => assertNotIn s (xhatBandCells p)

/-- The asserted leaves are off the `x_hat` window. -/
theorem assertLeavesOffBand_spec {V : Valuation F} [ConstraintHolds F c]
    [LawfulBasicSystem F c] [LawfulToNat F] (p : ℕ) (leaves : List (Leaf F nc)) :
    ⦃⌜True⌝⦄ assertLeavesOffBand (c := Builder V c) p leaves
    ⦃⇓ _ _ => ⌜∀ leaf ∈ leaves, Leaf.offBand p V leaf⌝⦄ := by
  refine builder_spec_imp _ _ _ (forM_spec (V := V) (c := c)
    (fun s : FVar F => assertNotIn (c := Builder V c) s (xhatBandCells p))
    (fun s => ∀ v ∈ xhatBandCells (F := F) p, s.val V ≠ v)
    (fun s => assertNotIn_spec (V := V) s (xhatBandCells p)) _) fun _ hall leaf hleaf => ?_
  cases leaf with
  | full s base corr =>
      have hne := hall s (List.mem_filterMap.mpr ⟨_, hleaf, rfl⟩)
      simp only [Leaf.offBand]
      by_contra hcon
      push Not at hcon
      obtain ⟨hlo, hhi⟩ := hcon
      refine hne ((ToNat.toNat (s.val V) : ℕ) : F) (List.mem_map.mpr
        ⟨ToNat.toNat (s.val V) - (2 * xhatBandDelta p - 4), List.mem_range.mpr (by omega), ?_⟩)
        (LawfulToNat.cast_toNat (s.val V)).symm
      rw [show 2 * xhatBandDelta p - 4 + (ToNat.toNat (s.val V) - (2 * xhatBandDelta p - 4))
          = ToNat.toNat (s.val V) by omega]
  | _ => trivial

end Leaves

end Pickles
