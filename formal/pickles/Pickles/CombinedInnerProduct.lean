import Snarky.DSL.Field
import Snarky.DSL.Boolean
import Kimchi.Protocol.Linearization
import Kimchi.Verifier.Kimchi
import Bulletproof.Protocol

set_option mvcgen.warning false

/-!
# The combined inner product in circuit

Port of the PureScript `Pickles.PlonkChecks.CombinedInnerProduct`: the verifier's
recomputation of the batched opening's claimed evaluation
`∑ⱼ ξʲ fⱼ(ζ) + r · ∑ⱼ ξʲ fⱼ(ζω)` from the proof's evaluations. Each point's sum is a Horner
fold over the batch, whose entries carry a bit keeping them in the batch; an entry whose
bit is clear leaves the batch, so the powers of `ξ` count the kept entries.

## Main definitions

* `buildEvalList`: the batch in order, `sg_evals, public, ft, z, selectors, w, coeffs, s`.
* `combinedInnerProduct`: the two folds and their `r`-combination, the `ζω` fold first.
* `keptEvals`: the evaluations a read batch keeps.

## Main results

* `combinedInnerProduct_spec`: the output reads as `alphaCombo ξ` of each point's kept
  evaluations, combined by `r`.
* `combinedInnerProduct_spec_cip`: the same as `Bulletproof.combinedInnerProduct` at the
  batch's evaluation rows.
-/

namespace Pickles

open Std.Do Snarky Kimchi.Protocol.Linearization
open scoped Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- One Horner step: `fx + ξ·acc` where the entry's bit is set, `acc` otherwise. -/
private def hornerStep (ξ acc : FVar F) (e : BoolVar F × FVar F) : CircuitM F c (FVar F) := do
  let xiAcc ← mul ξ acc
  selectField e.1 (CVar.add_ e.2 xiAcc) acc

/-- The Horner fold from an accumulator, in fold order. -/
private def hornerGo (ξ acc : FVar F) : List (BoolVar F × FVar F) → CircuitM F c (FVar F)
  | [] => pure acc
  | e :: rest => do
    let acc' ← hornerStep ξ acc e
    hornerGo ξ acc' rest

/-- The Horner sum of a batch, seeded from its last entry and folded from the back. -/
private def hornerCombine (ξ : FVar F) (evals : List (BoolVar F × FVar F)) :
    CircuitM F c (FVar F) :=
  match evals.reverse with
  | [] => pure (.const 0)
  | last :: revFront => hornerGo ξ last.2 revFront

/-- The batch in order: the previous proofs' challenge-polynomial evaluations with their
bits, then the public evaluation, `ft` and the column evaluations, all kept. -/
def buildEvalList (sgEvals : List (BoolVar F × FVar F)) (publicInput ftEval : FVar F)
    (evals : List (FVar F)) : List (BoolVar F × FVar F) :=
  sgEvals ++ (true_, publicInput) :: (true_, ftEval) :: evals.map (true_, ·)

/-- The combined inner product `combine(ζ) + r · combine(ζω)`, the `ζω` fold first. -/
def combinedInnerProduct (ξ r : FVar F) (evalsZeta evalsZetaw : List (BoolVar F × FVar F)) :
    CircuitM F c (FVar F) := do
  let combineZetaw ← hornerCombine ξ evalsZetaw
  let rTimesZetaw ← mul r combineZetaw
  let combineZeta ← hornerCombine ξ evalsZeta
  pure (CVar.add_ combineZeta rTimesZetaw)

/-- The evaluations a read batch keeps, in order. -/
def keptEvals (xs : List (Bool × F)) : List F :=
  (xs.filter (·.1)).map (·.2)

/-! ## Soundness -/

variable [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}

/-- A Horner step reads as `fx + ξ·acc` where the entry is kept and as `acc` otherwise. -/
private theorem hornerStep_spec (ξ acc : FVar F) (e : BoolVar F × FVar F) (x : Bool × F)
    (he : CircuitType.Reads V e x) :
    ⦃⌜True⌝⦄ hornerStep (c := Builder V c) ξ acc e
    ⦃⇓ a _ => ⌜a.val V = if x.1 then x.2 + ξ.val V * acc.val V else acc.val V⌝⦄ := by
  obtain ⟨hb, hx⟩ := CircuitType.reads_prod.mp he
  rw [CircuitType.reads_boolVar] at hb
  rw [CircuitType.reads_fvar] at hx
  simp only [hornerStep]
  mvcgen
  intro hsel
  rw [hsel x.1 hb]
  cases x.1 <;> simp [*]

/-- The fold reads as the Horner sum of the kept entries in batch order, then the seed. -/
private theorem hornerGo_spec (ξ : FVar F) :
    ∀ (acc : FVar F) (l : List (BoolVar F × FVar F)) (xs : List (Bool × F)),
      List.Forall₂ (CircuitType.Reads V) l xs →
      ⦃⌜True⌝⦄ hornerGo (c := Builder V c) ξ acc l
      ⦃⇓ a _ => ⌜a.val V = alphaCombo (ξ.val V) (keptEvals xs.reverse ++ [acc.val V])⌝⦄
  | acc, [], [], _ => by
    simp only [hornerGo]
    mvcgen
    simp [alphaCombo, keptEvals]
  | _, [], _ :: _, h => nomatch h
  | _, _ :: _, [], h => nomatch h
  | acc, e :: rest, x :: xs, h => by
    obtain ⟨hx, hrest⟩ := List.forall₂_cons.mp h
    simp only [hornerGo]
    have hstep := hornerStep_spec (c := c) (V := V) ξ acc e x hx
    have ih := fun acc' => hornerGo_spec ξ acc' rest xs hrest
    mvcgen [hstep, ih]
    intro hres
    rw [hres]
    simp only [keptEvals, List.reverse_cons, List.filter_append, List.filter_cons,
      List.filter_nil, List.map_append, List.append_assoc, *]
    split_ifs <;> simp [alphaCombo, List.foldr_append]

/-- The Horner sum of a batch whose last entry is kept. -/
private theorem hornerCombine_spec (ξ : FVar F) (evals : List (BoolVar F × FVar F))
    (xs : List (Bool × F)) (hx : List.Forall₂ (CircuitType.Reads V) evals xs)
    (hlast : ∀ x ∈ xs.getLast?, x.1 = true) :
    ⦃⌜True⌝⦄ hornerCombine (c := Builder V c) ξ evals
    ⦃⇓ a _ => ⌜a.val V = alphaCombo (ξ.val V) (keptEvals xs)⌝⦄ := by
  have hrev := List.forall₂_reverse_iff.mpr hx
  rw [← List.reverse_reverse xs]
  simp only [hornerCombine]
  match hr : evals.reverse, hxr : xs.reverse, hrev with
  | [], [], _ => mvcgen
  | last :: revFront, xl :: xrev, h =>
    obtain ⟨hl, hfront⟩ := List.forall₂_cons.mp h
    have hxl : xl.1 = true := by
      apply hlast
      rw [← List.reverse_reverse xs, hxr]
      simp
    have hval : last.2.val V = xl.2 := CircuitType.reads_fvar.mp (CircuitType.reads_prod.mp hl).2
    have hgo := hornerGo_spec (c := c) (V := V) ξ last.2 revFront xrev hfront
    mvcgen [hgo]
    intro hgoal
    rw [hgoal]
    congr 1
    simp [keptEvals, List.filter_append, hxl, hval]

/-- Under any valuation satisfying the emitted constraints, with `ξ`, `r` reading as `ξ`, `r`,
the `ζ`-entries as `(k₀, e₀), …, (kₘ, eₘ)` and the `ζω`-entries as `(k'₀, e'₀), …, (k'ₘ, e'ₘ)`,
the last entry of each kept, the output reads as
`∑ⱼ ξʲ · fⱼ + r · ∑ⱼ ξʲ · f'ⱼ`, where `f₀, f₁, …` are the `eᵢ` with `kᵢ` set, in order, and
`f'₀, f'₁, …` likewise the `e'ᵢ` with `k'ᵢ` set. -/
theorem combinedInnerProduct_spec (ξ r : FVar F)
    (evalsZeta evalsZetaw : List (BoolVar F × FVar F)) (xz xw : List (Bool × F))
    (hz : List.Forall₂ (CircuitType.Reads V) evalsZeta xz)
    (hw : List.Forall₂ (CircuitType.Reads V) evalsZetaw xw)
    (hlz : ∀ x ∈ xz.getLast?, x.1 = true) (hlw : ∀ x ∈ xw.getLast?, x.1 = true) :
    ⦃⌜True⌝⦄ combinedInnerProduct (c := Builder V c) ξ r evalsZeta evalsZetaw
    ⦃⇓ a _ => ⌜a.val V = alphaCombo (ξ.val V) (keptEvals xz)
      + r.val V * alphaCombo (ξ.val V) (keptEvals xw)⌝⦄ := by
  simp only [combinedInnerProduct]
  have hcz := hornerCombine_spec (c := c) (V := V) ξ evalsZeta xz hz hlz
  have hcw := hornerCombine_spec (c := c) (V := V) ξ evalsZetaw xw hw hlw
  mvcgen [hcz, hcw]
  simp only [CVar.val_add_, *]

omit [DecidableEq F] [BasicSystem F c] in
/-- Two Horner sums over the batch's rows, combined by `r`, are
`Bulletproof.combinedInnerProduct` at the rows' evaluation matrix. -/
private theorem alphaCombo_rows_eq_combinedInnerProduct (ξ r : F)
    (rows : List (Kimchi.Verifier.PointEvaluations F)) :
    alphaCombo ξ (rows.map (·.zeta)) + r * alphaCombo ξ (rows.map (·.zetaOmega))
      = Bulletproof.combinedInnerProduct ξ r
          (fun (i : Fin rows.length) (j : Fin evalPts) => ((rows.get i).toVector)[j]) := by
  rw [alphaCombo_eq_sum_getD ξ _ rows.length (by simp),
    alphaCombo_eq_sum_getD ξ _ rows.length (by simp), Bulletproof.combinedInnerProduct,
    Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Fin.sum_univ_two, Kimchi.Verifier.PointEvaluations.toVector,
    List.getD_eq_getElem?_getD]
  ring

/-- `combinedInnerProduct_spec` at the batch rows: when the kept `ζ`-evaluations are
`z₀, …, zₙ₋₁` and the kept `ζω`-evaluations `z'₀, …, z'ₙ₋₁`, the two columns of `rows`, the
output reads as `∑ⱼ ξʲ · (zⱼ + r · z'ⱼ)`, which is `Bulletproof.combinedInnerProduct ξ r E`
at the matrix `E j = (zⱼ, z'ⱼ)`. -/
theorem combinedInnerProduct_spec_cip (ξ r : FVar F)
    (evalsZeta evalsZetaw : List (BoolVar F × FVar F)) (xz xw : List (Bool × F))
    (hz : List.Forall₂ (CircuitType.Reads V) evalsZeta xz)
    (hw : List.Forall₂ (CircuitType.Reads V) evalsZetaw xw)
    (hlz : ∀ x ∈ xz.getLast?, x.1 = true) (hlw : ∀ x ∈ xw.getLast?, x.1 = true)
    (rows : List (Kimchi.Verifier.PointEvaluations F))
    (hrz : keptEvals xz = rows.map (·.zeta)) (hrw : keptEvals xw = rows.map (·.zetaOmega)) :
    ⦃⌜True⌝⦄ combinedInnerProduct (c := Builder V c) ξ r evalsZeta evalsZetaw
    ⦃⇓ a _ => ⌜a.val V = Bulletproof.combinedInnerProduct (ξ.val V) (r.val V)
      (fun (i : Fin rows.length) (j : Fin evalPts) => ((rows.get i).toVector)[j])⌝⦄ := by
  have h := combinedInnerProduct_spec (c := c) (V := V) ξ r evalsZeta evalsZetaw xz xw hz hw
    hlz hlw
  rw [hrz, hrw, alphaCombo_rows_eq_combinedInnerProduct] at h
  exact h

end Pickles
