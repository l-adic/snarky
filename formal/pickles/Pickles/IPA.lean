import Snarky.DSL.Field
import Bulletproof.Protocol

set_option mvcgen.warning false

/-!
# The challenge polynomial in circuit

Port of the PureScript `Pickles.IPA.bPolyCircuit` and `challengePolyEvals`: a previous
proof's challenge polynomial `b(c, X) = ∏_{i<k} (1 + cᵢ · X^{2^{k−1−i}})`, for its `k`
challenges `c₀, …, c_{k−1}`, evaluated at a point, and its evaluation for every previous
proof.

## Main definitions

* `bPolyCircuit`: the squarings of the point, then the product, in the PureScript's order.
* `challengePolyEvals`: `∏_{i<k} (1 + c_{j,i} · pt^{2^{k−1−i}})` for each of `n` challenge
  vectors `(c_{j,0}, …, c_{j,k−1})`, `j < n`.

## Main results

* `bPolyCircuit_spec`, `challengePolyEvals_spec`: the outputs read as `Bulletproof.bPoly`
  at the readings of the challenges and the point.
-/

namespace Pickles

open Std.Do Snarky

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- The successive squares `[x², x⁴, …, x^(2^n)]`. -/
private def squaresGo (x : FVar F) : ℕ → CircuitM F c (List (FVar F))
  | 0 => pure []
  | n + 1 => do
    let sq ← mul x x
    let rest ← squaresGo sq n
    pure (sq :: rest)

/-- The product `acc · ∏ (1 + c · pw)` over the pairs. -/
private def bPolyGo (acc : FVar F) : List (FVar F × FVar F) → CircuitM F c (FVar F)
  | [] => pure acc
  | (ch, pw) :: rest => do
    let cp ← mul ch pw
    let acc' ← mul (CVar.add_ (.const 1) cp) acc
    bPolyGo acc' rest

/-- The challenge polynomial `∏ᵢ (1 + cᵢ · pt^(2^(k−1−i)))` at `pt`. The product is seeded
from the constant `1`, whose multiplication folds to no row. -/
def bPolyCircuit (chals : List (FVar F)) (pt : FVar F) : CircuitM F c (FVar F) := do
  let squares ← squaresGo pt (chals.length - 1)
  bPolyGo (.const 1) (chals.zip (pt :: squares).reverse)

/-- For challenge vectors `(c_{j,0}, …, c_{j,k−1})`, `j < n`, the list whose `j`-th entry is
`∏_{i<k} (1 + c_{j,i} · pt^{2^{k−1−i}})`. -/
def challengePolyEvals (pt : FVar F) : List (List (FVar F)) → CircuitM F c (List (FVar F))
  | [] => pure []
  | chals :: rest => do
    -- last vector first
    let later ← challengePolyEvals pt rest
    let b ← bPolyCircuit chals pt
    pure (b :: later)

/-! ## Soundness -/

variable [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}

/-- The squares read as the successive powers `x^(2^(j+1))`. -/
private theorem squaresGo_spec (x : FVar F) :
    ∀ n : ℕ, ⦃⌜True⌝⦄ squaresGo (c := Builder V c) x n
      ⦃⇓ l _ => ⌜l.map (·.val V) = (List.range n).map fun j => x.val V ^ 2 ^ (j + 1)⌝⦄
  | 0 => by simp only [squaresGo]; mvcgen
  | n + 1 => by
    simp only [squaresGo]
    have ih := fun sq => squaresGo_spec sq n
    mvcgen [ih]
    clear ih
    simp only [List.map_cons, List.range_succ_eq_map, List.map_map, *]
    congr 1
    · ring
    · refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp, Nat.succ_eq_add_one, pow_succ]
      ring

/-- The fold reads as the accumulator times the product of the pairs' factors. -/
private theorem bPolyGo_spec (acc : FVar F) :
    ∀ ps : List (FVar F × FVar F), ⦃⌜True⌝⦄ bPolyGo (c := Builder V c) acc ps
      ⦃⇓ a _ => ⌜a.val V = acc.val V
        * (ps.map fun p => 1 + p.1.val V * p.2.val V).prod⌝⦄
  | [] => by simp only [bPolyGo]; mvcgen; all_goals simp
  | (ch, pw) :: rest => by
    simp only [bPolyGo]
    have ih := fun a => bPolyGo_spec a rest
    mvcgen [ih]
    clear ih
    intro hres
    simp only [List.map_cons, List.prod_cons, CVar.val_add_, CVar.val, *]
    ring

omit [DecidableEq F] in
/-- The product over the challenges zipped with the reversed powers is `Bulletproof.bPoly`. -/
private theorem prod_zip_pows_eq_bPoly (cs : List F) (x : F) :
    ((cs.zip ((List.range cs.length).map fun i => x ^ 2 ^ i).reverse).map
      fun p => 1 + p.1 * p.2).prod
      = Bulletproof.bPoly (fun i : Fin cs.length => cs.get i) x := by
  rw [Bulletproof.bPoly, ← List.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < cs.length := by simpa using h2
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn, List.getElem_reverse,
      List.length_map, List.length_range, List.getElem_range, List.get_eq_getElem]

omit [DecidableEq F] in
/-- Variables read entrywise map to their readings. -/
private theorem map_val_of_forall₂ {l : List (FVar F)} {xs : List F}
    (h : List.Forall₂ (CircuitType.Reads V) l xs) : l.map (·.val V) = xs := by
  induction h with
  | nil => rfl
  | cons hx _ ih => simp [CircuitType.reads_fvar.mp hx, ih]

/-- Under any valuation satisfying the emitted constraints, with the `k` challenges reading
as `c₀, …, c_{k−1}` and the point as `p`, the output reads as
`b(c, p) = ∏_{i<k} (1 + cᵢ · p^{2^{k−1−i}})`, which is `Bulletproof.bPoly c p`. -/
theorem bPolyCircuit_spec (chals : List (FVar F)) (pt : FVar F) (cs : List F)
    (hc : List.Forall₂ (CircuitType.Reads V) chals cs) :
    ⦃⌜True⌝⦄ bPolyCircuit (c := Builder V c) chals pt
    ⦃⇓ a _ => ⌜a.val V = Bulletproof.bPoly (fun i : Fin cs.length => cs.get i)
      (pt.val V)⌝⦄ := by
  simp only [bPolyCircuit]
  have hsq := squaresGo_spec (c := c) (V := V) pt (chals.length - 1)
  have hgo := fun ps => bPolyGo_spec (c := c) (V := V) (.const 1) ps
  mvcgen [hsq, hgo]
  rename_i squares _ hpows _ _
  intro hres
  obtain rfl := map_val_of_forall₂ hc
  rw [hres, ← prod_zip_pows_eq_bPoly (chals.map (·.val V)) (pt.val V)]
  simp only [CVar.val, one_mul, List.length_map]
  cases chals with
  | nil => simp
  | cons ch chs =>
    have hP : (pt :: squares).reverse.map (·.val V)
        = ((List.range (ch :: chs).length).map fun i => pt.val V ^ 2 ^ i).reverse := by
      rw [List.map_reverse, List.map_cons, hpows]
      simp only [List.length_cons, Nat.add_sub_cancel, List.range_succ_eq_map, List.map_cons,
        List.map_map, pow_zero, pow_one, Function.comp_def, Nat.succ_eq_add_one]
    rw [← hP, List.zip_map, List.map_map]
    rfl

/-- Under any valuation satisfying the emitted constraints, with the `j`-th of the `n`
challenge vectors reading as `(c_{j,0}, …, c_{j,k−1})` and the point as `p`, the `j`-th output
reads as `∏_{i<k} (1 + c_{j,i} · p^{2^{k−1−i}})`. -/
theorem challengePolyEvals_spec (pt : FVar F) :
    ∀ (prev : List (List (FVar F))) (cvs : List (List F)),
      List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) prev cvs →
      ⦃⌜True⌝⦄ challengePolyEvals (c := Builder V c) pt prev
      ⦃⇓ l _ => ⌜List.Forall₂ (CircuitType.Reads V) l (cvs.map fun cv =>
        Bulletproof.bPoly (fun i : Fin cv.length => cv.get i) (pt.val V))⌝⦄
  | [], [], _ => by simp only [challengePolyEvals]; mvcgen; all_goals simp
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | chals :: rest, cv :: cvs, h => by
    obtain ⟨hcv, hrest⟩ := List.forall₂_cons.mp h
    simp only [challengePolyEvals]
    have ih := challengePolyEvals_spec pt rest cvs hrest
    have hb := bPolyCircuit_spec (c := c) (V := V) chals pt cv hcv
    mvcgen [ih, hb]
    exact List.Forall₂.cons (CircuitType.reads_fvar.mpr ‹_›) ‹_›

end Pickles
