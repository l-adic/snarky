import Snarky.DSL.Field
import Snarky.Kimchi.Circuit.EndoScalar
import Bulletproof.Protocol

set_option mvcgen.warning false

/-!
# The challenge polynomial in circuit

Port of the PureScript `Pickles.IPA` scalar gadgets: the challenge polynomial
`b(c, X) = ∏_{i<k} (1 + cᵢ · X^{2^{k−1−i}})` of `k` challenges `c₀, …, c_{k−1}` evaluated at
a point, its evaluation for every previous proof, the endomorphism expansion of the
bulletproof challenges, and the `b_correct` check `b = b(c, ζ) + r · b(c, ζω)`.

## Main definitions

* `bPolyCircuit`: the squarings of the point, then the product, in the PureScript's order.
* `challengePolyEvals`: `∏_{i<k} (1 + c_{j,i} · pt^{2^{k−1−i}})` for each of `n` challenge
  vectors `(c_{j,0}, …, c_{j,k−1})`, `j < n`.
* `computeChallenges`: `EndoScalar.toField` on each 128-bit challenge.
* `computeBCircuit`, `bCorrectCircuit`: `b(c, ζ) + r · b(c, ζω)` and its comparison with
  the claimed `b`.

## Main results

* `bPolyCircuit_spec`, `challengePolyEvals_spec`: the outputs read as `Bulletproof.bPoly`
  at the readings of the challenges and the point.
* `computeChallenges_spec`: the outputs read as `endoExpand` of the challenges' naturals.
* `computeBCircuit_spec`, `bCorrectCircuit_spec`: the output reads as
  `Bulletproof.combinedB`, and the bit as its comparison with the claim.
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

/-- The bulletproof challenges expanded through the endomorphism `endo` (OCaml
`compute_challenges`): `EndoScalar.toField` on each, the last challenge first and the results
in vector order. -/
def computeChallenges [ToNat F] [Snarky.Kimchi.KimchiSystem F c] (endo : FVar F) :
    List (FVar F) → CircuitM F c (List (FVar F))
  | [] => pure []
  | ch :: rest => do
    let later ← computeChallenges endo rest
    let x ← Snarky.Kimchi.EndoScalar.toField 8 ch endo
    pure (x :: later)

/-- `b(c, ζ) + r · b(c, ζω)` for challenges `c`, the `ζω` evaluation first. -/
def computeBCircuit (chals : List (FVar F)) (zeta zetaOmega evalscale : FVar F) :
    CircuitM F c (FVar F) := do
  let bZetaOmega ← bPolyCircuit chals zetaOmega
  let scaledB ← mul evalscale bZetaOmega
  let bZeta ← bPolyCircuit chals zeta
  pure (CVar.add_ bZeta scaledB)

/-- The bit `expectedB = b(c, ζ) + r · b(c, ζω)`. -/
def bCorrectCircuit (chals : List (FVar F)) (zeta zetaOmega evalscale expectedB : FVar F) :
    CircuitM F c (BoolVar F) := do
  let computedB ← computeBCircuit chals zeta zetaOmega evalscale
  equals expectedB computedB

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

/-- Under any valuation satisfying the emitted constraints, with `endo` reading as `λ`, the
`j`-th challenge reads as a natural `nⱼ < 2^128` and the `j`-th output as `endoExpand λ nⱼ`,
Mina's `a·λ + b` from the GLV recoding of `nⱼ`. -/
theorem computeChallenges_spec [ToNat F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (endo : FVar F) :
    ∀ chals : List (FVar F),
      ⦃⌜True⌝⦄ computeChallenges (c := Builder V (Snarky.Kimchi.KimchiConstraint F)) endo chals
      ⦃⇓ l _ => ⌜∃ ns : List ℕ,
        List.Forall₂ (fun (ch : FVar F) (n : ℕ) => n < 2 ^ 128 ∧ ch.val V = (n : F)) chals ns ∧
        List.Forall₂ (CircuitType.Reads V) l
          (ns.map (Poseidon.FqSponge.endoExpand (endo.val V)))⌝⦄
  | [] => by
    simp only [computeChallenges]
    mvcgen
    exact ⟨[], .nil, .nil⟩
  | ch :: rest => by
    simp only [computeChallenges]
    have ih := computeChallenges_spec h2 h3 endo rest
    have hx := Snarky.Kimchi.EndoScalar.toField_spec (V := V) h2 h3 ch endo
    mvcgen [ih, hx]
    rename_i hrest _ _ hch
    obtain ⟨ns, hns, hl⟩ := hrest
    obtain ⟨n, hn, hchv, hrv⟩ := hch
    exact ⟨n :: ns, .cons ⟨hn, hchv⟩ hns, .cons (CircuitType.reads_fvar.mpr hrv) hl⟩

/-- Under any valuation satisfying the emitted constraints, with the challenges reading as
`c = (c₀, …, c_{k−1})` and `ζ`, `ζω`, `r` as themselves, the output reads as
`b(c, ζ) + r · b(c, ζω)`, which is `Bulletproof.combinedB c r ![ζ, ζω]`. -/
theorem computeBCircuit_spec (chals : List (FVar F)) (zeta zetaOmega evalscale : FVar F)
    (cs : List F) (hc : List.Forall₂ (CircuitType.Reads V) chals cs) :
    ⦃⌜True⌝⦄ computeBCircuit (c := Builder V c) chals zeta zetaOmega evalscale
    ⦃⇓ a _ => ⌜a.val V = Bulletproof.combinedB (fun i : Fin cs.length => cs.get i)
      (evalscale.val V) ![zeta.val V, zetaOmega.val V]⌝⦄ := by
  simp only [computeBCircuit]
  have hw := bPolyCircuit_spec (c := c) (V := V) chals zetaOmega cs hc
  have hz := bPolyCircuit_spec (c := c) (V := V) chals zeta cs hc
  mvcgen [hw, hz]
  simp only [CVar.val_add_, Bulletproof.combinedB, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one, *]

/-- Under any valuation satisfying the emitted constraints, with the challenges reading as
`c`, the claim as `b` and `ζ`, `ζω`, `r` as themselves, the output bit reads `1` where
`b = b(c, ζ) + r · b(c, ζω)` and `0` elsewhere. -/
theorem bCorrectCircuit_spec (chals : List (FVar F)) (zeta zetaOmega evalscale expectedB : FVar F)
    (cs : List F) (hc : List.Forall₂ (CircuitType.Reads V) chals cs) :
    ⦃⌜True⌝⦄ bCorrectCircuit (c := Builder V c) chals zeta zetaOmega evalscale expectedB
    ⦃⇓ b _ => ⌜(↑b : CVar F).val V = if expectedB.val V
      = Bulletproof.combinedB (fun i : Fin cs.length => cs.get i) (evalscale.val V)
          ![zeta.val V, zetaOmega.val V] then 1 else 0⌝⦄ := by
  simp only [bCorrectCircuit]
  have h := computeBCircuit_spec (c := c) (V := V) chals zeta zetaOmega evalscale cs hc
  mvcgen [h]
  intro hb
  simp only [*]

end Pickles
