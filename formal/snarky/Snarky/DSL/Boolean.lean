import Mathlib.Algebra.Field.Basic
import Snarky.DSL.Field
import Snarky.Traverse

namespace Snarky

variable {F c : Type}

/-! ## Constants -/

/-- The constant true bit — the underscore stays, `true` being a keyword. -/
def true_ [One F] : BoolVar F := .unchecked (.const 1)

@[simp] theorem true_val [Add F] [Mul F] [One F] (V : Valuation F) :
    (↑(true_ : BoolVar F) : CVar F).val V = 1 := rfl

@[simp] theorem true_scoped [One F] (st : ProverState F) :
    (↑(true_ : BoolVar F) : CVar F).Scoped st := trivial

attribute [irreducible] true_

/-- The constant false bit. -/
def false_ [Zero F] : BoolVar F := .unchecked (.const 0)

@[simp] theorem false_val [Add F] [Mul F] [Zero F] (V : Valuation F) :
    (↑(false_ : BoolVar F) : CVar F).val V = 0 := rfl

@[simp] theorem false_scoped [Zero F] (st : ProverState F) :
    (↑(false_ : BoolVar F) : CVar F).Scoped st := trivial

attribute [irreducible] false_

/-! ## Negation -/

/-- Negate a boolean variable: `1 − b`, pure — no rows; boolean because `b` is. The name
shadows core `not` inside the namespace; resolution is by type at use sites. -/
def not [Add F] [Sub F] [Zero F] [One F] [Neg F] [DecidableEq F] (b : BoolVar F) : BoolVar F :=
  .unchecked (CVar.sub_ (.const 1) ↑b)

/-- `not` reads as the negated bit. -/
theorem not_val [Field F] [DecidableEq F] {V : Valuation F} {b : BoolVar F} {bb : Bool}
    (hb : (↑b : CVar F).val V = bit bb) : (↑(Snarky.not b) : CVar F).val V = bit (!bb) := by
  show (CVar.sub_ (.const 1) ↑b).val V = _
  rw [CVar.val_sub_, hb]
  cases bb <;> simp [bit]

attribute [irreducible] Snarky.not

/-! ## Selection -/

/-- Conditionally select between two field variables: where `b` reads `1` the result
reads as `t`, where it reads `0` as `e` — `r = b·(t − e) + e`, one row. A constant
selector folds to the chosen branch; constant branches fold to the affine form with no
constraint. -/
def selectField [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (b : BoolVar F) (t e : FVar F) :
    CircuitM F c (FVar F) :=
  match (↑b : CVar F), t, e with
  | .const bv, t, e => pure (if bv = 1 then t else e)
  | b, .const tv, .const ev =>
    pure (CVar.add_ (.scale tv b) (CVar.scale_ ev (CVar.sub_ (.const 1) b)))
  | b, t, e => core b t e
where
  /-- The advice: read the selector, return the branch it picks. -/
  advice (b : CVar F) (t e : FVar F) : AsProver F F := do
    let bv ← AsProver.readCVar b
    if bv = 1 then AsProver.readCVar t else AsProver.readCVar e
  /-- The witnessing branch, isolated so its laws are stated in their own binders rather
  than under the shape match (as `xor.core` is). -/
  core (b : CVar F) (t e : FVar F) : CircuitM F c (FVar F) := do
    let r ← witness (val := F) (advice b t e)
    addConstraint (BasicSystem.r1cs b (CVar.sub_ t e) (CVar.sub_ r e))
    pure r

open Std.WP in
/-- `selectField b t e` reads as the branch the selector's bit picks. -/
@[spec] theorem selectField_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F) (t e : FVar F) :
    ⦃fun _ => True⦄
    selectField (c := Builder V c) b t e
    ⦃fun r _ => ∀ bb : Bool, (↑b : CVar F).val V = bit bb →
        r.val V = if bb then t.val V else e.val V⦄ := by
  simp only [selectField, selectField.core]
  vcgen
  · rename_i hbc bb hbb
    subst_vars
    rw [hbc] at hbb
    simp only [CVar.val] at hbb
    subst hbb
    cases bb <;> simp [bit, zero_ne_one]
  · rename_i bb hbb
    subst_vars
    simp only [CVar.val_add_, CVar.val_scale_, CVar.val_sub_, CVar.val, hbb]
    cases bb <;> simp [bit]
  · rename_i hrow bb hbb
    subst_vars
    have h := (LawfulBasicSystem.holds_r1cs V _ _ _).mp hrow
    simp only [CVar.val_sub_] at h
    rw [hbb] at h
    cases bb <;> simp only [bit] at h
    · rw [ite_eq_right Bool.false_ne_true, zero_mul] at h
      simp [sub_eq_zero.mp h.symm]
    · rw [ite_eq_left trivial, one_mul] at h
      simp [sub_left_inj.mp h]

attribute [irreducible] selectField

/-! ### Selection at a bundle

`select` dispatches on the bundle's shape, because the row order does: a product selects
its second component before its first, mirroring the reverse evaluation order of the
source's arrays, while a vector selects in index order. The encoding flattens that
distinction away, so it cannot be read off `CircuitType`. -/

/-- Conditional selection at a variable bundle. -/
class IfThenElse (F c : Type) (var : Type) where
  /-- `select b t e` is `t` where `b` reads `1` and `e` where it reads `0`. -/
  select : BoolVar F → var → var → CircuitM F c var

export IfThenElse (select)

/-- Field variables select by the arithmetic mux. -/
instance instIfThenElseFVar [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] :
    IfThenElse F c (FVar F) :=
  ⟨selectField⟩

/-- Selection at a field variable IS the arithmetic mux — the instance's defining
equation, for a caller whose program says `select` and whose law says `selectField`. -/
@[simp] theorem select_fvar [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (b : BoolVar F)
    (t e : FVar F) : select (c := c) b t e = selectField b t e := rfl

/-- Boolean variables select through the field mux, retagged: the mux of two bits is a
bit. -/
instance instIfThenElseBoolVar [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] :
    IfThenElse F c (BoolVar F) where
  select b x y := do
    let r ← selectField b ↑x ↑y
    pure (.unchecked r)

/-- Nothing to select. -/
instance instIfThenElseUnit : IfThenElse F c Unit where
  select _ _ _ := pure ()

/-- Pairs select componentwise, SECOND BEFORE FIRST. -/
instance instIfThenElseProd {va vb : Type} [IfThenElse F c va] [IfThenElse F c vb] :
    IfThenElse F c (va × vb) where
  select s p q := do
    let snd ← select s p.2 q.2
    let fst ← select s p.1 q.1
    pure (fst, snd)

/-- Vectors select entrywise, in index order. -/
instance instIfThenElseVector {va : Type} {n : Nat} [IfThenElse F c va] :
    IfThenElse F c (Vector va n) where
  select s v w := zipWithVecM (select s) v w

/-! ### Selection's laws

The law is per shape, like the definition. A bundle carries it through `LawfulIfThenElse`;
the leaves and the formers instantiate it, and a shape reaches it through its own
isomorphism. -/

open Std.WP in
/-- Selection's contract at a bundle, at the backend's reading of its constraints: the result
reads as the operand the selector's bit picks. -/
class LawfulIfThenElse (F c val var : Type) [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [CircuitType F val var] [IfThenElse F c var] where
  /-- The result reads as the operand the selector's bit picks. -/
  select_sound : ∀ (V : Valuation F) (b : BoolVar F) (t e : var) (tv ev : val) (bb : Bool),
    CircuitType.Reads V t tv → CircuitType.Reads V e ev → (↑b : CVar F).val V = bit bb →
    ⦃fun _ => True⦄
    atBuilder V (select (c := c) b t e)
    ⦃fun r _ => CircuitType.Reads V r (if bb then tv else ev)⦄

section Lawful

open Std.WP

variable [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]

instance instLawfulIfThenElseFVar : LawfulIfThenElse F c F (FVar F) where
  select_sound V b t e tv ev bb ht he hb := by
    constructor
    intro nv _ hsat
    show CircuitType.Reads V _ _
    rw [CircuitType.reads_fvar, ← CircuitType.reads_fvar.mp ht, ← CircuitType.reads_fvar.mp he]
    exact (selectField_spec (c := c) (V := V) b t e).le_wp nv trivial hsat bb hb

instance instLawfulIfThenElseBoolVar : LawfulIfThenElse F c Bool (BoolVar F) where
  select_sound V b t e tv ev bb ht he hb := by
    have h := selectField_spec (c := c) (V := V) b ↑t ↑e
    show ⦃fun _ => True⦄ (selectField (c := Builder V c) b ↑t ↑e >>= fun r =>
      pure (BoolVar.unchecked r)) ⦃_⦄
    vcgen [h]
    rename_i hr
    rw [CircuitType.reads_boolVar, BoolVar.coe_unchecked, hr bb hb,
      CircuitType.reads_boolVar.mp ht, CircuitType.reads_boolVar.mp he]
    cases bb <;> simp

instance instLawfulIfThenElseUnit : LawfulIfThenElse F c Unit Unit where
  select_sound _ _ _ _ _ _ _ _ _ _ := ⟨fun _ _ _ => CircuitType.reads_unit⟩

variable {a va b vb : Type}

instance instLawfulIfThenElseProd [CircuitType F a va] [CircuitType F b vb] [IfThenElse F c va]
    [IfThenElse F c vb] [A : LawfulIfThenElse F c a va] [B : LawfulIfThenElse F c b vb] :
    LawfulIfThenElse F c (a × b) (va × vb) where
  select_sound V s t e tv ev bb ht he hb := by
    obtain ⟨tv₁, tv₂⟩ := tv
    obtain ⟨ev₁, ev₂⟩ := ev
    rw [CircuitType.reads_prod] at ht he
    have h₂ := (builder_spec_iff _ _).mp
      (B.select_sound (c := c) V s t.2 e.2 tv₂ ev₂ bb ht.2 he.2 hb)
    have h₁ := (builder_spec_iff _ _).mp
      (A.select_sound (c := c) V s t.1 e.1 tv₁ ev₁ bb ht.1 he.1 hb)
    refine (builder_spec_iff _ _).mpr fun nv hsat => ?_
    replace hsat : ∀ con ∈ (build (IfThenElse.select (c := c) s t.2 e.2 >>= fun snd =>
        IfThenElse.select (c := c) s t.1 e.1 >>= fun fst => pure (fst, snd)) nv).constraints,
        ConstraintHolds.Holds V con := hsat
    show CircuitType.Reads V (build (IfThenElse.select (c := c) s t.2 e.2 >>= fun snd =>
      IfThenElse.select (c := c) s t.1 e.1 >>= fun fst => pure (fst, snd)) nv).result _
    rw [build_bind] at hsat ⊢
    rw [build_bind] at hsat ⊢
    have hrows₂ : ∀ con ∈ (build (IfThenElse.select (c := c) s t.2 e.2) nv).constraints,
        ConstraintHolds.Holds V con := fun con hcon => hsat con (List.mem_append_left _ hcon)
    have hrows₁ := fun con hcon => hsat con
      (List.mem_append_right _ (List.mem_append_left _ hcon))
    cases bb <;>
      exact CircuitType.reads_prod.mpr ⟨h₁ _ hrows₁, h₂ nv hrows₂⟩

instance instLawfulIfThenElseVector [CircuitType F a va] [IfThenElse F c va]
    [S : LawfulIfThenElse F c a va] {n : Nat} :
    LawfulIfThenElse F c (Vector a n) (Vector va n) where
  select_sound V s t e tv ev bb ht he hb := by
    rw [CircuitType.reads_vector] at ht he
    have hzip := zipWithVecM_spec (V := V)
      (IfThenElse.select (c := c) s : va → va → CircuitM F (Builder V c) va) t e
      (fun i r => CircuitType.Reads V r (if bb then tv[i.val] else ev[i.val]))
      (fun i => S.select_sound (c := c) V s t[i.val] e[i.val] tv[i.val] ev[i.val] bb
        (ht i.val i.isLt) (he i.val i.isLt) hb)
    refine (builder_spec_iff _ _).mpr fun nv hsat => ?_
    have h := (builder_spec_iff _ _).mp hzip nv hsat
    refine CircuitType.reads_vector.mpr fun i hi => ?_
    have hi' := h ⟨i, hi⟩
    simp only [Fin.getElem_fin] at hi'
    cases bb <;> exact hi'

end Lawful

/-! ## Conjunction -/

/-- Conjoin boolean variables: the product, retagged — boolean because a product of bits
is a bit. `mul`'s rows. -/
def and [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (a b : BoolVar F) :
    CircuitM F c (BoolVar F) := do
  let r ← mul ↑a ↑b
  pure (.unchecked r)

open Std.WP in
/-- `and`: on bit operands the result reads as the conjunction bit. -/
@[spec] theorem and_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃fun _ => True⦄
    Snarky.and (c := Builder V c) a b
    ⦃fun (r : BoolVar F) _ => ∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab && bb)⦄ := by
  simp only [Snarky.and]
  vcgen
  rename_i hr ab bb ha hb
  simp only [BoolVar.coe_unchecked, hr, ha, hb]
  cases ab <;> cases bb <;> simp [bit]

attribute [irreducible] Snarky.and

/-! ## Disjunction -/

/-- Disjoin boolean variables by De Morgan: `¬(¬a ∧ ¬b)` — one `and`, the negations pure
retags. -/
def or [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (a b : BoolVar F) :
    CircuitM F c (BoolVar F) := do
  let r ← Snarky.and (Snarky.not a) (Snarky.not b)
  pure (Snarky.not r)

open Std.WP in
/-- `or`: on bit operands the result reads as the disjunction bit. -/
@[spec] theorem or_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃fun _ => True⦄
    Snarky.or (c := Builder V c) a b
    ⦃fun (r : BoolVar F) _ => ∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab || bb)⦄ := by
  simp only [Snarky.or]
  vcgen
  rename_i hr ab bb ha hb
  rw [not_val (hr (!ab) (!bb) (not_val ha) (not_val hb))]
  cases ab <;> cases bb <;> simp

attribute [irreducible] Snarky.or

/-! ## Exclusive or -/

/-- Exclusive or: both constant folds; one constant selects the other operand (`0`) or
its negation (`1`), anything else falls through to the witnessing branch — the bit,
pinned by `2a · b = a + b − r`. -/
def xor [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (a b : BoolVar F) :
    CircuitM F c (BoolVar F) :=
  match (↑a : CVar F), (↑b : CVar F) with
  | .const av, .const bv => pure (.unchecked (.const (if av = bv then 0 else 1)))
  | .const av, _ =>
    if av = 0 then pure b else if av = 1 then pure (Snarky.not b) else core a b
  | _, .const bv =>
    if bv = 0 then pure a else if bv = 1 then pure (Snarky.not a) else core a b
  | _, _ => core a b
where
  /-- The advice: the inequality bit. -/
  advice (a b : BoolVar F) : AsProver F F := do
    let av ← AsProver.readCVar ↑a
    let bv ← AsProver.readCVar ↑b
    pure (if av = bv then 0 else 1)
  /-- The witnessing branch. -/
  core (a b : BoolVar F) : CircuitM F c (BoolVar F) := do
    let r ← witness (val := F) (advice a b)
    addConstraint (BasicSystem.r1cs (CVar.add_ (↑a : CVar F) ↑a) ↑b
      (CVar.sub_ (CVar.add_ ↑a ↑b) r))
    pure (.unchecked r)

/-- The row `2a · b = a + b − r` pins `r` to the xor bit. -/
private theorem xor_pin [Field F] {ab bb : Bool} {rv : F}
    (h : ((bit ab : F) + bit ab) * bit bb = bit ab + bit bb - rv) :
    rv = bit (ab ^^ bb) := by
  have h' : rv = (bit ab : F) + bit bb - (bit ab + bit ab) * bit bb :=
    eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp h.symm).symm
  rw [h']
  cases ab <;> cases bb <;> simp [bit]

open Std.WP in
/-- The witnessing branch reads as the xor bit on bit operands. -/
@[spec] private theorem xor.core_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃fun _ => True⦄
    Snarky.xor.core (c := Builder V c) a b
    ⦃fun (r : BoolVar F) _ => ∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab ^^ bb)⦄ := by
  simp only [Snarky.xor.core]
  vcgen
  rename_i hrow ab bb ha hb
  have h := (LawfulBasicSystem.holds_r1cs V _ _ _).mp hrow
  simp only [CVar.val_add_, CVar.val_sub_, BoolVar.coe_unchecked] at h ⊢
  rw [ha, hb] at h
  exact xor_pin h

open Std.WP in
/-- `xor`: on bit operands the result reads as the xor bit. -/
@[spec] theorem xor_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃fun _ => True⦄
    Snarky.xor (c := Builder V c) a b
    ⦃fun (r : BoolVar F) _ => ∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab ^^ bb)⦄ := by
  simp only [Snarky.xor]
  vcgen
  all_goals first
    | (rename_i ab bb ha hb
       have hA : a.toCVar = CVar.const _ := ‹_›
       have hB : b.toCVar = CVar.const _ := ‹_›
       rw [hA] at ha
       rw [hB] at hb
       simp only [CVar.val] at ha hb
       subst ha
       subst hb
       cases ab <;> cases bb <;> simp [bit])
    | (rename_i ab bb ha hb
       have hA : a.toCVar = CVar.const _ := ‹_›
       have h0 : _ = (0 : F) := ‹_›
       rw [hA] at ha
       simp only [CVar.val] at ha
       rw [h0] at ha
       cases ab
       · simpa using hb
       · exact absurd ha (by simp [bit]))
    | (rename_i ab bb ha hb
       have hA : a.toCVar = CVar.const _ := ‹_›
       have h1 : _ = (1 : F) := ‹_›
       rw [hA] at ha
       simp only [CVar.val] at ha
       rw [h1] at ha
       cases ab
       · exact absurd ha (by simp [bit])
       · rw [not_val hb]
         simp)
    | (rename_i ab bb ha hb
       have hB : b.toCVar = CVar.const _ := ‹_›
       have h0 : _ = (0 : F) := ‹_›
       rw [hB] at hb
       simp only [CVar.val] at hb
       rw [h0] at hb
       cases bb
       · simpa using ha
       · exact absurd hb (by simp [bit]))
    | (rename_i ab bb ha hb
       have hB : b.toCVar = CVar.const _ := ‹_›
       have h1 : _ = (1 : F) := ‹_›
       rw [hB] at hb
       simp only [CVar.val] at hb
       rw [h1] at hb
       cases bb
       · exact absurd hb (by simp [bit])
       · rw [not_val ha]
         simp)

attribute [irreducible] Snarky.xor

/-! ## Bit sums

A sum of `n` bits detects `n` only below the field characteristic, so the sum-based laws
carry a cast-injectivity hypothesis up to the list length. -/

/-- A list of bits — field values that are `0` or `1` — sums to its count of ones. -/
theorem sum_of_bits [Field F] [DecidableEq F] :
    ∀ (xs : List F), (∀ x ∈ xs, x = 0 ∨ x = 1) → xs.sum = (xs.count 1 : F)
  | [], _ => by simp
  | x :: xs, h => by
    rw [List.sum_cons, List.count_cons,
      sum_of_bits xs fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rcases h x (List.mem_cons_self ..) with rfl | rfl <;> simp [add_comm]

/-! ## Any -/

/-- Any of a list of bits: empty is false, a singleton is itself, a pair is `or`, and three
or more test the bit-sum against zero. -/
def any [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (xs : List (BoolVar F)) :
    CircuitM F c (BoolVar F) :=
  match xs with
  | [] => pure false_
  | [a] => pure a
  | [a, b] => Snarky.or a b
  | _ => neq (sum (xs.map BoolVar.toCVar)) (.const 0)

open Std.WP in
/-- `any`: on bit operands, below the characteristic, the result reads `1` exactly when
some operand reads `1`. -/
@[spec] theorem any_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F))
    (hchar : ∀ k : Nat, k ≤ xs.length → (k : F) = 0 → k = 0) :
    ⦃fun _ => True⦄
    Snarky.any (c := Builder V c) xs
    ⦃fun (r : BoolVar F) _ => (∀ b ∈ xs, (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
        (↑r : CVar F).val V = if ∃ b ∈ xs, (↑b : CVar F).val V = 1 then 1 else 0⦄ := by
  match xs, hchar with
  | [], _ =>
    simp only [Snarky.any]
    constructor
    intro nv _ _ _
    simp [build]
  | [a], _ =>
    simp only [Snarky.any]
    constructor
    intro nv _ _ hbits
    rcases hbits a (by simp) with h | h <;> simp [build, h]
  | [a, b], _ =>
    simp only [Snarky.any]
    vcgen
    rename_i hr hbits
    rcases hbits a (by simp) with ha | ha <;> rcases hbits b (by simp) with hb | hb <;>
      first
      | (rw [hr false false ha hb]; simp [ha, hb, bit])
      | (rw [hr false true ha hb]; simp [ha, hb, bit])
      | (rw [hr true false ha hb]; simp [ha, hb, bit])
      | (rw [hr true true ha hb]; simp [ha, hb, bit])
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [Snarky.any]
    vcgen
    rename_i hr hbits
    have hbits' : ∀ x ∈ ((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar).map (·.val V),
        x = 0 ∨ x = 1 := by
      intro x hx
      simp only [List.map_map, List.mem_map, Function.comp] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      exact hbits b hb
    rw [hr, sum_eval, sum_of_bits _ hbits']
    simp only [CVar.val]
    have hmem : (1 : F) ∈ ((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar).map (·.val V) ↔
        ∃ b ∈ x₁ :: x₂ :: x₃ :: t, (↑b : CVar F).val V = 1 := by
      simp only [List.map_map, List.mem_map, Function.comp]
    by_cases h : ∃ b ∈ x₁ :: x₂ :: x₃ :: t, (↑b : CVar F).val V = 1
    · have hpos : 0 < List.count (1 : F) _ := List.count_pos_iff.mpr (hmem.mpr h)
      have hle : List.count (1 : F) (((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar).map (·.val V))
          ≤ (x₁ :: x₂ :: x₃ :: t).length := by
        have := List.count_le_length (a := (1 : F))
          (l := ((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar).map (·.val V))
        simpa using this
      have hne : ((List.count (1 : F)
          (((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar).map (·.val V)) : ℕ) : F) ≠ 0 :=
        fun hc => absurd (hchar _ hle hc) (by omega)
      rw [ite_eq_left h]
      simp only [hne, ↓reduceIte]
    · have h0 : ((List.count (1 : F)
          (((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar).map (·.val V)) : ℕ) : F) = 0 := by
        rw [List.count_eq_zero.mpr (hmem.not.mpr h)]; simp
      rw [ite_eq_right h]
      simp only [h0, ↓reduceIte]

attribute [irreducible] Snarky.any

/-! ## All -/

/-- All of a list of bits: empty is true, a singleton is itself, a pair is `and`, and three
or more test the bit-sum against the length. -/
def all [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (xs : List (BoolVar F)) :
    CircuitM F c (BoolVar F) :=
  match xs with
  | [] => pure true_
  | [a] => pure a
  | [a, b] => Snarky.and a b
  | _ => equals (.const (xs.length : F)) (sum (xs.map BoolVar.toCVar))

open Std.WP in
/-- `all`: on bit operands, below the characteristic, the result reads `1` exactly when
every operand reads `1`. -/
@[spec] theorem all_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ xs.length → k ≤ xs.length → (j : F) = k → j = k) :
    ⦃fun _ => True⦄
    Snarky.all (c := Builder V c) xs
    ⦃fun (r : BoolVar F) _ => (∀ b ∈ xs, (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
        (↑r : CVar F).val V = if ∀ b ∈ xs, (↑b : CVar F).val V = 1 then 1 else 0⦄ := by
  match xs, hchar with
  | [], _ =>
    simp only [Snarky.all]
    constructor
    intro nv _ _ _
    simp [build]
  | [a], _ =>
    simp only [Snarky.all]
    constructor
    intro nv _ _ hbits
    rcases hbits a (by simp) with h | h <;> simp [build, h]
  | [a, b], _ =>
    simp only [Snarky.all]
    vcgen
    rename_i hr hbits
    rcases hbits a (by simp) with ha | ha <;> rcases hbits b (by simp) with hb | hb <;>
      first
      | (rw [hr false false ha hb]; simp [ha, hb, bit])
      | (rw [hr false true ha hb]; simp [ha, hb, bit])
      | (rw [hr true false ha hb]; simp [ha, hb, bit])
      | (rw [hr true true ha hb]; simp [ha, hb, bit])
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [Snarky.all]
    vcgen
    rename_i hr hbits
    generalize hxs : x₁ :: x₂ :: x₃ :: t = xs at hr hbits hchar ⊢
    have hbits' : ∀ x ∈ (xs.map BoolVar.toCVar).map (·.val V), x = 0 ∨ x = 1 := by
      intro x hx
      simp only [List.map_map, List.mem_map, Function.comp] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      exact hbits b hb
    rw [hr, sum_eval, sum_of_bits _ hbits']
    simp only [CVar.val]
    have hlenL : ((xs.map BoolVar.toCVar).map (·.val V)).length = xs.length := by simp
    have hle : List.count (1 : F) ((xs.map BoolVar.toCVar).map (·.val V)) ≤ xs.length := by
      have := List.count_le_length (a := (1 : F)) (l := (xs.map BoolVar.toCVar).map (·.val V))
      omega
    have hall : List.count (1 : F) ((xs.map BoolVar.toCVar).map (·.val V))
        = ((xs.map BoolVar.toCVar).map (·.val V)).length ↔
          ∀ b ∈ xs, (↑b : CVar F).val V = 1 := by
      rw [List.count_eq_length]
      simp only [List.map_map, List.mem_map, Function.comp]
      exact ⟨fun h b hb => (h _ ⟨b, hb, rfl⟩).symm, fun h x ⟨b, hb, hx⟩ => hx ▸ (h b hb).symm⟩
    by_cases h : ∀ b ∈ xs, (↑b : CVar F).val V = 1
    · have he : (xs.length : F)
          = ((List.count (1 : F) ((xs.map BoolVar.toCVar).map (·.val V)) : ℕ) : F) := by
        rw [hall.mpr h, hlenL]
      rw [ite_eq_left h]
      simp only [CVar.val, he, ↓reduceIte]
    · have hne : (xs.length : F)
          ≠ ((List.count (1 : F) ((xs.map BoolVar.toCVar).map (·.val V)) : ℕ) : F) :=
        fun hc => h (hall.mp (by
          have := hchar _ _ (Nat.le_refl _) hle hc
          omega))
      rw [ite_eq_right h]
      simp only [CVar.val, hne, ↓reduceIte]

attribute [irreducible] Snarky.all

/-! ## The completeness laws

Each gadget's law at the prover's reading (`Snarky.Prover.VCGen`): the operands' readings in, the
result's reading out, the values as parameters. A bit reads a `Bool`, a list of bits reads a list
of them pointwise (`Snarky.Prover.All₂`). `and`, `or`, `any` and `all` are proved by composition
through the laws of the gadgets they call. -/

section ProverReading

open Snarky.Prover Std.WP

/-- A scaled expression is in scope exactly where its operand is. -/
private theorem CVar.scoped_scale {k : F} {x : CVar F} {s : ProverState F} :
    (CVar.scale k x).Scoped s ↔ x.Scoped s := Iff.rfl

/-! The advices' runs: each returns its value wherever its operands are in scope. -/

/-- `selectField.advice` returns the branch the selector's reading picks. -/
private theorem Prover.selectField_advice_run [Field F] [DecidableEq F] {b : CVar F}
    {t e : FVar F} {s : ProverState F} (hb : b.Scoped s) (ht : t.Scoped s) (he : e.Scoped s) :
    (selectField.advice b t e).run s.env =
      .ok (if b.val s.env.get = 1 then t.val s.env.get else e.val s.env.get) := by
  split <;> simp [selectField.advice, AsProver.readCVar_run hb, AsProver.readCVar_run ht,
    AsProver.readCVar_run he, *]

/-- `xor.advice` returns the inequality bit. -/
private theorem Prover.xor_advice_run [Field F] [DecidableEq F] {a b : BoolVar F}
    {s : ProverState F} (ha : (↑a : CVar F).Scoped s) (hb : (↑b : CVar F).Scoped s) :
    (Snarky.xor.advice a b).run s.env =
      .ok (if (↑a : CVar F).val s.env.get = (↑b : CVar F).val s.env.get then 0 else 1) := by
  simp [Snarky.xor.advice, AsProver.readCVar_run ha, AsProver.readCVar_run hb]

/-- `selectField`'s completeness: the result reads the branch the selector's bit picks. -/
theorem Prover.selectField_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F) (t e : FVar F) (bb : Bool)
    (tv ev : F) :
    ⦃Reads b bb ⊓ Reads t tv ⊓ Reads e ev⦄ selectField (c := Prover c) b t e
    ⦃fun r ↦ Reads r (if bb then tv else ev)⦄ := by
  have hw := fun (b' : CVar F) (t' e' : FVar F) ↦
    Spec.witness (c := c) (selectField.advice b' t' e') (if bb then tv else ev) valid_fvar
  unfold selectField selectField.core
  vcgen [hw]
  all_goals prover_assert with
    (intros; simp_all (maxDischargeDepth := 3) [Reads.fvar_apply, Reads.boolVar_apply,
      Prover.selectField_advice_run, Checked.apply, LawfulBasicSystem.holds_r1cs,
      LawfulBasicSystem.cells_r1cs, CVar.val, CVar.val_add_, CVar.val_scale_, CVar.val_sub_,
      CVar.scoped_scale, bit]; (try (split_ifs <;> simp_all)))

/-- `and`'s completeness, by composition through `mul`: the result reads the conjunction of the
operands' bits. -/
theorem Prover.and_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) (ab bb : Bool) :
    ⦃Reads a ab ⊓ Reads b bb⦄ Snarky.and (c := Prover c) a b ⦃fun r ↦ Reads r (ab && bb)⦄ := by
  have hm := Prover.mul_spec (c := c) (↑a : CVar F) ↑b (bit ab) (bit bb)
  simp only [Snarky.and]
  vcgen [hm]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, Reads.boolVar_apply, bit];
      (try (split_ifs <;> simp_all)))

/-- `or`'s completeness, by composition through `and`: the result reads the disjunction of the
operands' bits. -/
theorem Prover.or_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) (ab bb : Bool) :
    ⦃Reads a ab ⊓ Reads b bb⦄ Snarky.or (c := Prover c) a b ⦃fun r ↦ Reads r (ab || bb)⦄ := by
  have ha := Prover.and_spec (c := c) (Snarky.not a) (Snarky.not b) (!ab) (!bb)
  simp only [Snarky.or]
  vcgen [ha]
  all_goals prover_assert with
    (intros; simp_all [Reads.boolVar_apply, Snarky.not, CVar.val_sub_, CVar.val, bit];
      (try (split_ifs <;> simp_all)))

/-- `xor`'s completeness: the result reads the exclusive or of the operands' bits. -/
theorem Prover.xor_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) (ab bb : Bool) :
    ⦃Reads a ab ⊓ Reads b bb⦄ Snarky.xor (c := Prover c) a b ⦃fun r ↦ Reads r (ab ^^ bb)⦄ := by
  have hw := fun a' b' : BoolVar F ↦
    Spec.witness (c := c) (Snarky.xor.advice a' b') (bit (ab ^^ bb) : F) valid_fvar
  unfold Snarky.xor Snarky.xor.core
  vcgen [hw]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, Reads.boolVar_apply, Prover.xor_advice_run,
      Checked.apply, LawfulBasicSystem.holds_r1cs, LawfulBasicSystem.cells_r1cs, CVar.val,
      CVar.val_add_, CVar.val_sub_, Snarky.not, bit]; (try (split_ifs <;> simp_all)))

/-! Bit sums at the prover's reading, from field readings and from `Bool` readings: the
arithmetic of the sum-based gadgets here and of the assertions over bit sums. -/

/-- Bit operands' sum is in scope where they are. -/
theorem scoped_sum_of_bits [Field F] {st : ProverState F}
    {xs : List (BoolVar F)} (h : ∀ x ∈ xs, (↑x : CVar F).Scoped st) :
    (sum (xs.map BoolVar.toCVar)).Scoped st :=
  CVar.Scoped.sum fun _ hx => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact h b hb

/-- Bits reading a list of `Bool` values are in scope and read those values' field bits. -/
theorem scoped_read_of_all₂_reads [Field F] [DecidableEq F] {xs : List (BoolVar F)}
    {bs : List Bool} {s : ProverState F}
    (h : All₂ (Reads (F := F)) xs bs s) :
    (∀ x ∈ xs, (↑x : CVar F).Scoped s) ∧
      xs.map (fun x : BoolVar F ↦ s.read x) = bs.map (bit : Bool → F) := by
  induction xs generalizing bs with
  | nil =>
    cases bs with
    | nil => simp
    | cons => simp [All₂] at h
  | cons x xs ih =>
    cases bs with
    | nil => simp [All₂] at h
    | cons b bs =>
      rw [All₂, Pred.inf_apply, Reads.boolVar_apply] at h
      obtain ⟨⟨hsc, hv⟩, ht⟩ := h
      obtain ⟨ihs, ihv⟩ := ih ht
      refine ⟨fun y hy ↦ ?_, ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hsc
        · exact ihs y hy
      · simp only [List.map_cons, ihv, ProverState.read, hv]

/-- Field bits of `Bool` values count their `true` entries as ones. -/
private theorem count_one_map_bit [Field F] [DecidableEq F] (bs : List Bool) :
    (bs.map (bit : Bool → F)).count 1 = bs.count true := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [bit, ih]

/-- Where bits read a list of `Bool` values, their sum reads the count of `true`. -/
theorem read_sum_of_all₂_reads [Field F] [DecidableEq F] {xs : List (BoolVar F)}
    {bs : List Bool} {s : ProverState F}
    (h : All₂ (Reads (F := F)) xs bs s) :
    s.read (sum (xs.map BoolVar.toCVar)) = (bs.count true : F) := by
  have hmap := (scoped_read_of_all₂_reads h).2
  rw [ProverState.read, sum_eval, List.map_map]
  change (xs.map fun x : BoolVar F ↦ s.read x).sum = _
  rw [hmap, sum_of_bits _ fun v hv ↦ ?_, count_one_map_bit]
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hv
  cases b <;> simp [bit]

/-- Bits reading a list of `Bool` values entail that their sum, in scope, reads the count of
`true`. -/
theorem all₂_reads_le_reads_sum [Field F] [DecidableEq F] (xs : List (BoolVar F)) (bs : List Bool) :
    All₂ (Reads (F := F)) xs bs ≤
      Reads (sum (xs.map BoolVar.toCVar)) (bs.count true : F) := by
  rw [Pred.le_iff]
  intro s h
  rw [Reads.fvar_apply]
  exact ⟨scoped_sum_of_bits (scoped_read_of_all₂_reads h).1, read_sum_of_all₂_reads h⟩

/-- Below the characteristic, the count of `true` in a list of `Bool` values is nonzero in the
field exactly where one of them is `true`. -/
theorem cast_count_true_ne_zero_iff [Field F] {bs : List Bool}
    (hchar : ∀ k : Nat, k ≤ bs.length → (k : F) = 0 → k = 0) :
    (bs.count true : F) ≠ 0 ↔ bs.any id = true := by
  rw [List.any_eq_true]
  constructor
  · intro h
    have hpos : 0 < bs.count true := Nat.pos_of_ne_zero fun h0 ↦ h (by rw [h0]; simp)
    exact ⟨true, List.count_pos_iff.mp hpos, rfl⟩
  · rintro ⟨b, hb, hb1⟩ hc
    have h0 := hchar _ List.count_le_length hc
    rw [List.count_eq_zero] at h0
    simp only [id] at hb1
    exact h0 (hb1 ▸ hb)

/-- Below the characteristic, the count of `true` in a list of `Bool` values is its length in
the field exactly where all of them are `true`. -/
private theorem cast_length_eq_count_true_iff [Field F] {bs : List Bool}
    (hchar : ∀ j k : Nat, j ≤ bs.length → k ≤ bs.length → (j : F) = k → j = k) :
    (bs.length : F) = (bs.count true : F) ↔ bs.all id = true := by
  rw [List.all_eq_true]
  constructor
  · intro h b hb
    have hl := hchar _ _ le_rfl List.count_le_length h
    exact (List.count_eq_length.mp hl.symm b hb).symm
  · intro h
    rw [List.count_eq_length.mpr fun b hb ↦ (h b hb).symm]

/-- `any`'s completeness: below the characteristic, the result reads whether some operand's
bit is `true`. -/
theorem Prover.any_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F)) (bs : List Bool)
    (hchar : ∀ k : Nat, k ≤ bs.length → (k : F) = 0 → k = 0) :
    ⦃All₂ Reads xs bs⦄ Snarky.any (c := Prover c) xs
    ⦃fun r ↦ Reads r (bs.any id)⦄ := by
  match xs, bs, hchar with
  | [], [], _ =>
    simp only [Snarky.any]
    vcgen
    all_goals prover_assert with (intros; simp_all [Reads.boolVar_apply, bit])
  | [a], [b], _ =>
    simp only [Snarky.any]
    vcgen
    all_goals prover_assert with (intros; simp_all [All₂])
  | [a₁, a₂], [b₁, b₂], _ =>
    have ho := Prover.or_spec (c := c) a₁ a₂ b₁ b₂
    simp only [Snarky.any]
    vcgen [ho]
    all_goals prover_assert with simp_all [All₂]
  | x₁ :: x₂ :: x₃ :: t, bs, hchar =>
    have hsum := all₂_reads_le_reads_sum (x₁ :: x₂ :: x₃ :: t) bs
    have hn := Prover.neq_spec (c := c) (sum ((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar))
      (.const 0) (bs.count true : F) 0
    have hval : (!decide ((bs.count true : F) = 0)) = bs.any id := by
      rw [Bool.eq_iff_iff, ← cast_count_true_ne_zero_iff hchar]
      simp
    rw [hval] at hn
    simp only [Snarky.any]
    vcgen [hn]
    all_goals prover_assert with simp_all [Reads.fvar_apply, CVar.val]
  | [], _ :: _, _ | [_], [], _ | [_], _ :: _ :: _, _ | [_, _], [], _ | [_, _], [_], _
  | [_, _], _ :: _ :: _ :: _, _ =>
    simp only [All₂, inf_bot_eq]
    rw [triple_iff]
    intro _ h
    simp at h

/-- `all`'s completeness: below the characteristic, the result reads whether every operand's
bit is `true`. -/
theorem Prover.all_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F)) (bs : List Bool)
    (hchar : ∀ j k : Nat, j ≤ bs.length → k ≤ bs.length → (j : F) = k → j = k) :
    ⦃All₂ Reads xs bs⦄ Snarky.all (c := Prover c) xs
    ⦃fun r ↦ Reads r (bs.all id)⦄ := by
  match xs, bs, hchar with
  | [], [], _ =>
    simp only [Snarky.all]
    vcgen
    all_goals prover_assert with (intros; simp_all [Reads.boolVar_apply, bit])
  | [a], [b], _ =>
    simp only [Snarky.all]
    vcgen
    all_goals prover_assert with (intros; simp_all [All₂])
  | [a₁, a₂], [b₁, b₂], _ =>
    have ha := Prover.and_spec (c := c) a₁ a₂ b₁ b₂
    simp only [Snarky.all]
    vcgen [ha]
    all_goals prover_assert with simp_all [All₂]
  | x₁ :: x₂ :: x₃ :: t, bs, hchar =>
    have hsum := all₂_reads_le_reads_sum (x₁ :: x₂ :: x₃ :: t) bs
    have hlen : All₂ (Reads (F := F)) (x₁ :: x₂ :: x₃ :: t) bs ≤
        Reads (CVar.const ((x₁ :: x₂ :: x₃ :: t).length : F)) (bs.length : F) := by
      rw [Pred.le_iff]
      intro s h
      rw [Reads.fvar_apply]
      have hl := congrArg List.length (scoped_read_of_all₂_reads h).2
      simp only [List.length_map] at hl
      exact ⟨trivial, by simp [CVar.val, hl]⟩
    have he := Prover.equals_spec (c := c) (.const ((x₁ :: x₂ :: x₃ :: t).length : F))
      (sum ((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar)) (bs.length : F) (bs.count true : F)
    have hval : decide ((bs.length : F) = (bs.count true : F)) = bs.all id := by
      rw [Bool.eq_iff_iff, ← cast_length_eq_count_true_iff hchar]
      simp
    rw [hval] at he
    simp only [Snarky.all]
    vcgen [he]
    all_goals prover_assert with simp_all
  | [], _ :: _, _ | [_], [], _ | [_], _ :: _ :: _, _ | [_, _], [], _ | [_, _], [_], _
  | [_, _], _ :: _ :: _ :: _, _ =>
    simp only [All₂, inf_bot_eq]
    rw [triple_iff]
    intro _ h
    simp at h

end ProverReading

end Snarky
