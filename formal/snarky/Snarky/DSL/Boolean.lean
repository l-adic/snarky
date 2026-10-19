import Mathlib.Algebra.Field.Basic
import Snarky.DSL.Field
import Snarky.Traverse

namespace Snarky

set_option mvcgen.warning false

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

/-- `not`'s expression is scoped when the operand's is. -/
theorem not_scoped [Add F] [Sub F] [Zero F] [One F] [Neg F] [DecidableEq F]
    {st : ProverState F} {b : BoolVar F} (hb : (↑b : CVar F).Scoped st) :
    (↑(Snarky.not b) : CVar F).Scoped st :=
  CVar.Scoped.sub_ trivial hb

/-- A boolean bundle's reading, at its cell: the bit it spells. A law over `FVar`
consumes a boolean operand through this. -/
private theorem asField [Field F] [DecidableEq F] {st : ProverState F} {v : BoolVar F}
    {vb : Bool} (h : CircuitType.ReadsAs (val := Bool) st v vb) :
    CircuitType.ReadsAs (val := F) st (↑v : CVar F) (bit vb) :=
  ⟨CircuitType.scoped_fvar.mpr (CircuitType.scoped_boolVar.mp h.1),
    CircuitType.reads_fvar.mpr (CircuitType.reads_boolVar.mp h.2)⟩

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

open Std.Do in
/-- `selectField b t e` reads as the branch the selector's bit picks. -/
@[spec] theorem selectField_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F) (t e : FVar F) :
    ⦃⌜True⌝⦄
    selectField (c := Builder V c) b t e
    ⦃⇓ r _ => ⌜∀ bb : Bool, (↑b : CVar F).val V = bit bb →
        r.val V = if bb then t.val V else e.val V⌝⦄ := by
  simp only [selectField, selectField.core]
  mvcgen
  · subst_vars
    rename_i hbc _
    intro bb hbb
    rw [hbc] at hbb
    simp only [CVar.val] at hbb
    subst hbb
    cases bb <;> simp [bit, zero_ne_one]
  · subst_vars
    intro bb hbb
    simp only [CVar.val_add_, CVar.val_scale_, CVar.val_sub_, CVar.val, hbb]
    cases bb <;> simp [bit]
  · subst_vars
    rename_i hrow
    intro bb hbb
    have h := (LawfulBasicSystem.holds_r1cs V _ _ _).mp hrow
    simp only [CVar.val_sub_] at h
    rw [hbb] at h
    cases bb <;> simp only [bit] at h
    · rw [if_neg Bool.false_ne_true, zero_mul] at h
      simp [sub_eq_zero.mp h.symm]
    · rw [if_pos trivial, one_mul] at h
      simp [sub_left_inj.mp h]

/-- The witnessing branch's completeness law, in its own binders: advise the selected
branch, then pin it by the row. The three operand readings are framed across the
allocation — the row needs them, the witness rule does not carry them. -/
private theorem selectField.core_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (b : CVar F) (t e : FVar F)
    (bb : Bool) (tv ev : F) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := F) st b (bit bb) ∧
        CircuitType.ReadsAs (val := F) st t tv ∧ CircuitType.ReadsAs (val := F) st e ev)
      (selectField.core (c := c) b t e)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a (if bb then tv else ev)) := by
  have hrd : ∀ {st : ProverState F} {v : FVar F} {a : F},
      CircuitType.ReadsAs (val := F) st v a → v.val st.env.get = a :=
    fun h => CircuitType.reads_fvar.mp h.2
  simp only [selectField.core]
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?_, h⟩) (fun _ _ h => h)
      (Complete.frame (monotone_and CircuitType.monotone_readsAs (monotone_and
        CircuitType.monotone_readsAs CircuitType.monotone_readsAs))
        (Complete.witness (selectField.advice b t e) (if bb then tv else ev) (by simp))))
    (fun r => Complete.bind (Complete.addConstraint ?_)
      fun _ => Complete.pure_of fun _ h => h.1)
  · rintro st ⟨hr, hb, ht, he⟩ stf hle
    refine (LawfulBasicSystem.holds_r1cs ..).mpr ?_
    simp only [CVar.val_sub_]
    rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp hb.1),
      CVar.val_of_le hle (CircuitType.scoped_fvar.mp ht.1),
      CVar.val_of_le hle (CircuitType.scoped_fvar.mp he.1),
      CVar.val_of_le hle (CircuitType.scoped_fvar.mp hr.1),
      hrd hb, hrd ht, hrd he, hrd hr]
    cases bb <;> simp [bit]
  · cases bb <;>
      simp [selectField.advice, AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1.1),
        AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.1.1),
        AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.1),
        hrd h.1, hrd h.2.1, hrd h.2.2, bit, zero_ne_one]

/-- `selectField`'s completeness law: from a state with scoped operands and a well-formed
selector the run succeeds, the row it built is satisfied at every extension of the
final table, and the result is scoped. -/
theorem selectField_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F) (t e : FVar F)
    (bb : Bool) (tv ev : F) :
    Complete (fun st => CircuitType.ReadsAs (val := Bool) st b bb ∧
      CircuitType.ReadsAs (val := F) st t tv ∧
        CircuitType.ReadsAs (val := F) st e ev)
      (selectField (c := c) b t e)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a (if bb then tv else ev)) := by
  have hrd : ∀ {st : ProverState F} {v : FVar F} {a : F},
      CircuitType.ReadsAs (val := F) st v a → v.val st.env.get = a :=
    fun h => CircuitType.reads_fvar.mp h.2
  -- the witnessing branch, in its own binders
  have hcore : Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := Bool) st b bb ∧
        CircuitType.ReadsAs (val := F) st t tv ∧ CircuitType.ReadsAs (val := F) st e ev)
      (selectField.core (c := c) (↑b : CVar F) t e)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a (if bb then tv else ev)) :=
    Complete.imp (fun _ h => ⟨asField h.1, h.2⟩) (fun _ _ h => h)
      (selectField.core_complete (↑b : CVar F) t e bb tv ev)
  simp only [selectField]
  split
  · -- the selector is a constant: the branch is decided out of circuit
    rename_i _ _ _ bv hbv
    refine Complete.pure_of fun st h => ?_
    have hv : bv = bit bb := by
      rw [← CircuitType.reads_fvar.mp (asField (st := st) h.1).2, hbv]
      rfl
    subst hv
    cases bb
    · simpa [bit] using h.2.2
    · simpa [bit] using h.2.1
  · -- both branches constant: the select is an affine combination
    refine Complete.pure_of fun st h => ⟨CircuitType.scoped_fvar.mpr ?_,
      CircuitType.reads_fvar.mpr ?_⟩
    · have hbsc : (↑b : CVar F).Scoped st := CircuitType.scoped_boolVar.mp h.1.1
      exact CVar.Scoped.add_ hbsc (CVar.ScopedBy.scale_ (CVar.Scoped.sub_ trivial hbsc))
    · have h1 := hrd h.2.1
      have h2 := hrd h.2.2
      have hbv := CircuitType.reads_fvar.mp (asField (st := st) h.1).2
      simp only [CVar.val_add_, CVar.val_scale_, CVar.val_sub_, CVar.val] at h1 h2 ⊢
      rw [hbv, h1, h2]
      cases bb <;> simp [bit]
  · exact hcore

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

open Std.Do in
/-- Selection's contract at a bundle, at the backend's reading of its constraints: the result
reads as the operand the selector's bit picks. -/
class LawfulIfThenElse (F c val var : Type) [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [CircuitType F val var] [IfThenElse F c var] where
  /-- The result reads as the operand the selector's bit picks. -/
  select_sound : ∀ (V : Valuation F) (b : BoolVar F) (t e : var) (tv ev : val) (bb : Bool),
    CircuitType.Reads V t tv → CircuitType.Reads V e ev → (↑b : CVar F).val V = bit bb →
    ⦃⌜True⌝⦄
    atBuilder V (select (c := c) b t e)
    ⦃⇓ r _ => ⌜CircuitType.Reads V r (if bb then tv else ev)⌝⦄

section Lawful

open Std.Do

variable [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]

instance instLawfulIfThenElseFVar : LawfulIfThenElse F c F (FVar F) where
  select_sound V b t e tv ev bb ht he hb := by
    intro nv _ hsat
    show CircuitType.Reads V _ _
    rw [CircuitType.reads_fvar, ← CircuitType.reads_fvar.mp ht, ← CircuitType.reads_fvar.mp he]
    exact selectField_spec (c := c) (V := V) b t e nv trivial hsat bb hb

instance instLawfulIfThenElseBoolVar : LawfulIfThenElse F c Bool (BoolVar F) where
  select_sound V b t e tv ev bb ht he hb := by
    have h := selectField_spec (c := c) (V := V) b ↑t ↑e
    show ⦃⌜True⌝⦄ (selectField (c := Builder V c) b ↑t ↑e >>= fun r =>
      pure (BoolVar.unchecked r)) ⦃_⦄
    mvcgen [h]
    rename_i r _ hr
    rw [CircuitType.reads_boolVar, BoolVar.coe_unchecked, hr bb hb,
      CircuitType.reads_boolVar.mp ht, CircuitType.reads_boolVar.mp he]
    cases bb <;> simp

instance instLawfulIfThenElseUnit : LawfulIfThenElse F c Unit Unit where
  select_sound V b t e tv ev bb _ _ _ := by
    intro _ _ _
    exact CircuitType.reads_unit

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

open Std.Do in
/-- `and`: on bit operands the result reads as the conjunction bit. -/
@[spec] theorem and_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃⌜True⌝⦄
    Snarky.and (c := Builder V c) a b
    ⦃⇓ r _ => ⌜∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab && bb)⌝⦄ := by
  simp only [Snarky.and]
  mvcgen
  rename_i r _ hr
  intro ab bb ha hb
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

open Std.Do in
/-- `or`: on bit operands the result reads as the disjunction bit. -/
@[spec] theorem or_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃⌜True⌝⦄
    Snarky.or (c := Builder V c) a b
    ⦃⇓ r _ => ⌜∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab || bb)⌝⦄ := by
  simp only [Snarky.or]
  mvcgen
  rename_i r _ hr
  intro ab bb ha hb
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

open Std.Do in
/-- The witnessing branch reads as the xor bit on bit operands. -/
@[spec] private theorem xor.core_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃⌜True⌝⦄
    Snarky.xor.core (c := Builder V c) a b
    ⦃⇓ r _ => ⌜∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab ^^ bb)⌝⦄ := by
  simp only [Snarky.xor.core]
  mvcgen
  rename_i r _ hrow
  intro ab bb ha hb
  have h := (LawfulBasicSystem.holds_r1cs V _ _ _).mp hrow
  simp only [CVar.val_add_, CVar.val_sub_, BoolVar.coe_unchecked] at h ⊢
  rw [ha, hb] at h
  exact xor_pin h

open Std.Do in
/-- `xor`: on bit operands the result reads as the xor bit. -/
@[spec] theorem xor_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃⌜True⌝⦄
    Snarky.xor (c := Builder V c) a b
    ⦃⇓ r _ => ⌜∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab ^^ bb)⌝⦄ := by
  simp only [Snarky.xor]
  mvcgen
  all_goals first
    | (intro ab bb ha hb
       have hA : a.toCVar = CVar.const _ := ‹_›
       have hB : b.toCVar = CVar.const _ := ‹_›
       rw [hA] at ha
       rw [hB] at hb
       simp only [CVar.val] at ha hb
       subst ha
       subst hb
       cases ab <;> cases bb <;> simp [bit])
    | (intro ab bb ha hb
       have hA : a.toCVar = CVar.const _ := ‹_›
       have h0 : _ = (0 : F) := ‹_›
       rw [hA] at ha
       simp only [CVar.val] at ha
       rw [h0] at ha
       cases ab
       · simpa using hb
       · exact absurd ha (by simp [bit]))
    | (intro ab bb ha hb
       have hA : a.toCVar = CVar.const _ := ‹_›
       have h1 : _ = (1 : F) := ‹_›
       rw [hA] at ha
       simp only [CVar.val] at ha
       rw [h1] at ha
       cases ab
       · exact absurd ha (by simp [bit])
       · rw [not_val hb]
         simp)
    | (intro ab bb ha hb
       have hB : b.toCVar = CVar.const _ := ‹_›
       have h0 : _ = (0 : F) := ‹_›
       rw [hB] at hb
       simp only [CVar.val] at hb
       rw [h0] at hb
       cases bb
       · simpa using ha
       · exact absurd hb (by simp [bit]))
    | (intro ab bb ha hb
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

open Std.Do in
/-- `any`: on bit operands, below the characteristic, the result reads `1` exactly when
some operand reads `1`. -/
@[spec] theorem any_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F))
    (hchar : ∀ k : Nat, k ≤ xs.length → (k : F) = 0 → k = 0) :
    ⦃⌜True⌝⦄
    Snarky.any (c := Builder V c) xs
    ⦃⇓ r _ => ⌜(∀ b ∈ xs, (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
        (↑r : CVar F).val V = if ∃ b ∈ xs, (↑b : CVar F).val V = 1 then 1 else 0⌝⦄ := by
  match xs, hchar with
  | [], _ =>
    simp only [Snarky.any]
    intro nv _ _ _
    simp [build]
  | [a], _ =>
    simp only [Snarky.any]
    intro nv _ _ hbits
    rcases hbits a (by simp) with h | h <;> simp [build, h]
  | [a, b], _ =>
    simp only [Snarky.any]
    mvcgen
    intro hr hbits
    rcases hbits a (by simp) with ha | ha <;> rcases hbits b (by simp) with hb | hb <;>
      first
      | (rw [hr false false ha hb]; simp [ha, hb, bit])
      | (rw [hr false true ha hb]; simp [ha, hb, bit])
      | (rw [hr true false ha hb]; simp [ha, hb, bit])
      | (rw [hr true true ha hb]; simp [ha, hb, bit])
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [Snarky.any]
    mvcgen
    intro hr hbits
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
      rw [if_pos h, if_neg fun hc => absurd (hchar _ hle hc) (by omega)]
    · rw [if_neg h, if_pos (by rw [List.count_eq_zero.mpr (hmem.not.mpr h)]; simp)]

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

open Std.Do in
/-- `all`: on bit operands, below the characteristic, the result reads `1` exactly when
every operand reads `1`. -/
@[spec] theorem all_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ xs.length → k ≤ xs.length → (j : F) = k → j = k) :
    ⦃⌜True⌝⦄
    Snarky.all (c := Builder V c) xs
    ⦃⇓ r _ => ⌜(∀ b ∈ xs, (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
        (↑r : CVar F).val V = if ∀ b ∈ xs, (↑b : CVar F).val V = 1 then 1 else 0⌝⦄ := by
  match xs, hchar with
  | [], _ =>
    simp only [Snarky.all]
    intro nv _ _ _
    simp [build]
  | [a], _ =>
    simp only [Snarky.all]
    intro nv _ _ hbits
    rcases hbits a (by simp) with h | h <;> simp [build, h]
  | [a, b], _ =>
    simp only [Snarky.all]
    mvcgen
    intro hr hbits
    rcases hbits a (by simp) with ha | ha <;> rcases hbits b (by simp) with hb | hb <;>
      first
      | (rw [hr false false ha hb]; simp [ha, hb, bit])
      | (rw [hr false true ha hb]; simp [ha, hb, bit])
      | (rw [hr true false ha hb]; simp [ha, hb, bit])
      | (rw [hr true true ha hb]; simp [ha, hb, bit])
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [Snarky.all]
    mvcgen
    intro hr hbits
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
    · rw [if_pos h, if_pos (by rw [hall.mpr h, hlenL])]
    · rw [if_neg h, if_neg fun hc => h (hall.mp (by
        have := hchar _ _ (Nat.le_refl _) hle hc
        omega))]

attribute [irreducible] Snarky.all

/-! ## The state-relative completeness laws

Each gadget's law at the prover's reading (`Snarky.Prover.WP`), and its registered reading for
`mvcgen`. A bit operand is a scoped cell reading `0` or `1`; a bit result reads its answer as
the field's `1` or `0`. -/

section ProverReading

open Std.Do

/-- `selectField.advice` returns the branch the selector's reading picks. -/
@[spec] private def Prover.selectField_advice_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (b : CVar F) (t e : FVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (selectField.advice b t e)
    (fun st => b.Scoped st ∧ t.Scoped st ∧ e.Scoped st)
    (fun st => if st.read b = 1 then st.read t else st.read e)
    (fun _ h => by
      simp only [ProverState.read]
      split <;> simp [selectField.advice, AsProver.readCVar_run h.1, AsProver.readCVar_run h.2.1,
        AsProver.readCVar_run h.2.2, *])
    fun _ _ => by simp)

/-- `selectField`'s completeness: where the operands are in scope and the selector reads a
bit, the result reads the branch it picks. -/
theorem Prover.selectField_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F) (t e : FVar F)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (↑b : CVar F).Scoped st₀ ∧ t.Scoped st₀ ∧ e.Scoped st₀ ∧
      (st₀.read b = 0 ∨ st₀.read b = 1)⌝⦄
    selectField (c := Prover c) b t e
    ⦃⇓ r s' => ⌜r.Scoped s' ∧
      s'.read r = (if st₀.read b = 1 then st₀.read t else st₀.read e) ∧ st₀ ≤ s'⌝⦄ := by
  unfold selectField selectField.core
  mvcgen
  all_goals grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_fvar,
    CircuitType.reads_fvar, ProverState.read_of_le, CVar.Scoped.of_le,
    LawfulBasicSystem.holds_r1cs, CVar.val_add_, CVar.val_scale_, CVar.val_sub_, CVar.val,
    CVar.Scoped.add_, CVar.Scoped.scale_, CVar.Scoped.sub_, CVar.Scoped, CVar.ScopedBy]

/-- Registered. -/
@[spec] def Prover.selectField_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F) (t e : FVar F) :=
  Prover.register (Prover.selectField_spec (c := c) b t e)

/-- `and`'s completeness: on bit operands the result reads `1` exactly where both read `1`. -/
theorem Prover.and_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (↑a : CVar F).Scoped st₀ ∧ (↑b : CVar F).Scoped st₀ ∧
      (st₀.read a = 0 ∨ st₀.read a = 1) ∧ (st₀.read b = 0 ∨ st₀.read b = 1)⌝⦄
    Snarky.and (c := Prover c) a b
    ⦃⇓ r s' => ⌜(↑r : CVar F).Scoped s' ∧
      s'.read r = (if st₀.read a = 1 ∧ st₀.read b = 1 then 1 else 0) ∧ st₀ ≤ s'⌝⦄ := by
  simp only [Snarky.and]
  mvcgen
  all_goals grind [Prover.Reg.iff, BoolVar.coe_unchecked]

/-- Registered. -/
@[spec] private def Prover.and_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :=
  Prover.register (Prover.and_spec (c := c) a b)

/-- `or`'s completeness: on bit operands the result reads `1` exactly where either reads
`1`. -/
theorem Prover.or_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (↑a : CVar F).Scoped st₀ ∧ (↑b : CVar F).Scoped st₀ ∧
      (st₀.read a = 0 ∨ st₀.read a = 1) ∧ (st₀.read b = 0 ∨ st₀.read b = 1)⌝⦄
    Snarky.or (c := Prover c) a b
    ⦃⇓ r s' => ⌜(↑r : CVar F).Scoped s' ∧
      s'.read r = (if st₀.read a = 1 ∨ st₀.read b = 1 then 1 else 0) ∧ st₀ ≤ s'⌝⦄ := by
  simp only [Snarky.or]
  mvcgen
  all_goals grind [Prover.Reg.iff, Snarky.not, BoolVar.coe_unchecked, CVar.val_sub_,
    CVar.val, CVar.Scoped.sub_, CVar.scoped_const, ProverState.read_of_le, CVar.Scoped.of_le]

/-- Registered. -/
@[spec] private def Prover.or_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :=
  Prover.register (Prover.or_spec (c := c) a b)

/-- `xor.advice` returns the inequality bit. -/
@[spec] private def Prover.xor_advice_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (a b : BoolVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (Snarky.xor.advice a b)
    (fun st => (↑a : CVar F).Scoped st ∧ (↑b : CVar F).Scoped st)
    (fun st => if st.read a = st.read b then 0 else 1)
    (fun _ h => by
      simp [Snarky.xor.advice, AsProver.readCVar_run h.1, AsProver.readCVar_run h.2])
    fun _ _ => by simp)

/-- `xor`'s completeness: on bit operands the result reads `1` exactly where they read
unequal. -/
theorem Prover.xor_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (↑a : CVar F).Scoped st₀ ∧ (↑b : CVar F).Scoped st₀ ∧
      (st₀.read a = 0 ∨ st₀.read a = 1) ∧ (st₀.read b = 0 ∨ st₀.read b = 1)⌝⦄
    Snarky.xor (c := Prover c) a b
    ⦃⇓ r s' => ⌜(↑r : CVar F).Scoped s' ∧
      s'.read r = (if st₀.read a ≠ st₀.read b then 1 else 0) ∧ st₀ ≤ s'⌝⦄ := by
  unfold Snarky.xor Snarky.xor.core
  mvcgen
  all_goals grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_fvar,
    CircuitType.reads_fvar, ProverState.read_of_le, CVar.Scoped.of_le,
    LawfulBasicSystem.holds_r1cs, Snarky.not, BoolVar.coe_unchecked, CVar.val_add_,
    CVar.val_sub_, CVar.val, CVar.Scoped.add_, CVar.Scoped.sub_, CVar.scoped_const]

/-- Registered. -/
@[spec] def Prover.xor_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :=
  Prover.register (Prover.xor_spec (c := c) a b)

/-! Bit sums at the prover's reading: the arithmetic of the sum-based gadgets here and of the
assertions over bit sums. -/

/-- Bit operands' sum is in scope where they are. -/
theorem scoped_sum_of_bits [Field F] [DecidableEq F] {st : ProverState F}
    {xs : List (BoolVar F)} (h : ∀ x ∈ xs, (↑x : CVar F).Scoped st) :
    (sum (xs.map BoolVar.toCVar)).Scoped st :=
  CVar.Scoped.sum fun _ hx => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact h b hb

/-- Bit operands' sum reads their count of ones. -/
theorem read_sum_of_bits [Field F] [DecidableEq F] {st : ProverState F} {xs : List (BoolVar F)}
    (hbits : ∀ x ∈ xs, st.read x = 0 ∨ st.read x = 1) :
    st.read (sum (xs.map BoolVar.toCVar)) =
      ((xs.map fun x : BoolVar F => st.read x).count 1 : F) := by
  rw [ProverState.read, sum_eval, List.map_map]
  exact sum_of_bits _ (by simpa using hbits)

/-- Below the characteristic, bit operands' sum reads nonzero exactly where one of them
reads `1`. -/
theorem read_sum_ne_zero_iff [Field F] [DecidableEq F] {st : ProverState F}
    {xs : List (BoolVar F)} (hbits : ∀ x ∈ xs, st.read x = 0 ∨ st.read x = 1)
    (hchar : ∀ k : Nat, k ≤ xs.length → (k : F) = 0 → k = 0) :
    st.read (sum (xs.map BoolVar.toCVar)) ≠ 0 ↔ ∃ x ∈ xs, st.read x = 1 := by
  have hle : (xs.map fun x : BoolVar F => st.read x).count 1 ≤ xs.length := by
    simpa using List.count_le_length (a := (1 : F)) (l := xs.map fun x : BoolVar F => st.read x)
  rw [read_sum_of_bits hbits]
  constructor
  · intro h
    obtain ⟨x, hx, hx1⟩ := List.mem_map.mp (List.count_pos_iff.mp
      (Nat.pos_of_ne_zero fun h0 => h (by rw [h0]; simp)))
    exact ⟨x, hx, hx1⟩
  · rintro ⟨x, hx, hx1⟩ hc
    exact absurd (hchar _ hle hc)
      (Nat.pos_iff_ne_zero.mp (List.count_pos_iff.mpr (List.mem_map.mpr ⟨x, hx, hx1⟩)))

/-- Below the characteristic, bit operands' sum reads their number exactly where every one
of them reads `1`. -/
private theorem read_sum_eq_length_iff [Field F] [DecidableEq F] {st : ProverState F}
    {xs : List (BoolVar F)} (hbits : ∀ x ∈ xs, st.read x = 0 ∨ st.read x = 1)
    (hchar : ∀ j k : Nat, j ≤ xs.length → k ≤ xs.length → (j : F) = k → j = k) :
    st.read (sum (xs.map BoolVar.toCVar)) = xs.length ↔ ∀ x ∈ xs, st.read x = 1 := by
  have hle : (xs.map fun x : BoolVar F => st.read x).count 1 ≤ xs.length := by
    simpa using List.count_le_length (a := (1 : F)) (l := xs.map fun x : BoolVar F => st.read x)
  rw [read_sum_of_bits hbits]
  constructor
  · intro h x hx
    have hcount := hchar _ _ hle le_rfl h
    exact (List.count_eq_length.mp (by simpa using hcount) _ (List.mem_map.mpr ⟨x, hx, rfl⟩)).symm
  · intro h
    rw [List.count_eq_length.mpr fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact (h x hx).symm]
    simp

/-- `any`'s completeness: on bit operands, below the characteristic, the result reads `1`
exactly where some operand reads `1`. -/
theorem Prover.any_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F))
    (hchar : ∀ k : Nat, k ≤ xs.length → (k : F) = 0 → k = 0) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (∀ x ∈ xs, (↑x : CVar F).Scoped st₀) ∧
      (∀ x ∈ xs, st₀.read x = 0 ∨ st₀.read x = 1)⌝⦄
    Snarky.any (c := Prover c) xs
    ⦃⇓ r s' => ⌜(↑r : CVar F).Scoped s' ∧
      s'.read r = (if ∃ x ∈ xs, st₀.read x = 1 then 1 else 0) ∧ st₀ ≤ s'⌝⦄ := by
  unfold Snarky.any
  mvcgen
  -- one or two operands: `grind` cannot supply the bounded existential's witness
  case vc2.h_2 =>
    rename_i a hxs s h
    subst hxs
    obtain ⟨rfl, hsc, hbits⟩ := h
    refine ⟨hsc a (List.mem_singleton_self a), ?_, le_rfl⟩
    rcases hbits a (List.mem_singleton_self a) with h0 | h1 <;> simp [*]
  case vc4.h_3.post.success =>
    rename_i a b hxs s₀ h₀ r s₁
    subst hxs
    obtain ⟨rfl, -, -⟩ := h₀
    intro h
    obtain ⟨hr, hv, hle⟩ := Prover.Reg.iff.mp h
    exact ⟨hr, by simp [hv], hle⟩
  -- three or more operands: the bit-sum is in scope, and reads nonzero exactly where some
  -- operand reads `1`
  case vc5.h_4.pre =>
    rename_i l _ _ _ hxs s h
    subst hxs
    obtain ⟨rfl, hsc, -⟩ := h
    exact ⟨trivial, scoped_sum_of_bits hsc, trivial⟩
  case vc6.h_4.post.success =>
    rename_i l _ _ _ hxs s₀ h₀ r s₁
    subst hxs
    obtain ⟨rfl, -, hbits⟩ := h₀
    have key := read_sum_ne_zero_iff hbits hchar
    grind [Prover.Reg.iff, CVar.val]
  all_goals grind [Prover.Reg.iff, false_val, false_scoped]

/-- Registered. -/
@[spec] def Prover.any_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F))
    (hchar : ∀ k : Nat, k ≤ xs.length → (k : F) = 0 → k = 0) :=
  Prover.register (Prover.any_spec (c := c) xs hchar)

/-- `all`'s completeness: on bit operands, below the characteristic, the result reads `1`
exactly where every operand reads `1`. -/
theorem Prover.all_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ xs.length → k ≤ xs.length → (j : F) = k → j = k)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (∀ x ∈ xs, (↑x : CVar F).Scoped st₀) ∧
      (∀ x ∈ xs, st₀.read x = 0 ∨ st₀.read x = 1)⌝⦄
    Snarky.all (c := Prover c) xs
    ⦃⇓ r s' => ⌜(↑r : CVar F).Scoped s' ∧
      s'.read r = (if ∀ x ∈ xs, st₀.read x = 1 then 1 else 0) ∧ st₀ ≤ s'⌝⦄ := by
  unfold Snarky.all
  mvcgen
  -- three or more operands: the bit-sum is in scope, and reads the length exactly where every
  -- operand reads `1`
  case vc5.h_4.pre =>
    rename_i l _ _ _ hxs s h
    subst hxs
    obtain ⟨rfl, hsc, -⟩ := h
    exact ⟨trivial, trivial, scoped_sum_of_bits hsc⟩
  case vc6.h_4.post.success =>
    rename_i l _ _ _ hxs s₀ h₀ r s₁
    subst hxs
    obtain ⟨rfl, -, hbits⟩ := h₀
    have key := read_sum_eq_length_iff hbits hchar
    grind [Prover.Reg.iff, CVar.val]
  all_goals grind [Prover.Reg.iff, true_val, true_scoped]

/-- Registered. -/
@[spec] def Prover.all_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ xs.length → k ≤ xs.length → (j : F) = k → j = k) :=
  Prover.register (Prover.all_spec (c := c) xs hchar)

end ProverReading

end Snarky
