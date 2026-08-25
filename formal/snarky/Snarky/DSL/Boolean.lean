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

attribute [irreducible] Snarky.not

/-! ## Selection -/

/-- Conditionally select between two field variables: where `b` reads `1` the result
reads as `t`, where it reads `0` as `e` — `r = b·(t − e) + e`, one row. A constant
selector folds to the chosen branch; constant branches fold to the affine form with no
constraint. -/
def selectField [Field F] [DecidableEq F] [BasicSystem F c] (b : BoolVar F) (t e : FVar F) :
    CircuitM F c (FVar F) :=
  match (↑b : CVar F), t, e with
  | .const bv, t, e => pure (if bv = 1 then t else e)
  | b, .const tv, .const ev =>
    pure (CVar.add_ (.scale tv b) (CVar.scale_ ev (CVar.sub_ (.const 1) b)))
  | b, t, e => do
    let r ← witness (val := F) (advice b t e)
    addConstraint (BasicSystem.r1cs b (CVar.sub_ t e) (CVar.sub_ r e))
    pure r
where
  /-- The advice: read the selector, return the branch it picks. -/
  advice (b : CVar F) (t e : FVar F) : AsProver F F := do
    let bv ← AsProver.readCVar b
    if bv = 1 then AsProver.readCVar t else AsProver.readCVar e

open Std.Do in
/-- `selectField b t e` reads as the branch the selector's bit picks. -/
@[spec] theorem selectField_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F) (t e : FVar F) :
    ⦃⌜True⌝⦄
    selectField (c := Builder V c) b t e
    ⦃⇓ r _ => ⌜∀ bb : Bool, (↑b : CVar F).val V = bit bb →
        r.val V = if bb then t.val V else e.val V⌝⦄ := by
  simp only [selectField]
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

/-- `selectField`'s completeness law: from a state with scoped operands and a well-formed
selector the run succeeds, the row it built is satisfied at every extension of the
final table, and the result is scoped. -/
theorem selectField_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F) (t e : FVar F)
    (bb : Bool) (tv ev : F) :
    Complete (fun st => CircuitType.ReadsAs (val := Bool) st b bb ∧ CircuitType.ReadsAs (val := F) st t tv ∧
        CircuitType.ReadsAs (val := F) st e ev)
      (selectField (c := c) b t e)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a (if bb then tv else ev)) := by
  rintro st ⟨hb, ht, he⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar,
    CircuitType.scoped_boolVar, CircuitType.reads_boolVar] at hb ht he ⊢
  obtain ⟨hb, hval⟩ := hb
  obtain ⟨ht, hvt⟩ := ht
  obtain ⟨he, hve⟩ := he
  subst hvt hve
  simp only [selectField]
  generalize (↑b : CVar F) = b' at hb hval ⊢
  split
  · refine ⟨_, st, rfl, by simp [Sat, build], by split <;> assumption, ?_⟩
    rename_i bv _ _
    simp only [CVar.val] at hval
    subst hval
    cases bb <;> simp [bit, zero_ne_one]
  · refine ⟨_, st, rfl, by simp [Sat, build],
      CVar.Scoped.add_ hb (CVar.Scoped.scale_ (CVar.Scoped.sub_ trivial hb)), ?_⟩
    cases bb <;> simp [CVar.val, bit, hval]
  · obtain ⟨r, st₁, hrun, hsat, hnv, hle, hscope, hreads⟩ :=
      witness_complete (c := c) (selectField.advice b' t e)
        (st := st) (v := if b'.val st.env.get = 1 then t.val st.env.get else e.val st.env.get)
        (by by_cases hb1 : b'.val st.env.get = 1 <;> simp [selectField.advice, hb, ht, he, hb1])
    refine ⟨r, st₁, hrun.bind rfl, ?_, CircuitType.scoped_fvar.mp hscope, ?_⟩
    on_goal 2 =>
      rw [CircuitType.reads_fvar.mp hreads, hval]
      cases bb <;> simp [bit, zero_ne_one]
    intro stf hnv' hle'
    refine Sat.bind hrun (hsat hnv' hle')
      (Sat.bind Runs.addConstraint (Sat.addConstraint ?_) Sat.pure)
    refine (LawfulBasicSystem.holds_r1cs ..).mpr ?_
    have hr : r.val stf.env.get
        = (if b'.val st.env.get = 1 then t.val st.env.get else e.val st.env.get) :=
      (CircuitType.reads_iff.mp (hreads.of_le hscope hle')).2
    simp only [CVar.val_sub_]
    rw [CVar.val_of_le (hle.trans hle') hb, CVar.val_of_le (hle.trans hle') ht,
      CVar.val_of_le (hle.trans hle') he, hr, hval]
    cases bb <;> simp [bit, zero_ne_one]

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
instance instIfThenElseFVar [Field F] [DecidableEq F] [BasicSystem F c] :
    IfThenElse F c (FVar F) :=
  ⟨selectField⟩

/-- Selection at a field variable IS the arithmetic mux — the instance's defining
equation, for a caller whose program says `select` and whose law says `selectField`. -/
@[simp] theorem select_fvar [Field F] [DecidableEq F] [BasicSystem F c] (b : BoolVar F)
    (t e : FVar F) : select (c := c) b t e = selectField b t e := rfl

/-- Boolean variables select through the field mux, retagged: the mux of two bits is a
bit. -/
instance instIfThenElseBoolVar [Field F] [DecidableEq F] [BasicSystem F c] :
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

/-- A bundle isomorphic to one that selects, selects through the isomorphism. -/
@[reducible] def IfThenElse.ofEquiv {va vb : Type} [S : IfThenElse F c va] (ew : vb ≃ va) :
    IfThenElse F c vb where
  select b t e := do
    let r ← S.select b (ew t) (ew e)
    pure (ew.symm r)

/-! ### Selection's laws

The laws are per shape, like the definition. A bundle carries them through
`LawfulIfThenElse`; the leaves and the formers instantiate it, and a shape reaches them
through its own isomorphism. -/

open Std.Do in
/-- Selection's contract at a bundle: the result reads as the operand the selector's bit
picks, and from scoped operands the run succeeds with a scoped bundle out. -/
class LawfulIfThenElse (F c val var : Type) [Field F] [DecidableEq F] [BasicSystem F c]
    [CircuitType F val var] [IfThenElse F c var] where
  /-- The result reads as the operand the selector's bit picks. -/
  select_sound : ∀ [ConstraintHolds F c] [LawfulBasicSystem F c] (V : Valuation F)
    (b : BoolVar F) (t e : var) (tv ev : val) (bb : Bool),
    CircuitType.Reads V t tv → CircuitType.Reads V e ev → (↑b : CVar F).val V = bit bb →
    ⦃⌜True⌝⦄
    atBuilder V (select (c := c) b t e)
    ⦃⇓ r _ => ⌜CircuitType.Reads V r (if bb then tv else ev)⌝⦄
  /-- From operands that read `tv` and `ev` and a selector that reads `bb`, the run
  succeeds, its rows hold at every extension of the final table, and the result reads the
  branch the selector picks. -/
  select_complete : ∀ [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F)
    (t e : var) (bb : Bool) (tv ev : val),
    Complete (fun st => CircuitType.ReadsAs (val := Bool) st b bb ∧
        CircuitType.ReadsAs (val := val) st t tv ∧ CircuitType.ReadsAs (val := val) st e ev)
      (select (c := c) b t e)
      (fun a st' => CircuitType.ReadsAs (val := val) st' a (if bb then tv else ev))

section Lawful

open Std.Do

variable [Field F] [DecidableEq F] [BasicSystem F c]

instance instLawfulIfThenElseFVar : LawfulIfThenElse F c F (FVar F) where
  select_sound V b t e tv ev bb ht he hb := by
    intro nv _ hsat
    show CircuitType.Reads V _ _
    rw [CircuitType.reads_fvar, ← CircuitType.reads_fvar.mp ht, ← CircuitType.reads_fvar.mp he]
    exact selectField_spec (c := c) (V := V) b t e nv trivial hsat bb hb
  select_complete b t e bb tv ev := selectField_complete (c := c) b t e bb tv ev

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
  select_complete b t e bb tv ev := by
    rintro st ⟨hb, ht, he⟩
    obtain ⟨r, st₁, hrun, hsat, hr⟩ :=
      selectField_complete (c := c) b ↑t ↑e bb (bit tv) (bit ev) st
        ⟨hb,
          ⟨CircuitType.scoped_fvar.mpr (CircuitType.scoped_boolVar.mp ht.1),
            CircuitType.reads_fvar.mpr (CircuitType.reads_boolVar.mp ht.2)⟩,
          ⟨CircuitType.scoped_fvar.mpr (CircuitType.scoped_boolVar.mp he.1),
            CircuitType.reads_fvar.mpr (CircuitType.reads_boolVar.mp he.2)⟩⟩
    refine ⟨.unchecked r, st₁, hrun.bind rfl, fun hnv hle =>
      Sat.bind hrun (hsat hnv hle) Sat.pure,
      CircuitType.scoped_boolVar.mpr (CircuitType.scoped_fvar.mp hr.1),
      CircuitType.reads_boolVar.mpr ?_⟩
    rw [BoolVar.coe_unchecked, CircuitType.reads_fvar.mp hr.2]
    cases bb <;> simp

instance instLawfulIfThenElseUnit : LawfulIfThenElse F c Unit Unit where
  select_sound V b t e tv ev bb _ _ _ := by
    intro _ _ _
    exact CircuitType.reads_unit
  select_complete _ _ _ _ _ _ := fun st _ =>
    ⟨(), st, rfl, fun _ _ => by simp [Sat, build],
      CircuitType.scoped_unit, CircuitType.reads_unit⟩

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
  select_complete s t e bb tv ev := by
    rintro st ⟨hb, ht, he⟩
    obtain ⟨tv₁, tv₂⟩ := tv
    obtain ⟨ev₁, ev₂⟩ := ev
    rw [CircuitType.ReadsAs, CircuitType.scoped_prod, CircuitType.reads_prod] at ht he
    obtain ⟨r₂, st₁, hrun₂, hsat₂, hr₂⟩ :=
      B.select_complete (c := c) s t.2 e.2 bb tv₂ ev₂ st
        ⟨hb, ⟨ht.1.2, ht.2.2⟩, ⟨he.1.2, he.2.2⟩⟩
    obtain ⟨r₁, st₂, hrun₁, hsat₁, hr₁⟩ :=
      A.select_complete (c := c) s t.1 e.1 bb tv₁ ev₁ st₁
        ⟨hb.mono hrun₂.nv_le hrun₂.le,
          CircuitType.ReadsAs.mono hrun₂.nv_le hrun₂.le ⟨ht.1.1, ht.2.1⟩,
          CircuitType.ReadsAs.mono hrun₂.nv_le hrun₂.le ⟨he.1.1, he.2.1⟩⟩
    refine ⟨(r₁, r₂), st₂, hrun₂.bind (hrun₁.bind rfl), fun hnv hle =>
      Sat.bind hrun₂ (hsat₂ (Nat.le_trans hrun₁.nv_le hnv) (hrun₁.le.trans hle))
        (Sat.bind hrun₁ (hsat₁ hnv hle) Sat.pure), ?_⟩
    have hr₂' := CircuitType.ReadsAs.mono hrun₁.nv_le hrun₁.le hr₂
    refine ⟨CircuitType.scoped_prod.mpr ⟨hr₁.1, hr₂'.1⟩,
      CircuitType.reads_prod.mpr ?_⟩
    cases bb <;> exact ⟨hr₁.2, hr₂'.2⟩

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
  select_complete s t e bb tv ev := by
    rintro st ⟨hb, ht, he⟩
    obtain ⟨rs, st₁, hrun, hsat, hrs⟩ :=
      zipWithVecM_complete (c := c) (IfThenElse.select s) t e
        (fun st => CircuitType.ReadsAs (val := Bool) st s bb ∧
          CircuitType.ReadsAs (val := Vector a n) st t tv ∧
          CircuitType.ReadsAs (val := Vector a n) st e ev)
        (fun i r st' => CircuitType.ReadsAs (val := a) st' r
          (if bb then tv[i.val] else ev[i.val]))
        (fun {_ _} hnv hle h => ⟨h.1.mono hnv hle,
          CircuitType.ReadsAs.mono hnv hle h.2.1, CircuitType.ReadsAs.mono hnv hle h.2.2⟩)
        (fun _ {_ _ _} hnv hle h => CircuitType.ReadsAs.mono hnv hle h)
        (fun i st' h => S.select_complete (c := c) s t[i.val] e[i.val] bb tv[i.val]
          ev[i.val] st'
          ⟨h.1,
            ⟨CircuitType.scoped_vector.mp h.2.1.1 i.val i.isLt,
              CircuitType.reads_vector.mp h.2.1.2 i.val i.isLt⟩,
            ⟨CircuitType.scoped_vector.mp h.2.2.1 i.val i.isLt,
              CircuitType.reads_vector.mp h.2.2.2 i.val i.isLt⟩⟩)
        st ⟨hb, ht, he⟩
    refine ⟨rs, st₁, hrun, hsat, CircuitType.scoped_vector.mpr fun i hi => (hrs ⟨i, hi⟩).1,
      CircuitType.reads_vector.mpr fun i hi => ?_⟩
    have h := (hrs ⟨i, hi⟩).2
    cases bb <;> exact h

/-- A bundle isomorphic to one whose selection is lawful, selects lawfully through the
isomorphism. -/
@[reducible] def LawfulIfThenElse.ofEquiv [CircuitType F a va] [IfThenElse F c va]
    [S : LawfulIfThenElse F c a va] (ev : b ≃ a) (ew : vb ≃ va) :
    @LawfulIfThenElse F c b vb _ _ _ (CircuitType.ofEquiv ev ew) (IfThenElse.ofEquiv ew) :=
  letI : CircuitType F b vb := CircuitType.ofEquiv ev ew
  letI : IfThenElse F c vb := IfThenElse.ofEquiv ew
  { select_sound := fun V s t e tv ev' bb ht he hb => by
      have h := (builder_spec_iff _ _).mp
        (S.select_sound (c := c) V s (ew t) (ew e) (ev tv) (ev ev') bb ht he hb)
      refine (builder_spec_iff _ _).mpr fun nv hsat => ?_
      replace hsat : ∀ con ∈ (build (IfThenElse.select (c := c) s (ew t) (ew e) >>= fun r =>
          (pure (ew.symm r) : CircuitM F c vb)) nv).constraints,
          ConstraintHolds.Holds V con := hsat
      show CircuitType.Reads V (ew (build (IfThenElse.select (c := c) s (ew t) (ew e) >>= fun r =>
        (pure (ew.symm r) : CircuitM F c vb)) nv).result) (ev (if bb then tv else ev'))
      simp only [build_bind, build, List.append_nil, Equiv.apply_symm_apply] at hsat ⊢
      cases bb <;> simpa using h nv hsat
    select_complete := fun s t e bb tv ev' => by
      intro st hst
      obtain ⟨r, st₁, hrun, hsat, hr⟩ :=
        S.select_complete (c := c) s (ew t) (ew e) bb (ev tv) (ev ev') st hst
      refine ⟨ew.symm r, st₁, hrun.bind rfl, fun hnv hle =>
        Sat.bind hrun (hsat hnv hle) Sat.pure, ?_⟩
      show CircuitType.Scoped (val := a) st₁ (ew (ew.symm r)) ∧
        CircuitType.Reads st₁.env.get (ew (ew.symm r)) (ev (if bb then tv else ev'))
      rw [Equiv.apply_symm_apply]
      refine ⟨hr.1, ?_⟩
      cases bb <;> exact hr.2 }

/-- A shape selects through its decomposition, laws and all. -/
@[reducible] def IfThenElse.ofShape {S T : Type → Type} {var : Type}
    [IfThenElse F c (T var)] (e : ∀ a, S a ≃ T a) : IfThenElse F c (S var) :=
  IfThenElse.ofEquiv (e var)

/-- A shape's selection laws, through its decomposition. -/
@[reducible] def LawfulIfThenElse.ofShape {S T : Type → Type} {val var : Type}
    [CircuitType F (T val) (T var)] [IfThenElse F c (T var)]
    [LawfulIfThenElse F c (T val) (T var)] (e : ∀ a, S a ≃ T a) :
    @LawfulIfThenElse F c (S val) (S var) _ _ _ (CircuitType.ofShape e) (IfThenElse.ofShape e) :=
  LawfulIfThenElse.ofEquiv (e val) (e var)

end Lawful

/-! ## Conjunction -/

/-- Conjoin boolean variables: the product, retagged — boolean because a product of bits
is a bit. `mul`'s rows. -/
def and [Field F] [DecidableEq F] [BasicSystem F c] (a b : BoolVar F) :
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

/-- `and`'s completeness law: `mul`'s run, its reading recovered from `mul_spec` for the
result's booleanity. -/
theorem and_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) (ab bb : Bool) :
    Complete (fun st => CircuitType.ReadsAs (val := Bool) st a ab ∧ CircuitType.ReadsAs (val := Bool) st b bb)
      (Snarky.and (c := c) a b)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r (ab && bb)) := by
  rintro st ⟨ha, hb⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar,
    CircuitType.scoped_boolVar, CircuitType.reads_boolVar] at ha hb ⊢
  obtain ⟨ha, hva⟩ := ha
  obtain ⟨hb, hvb⟩ := hb
  simp only [Snarky.and]
  obtain ⟨r, st₁, hrun, hsat, hr⟩ :=
    mul_complete (c := c) (↑a : CVar F) (↑b : CVar F) (bit ab) (bit bb) st
      ⟨⟨CircuitType.scoped_fvar.mpr ha, CircuitType.reads_fvar.mpr hva⟩,
        ⟨CircuitType.scoped_fvar.mpr hb, CircuitType.reads_fvar.mpr hvb⟩⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at hr
  refine ⟨.unchecked r, st₁, hrun.bind rfl, ?_, hr.1, ?_⟩
  · intro stf hnv hle
    exact Sat.bind hrun (hsat hnv hle) Sat.pure
  · rw [BoolVar.coe_unchecked, hr.2]
    cases ab <;> cases bb <;> simp [bit]

attribute [irreducible] Snarky.and

/-! ## Disjunction -/

/-- Disjoin boolean variables by De Morgan: `¬(¬a ∧ ¬b)` — one `and`, the negations pure
retags. -/
def or [Field F] [DecidableEq F] [BasicSystem F c] (a b : BoolVar F) :
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

/-- `or`'s completeness law: `and`'s, on the negated operands, the result negated. -/
theorem or_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) (ab bb : Bool) :
    Complete (fun st => CircuitType.ReadsAs (val := Bool) st a ab ∧ CircuitType.ReadsAs (val := Bool) st b bb)
      (Snarky.or (c := c) a b)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r (ab || bb)) := by
  rintro st ⟨ha, hb⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar,
    CircuitType.scoped_boolVar, CircuitType.reads_boolVar] at ha hb ⊢
  obtain ⟨ha, hva⟩ := ha
  obtain ⟨hb, hvb⟩ := hb
  simp only [Snarky.or]
  obtain ⟨r, st₁, hrun, hsat, hr⟩ :=
    and_complete (c := c) (Snarky.not a) (Snarky.not b) (!ab) (!bb) st
      ⟨⟨CircuitType.scoped_boolVar.mpr (not_scoped ha),
          CircuitType.reads_boolVar.mpr (not_val hva)⟩,
        ⟨CircuitType.scoped_boolVar.mpr (not_scoped hb),
          CircuitType.reads_boolVar.mpr (not_val hvb)⟩⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar,
    CircuitType.scoped_boolVar, CircuitType.reads_boolVar] at hr
  refine ⟨Snarky.not r, st₁, hrun.bind rfl, ?_, not_scoped hr.1, ?_⟩
  · intro stf hnv hle
    exact Sat.bind hrun (hsat hnv hle) Sat.pure
  · rw [not_val hr.2]
    cases ab <;> cases bb <;> simp [bit]

attribute [irreducible] Snarky.or

/-! ## Exclusive or -/

/-- Exclusive or: both constant folds; one constant selects the other operand (`0`) or
its negation (`1`), anything else falls through to the witnessing branch — the bit,
pinned by `2a · b = a + b − r`. -/
def xor [Field F] [DecidableEq F] [BasicSystem F c] (a b : BoolVar F) :
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

/-- The witnessing branch's completeness law. -/
private theorem xor.core_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    Complete (fun st => (↑a : CVar F).Scoped st ∧ (↑b : CVar F).Scoped st ∧
        CircuitType.WellFormed (val := Bool) st.env.get a ∧
        CircuitType.WellFormed (val := Bool) st.env.get b)
      (Snarky.xor.core (c := c) a b)
      (fun r st' => (↑r : CVar F).Scoped st' ∧
        CircuitType.WellFormed (val := Bool) st'.env.get r) := by
  rintro st ⟨ha, hb, ⟨ab, hab⟩, ⟨bb, hbb⟩⟩
  have hva := CircuitType.reads_boolVar.mp hab
  have hvb := CircuitType.reads_boolVar.mp hbb
  simp only [Snarky.xor.core]
  obtain ⟨r, st₁, hrun, hsat, hnv, hle, hscope, hreads⟩ :=
    witness_complete (c := c) (Snarky.xor.advice a b) (st := st) (v := bit (ab ^^ bb))
      (by cases ab <;> cases bb <;> simp [Snarky.xor.advice, ha, hb, hva, hvb, bit])
  have hr : r.val st₁.env.get = bit (ab ^^ bb) := (CircuitType.reads_iff.mp hreads).2
  refine ⟨.unchecked r, st₁, hrun.bind rfl, ?_, CircuitType.scoped_fvar.mp hscope, ab ^^ bb,
    CircuitType.reads_boolVar.mpr (by rw [BoolVar.coe_unchecked]; exact hr)⟩
  intro stf hnv' hle'
  refine Sat.bind hrun (hsat hnv' hle')
    (Sat.bind Runs.addConstraint (Sat.addConstraint ?_) Sat.pure)
  refine (LawfulBasicSystem.holds_r1cs ..).mpr ?_
  have hrf : r.val stf.env.get = bit (ab ^^ bb) :=
    (CircuitType.reads_iff.mp (hreads.of_le hscope hle')).2
  simp only [CVar.val_add_, CVar.val_sub_]
  rw [CVar.val_of_le (hle.trans hle') ha, CVar.val_of_le (hle.trans hle') hb, hrf, hva, hvb]
  cases ab <;> cases bb <;> simp [bit]

/-- `xor`'s completeness law: the folds are the operands' own contracts; the witnessing
branch is `xor.core`'s. -/
theorem xor_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    Complete (fun st => (↑a : CVar F).Scoped st ∧ (↑b : CVar F).Scoped st ∧
        CircuitType.WellFormed (val := Bool) st.env.get a ∧
        CircuitType.WellFormed (val := Bool) st.env.get b)
      (Snarky.xor (c := c) a b)
      (fun r st' => (↑r : CVar F).Scoped st' ∧
        CircuitType.WellFormed (val := Bool) st'.env.get r) := by
  rintro st ⟨ha, hb, ⟨ab, hab⟩, ⟨bb, hbb⟩⟩
  have hva := CircuitType.reads_boolVar.mp hab
  have hvb := CircuitType.reads_boolVar.mp hbb
  have hcore := Snarky.xor.core_complete (c := c) a b st ⟨ha, hb, ⟨ab, hab⟩, ⟨bb, hbb⟩⟩
  simp only [Snarky.xor]
  split
  · have hA : a.toCVar = CVar.const _ := ‹_›
    have hB : b.toCVar = CVar.const _ := ‹_›
    rw [hA] at hva
    rw [hB] at hvb
    simp only [CVar.val] at hva hvb
    subst hva
    subst hvb
    exact ⟨_, st, rfl, by simp [Sat, build], trivial, ab ^^ bb,
      CircuitType.reads_boolVar.mpr (by cases ab <;> cases bb <;> simp [bit])⟩
  · split
    · exact ⟨b, st, rfl, by simp [Sat, build], hb, bb, hbb⟩
    · split
      · exact ⟨Snarky.not b, st, rfl, by simp [Sat, build], not_scoped hb, !bb,
          CircuitType.reads_boolVar.mpr (not_val hvb)⟩
      · exact hcore
  · split
    · exact ⟨a, st, rfl, by simp [Sat, build], ha, ab, hab⟩
    · split
      · exact ⟨Snarky.not a, st, rfl, by simp [Sat, build], not_scoped ha, !ab,
          CircuitType.reads_boolVar.mpr (not_val hva)⟩
      · exact hcore
  · exact hcore

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
def any [Field F] [DecidableEq F] [BasicSystem F c] (xs : List (BoolVar F)) :
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

/-- `any`'s completeness law: the cases' own — the constants', an operand's, `or`'s, or
`neq`'s over the scoped bit-sum. -/
theorem any_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F))
    (f : BoolVar F → Bool) (hchar : ∀ k : Nat, k ≤ xs.length → (k : F) = 0 → k = 0) :
    Complete (fun st => ∀ b ∈ xs, CircuitType.ReadsAs (val := Bool) st b (f b))
      (Snarky.any (c := c) xs)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r (xs.any f)) := by
  have hbase : Complete (fun st => ∀ b ∈ xs,
      (↑b : CVar F).Scoped st ∧ CircuitType.WellFormed (val := Bool) st.env.get b)
      (Snarky.any (c := c) xs)
      (fun r st' => (↑r : CVar F).Scoped st' ∧
        CircuitType.WellFormed (val := Bool) st'.env.get r) := by
    intro st h
    match xs with
    | [] =>
      simp only [Snarky.any]
      exact ⟨false_, st, rfl, by simp [Sat, build], false_scoped st, false,
        CircuitType.reads_boolVar.mpr (by simp [bit])⟩
    | [a] =>
      simp only [Snarky.any]
      exact ⟨a, st, rfl, by simp [Sat, build], h a (List.mem_cons_self ..)⟩
    | [a, b] =>
      simp only [Snarky.any]
      obtain ⟨ab, hab⟩ := (h a (by simp)).2
      obtain ⟨bb, hbb⟩ := (h b (by simp)).2
      obtain ⟨r, st₁, hrun, hsat, hr⟩ := or_complete (c := c) a b ab bb st
        ⟨⟨CircuitType.scoped_boolVar.mpr (h a (by simp)).1, hab⟩,
          ⟨CircuitType.scoped_boolVar.mpr (h b (by simp)).1, hbb⟩⟩
      exact ⟨r, st₁, hrun, hsat, CircuitType.scoped_boolVar.mp hr.1, ab || bb, hr.2⟩
    | x₁ :: x₂ :: x₃ :: t =>
      simp only [Snarky.any]
      have hsc : (sum ((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar)).Scoped st :=
        CVar.Scoped.sum fun x hx => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact (h b hb).1
      obtain ⟨r, st₁, hrun, hsat, hr⟩ :=
        neq_complete (c := c) (sum ((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar))
          (CVar.const 0) _ 0 st
          ⟨⟨CircuitType.scoped_fvar.mpr hsc, rfl⟩,
            ⟨CircuitType.scoped_fvar.mpr trivial, rfl⟩⟩
      exact ⟨r, st₁, hrun, hsat, CircuitType.scoped_boolVar.mp hr.1, _, hr.2⟩
  intro st hF
  obtain ⟨r, st₁, hrun, hsat, hsc, -⟩ :=
    hbase st (fun b hb => ⟨CircuitType.scoped_boolVar.mp (hF b hb).1, ⟨f b, (hF b hb).2⟩⟩)
  refine ⟨r, st₁, hrun, hsat, CircuitType.scoped_boolVar.mpr hsc,
    CircuitType.reads_boolVar.mpr ?_⟩
  have hval := runs_post (fun V => any_spec (c := c) (V := V) xs hchar) hrun
    (hsat (Nat.le_refl _) (Assignments.Le.refl _))
  have hread : ∀ b ∈ xs, (↑b : CVar F).val st₁.env.get = bit (f b) := fun b hb =>
    CircuitType.reads_boolVar.mp
      (CircuitType.ReadsAs.mono hrun.nv_le hrun.le (hF b hb)).2
  have hbits : ∀ b ∈ xs, (↑b : CVar F).val st₁.env.get = 0 ∨
      (↑b : CVar F).val st₁.env.get = 1 := by
    intro b hb
    rw [hread b hb]
    cases f b <;> simp [bit]
  rw [hval hbits]
  have hone : ∀ b ∈ xs, ((↑b : CVar F).val st₁.env.get = 1 ↔ f b = true) := by
    intro b hb
    rw [hread b hb]
    cases f b <;> simp [bit]
  by_cases h : xs.any f = true
  · obtain ⟨b, hb, hfb⟩ := List.any_eq_true.mp h
    rw [if_pos ⟨b, hb, (hone b hb).mpr hfb⟩, h]
    rfl
  · simp only [Bool.not_eq_true, List.any_eq_false] at h
    rw [if_neg (fun hc => by
      obtain ⟨b, hb, hv⟩ := hc
      exact absurd ((hone b hb).mp hv) (by simpa using h b hb))]
    rw [show xs.any f = false from List.any_eq_false.mpr (fun b hb => by simp [h b hb])]
    rfl

attribute [irreducible] Snarky.any

/-! ## All -/

/-- All of a list of bits: empty is true, a singleton is itself, a pair is `and`, and three
or more test the bit-sum against the length. -/
def all [Field F] [DecidableEq F] [BasicSystem F c] (xs : List (BoolVar F)) :
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

/-- `all`'s completeness law: the cases' own — the constants', an operand's, `and`'s, or
`equals`'s over the scoped bit-sum. -/
theorem all_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (xs : List (BoolVar F))
    (f : BoolVar F → Bool) (hchar : ∀ j k : Nat, j ≤ xs.length → k ≤ xs.length → (j : F) = k → j = k) :
    Complete (fun st => ∀ b ∈ xs, CircuitType.ReadsAs (val := Bool) st b (f b))
      (Snarky.all (c := c) xs)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r (xs.all f)) := by
  have hbase : Complete (fun st => ∀ b ∈ xs,
      (↑b : CVar F).Scoped st ∧ CircuitType.WellFormed (val := Bool) st.env.get b)
      (Snarky.all (c := c) xs)
      (fun r st' => (↑r : CVar F).Scoped st' ∧
        CircuitType.WellFormed (val := Bool) st'.env.get r) := by
    intro st h
    match xs with
    | [] =>
      simp only [Snarky.all]
      exact ⟨true_, st, rfl, by simp [Sat, build], true_scoped st, true,
        CircuitType.reads_boolVar.mpr (by simp [bit])⟩
    | [a] =>
      simp only [Snarky.all]
      exact ⟨a, st, rfl, by simp [Sat, build], h a (List.mem_cons_self ..)⟩
    | [a, b] =>
      simp only [Snarky.all]
      obtain ⟨ab, hab⟩ := (h a (by simp)).2
      obtain ⟨bb, hbb⟩ := (h b (by simp)).2
      obtain ⟨r, st₁, hrun, hsat, hr⟩ := and_complete (c := c) a b ab bb st
        ⟨⟨CircuitType.scoped_boolVar.mpr (h a (by simp)).1, hab⟩,
          ⟨CircuitType.scoped_boolVar.mpr (h b (by simp)).1, hbb⟩⟩
      exact ⟨r, st₁, hrun, hsat, CircuitType.scoped_boolVar.mp hr.1, ab && bb, hr.2⟩
    | x₁ :: x₂ :: x₃ :: t =>
      simp only [Snarky.all]
      have hsc : (sum ((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar)).Scoped st :=
        CVar.Scoped.sum fun x hx => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact (h b hb).1
      obtain ⟨r, st₁, hrun, hsat, hr⟩ :=
        equals_complete (c := c) (CVar.const ((x₁ :: x₂ :: x₃ :: t).length : F))
          (sum ((x₁ :: x₂ :: x₃ :: t).map BoolVar.toCVar)) _ _ st
          ⟨⟨CircuitType.scoped_fvar.mpr trivial, rfl⟩,
            ⟨CircuitType.scoped_fvar.mpr hsc, rfl⟩⟩
      exact ⟨r, st₁, hrun, hsat, CircuitType.scoped_boolVar.mp hr.1, _, hr.2⟩
  intro st hF
  obtain ⟨r, st₁, hrun, hsat, hsc, -⟩ :=
    hbase st (fun b hb => ⟨CircuitType.scoped_boolVar.mp (hF b hb).1, ⟨f b, (hF b hb).2⟩⟩)
  refine ⟨r, st₁, hrun, hsat, CircuitType.scoped_boolVar.mpr hsc,
    CircuitType.reads_boolVar.mpr ?_⟩
  have hval := runs_post (fun V => all_spec (c := c) (V := V) xs hchar) hrun
    (hsat (Nat.le_refl _) (Assignments.Le.refl _))
  have hread : ∀ b ∈ xs, (↑b : CVar F).val st₁.env.get = bit (f b) := fun b hb =>
    CircuitType.reads_boolVar.mp
      (CircuitType.ReadsAs.mono hrun.nv_le hrun.le (hF b hb)).2
  have hbits : ∀ b ∈ xs, (↑b : CVar F).val st₁.env.get = 0 ∨
      (↑b : CVar F).val st₁.env.get = 1 := by
    intro b hb
    rw [hread b hb]
    cases f b <;> simp [bit]
  rw [hval hbits]
  have hone : ∀ b ∈ xs, ((↑b : CVar F).val st₁.env.get = 1 ↔ f b = true) := by
    intro b hb
    rw [hread b hb]
    cases f b <;> simp [bit]
  by_cases h : xs.all f = true
  · rw [if_pos (fun b hb => (hone b hb).mpr (List.all_eq_true.mp h b hb)), h]
    rfl
  · simp only [Bool.not_eq_true, List.all_eq_false] at h
    obtain ⟨b, hb, hfb⟩ := h
    rw [if_neg (fun hc => absurd ((hone b hb).mp (hc b hb)) (by simpa using hfb)),
      show xs.all f = false from List.all_eq_false.mpr ⟨b, hb, by simp [hfb]⟩]
    rfl

attribute [irreducible] Snarky.all

end Snarky
