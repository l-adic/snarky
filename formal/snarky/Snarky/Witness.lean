import Mathlib.Algebra.Field.Defs
import Snarky.Prover
import Snarky.Prover.WP

/-!
# The witness combinator

`CheckedType` pairs an encoding with the constraint circuit enforcing its
well-formedness; `witness` allocates a bundle, runs the prover's advice, and emits the
check. Its soundness and completeness laws, two readings of the same rows, are the leaf
interface every gadget builds on; completeness is a triple at the prover's
weakest-precondition reading (`Snarky.Prover.WP`), on the checked type's own law of that form
(`WPCheckedType`).
-/

namespace Snarky

open Std.Do

set_option mvcgen.warning false

/-- Variable bundles whose well-formedness is enforced by constraints: `check` is
emitted by `witness` under both interpreters, with what its rows force about the bundle
(`post`, `check_sound`); the prover's side is `WPCheckedType`. The law holds at the backend's
reading of its constraints, a parameter, so a check may emit any row that reading gives
meaning to; the value type is a parameter because admissibility (`CheckedType.Valid`) speaks
of values. -/
class CheckedType (F c val var : Type) [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F val var] where
  /-- The circuit that constrains the bundle to well-formed values. -/
  check : var → CircuitM F c PUnit
  /-- What the check's rows force about the bundle under a valuation. -/
  post : Valuation F → var → Prop
  /-- The rows of `check v`, satisfied at `V`, force `post V v`. -/
  check_sound : ∀ (V : Valuation F) (v : var) (nv : Nat),
    (∀ con ∈ (build (check v) nv).constraints, ConstraintHolds.Holds V con) → post V v

/-- The values a check admits: those whose every bundle reading satisfies `post`. A
definition rather than a field, so no completeness law can assume more than the type's
own rows force. -/
def CheckedType.Valid {F c val var : Type} [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F val var] [CheckedType F c val var] (a : val) : Prop :=
  ∀ (V : Valuation F) (w : var), CircuitType.Reads V w a →
    CheckedType.post (c := c) (val := val) V w

/-- A checked type whose check has its law at the prover's weakest-precondition reading
(`Snarky.Prover.WP`), over the carrier's own transformer: from a state where the bundle is in
scope and reads an admissible value, the check runs, its rows hold where they are emitted,
and the state only grows (a check may allocate auxiliaries). A class beside `CheckedType`
rather than a field of it: a check built from gadgets without a law at that reading has none
yet, and the witness law asks it only of the types it witnesses. -/
class WPCheckedType (F c val var : Type) [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F val var] [CheckedType F c val var] : Prop where
  /-- The check's law, over the transformer. -/
  check_wp : ∀ (v : var) (a : val) (st : ProverState F),
    CircuitType.ReadsAs (val := val) st v a →
    CheckedType.Valid (F := F) (c := c) (var := var) a →
    (proverWP.{0} (CheckedType.check (c := c) (val := val) v)
      (fun _ s' => ULift.up.{0} (st ≤ s')) (fun _ _ => ULift.up.{0} False) st).down

/-- The check's law at the completeness tag, registered: the step `mvcgen` takes inside
`witness`, after the allocation. The value is a ghost beside the entry state, so an instance's
law is applied at whatever the bundle reads. -/
@[spec] theorem Prover.check_spec {F c val var : Type} [Field F] [BasicSystem F c]
    [ConstraintHolds F c] [CircuitType F val var] [CheckedType F (Prover c) val var]
    [WPCheckedType F (Prover c) val var] (v : var) (a : val) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ CircuitType.ReadsAs (val := val) st₀ v a ∧
      CheckedType.Valid (F := F) (c := Prover c) (var := var) a⌝⦄
    CheckedType.check (F := F) (c := Prover c) (val := val) v
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  rintro s ⟨rfl, hr, hv⟩
  exact WPCheckedType.check_wp v a s hr hv

section Instances

variable {F c : Type}

/-- A field element carries no well-formedness constraint. -/
instance instCheckedTypeFVar [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    CheckedType F c F (FVar F) where
  check _ := .pure PUnit.unit
  post _ _ := True
  check_sound := by intros; trivial

instance instWPCheckedTypeFVar [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    WPCheckedType F c F (FVar F) :=
  ⟨fun _ _ _ _ _ => le_rfl⟩

/-- The empty bundle carries no well-formedness constraint. -/
instance instCheckedTypeUnit [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    CheckedType F c Unit Unit where
  check _ := .pure PUnit.unit
  post _ _ := True
  check_sound := by intros; trivial

/-- A freshly witnessed boolean must be constrained to `{0, 1}`: one `boolean` row, whose
reading is the booleanity every consumer of the bundle assumes. -/
instance instCheckedTypeBool [Field F] [DecidableEq F] [NeZero (1 : F)] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] : CheckedType F c Bool (BoolVar F) where
  check b := addConstraint (BasicSystem.boolean b.toCVar)
  post V b := ∃ bb : Bool, (↑b : CVar F).val V = bit bb
  check_sound V b nv hsat := by
    rcases (LawfulBasicSystem.holds_boolean V (↑b)).mp
        (hsat (BasicSystem.boolean b.toCVar) (by simp [Snarky.addConstraint, build])) with h | h
    · exact ⟨false, by simpa [bit] using h⟩
    · exact ⟨true, by simpa [bit] using h⟩

/-- The booleanity row holds at a bit's reading. -/
instance instWPCheckedTypeBool [Field F] [DecidableEq F] [NeZero (1 : F)] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] : WPCheckedType F c Bool (BoolVar F) :=
  ⟨fun b a st hr _ => by
    show ConstraintHolds.Holds st.env.get (BasicSystem.boolean (c := c) b.toCVar) ∧
      (∀ x ∈ ConstraintHolds.cells (F := F) (BasicSystem.boolean (c := c) b.toCVar),
        x.Scoped st) ∧ st ≤ st
    refine ⟨(LawfulBasicSystem.holds_boolean _ _).mpr ?_,
      LawfulBasicSystem.scoped_boolean.mpr (CircuitType.scoped_boolVar.mp hr.1), le_rfl⟩
    rw [CircuitType.reads_boolVar.mp hr.2]
    cases a <;> simp [bit]⟩

section Product

variable {a va b vb : Type}

/-- A product is checked factor by factor; its rows concatenate. -/
instance instCheckedTypeProd [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a va] [CircuitType F b vb] [CheckedType F c a va] [CheckedType F c b vb] :
    CheckedType F c (a × b) (va × vb) where
  check p := do
    CheckedType.check (c := c) (val := a) p.1
    CheckedType.check (c := c) (val := b) p.2
  post V p := CheckedType.post (c := c) (val := a) V p.1 ∧
    CheckedType.post (c := c) (val := b) V p.2
  check_sound V p nv hsat := by
    simp only [build_bind] at hsat
    exact ⟨CheckedType.check_sound V p.1 nv fun con h => hsat con (List.mem_append_left _ h),
      CheckedType.check_sound V p.2 _ fun con h => hsat con (List.mem_append_right _ h)⟩

/-- A product's check composes its factors' laws through the transformer. -/
instance instWPCheckedTypeProd [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a va] [CircuitType F b vb] [CheckedType F c a va] [CheckedType F c b vb]
    [WPCheckedType F c a va] [WPCheckedType F c b vb] : WPCheckedType F c (a × b) (va × vb) :=
  ⟨fun p x st hr hv => by
    have hx : ∀ (V : Valuation F) (u : va), CircuitType.Reads V u x.1 →
        CheckedType.post (c := c) (val := a) V u := fun V u hu =>
      (hv V (u, CircuitType.constVar x.2) (CircuitType.reads_prod'.mpr
        ⟨hu, CircuitType.reads_constVar V x.2⟩)).1
    have hy : ∀ (V : Valuation F) (u : vb), CircuitType.Reads V u x.2 →
        CheckedType.post (c := c) (val := b) V u := fun V u hu =>
      (hv V (CircuitType.constVar x.1, u) (CircuitType.reads_prod'.mpr
        ⟨CircuitType.reads_constVar V x.1, hu⟩)).2
    show (proverWP (do CheckedType.check (c := c) (val := a) p.1
                       CheckedType.check (c := c) (val := b) p.2) _ _ st).down
    rw [proverWP_bind]
    refine proverWP_mono (fun _ s₁ h₁ => ?_) (WPCheckedType.check_wp p.1 x.1 st
      ⟨(CircuitType.scoped_prod'.mp hr.1).1, (CircuitType.reads_prod'.mp hr.2).1⟩ hx)
    exact proverWP_mono (fun _ _ h₂ => h₁.trans h₂) (WPCheckedType.check_wp p.2 x.2 s₁
      (CircuitType.ReadsAs.of_le h₁ ⟨(CircuitType.scoped_prod'.mp hr.1).2,
        (CircuitType.reads_prod'.mp hr.2).2⟩) hy)⟩

end Product

section VectorFormer

variable {a va : Type}

/-- Check each bundle in turn. -/
def checkAll [Field F] [BasicSystem F c] [ConstraintHolds F c] [CircuitType F a va]
    [CheckedType F c a va] : List va → CircuitM F c PUnit
  | [] => pure PUnit.unit
  | v :: vs => do
    CheckedType.check (c := c) (val := a) v
    checkAll vs

section Laws

variable [Field F] [BasicSystem F c] [ConstraintHolds F c] [CircuitType F a va]
  [CheckedType F c a va]

private theorem checkAll_sound (V : Valuation F) :
    ∀ (l : List va) (nv : Nat),
      (∀ con ∈ (build (checkAll (F := F) (c := c) (a := a) l) nv).constraints,
        ConstraintHolds.Holds V con) →
      ∀ v ∈ l, CheckedType.post (c := c) (val := a) V v
  | [], _, _, _, h => nomatch h
  | v :: l, nv, hsat, w, hw => by
    simp only [checkAll, build_bind] at hsat
    rcases List.mem_cons.mp hw with rfl | hw
    · exact CheckedType.check_sound V w nv fun con h => hsat con (List.mem_append_left _ h)
    · exact checkAll_sound V l _ (fun con h => hsat con (List.mem_append_right _ h)) w hw

/-- Admissibility of a vector is admissibility of its entries: a bundle reading as one
entry sits in a vector of constant bundles reading as the whole. -/
private theorem valid_getElem {n : Nat} {xs : Vector a n}
    (hv : ∀ (V : Valuation F) (ws : Vector va n), CircuitType.Reads V ws xs →
      ∀ w ∈ ws.toList, CheckedType.post (c := c) (val := a) V w)
    {i : Nat} (hi : i < n) : CheckedType.Valid (F := F) (c := c) (var := va) xs[i] := by
  intro V w hw
  have hwsi : (Vector.ofFn fun j : Fin n =>
      if (j : Nat) = i then w else CircuitType.constVar (F := F) (var := va) xs[j])[i] = w := by
    simp
  refine hv V _ ?_ w (Vector.mem_toList_iff.mpr (hwsi ▸ Vector.getElem_mem hi))
  rw [CircuitType.reads_vector]
  intro k hk
  rcases eq_or_ne k i with rfl | hne
  · simpa using hw
  · simpa [hne] using CircuitType.reads_constVar (F := F) (var := va) V xs[k]

/-- The entries' checks in turn, over the transformer: each entry's law at its own state,
the state only growing. -/
private theorem Prover.checkAll_wp [WPCheckedType F c a va] :
    ∀ (l : List va) (st : ProverState F),
      (∀ v ∈ l, ∃ x : a, CheckedType.Valid (F := F) (c := c) (var := va) x ∧
        CircuitType.ReadsAs (val := a) st v x) →
      (proverWP.{0} (checkAll (F := F) (c := c) (a := a) l) (fun _ s' => ULift.up.{0} (st ≤ s'))
        (fun _ _ => ULift.up.{0} False) st).down
  | [], _, _ => le_rfl
  | v :: l, st, hl => by
    obtain ⟨x, hx, hr⟩ := hl v (List.mem_cons_self ..)
    rw [checkAll, proverWP_bind]
    refine proverWP_mono (fun _ s₁ h₁ => ?_) (WPCheckedType.check_wp v x st hr hx)
    exact proverWP_mono (fun _ _ h₂ => h₁.trans h₂) (Prover.checkAll_wp l s₁ fun w hw =>
      (hl w (List.mem_cons_of_mem _ hw)).imp fun y hy => ⟨hy.1, hy.2.of_le h₁⟩)

end Laws

/-- A vector is checked entry by entry; its rows concatenate. -/
instance instCheckedTypeVector [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a va] [CheckedType F c a va] {n : Nat} :
    CheckedType F c (Vector a n) (Vector va n) where
  check vs := checkAll (F := F) (c := c) (a := a) vs.toList
  post V vs := ∀ v ∈ vs.toList, CheckedType.post (c := c) (val := a) V v
  check_sound V vs nv hsat := checkAll_sound V vs.toList nv hsat

/-- A vector's check composes its entries' laws through the transformer. -/
instance instWPCheckedTypeVector [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a va] [CheckedType F c a va] [WPCheckedType F c a va] {n : Nat} :
    WPCheckedType F c (Vector a n) (Vector va n) :=
  ⟨fun vs xs st hr hv => by
    refine Prover.checkAll_wp vs.toList st fun v hv' => ?_
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hv')
    exact ⟨xs[i], valid_getElem hv hi, (CircuitType.scoped_vector.mp hr.1) i hi,
      (CircuitType.reads_vector.mp hr.2) i hi⟩⟩

end VectorFormer

section UnChecked

variable {val var : Type}

/-- An `UnChecked` bundle emits no check: it grants nothing, which is what the wrapper
is for. -/
instance instCheckedTypeUnChecked [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F val var] : CheckedType F c (UnChecked val) (UnChecked var) where
  check _ := pure PUnit.unit
  post _ _ := True
  check_sound _ _ _ _ := trivial

instance instWPCheckedTypeUnChecked [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F val var] : WPCheckedType F c (UnChecked val) (UnChecked var) :=
  ⟨fun _ _ _ _ _ => le_rfl⟩

end UnChecked

section Equiv

variable {a va b vb : Type}

/-- A type isomorphic to a checked type is checked through the isomorphism. -/
@[reducible] def CheckedType.ofEquiv [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a va] [S : CheckedType F c a va] (ev : b ≃ a) (ew : vb ≃ va) :
    @CheckedType F c b vb _ _ _ (CircuitType.ofEquiv ev ew) :=
  letI : CircuitType F b vb := CircuitType.ofEquiv ev ew
  { check := fun v => S.check (ew v)
    post := fun V v => S.post V (ew v)
    check_sound := fun V v nv h => S.check_sound V (ew v) nv h }

/-- The law transfers along the isomorphism. -/
instance instWPCheckedTypeOfEquiv [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a va] [S : CheckedType F c a va] [WPCheckedType F c a va] (ev : b ≃ a)
    (ew : vb ≃ va) :
    @WPCheckedType F c b vb _ _ _ (CircuitType.ofEquiv ev ew) (CheckedType.ofEquiv ev ew) :=
  letI : CircuitType F b vb := CircuitType.ofEquiv ev ew
  letI : CheckedType F c b vb := CheckedType.ofEquiv ev ew
  ⟨fun v x st hr hx =>
    WPCheckedType.check_wp (c := c) (val := a) (ew v) (ev x) st
      ⟨(CircuitType.scoped_ofEquiv ev ew).mp hr.1, (CircuitType.reads_ofEquiv ev ew).mp hr.2⟩
      fun V w hw => by
        have h := hx V (ew.symm w)
          (by rwa [CircuitType.reads_ofEquiv, Equiv.apply_symm_apply])
        change CheckedType.post (c := c) (val := a) V (ew (ew.symm w)) at h
        rwa [Equiv.apply_symm_apply] at h⟩

end Equiv

section FinFamily

/-- A `Fin`-indexed family is checked entry by entry in index order: through `Fin.consEquiv`,
entry `0`'s check, then the rest's. -/
@[reducible] private def CheckedType.finFamily [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    (n : ℕ) → (β γ : Fin n → Type) → [∀ i, CircuitType F (β i) (γ i)] →
      [∀ i, CheckedType F c (β i) (γ i)] →
      @CheckedType F c ((i : Fin n) → β i) ((i : Fin n) → γ i) _ _ _
        (CircuitType.finFamily n β γ)
  | 0, _, _, _, _ => CheckedType.ofEquiv (Equiv.ofUnique _ Unit) (Equiv.ofUnique _ Unit)
  | n + 1, β, γ, _, _ =>
    letI := CircuitType.finFamily (F := F) n (fun i => β i.succ) (fun i => γ i.succ)
    letI := CheckedType.finFamily n (fun i => β i.succ) (fun i => γ i.succ)
    CheckedType.ofEquiv (Fin.consEquiv β).symm (Fin.consEquiv γ).symm

instance instCheckedTypeFinFamily [Field F] [BasicSystem F c] [ConstraintHolds F c] {n : ℕ}
    {β γ : Fin n → Type} [∀ i, CircuitType F (β i) (γ i)] [∀ i, CheckedType F c (β i) (γ i)] :
    CheckedType F c ((i : Fin n) → β i) ((i : Fin n) → γ i) :=
  CheckedType.finFamily n β γ

/-- A family's check forces each entry's. -/
theorem CheckedType.post_finFamily [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    ∀ {n : ℕ} {β γ : Fin n → Type} [∀ i, CircuitType F (β i) (γ i)]
      [∀ i, CheckedType F c (β i) (γ i)] (V : Valuation F) (v : (i : Fin n) → γ i),
      CheckedType.post (c := c) (val := (i : Fin n) → β i) V v ↔
        ∀ i, CheckedType.post (c := c) (val := β i) V (v i)
  | 0, _, _, _, _, _, _ => ⟨fun _ i => i.elim0, fun _ => trivial⟩
  | n + 1, β, γ, _, _, V, v => by
    rw [Fin.forall_fin_succ, ← CheckedType.post_finFamily (β := fun i => β i.succ)
      (γ := fun i => γ i.succ) V fun i => v i.succ]
    exact Iff.rfl

end FinFamily

end Instances

/-! ## Admissibility, at the concrete types and the formers

The concrete types below admit every value: their checks force only that the wires lie in
the encoding's image. The formers reduce admissibility to their components'. A type whose
rows constrain the value (a curve point's on-curve rows) proves its own characterization. -/

section Valid

variable {F c : Type}

@[simp] theorem valid_fvar [Field F] [BasicSystem F c] [ConstraintHolds F c] {x : F} :
    CheckedType.Valid (F := F) (c := c) (var := FVar F) x := fun _ _ _ => trivial

@[simp] theorem valid_bool [Field F] [DecidableEq F] [NeZero (1 : F)]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] {b : Bool} :
    CheckedType.Valid (F := F) (c := c) (var := BoolVar F) b :=
  fun _ _ h => ⟨b, CircuitType.reads_boolVar.mp h⟩

@[simp] theorem valid_unchecked {val var : Type} [Field F]
    [BasicSystem F c] [ConstraintHolds F c] [CircuitType F val var] {x : UnChecked val} :
    CheckedType.Valid (F := F) (c := c) (var := UnChecked var) x := fun _ _ _ => trivial

variable {a va b vb : Type}

@[simp] theorem valid_prod [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a va] [CircuitType F b vb] [CheckedType F c a va] [CheckedType F c b vb]
    {p : a × b} :
    CheckedType.Valid (F := F) (c := c) (var := va × vb) p ↔
      CheckedType.Valid (F := F) (c := c) (var := va) p.1 ∧
        CheckedType.Valid (F := F) (c := c) (var := vb) p.2 := by
  constructor
  · intro h
    exact ⟨fun V u hu => (h V (u, CircuitType.constVar (F := F) (var := vb) p.2)
        (CircuitType.reads_prod.mpr ⟨hu, CircuitType.reads_constVar V p.2⟩)).1,
      fun V u hu => (h V (CircuitType.constVar (F := F) (var := va) p.1, u)
        (CircuitType.reads_prod.mpr ⟨CircuitType.reads_constVar V p.1, hu⟩)).2⟩
  · rintro ⟨hx, hy⟩ V ⟨u, w⟩ hu
    rw [CircuitType.reads_prod] at hu
    exact ⟨hx V u hu.1, hy V w hu.2⟩

@[simp] theorem valid_vector [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a va] [CheckedType F c a va] {n : Nat} {xs : Vector a n} :
    CheckedType.Valid (F := F) (c := c) (var := Vector va n) xs ↔
      ∀ (i : Nat) (hi : i < n), CheckedType.Valid (F := F) (c := c) (var := va) xs[i] := by
  constructor
  · exact fun h _ hi => valid_getElem h hi
  · rintro h V ws hws w hw
    rw [CircuitType.reads_vector] at hws
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hw)
    exact h i hi V ws[i] (hws i hi)

/-- Admissibility transfers along the isomorphism. -/
@[simp] theorem valid_ofEquiv [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a va] [S : CheckedType F c a va] (ev : b ≃ a) (ew : vb ≃ va) {x : b} :
    @CheckedType.Valid F c b vb _ _ _ (CircuitType.ofEquiv ev ew)
        (CheckedType.ofEquiv ev ew) x ↔
      CheckedType.Valid (F := F) (c := c) (var := va) (ev x) := by
  constructor
  · intro h V u hu
    have hx : @CircuitType.Reads F b vb _ _ (CircuitType.ofEquiv ev ew) V (ew.symm u) x := by
      rw [CircuitType.reads_ofEquiv, Equiv.apply_symm_apply]
      exact hu
    have h2 : CheckedType.post (c := c) (val := a) V (ew (ew.symm u)) := h V (ew.symm u) hx
    rwa [Equiv.apply_symm_apply] at h2
  · intro h V w hw
    exact h V (ew w) ((CircuitType.reads_ofEquiv ev ew).mp hw)

end Valid

section Combinators

variable {F c val var : Type}

/-- Witness a typed value, the circuit's nondeterminism primitive. The builder allocates
`CircuitType.size` variables for the bundle and emits the type's `CheckedType.check` rows;
only prover runs execute `compute`, whose output is the witness to that existential. -/
def witness [Field F] [BasicSystem F c] [ConstraintHolds F c] [inst : CircuitType F val var]
    [CheckedType F c val var] (compute : AsProver F val) : CircuitM F c var :=
  .existsOp inst.size (inst.valueToFields <$> compute) fun vs => do
    let v := inst.fieldsToVar (mapVec CVar.var vs)
    CheckedType.check (c := c) (val := val) v
    pure v

/-- Read a typed variable bundle back to its value during a prover run. The length check
is dynamic (it always succeeds) to keep the definition kernel-reducible without a
`List.mapM` length lemma. -/
def readVar [Add F] [Mul F] [inst : CircuitType F val var] (v : var) : AsProver F val := do
  let fields ← (inst.varToFields v).toList.mapM AsProver.readCVar
  if h : fields.length = inst.size then
    pure (inst.fieldsToValue ⟨⟨fields⟩, by simpa using h⟩)
  else
    AsProver.throw "readVar: size mismatch"

open Std.Do in
/-- A witnessed bundle satisfies its type's `CheckedType.post` wherever the rows hold. -/
@[spec] theorem witness_spec {V : Valuation F} [Field F]
    [BasicSystem F c] [ConstraintHolds F c] [CircuitType F val var]
    [S : CheckedType F (Builder V c) val var] (compute : AsProver F val) :
    ⦃⌜True⌝⦄
    (witness (val := val) compute : CircuitM F (Builder V c) var)
    ⦃⇓ r _ => ⌜S.post V r⌝⦄ := by
  intro nv _ hsat
  simp only [witness, build, build_bind, build_pure, List.append_nil] at hsat ⊢
  exact S.check_sound V _ _ hsat

/-! ## The leaves -/

/-- Reading scoped expressions is reading them totally. -/
theorem run_mapM_readCVar [Add F] [Mul F] [Zero F] {st : ProverState F} :
    ∀ {l : List (CVar F)}, (∀ cv ∈ l, cv.Scoped st) →
      (l.mapM AsProver.readCVar).run st.env = .ok (l.map (·.val st.env.get))
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.mapM_cons, AsProver.bind_eq, AsProver.pure_eq, AsProver.run_bind,
      AsProver.readCVar_run (h x (List.mem_cons_self ..)), Except.bind,
      run_mapM_readCVar fun cv hcv => h cv (List.mem_cons_of_mem _ hcv), AsProver.run_pure,
      List.map_cons]

/-- `readVar` of a scoped bundle returns its `CircuitType.readVal`. -/
@[simp] theorem readVar_run [Add F] [Mul F] [Zero F] [CircuitType F val var] {st : ProverState F}
    {v : var} (hs : CircuitType.Scoped (val := val) st v) :
    (readVar (val := val) v).run st.env = .ok (CircuitType.readVal st.env.get v) := by
  simp only [readVar, AsProver.bind_eq, AsProver.run_bind, run_mapM_readCVar hs, Except.bind]
  rw [dif_pos (by simp)]
  rfl

end Combinators

/-- Witnessing an unchecked bundle emits no rows — the wrapper's whole content. -/
example {val var : Type} [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F val var] (compute : AsProver F (UnChecked val)) (nv : Nat) :
    (build (witness (c := c) (val := UnChecked val) compute) nv).constraints = [] := by
  rfl

/-! ## The witness law at the prover's reading

Generic in the computation and not registered. A gadget derives, once per advice, the law
at that advice's run (`Prover.witness_of_run`), with the value a named function of the
entry readings, and registers that through `Prover.register`: no existential and no run
term reaches a gadget's proof, which transports bundle readings alone. The check's step is
the checked type's registered `Prover.check_spec`, so every bundle whose type has the law is
witnessed. -/

section ProverReading

variable {val var : Type}

/-- Witnessing a bundle: when the computation succeeds at the entry table with an admissible
value, the fresh bundle is in scope and reads what the computation returned, at a state
extending the entry. The value is existential in the postcondition, so that the computation's
run is a fact a later condition can match. -/
theorem Prover.witness_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [inst : CircuitType F val var] [CheckedType F (Prover c) val var]
    [WPCheckedType F (Prover c) val var] (compute : AsProver F val) (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ (∀ e, compute.run st₀.env ≠ .error e) ∧
      ∀ v, compute.run st₀.env = .ok v →
        CheckedType.Valid (F := F) (c := Prover c) (var := var) v⌝⦄
    witness (c := Prover c) (val := val) compute
    ⦃⇓ r st' => ⌜(∃ v, compute.run st₀.env = .ok v ∧ CircuitType.ReadsAs (val := val) st' r v) ∧
      st₀ ≤ st'⌝⦄ := by
  rintro st ⟨rfl, hok, hvalid⟩
  obtain ⟨v₀, h⟩ : ∃ v, compute.run st.env = .ok v := by
    rcases hrun : compute.run st.env with e | v
    · exact absurd hrun (hok e)
    · exact ⟨v, rfl⟩
  have hscope : CircuitType.Scoped (val := val)
      (st.alloc (CircuitType.valueToFields (F := F) v₀))
      (CircuitType.fieldsToVar (F := F) (val := val)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F val)))) := by
    intro cv hcv
    rw [CircuitType.var_roundTrip, toList_mapVec, List.mem_map] at hcv
    obtain ⟨w, hw, rfl⟩ := hcv
    exact show w < st.nv + CircuitType.size F val from (List.mem_range'_1.mp hw).2
  have hreads : CircuitType.Reads (st.alloc (CircuitType.valueToFields (F := F) v₀)).env.get
      (CircuitType.fieldsToVar (F := F) (val := val)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F val)))) v₀ := by
    unfold CircuitType.Reads
    rw [CircuitType.var_roundTrip]
    ext i hi
    simp only [getElem_mapVec, getElem_allocRange, CVar.val, ProverState.get_alloc]
    simp [Assignments.get, Assignments.extendList_get
      (show i < (CircuitType.valueToFields (F := F) v₀).toList.length by simpa using hi)]
  -- after the allocation, the check and the return, as a triple at the allocated state
  have hk : ∀ st₁ : ProverState F,
      ⦃fun s => ⌜s = st₁ ∧ CircuitType.ReadsAs (val := val) st₁
        (CircuitType.fieldsToVar (F := F) (val := val)
          (mapVec CVar.var (allocRange st.nv (CircuitType.size F val)))) v₀ ∧ st ≤ st₁⌝⦄
      (do CheckedType.check (c := Prover c) (val := val)
            (CircuitType.fieldsToVar (F := F) (val := val)
              (mapVec CVar.var (allocRange st.nv (CircuitType.size F val))))
          pure (CircuitType.fieldsToVar (F := F) (val := val)
            (mapVec CVar.var (allocRange st.nv (CircuitType.size F val)))) :
        CircuitM F (Prover c) var)
      ⦃⇓ r st' => ⌜(∃ v, compute.run st.env = .ok v ∧
        CircuitType.ReadsAs (val := val) st' r v) ∧ st ≤ st'⌝⦄ := by
    intro st₁
    mvcgen
    · rename_i s hs
      obtain ⟨rfl, hr, -⟩ := hs
      exact ⟨trivial, hr, hvalid v₀ h⟩
    · rename_i s hs u s₁ h₁
      obtain ⟨rfl, hr, hle⟩ := hs
      exact ⟨⟨v₀, h, hr.of_le h₁⟩, hle.trans h₁⟩
  have hmap : (CircuitType.valueToFields (F := F) <$> compute).run st.env =
      .ok (CircuitType.valueToFields (F := F) v₀) := by
    simp [AsProver.map_eq, AsProver.run_bind, h, Except.bind, AsProver.run_pure]
  show (proverWP (c := Prover c) (witness (c := Prover c) (val := val) compute) _ _ st).down
  simp only [Snarky.witness, proverWP, hmap]
  exact hk _ _ ⟨rfl, ⟨hscope, hreads⟩, st.dom.le_extendList _⟩

/-- The witness law at one advice: where the advice's run at the entry table is known to
return `value` of the entry, admissible, the fresh bundle reads that value. What a gadget
registers, once per advice, with `value` a named function of the entry readings. -/
theorem Prover.witness_of_run [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F val var] [CheckedType F (Prover c) val var]
    [WPCheckedType F (Prover c) val var] (compute : AsProver F val)
    (pre : ProverState F → Prop) (value : ProverState F → val)
    (hrun : ∀ st, pre st → compute.run st.env = .ok (value st))
    (hvalid : ∀ st, pre st → CheckedType.Valid (F := F) (c := Prover c) (var := var) (value st))
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ pre st₀⌝⦄
    witness (c := Prover c) (val := val) compute
    ⦃⇓ r s' => ⌜CircuitType.ReadsAs (val := val) s' r (value st₀) ∧ st₀ ≤ s'⌝⦄ := by
  intro s hs
  have hr := hrun st₀ hs.2
  have hne : ∀ e, compute.run st₀.env ≠ .error e := fun e he => by
    rw [hr] at he
    cases he
  have hv' : ∀ v, compute.run st₀.env = .ok v →
      CheckedType.Valid (F := F) (c := Prover c) (var := var) v := by
    intro v hv
    rw [hr] at hv
    cases Except.ok.inj hv
    exact hvalid st₀ hs.2
  have hs' : s = st₀ ∧ (∀ e, compute.run st₀.env ≠ .error e) ∧
      ∀ v, compute.run st₀.env = .ok v →
        CheckedType.Valid (F := F) (c := Prover c) (var := var) v := ⟨hs.1, hne, hv'⟩
  refine (wp (witness (c := Prover c) (val := val) compute)).mono _ _ ?_ s
    (Prover.witness_spec (c := c) (val := val) compute st₀ s hs')
  refine ⟨fun r s' hpost => ?_, .rfl⟩
  obtain ⟨⟨v, hv, hrd⟩, hle⟩ := hpost
  rw [hr] at hv
  cases Except.ok.inj hv
  exact ⟨hrd, hle⟩

end ProverReading

end Snarky
