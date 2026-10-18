import Std.Tactic.Do
import Snarky.Prover
import Snarky.Witness
import Snarky.DSL.Field

/-!
# The weakest-precondition interpretation of `prove`

The completeness reading of a circuit as a `Std.Do.WP` instance: the state is the prover state,
counter and table; a failing witness computation is the exception; and each emitted row is an
obligation at the state where it is emitted. The tag `Prover c` selects this reading, as
`Builder V c` selects the soundness reading, where rows are assumptions on a valuation.
-/

namespace Snarky

open Std.Do

variable {F c : Type}

/-- The completeness tag: `c` read by the prover. A program enters the completeness reading as
`g (c := Prover c)`; instance search does not unfold `Prover`, so the tag gets its own `WP`
instance while the term stays a `CircuitM F c` program. -/
def Prover (c : Type) := c

instance [inst : ConstraintHolds F c] : ConstraintHolds F (Prover c) := inst

instance [inst : BasicSystem F c] : BasicSystem F (Prover c) := inst

instance [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] [ConstraintHolds F c]
    [inst : LawfulBasicSystem F c] : LawfulBasicSystem F (Prover c) := inst

/-- The prover's postcondition shape: the witness computations' errors, over the prover state. -/
abbrev ProverShape (F : Type) : PostShape := .except EvalError (.arg (ProverState F) .pure)

/-- The prover's predicate transformer, by recursion on the program: `pure` lands the result at
the current state; an emitted row is an obligation at the current table; a witness computation
that fails hands its error and the current state to the failure condition, and one that succeeds
continues at the state allocating its values, as `prove` does. -/
def proverWP [Zero F] [ConstraintHolds F c] {α : Type} :
    CircuitM F c α → (α → ProverState F → ULift Prop) →
      (EvalError → ProverState F → ULift Prop) → ProverState F → ULift Prop
  | .pure a, Q, _, st => Q a st
  | .addConstraintOp con k, Q, E, st =>
      .up (ConstraintHolds.Holds st.env.get con ∧ (proverWP k Q E st).down)
  | .existsOp n wit k, Q, E, st =>
      match wit.run st.env with
      | .error e => E e st
      | .ok xs => proverWP (k (allocRange st.nv n)) Q E (st.alloc xs)

/-- The transformer distributes over conjunction, pointwise in both conditions. -/
theorem proverWP_and [Zero F] [ConstraintHolds F c] {α : Type} (x : CircuitM F c α)
    (Q₁ Q₂ : α → ProverState F → ULift Prop) (E₁ E₂ : EvalError → ProverState F → ULift Prop)
    (st : ProverState F) :
    (proverWP x (fun a s => .up ((Q₁ a s).down ∧ (Q₂ a s).down))
        (fun e s => .up ((E₁ e s).down ∧ (E₂ e s).down)) st).down ↔
      (proverWP x Q₁ E₁ st).down ∧ (proverWP x Q₂ E₂ st).down := by
  induction x generalizing st with
  | pure a => exact Iff.rfl
  | addConstraintOp con k ih =>
    simp only [proverWP]
    constructor
    · intro h
      exact ⟨⟨h.1, ((ih st).mp h.2).1⟩, h.1, ((ih st).mp h.2).2⟩
    · intro h
      exact ⟨h.1.1, (ih st).mpr ⟨h.1.2, h.2.2⟩⟩
  | existsOp n wit k ih =>
    simp only [proverWP]
    rcases h : wit.run st.env with e | xs
    · exact Iff.rfl
    · exact ih _ _

/-- A sequence's transformer is the head's at the tail's, the shape `WPMonad` needs. -/
theorem proverWP_bind [Zero F] [ConstraintHolds F c] {α β : Type} (x : CircuitM F c α)
    (f : α → CircuitM F c β) (Q : β → ProverState F → ULift Prop)
    (E : EvalError → ProverState F → ULift Prop) (st : ProverState F) :
    proverWP (x >>= f) Q E st = proverWP x (fun a s => proverWP (f a) Q E s) E st := by
  show proverWP (CircuitM.bind x f) Q E st = _
  induction x generalizing st with
  | pure a => rfl
  | addConstraintOp con k ih => simp only [CircuitM.bind, proverWP, ih]
  | existsOp n wit k ih =>
    simp only [CircuitM.bind, proverWP]
    rcases h : wit.run st.env with e | xs
    · rfl
    · exact ih _ _

/-- The completeness reading of `prove`: rows are obligations, failures are exceptions, the
prover state is the state. -/
instance Prover.instWP [Zero F] [ConstraintHolds F c] :
    WP (CircuitM F (Prover c)) (ProverShape F) where
  wp x := {
    trans := fun Q st => proverWP (c := Prover c) x Q.1 Q.2.1 st
    conjunctiveRaw := by
      intro Q₁ Q₂
      apply SPred.bientails.of_eq
      funext st
      show ULift.up (proverWP (c := Prover c) x (Q₁ ∧ₚ Q₂).1 (Q₁ ∧ₚ Q₂).2.1 st).down =
        ULift.up ((proverWP (c := Prover c) x Q₁.1 Q₁.2.1 st).down ∧
          (proverWP (c := Prover c) x Q₂.1 Q₂.2.1 st).down)
      exact congrArg ULift.up
        (propext (proverWP_and (c := Prover c) x Q₁.1 Q₂.1 Q₁.2.1 Q₂.2.1 st))
  }

/-- `wp` is a monad morphism: `pure` is the identity transformer and a sequence composes. -/
instance Prover.instWPMonad [Zero F] [ConstraintHolds F c] :
    WPMonad (CircuitM F (Prover c)) (ProverShape F) where
  wp_pure a := by
    ext Q st
    rfl
  wp_bind x f := by
    ext Q st
    simp only [PredTrans.apply_Bind_bind]
    exact Iff.of_eq (congrArg ULift.down (proverWP_bind (c := Prover c) x f Q.1 Q.2.1 st))

/-! ## Primitive specs -/

/-- Emitting a row obliges it at the current table; the state is unchanged. -/
@[spec] theorem Prover.addConstraint_spec [Zero F] [ConstraintHolds F c] (con : Prover c)
    (Q : PostCond PUnit (ProverShape F)) :
    Triple (addConstraint (F := F) (c := Prover c) con)
      (fun st => .up (ConstraintHolds.Holds st.env.get con ∧ (Q.1 ⟨⟩ st).down)) Q := by
  intro st h
  exact h

/-- Witnessing a field element: when the computation succeeds with `v` at the current table,
the fresh cell reads `v` at the state allocating it, which extends the current one. A gadget's
proof passes it instantiated at the value its advice computes, which no context fact pins. -/
theorem Prover.witnessF_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (compute : AsProver F F) (v : F) (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ compute.run st.env = .ok v⌝⦄
    witness (c := Prover c) (val := F) compute
    ⦃⇓ r st' => ⌜CircuitType.ReadsAs (val := F) st' r v ∧ st₀ ≤ st'⌝⦄ := by
  rintro st ⟨rfl, h⟩
  show (proverWP (c := Prover c) (witness (c := Prover c) (val := F) compute) _ _ st).down
  simp only [Snarky.witness, proverWP, AsProver.map_eq, AsProver.run_bind, h, Except.bind,
    AsProver.run_pure, CheckedType.check]
  change CircuitType.ReadsAs (val := F) (st.alloc (CircuitType.valueToFields (F := F) v))
      (CircuitType.fieldsToVar (F := F) (val := F)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F F)))) v ∧
    st ≤ st.alloc (CircuitType.valueToFields (F := F) v)
  refine ⟨⟨?_, ?_⟩, st.dom.le_extendList _⟩
  · intro cv hcv
    rw [CircuitType.var_roundTrip, toList_mapVec, List.mem_map] at hcv
    obtain ⟨w, hw, rfl⟩ := hcv
    exact show w < st.nv + CircuitType.size F F from (List.mem_range'_1.mp hw).2
  · unfold CircuitType.Reads
    rw [CircuitType.var_roundTrip]
    ext i hi
    simp only [getElem_mapVec, getElem_allocRange, CVar.val, ProverState.get_alloc]
    simp [Assignments.get, Assignments.extendList_get
      (show i < (CircuitType.valueToFields (F := F) v).toList.length by simpa using hi)]

/-! ## The pilot: `inv`, `mul`, and `div` by composition -/

/-- `inv`'s completeness: where the operand reads nonzero the run succeeds and the result reads
the inverse. -/
@[spec] theorem Prover.inv_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) (xv : F) (hne : xv ≠ 0)
    (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ CircuitType.ReadsAs (val := F) st x xv⌝⦄
    inv (c := Prover c) x
    ⦃⇓ r st' => ⌜CircuitType.ReadsAs (val := F) st' r xv⁻¹ ∧ st₀ ≤ st'⌝⦄ := by
  unfold inv
  have hw := Prover.witnessF_spec (c := c) (compute := inv.advice x) (v := xv⁻¹)
  mvcgen [hw]
  case h_1.isTrue.pre =>
    rename_i a hxa ha s h
    exact absurd ((CircuitType.reads_fvar.mp h.2.2).symm.trans ha) hne
  case h_1.isTrue.post.success =>
    rename_i a hxa ha s₁ h₁ r s h
    exact absurd ((CircuitType.reads_fvar.mp h₁.2.2).symm.trans ha) hne
  case h_1.isFalse =>
    rename_i a hxa ha s h
    have hv : xv = a := (CircuitType.reads_fvar.mp h.2.2).symm
    exact ⟨⟨CircuitType.scoped_fvar.mpr (CVar.scoped_const _ _),
      CircuitType.reads_fvar.mpr (by rw [hv]; rfl)⟩, le_of_eq h.1.symm⟩
  case h_2.pre =>
    rename_i x' hnc hxx s h
    subst hxx
    refine ⟨trivial, ?_⟩
    simp [inv.advice, readVar_run h.2.1, CircuitType.readVal_fvar,
      CircuitType.reads_fvar.mp h.2.2, hne]
  case h_2.post.success =>
    rename_i x' hnc hxx s₁ h₁ r s h
    subst hxx
    refine ⟨(LawfulBasicSystem.holds_r1cs ..).mpr ?_, ?_⟩
    · rw [CVar.val_of_le h.2 (CircuitType.scoped_fvar.mp h₁.2.1),
        CircuitType.reads_fvar.mp h₁.2.2, CircuitType.reads_fvar.mp h.1.2]
      simp [hne]
    · exact (show CircuitType.ReadsAs (val := F) s r xv⁻¹ ∧ st₀ ≤ s from ⟨h.1, h₁.1 ▸ h.2⟩)

/-- `mul`'s completeness: the result reads the product. -/
@[spec] theorem Prover.mul_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (xv yv : F)
    (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ CircuitType.ReadsAs (val := F) st x xv ∧
        CircuitType.ReadsAs (val := F) st y yv⌝⦄
    mul (c := Prover c) x y
    ⦃⇓ r st' => ⌜CircuitType.ReadsAs (val := F) st' r (xv * yv) ∧ st₀ ≤ st'⌝⦄ := by
  unfold mul
  -- the leaf spec at the advice's value, over the operands the branches substitute
  have hw := fun x y : FVar F =>
    Prover.witnessF_spec (c := c) (compute := mul.advice x y) (v := xv * yv)
  mvcgen [hw]
  case h_1 =>
    rename_i a b hy hx s h
    have ha : xv = a := (CircuitType.reads_fvar.mp h.2.1.2).symm
    have hb : yv = b := (CircuitType.reads_fvar.mp h.2.2.2).symm
    exact ⟨⟨CircuitType.scoped_fvar.mpr (CVar.scoped_const _ _),
      CircuitType.reads_fvar.mpr (by rw [ha, hb]; rfl)⟩, le_of_eq h.1.symm⟩
  case h_2 =>
    rename_i a y' hnc hy hx s h
    have ha : xv = a := (CircuitType.reads_fvar.mp h.2.1.2).symm
    exact ⟨⟨CircuitType.scoped_fvar.mpr (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp h.2.2.1)),
      CircuitType.reads_fvar.mpr (by
        rw [CVar.val_scale_, CircuitType.reads_fvar.mp h.2.2.2, ha])⟩, le_of_eq h.1.symm⟩
  case h_3 =>
    rename_i x' b hnc hy hx s h
    have hb : yv = b := (CircuitType.reads_fvar.mp h.2.2.2).symm
    exact ⟨⟨CircuitType.scoped_fvar.mpr (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp h.2.1.1)),
      CircuitType.reads_fvar.mpr (by
        rw [CVar.val_scale_, CircuitType.reads_fvar.mp h.2.1.2, hb, mul_comm])⟩,
      le_of_eq h.1.symm⟩
  case h_4.pre =>
    rename_i x' y' hnc hncx hncy hy hx s h
    refine ⟨trivial, ?_⟩
    simp [mul.advice, AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.1),
      CircuitType.reads_fvar.mp h.2.1.2, CircuitType.reads_fvar.mp h.2.2.2]
  case h_4.post.success =>
    rename_i x' y' hnc hncx hncy hy hx s₁ h₁ r s h
    refine ⟨(LawfulBasicSystem.holds_r1cs ..).mpr ?_, ?_⟩
    · rw [CVar.val_of_le h.2 (CircuitType.scoped_fvar.mp h₁.2.1.1),
        CVar.val_of_le h.2 (CircuitType.scoped_fvar.mp h₁.2.2.1),
        CircuitType.reads_fvar.mp h₁.2.1.2, CircuitType.reads_fvar.mp h₁.2.2.2,
        CircuitType.reads_fvar.mp h.1.2]
    · exact (show CircuitType.ReadsAs (val := F) s r (xv * yv) ∧ st₀ ≤ s from
        ⟨h.1, h₁.1 ▸ h.2⟩)

/-- `div`'s completeness, by composition of the registered `inv` and `mul` specs. -/
theorem Prover.div_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (xv yv : F) (hne : yv ≠ 0)
    (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ CircuitType.ReadsAs (val := F) st x xv ∧
        CircuitType.ReadsAs (val := F) st y yv⌝⦄
    div (c := Prover c) x y
    ⦃⇓ r st' => ⌜CircuitType.ReadsAs (val := F) st' r (xv / yv) ∧ st₀ ≤ st'⌝⦄ := by
  simp only [div]
  mvcgen
  case vc6 => exact fun _ _ => xv
  case vc7 => exact fun _ _ => yv⁻¹
  case vc3.pre =>
    rename_i s h
    exact ⟨trivial, h.2.2⟩
  case vc4.post.success.pre =>
    rename_i s₁ h₁ r s₂ h₂
    exact ⟨trivial, CircuitType.monotone_readsAs h₂.2 h₁.2.1, h₂.1⟩
  case vc5.post.success.post.success =>
    rename_i s₁ h₁ r₁ s₂ h₂ r₂ s₃
    intro hr hle
    exact ⟨by rwa [div_eq_mul_inv], h₁.1 ▸ h₂.2.trans hle⟩

end Snarky
