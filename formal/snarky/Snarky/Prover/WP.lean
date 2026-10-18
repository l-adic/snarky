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

/-! ## The reading vocabulary

A cell's reading at a state is the total function `read`; a spec's values are all readings at
its one ghost, the entry state, so nothing is left for a caller to guess. Two lemmas carry a
cell's scope and reading across a run; they are what `grind` needs at a chain's conditions. -/

/-- A cell's reading at a state. -/
abbrev ProverState.read [Add F] [Mul F] [Zero F] (st : ProverState F) (x : CVar F) : F :=
  x.val st.env.get

/-- A cell in scope stays in scope. -/
theorem CVar.Scoped.of_le {st st' : ProverState F} (hle : st ≤ st') {x : CVar F}
    (hx : x.Scoped st) : x.Scoped st' :=
  hx.mono (ProverState.nv_le_of_le hle)

/-- A scoped cell reads the same at every later state. -/
theorem ProverState.read_of_le [Add F] [Mul F] [Zero F] {st st' : ProverState F}
    (hle : st ≤ st') {x : CVar F} (hx : x.Scoped st) : st'.read x = st.read x :=
  CVar.val_of_le hle hx

/-! ## Primitive specs -/

/-- Emitting a row obliges it at the entry table; the state is unchanged. -/
@[spec] theorem Prover.addConstraint_spec [Zero F] [ConstraintHolds F c] (con : Prover c)
    (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ ConstraintHolds.Holds st₀.env.get con⌝⦄
    addConstraint (F := F) (c := Prover c) con
    ⦃⇓ _ st' => ⌜st' = st₀⌝⦄ := by
  rintro st ⟨rfl, h⟩
  show ConstraintHolds.Holds st.env.get con ∧ st = st
  exact ⟨h, rfl⟩

/-- Witnessing a field element: when the computation succeeds at the entry table, the fresh
cell is in scope and reads whatever the computation returned there, at a state extending the
entry. The value is the computation's, not a free variable, so the spec has one ghost. -/
@[spec] theorem Prover.witnessF_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (compute : AsProver F F) (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ ∃ v, compute.run st₀.env = .ok v⌝⦄
    witness (c := Prover c) (val := F) compute
    ⦃⇓ r st' => ⌜(∀ v, compute.run st₀.env = .ok v → r.Scoped st' ∧ st'.read r = v) ∧
      st₀ ≤ st'⌝⦄ := by
  rintro st ⟨rfl, v₀, h⟩
  show (proverWP (c := Prover c) (witness (c := Prover c) (val := F) compute) _ _ st).down
  simp only [Snarky.witness, proverWP, AsProver.map_eq, AsProver.run_bind, h, Except.bind,
    AsProver.run_pure, CheckedType.check]
  have hscope : CircuitType.Scoped (val := F) (st.alloc (CircuitType.valueToFields (F := F) v₀))
      (CircuitType.fieldsToVar (F := F) (val := F)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F F)))) := by
    intro cv hcv
    rw [CircuitType.var_roundTrip, toList_mapVec, List.mem_map] at hcv
    obtain ⟨w, hw, rfl⟩ := hcv
    exact show w < st.nv + CircuitType.size F F from (List.mem_range'_1.mp hw).2
  have hreads : CircuitType.Reads (st.alloc (CircuitType.valueToFields (F := F) v₀)).env.get
      (CircuitType.fieldsToVar (F := F) (val := F)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F F)))) v₀ := by
    unfold CircuitType.Reads
    rw [CircuitType.var_roundTrip]
    ext i hi
    simp only [getElem_mapVec, getElem_allocRange, CVar.val, ProverState.get_alloc]
    simp [Assignments.get, Assignments.extendList_get
      (show i < (CircuitType.valueToFields (F := F) v₀).toList.length by simpa using hi)]
  change (∀ v, Except.ok v₀ = Except.ok v →
      (CircuitType.fieldsToVar (F := F) (val := F)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F F)))).Scoped
          (st.alloc (CircuitType.valueToFields (F := F) v₀)) ∧
      (st.alloc (CircuitType.valueToFields (F := F) v₀)).read
        (CircuitType.fieldsToVar (F := F) (val := F)
          (mapVec CVar.var (allocRange st.nv (CircuitType.size F F)))) = v) ∧
    st ≤ st.alloc (CircuitType.valueToFields (F := F) v₀)
  refine ⟨fun v hv => ?_, st.dom.le_extendList _⟩
  cases Except.ok.inj hv
  exact ⟨CircuitType.scoped_fvar.mp hscope, CircuitType.reads_fvar.mp hreads⟩

/-! ## The pilot: `inv`, `mul`, `div` by composition, and a chain with reuse -/

/-- `inv`'s completeness: where the operand is in scope and reads nonzero, the run succeeds
and the result reads the inverse of the operand's entry reading. -/
@[spec] theorem Prover.inv_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ x.Scoped st₀ ∧ st₀.read x ≠ 0⌝⦄
    inv (c := Prover c) x
    ⦃⇓ r st' => ⌜r.Scoped st' ∧ st'.read r = (st₀.read x)⁻¹ ∧ st₀ ≤ st'⌝⦄ := by
  unfold inv
  mvcgen
  -- the constant-zero branch is unreachable: its reading is the operand's nonzero reading
  case h_1.isTrue.pre =>
    rename_i a hxa ha s h
    exact absurd ha h.2.2
  case h_1.isTrue.post.success.pre =>
    rename_i a hxa ha s₁ h₁ r s h
    exact absurd ha h₁.2.2
  case h_1.isTrue.post.success.post.success =>
    rename_i a hxa ha s₁ h₁ r s h u s' h'
    exact absurd ha h₁.2.2
  case h_1.isFalse =>
    rename_i a hxa ha s h
    exact ⟨CVar.scoped_const _ _, rfl, le_of_eq h.1.symm⟩
  case h_2.pre =>
    rename_i x' hnc hxx s h
    subst hxx
    obtain ⟨rfl, hxs, hne⟩ := h
    exact ⟨trivial, (s.read x)⁻¹, by
      simp [inv.advice, readVar_run (CircuitType.scoped_fvar.mpr hxs), CircuitType.readVal_fvar,
        hne]⟩
  case h_2.post.success.pre =>
    rename_i x' hnc hxx s₁ h₁ r s h
    subst hxx
    obtain ⟨rfl, hxs, hne⟩ := h₁
    have hrun : (inv.advice x).run s₁.env = .ok (s₁.read x)⁻¹ := by
      simp [inv.advice, readVar_run (CircuitType.scoped_fvar.mpr hxs), CircuitType.readVal_fvar,
        hne]
    obtain ⟨hr, hrv⟩ := h.1 _ hrun
    refine ⟨trivial, (LawfulBasicSystem.holds_r1cs ..).mpr ?_⟩
    rw [CVar.val_of_le h.2 hxs]
    show s₁.read x * s.read r = 1
    rw [hrv]
    exact mul_inv_cancel₀ hne
  case h_2.post.success.post.success =>
    rename_i x' hnc hxx s₁ h₁ r s h u s' h'
    subst hxx h'
    obtain ⟨rfl, hxs, hne⟩ := h₁
    have hrun : (inv.advice x).run s₁.env = .ok (s₁.read x)⁻¹ := by
      simp [inv.advice, readVar_run (CircuitType.scoped_fvar.mpr hxs), CircuitType.readVal_fvar,
        hne]
    obtain ⟨hr, hrv⟩ := h.1 _ hrun
    exact ⟨hr, hrv, h.2⟩

/-- `mul`'s completeness: the result reads the product of the operands' entry readings. -/
@[spec] theorem Prover.mul_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀⌝⦄
    mul (c := Prover c) x y
    ⦃⇓ r st' => ⌜r.Scoped st' ∧ st'.read r = st₀.read x * st₀.read y ∧ st₀ ≤ st'⌝⦄ := by
  unfold mul
  mvcgen
  case h_1 =>
    rename_i a b hy hx s h
    exact ⟨CVar.scoped_const _ _, rfl, le_of_eq h.1.symm⟩
  case h_2 =>
    rename_i a y' hnc hy hx s h
    obtain ⟨rfl, hxs, hys⟩ := h
    exact ⟨CVar.Scoped.scale_ hys, by show (CVar.scale_ a y').val _ = _; rw [CVar.val_scale_]; rfl,
      le_refl _⟩
  case h_3 =>
    rename_i x' b hnc hy hx s h
    obtain ⟨rfl, hxs, hys⟩ := h
    exact ⟨CVar.Scoped.scale_ hxs, by
      show (CVar.scale_ b x').val _ = _; rw [CVar.val_scale_]; exact mul_comm _ _, le_refl _⟩
  case h_4.pre =>
    rename_i x' y' hnc hncx hncy hy hx s h
    obtain ⟨rfl, hxs, hys⟩ := h
    exact ⟨trivial, s.read x' * s.read y', by
      simp [mul.advice, AsProver.readCVar_run hxs, AsProver.readCVar_run hys]⟩
  case h_4.post.success.pre =>
    rename_i x' y' hnc hncx hncy hy hx s₁ h₁ r s h
    obtain ⟨rfl, hxs, hys⟩ := h₁
    have hrun : (mul.advice x' y').run s₁.env = .ok (s₁.read x' * s₁.read y') := by
      simp [mul.advice, AsProver.readCVar_run hxs, AsProver.readCVar_run hys]
    obtain ⟨hr, hrv⟩ := h.1 _ hrun
    refine ⟨trivial, (LawfulBasicSystem.holds_r1cs ..).mpr ?_⟩
    rw [CVar.val_of_le h.2 hxs, CVar.val_of_le h.2 hys]
    exact hrv.symm
  case h_4.post.success.post.success =>
    rename_i x' y' hnc hncx hncy hy hx s₁ h₁ r s h u s' h'
    subst h'
    obtain ⟨rfl, hxs, hys⟩ := h₁
    have hrun : (mul.advice x' y').run s₁.env = .ok (s₁.read x' * s₁.read y') := by
      simp [mul.advice, AsProver.readCVar_run hxs, AsProver.readCVar_run hys]
    obtain ⟨hr, hrv⟩ := h.1 _ hrun
    exact ⟨hr, hrv, h.2⟩

/-- `div`'s completeness, by composition of the registered `inv` and `mul` specs; the
conditions are transport, which `grind` does from the two carrying lemmas. -/
theorem Prover.div_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀ ∧ st₀.read y ≠ 0⌝⦄
    div (c := Prover c) x y
    ⦃⇓ r st' => ⌜r.Scoped st' ∧ st'.read r = st₀.read x / st₀.read y ∧ st₀ ≤ st'⌝⦄ := by
  simp only [div]
  mvcgen
  all_goals grind [ProverState.read_of_le, CVar.Scoped.of_le, div_eq_mul_inv]

/-- A six-step chain reusing early results late: `a` at step 5, `c` at step 6, so the
conditions carry readings across up to four runs. -/
def chain6 [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (x y : FVar F) : CircuitM F c (FVar F) := do
  let a ← mul x y
  let b ← mul a x
  let cc ← inv b
  let d ← mul cc y
  let e ← mul d a
  let f ← mul e cc
  pure f

/-- The chain's completeness, with no transport written by hand. -/
theorem Prover.chain6_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀ ∧ st₀.read x * st₀.read y * st₀.read x ≠ 0⌝⦄
    chain6 (c := Prover c) x y
    ⦃⇓ r st' => ⌜r.Scoped st' ∧
      st'.read r = (st₀.read x * st₀.read y * st₀.read x)⁻¹ * st₀.read y *
        (st₀.read x * st₀.read y) * (st₀.read x * st₀.read y * st₀.read x)⁻¹ ∧
      st₀ ≤ st'⌝⦄ := by
  simp only [chain6]
  mvcgen
  all_goals grind [ProverState.read_of_le, CVar.Scoped.of_le]

/-- A twelve-step chain, every result reused later, for the cost of the conditions at length. -/
def chain12 [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (x y : FVar F) : CircuitM F c (FVar F) := do
  let a ← mul x y
  let b ← mul a x
  let cc ← inv b
  let d ← mul cc y
  let e ← mul d a
  let f ← mul e cc
  let g ← mul f b
  let h ← inv g
  let i ← mul h d
  let j ← mul i e
  let k ← mul j f
  let l ← mul k h
  pure l

/-- The twelve-step chain's completeness, the same two lines. -/
theorem Prover.chain12_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F)
    (hb : st₀.read x * st₀.read y * st₀.read x ≠ 0)
    (hg : (st₀.read x * st₀.read y * st₀.read x)⁻¹ * st₀.read y * (st₀.read x * st₀.read y) *
      (st₀.read x * st₀.read y * st₀.read x)⁻¹ * (st₀.read x * st₀.read y * st₀.read x) ≠ 0) :
    ⦃fun st => ⌜st = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀⌝⦄
    chain12 (c := Prover c) x y
    ⦃⇓ r st' => ⌜r.Scoped st' ∧ st₀ ≤ st'⌝⦄ := by
  simp only [chain12]
  mvcgen
  all_goals grind (ematch := 20) (gen := 20) (instances := 5000)
    [ProverState.read_of_le, CVar.Scoped.of_le]

/-- `isZero`'s completeness: the bit reads `1` exactly where the operand reads `0`. -/
@[spec] theorem Prover.isZero_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ x.Scoped st₀⌝⦄
    isZero (c := Prover c) x
    ⦃⇓ r st' => ⌜(↑r : CVar F).Scoped st' ∧
      st'.read r = (if st₀.read x = 0 then 1 else 0) ∧ st₀ ≤ st'⌝⦄ := by
  unfold isZero
  mvcgen
  case h_1 =>
    rename_i a hxa s h
    exact ⟨CVar.scoped_const _ _, rfl, le_of_eq h.1.symm⟩
  case h_2.pre =>
    rename_i x' hnc hxx s h
    subst hxx
    obtain ⟨rfl, hxs⟩ := h
    exact ⟨trivial, if s.read x = 0 then 1 else 0, by
      simp [isZero.bitAdvice, AsProver.readCVar_run hxs]⟩
  case h_2.post.success.pre =>
    rename_i x' hnc hxx s₀ h₀ r₁ s₁ h₁
    subst hxx
    obtain ⟨rfl, hxs⟩ := h₀
    exact ⟨trivial, if s₁.read x = 0 then 0 else (s₁.read x)⁻¹, by
      simp [isZero.invAdvice, AsProver.readCVar_run (CVar.Scoped.of_le h₁.2 hxs)]⟩
  case h_2.post.success.post.success.pre =>
    rename_i x' hnc hxx s₀ h₀ r₁ s₁ h₁ r₂ s₂ h₂
    subst hxx
    obtain ⟨rfl, hxs⟩ := h₀
    have hrun₁ : (isZero.bitAdvice x).run s₀.env = .ok (if s₀.read x = 0 then 1 else 0) := by
      simp [isZero.bitAdvice, AsProver.readCVar_run hxs]
    obtain ⟨hr₁, hr₁v⟩ := h₁.1 _ hrun₁
    refine ⟨trivial, (LawfulBasicSystem.holds_r1cs ..).mpr ?_⟩
    rw [CVar.val_of_le h₂.2 hr₁, CVar.val_of_le (h₁.2.trans h₂.2) hxs]
    show s₁.read r₁ * s₀.read x = 0
    rw [hr₁v]
    split <;> simp [*]
  case h_2.post.success.post.success.post.success.pre =>
    rename_i x' hnc hxx s₀ h₀ r₁ s₁ h₁ r₂ s₂ h₂ u₁ s₃ h₃
    subst hxx h₃
    obtain ⟨rfl, hxs⟩ := h₀
    have hrun₁ : (isZero.bitAdvice x).run s₀.env = .ok (if s₀.read x = 0 then 1 else 0) := by
      simp [isZero.bitAdvice, AsProver.readCVar_run hxs]
    have hrun₂ : (isZero.invAdvice x).run s₁.env =
        .ok (if s₁.read x = 0 then 0 else (s₁.read x)⁻¹) := by
      simp [isZero.invAdvice, AsProver.readCVar_run (CVar.Scoped.of_le h₁.2 hxs)]
    obtain ⟨hr₁, hr₁v⟩ := h₁.1 _ hrun₁
    obtain ⟨hr₂, hr₂v⟩ := h₂.1 _ hrun₂
    refine ⟨trivial, (LawfulBasicSystem.holds_r1cs ..).mpr ?_⟩
    rw [CVar.val_sub_, CVar.val_of_le (h₁.2.trans h₂.2) hxs, CVar.val_of_le h₂.2 hr₁]
    show s₃.read r₂ * s₀.read x = 1 - s₁.read r₁
    rw [hr₂v, hr₁v, ProverState.read_of_le h₁.2 hxs]
    split
    · simp [*]
    · simp [inv_mul_cancel₀ ‹_›]
  case h_2.post.success.post.success.post.success.post.success =>
    rename_i x' hnc hxx s₀ h₀ r₁ s₁ h₁ r₂ s₂ h₂ u₁ s₃ h₃ u₂ s₄ h₄
    subst hxx h₃ h₄
    obtain ⟨rfl, hxs⟩ := h₀
    have hrun₁ : (isZero.bitAdvice x).run s₀.env = .ok (if s₀.read x = 0 then 1 else 0) := by
      simp [isZero.bitAdvice, AsProver.readCVar_run hxs]
    obtain ⟨hr₁, hr₁v⟩ := h₁.1 _ hrun₁
    exact ⟨CVar.Scoped.of_le h₂.2 hr₁, by
      show s₄.read r₁ = _
      rw [ProverState.read_of_le h₂.2 hr₁, hr₁v], h₁.2.trans h₂.2⟩

/-! ## Traversal: the `List.mapM` and `Vector.mapM` laws

Higher-order specs, proved once: an element spec quantified over its entry state, with the
precondition "in scope at the entry and a condition on its reading there" and the postcondition
"the result reads a function of that reading", gives the traversal's spec with every element's
precondition at the traversal's entry and every result's reading in terms of it. The list law is
the induction against `List.mapM_nil` and `List.mapM_cons`; the vector law reads it per index,
the shape `grind` carries through later runs. Neither is `@[spec]`: the reading condition and
function are not determined by the program, so a use site passes the law instantiated, as the
soundness side passes `builder_spec_mapM`. -/

/-- The `List.mapM` law. -/
theorem Prover.mapM_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (f : FVar F → CircuitM F (Prover c) (FVar F)) (p : F → Prop) (g : F → F)
    (hf : ∀ (st : ProverState F) (x : FVar F),
      ⦃fun s => ⌜s = st ∧ x.Scoped st ∧ p (st.read x)⌝⦄
      f x
      ⦃⇓ r s' => ⌜r.Scoped s' ∧ s'.read r = g (st.read x) ∧ st ≤ s'⌝⦄) :
    ∀ (xs : List (FVar F)) (st₀ : ProverState F),
      ⦃fun s => ⌜s = st₀ ∧ ∀ x ∈ xs, x.Scoped st₀ ∧ p (st₀.read x)⌝⦄
      xs.mapM f
      ⦃⇓ rs s' => ⌜List.Forall₂ (fun x r => r.Scoped s' ∧ s'.read r = g (st₀.read x)) xs rs ∧
        st₀ ≤ s'⌝⦄
  | [], st₀ => by
    rw [List.mapM_nil]
    mvcgen
    rename_i s h
    exact ⟨.nil, le_of_eq h.1.symm⟩
  | x :: xs, st₀ => by
    rw [List.mapM_cons]
    have ih := Prover.mapM_spec f p g hf xs
    mvcgen [hf, ih]
    case pre => grind
    case post.success.pre => grind [ProverState.read_of_le, CVar.Scoped.of_le]
    case post.success.post.success =>
      rename_i s h r s₁ hr rs s₂ hrs
      obtain ⟨rfl, hmem⟩ := h
      refine ⟨.cons ⟨hr.1.of_le hrs.2, by rw [ProverState.read_of_le hrs.2 hr.1, hr.2.1]⟩ ?_,
        hr.2.2.trans hrs.2⟩
      exact ((List.forall₂_and_left xs rs).mpr
        ⟨fun y hy => (hmem y (List.mem_cons_of_mem _ hy)).1, hrs.1⟩).imp
          fun y r' ⟨hy, hs, hv⟩ => ⟨hs, by rw [hv, ProverState.read_of_le hr.2.2 hy]⟩

/-- A specification of `f <$> m` is one of `m` read through `f`. -/
theorem Prover.spec_of_map [Zero F] [ConstraintHolds F c] {α β : Type}
    (m : CircuitM F (Prover c) α) (f : α → β) {P : Assertion (ProverShape F)}
    {Q : PostCond β (ProverShape F)} (h : Triple (f <$> m) P Q) :
    Triple m P (fun a => Q.1 (f a), Q.2) := by
  intro s hs
  have hb := h s hs
  rw [CircuitM.map_eq] at hb
  change (proverWP (c := Prover c) (m >>= fun a => pure (f a)) Q.1 Q.2.1 s).down at hb
  rw [proverWP_bind] at hb
  exact hb

/-- The `Vector.mapM` law: the list law's postcondition read per index. -/
theorem Prover.vector_mapM_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    {n : ℕ} (f : FVar F → CircuitM F (Prover c) (FVar F)) (p : F → Prop) (g : F → F)
    (hf : ∀ (st : ProverState F) (x : FVar F),
      ⦃fun s => ⌜s = st ∧ x.Scoped st ∧ p (st.read x)⌝⦄
      f x
      ⦃⇓ r s' => ⌜r.Scoped s' ∧ s'.read r = g (st.read x) ∧ st ≤ s'⌝⦄)
    (xs : Vector (FVar F) n) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ ∀ i : Fin n, xs[i].Scoped st₀ ∧ p (st₀.read xs[i])⌝⦄
    xs.mapM f
    ⦃⇓ rs s' => ⌜(∀ i : Fin n, rs[i].Scoped s' ∧ s'.read rs[i] = g (st₀.read xs[i])) ∧
      st₀ ≤ s'⌝⦄ := by
  have hl := Prover.mapM_spec f p g hf xs.toList st₀
  have heq : (fun rs : Vector (FVar F) n => rs.toList) <$> xs.mapM f = xs.toList.mapM f := by
    rw [← Vector.toList_toArray, ← Array.toList_mapM, ← Vector.toArray_mapM, ← comp_map]
    rfl
  rw [← heq] at hl
  refine Triple.of_entails_wp (Triple.entails_wp_of_pre_post (Prover.spec_of_map _ _ hl) ?_ ?_)
  · rintro s ⟨rfl, hpre⟩
    refine ⟨rfl, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simpa using hpre ⟨i, by simpa using hi⟩
  · refine ⟨fun rs s' ⟨h, hle⟩ => ⟨fun i => ?_, hle⟩, .rfl⟩
    have hg := (List.forall₂_iff_get.mp h).2 i (by simp) (by simp)
    simpa using hg

/-- Invert every entry, then one more gadget: the vector law at a use site, its readings carried
through a later run. -/
def invAllThenSquare [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] {n : ℕ}
    (xs : Vector (FVar F) n) (y : FVar F) : CircuitM F c (Vector (FVar F) n × FVar F) := do
  let rs ← xs.mapM (inv (c := c))
  let z ← mul y y
  pure (rs, z)

theorem Prover.invAllThenSquare_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {n : ℕ} (xs : Vector (FVar F) n) (y : FVar F)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ y.Scoped st₀ ∧ ∀ i : Fin n, xs[i].Scoped st₀ ∧ st₀.read xs[i] ≠ 0⌝⦄
    invAllThenSquare (c := Prover c) xs y
    ⦃⇓ r s' => ⌜(∀ i : Fin n, r.1[i].Scoped s' ∧ s'.read r.1[i] = (st₀.read xs[i])⁻¹) ∧
      r.2.Scoped s' ∧ s'.read r.2 = st₀.read y * st₀.read y ∧ st₀ ≤ s'⌝⦄ := by
  have hmap := Prover.vector_mapM_spec (c := c) (n := n) (inv (c := Prover c)) (fun v : F => v ≠ 0)
    (fun v => v⁻¹) fun st x => Prover.inv_spec x st
  simp only [invAllThenSquare]
  mvcgen [hmap]
  all_goals grind [ProverState.read_of_le, CVar.Scoped.of_le]

end Snarky
