import Snarky.Prover.StableWP
import Snarky.Witness
import Snarky.Traverse
import Lean.Elab.Tactic.VCGen.FrameProc

/-!
# Prover verification conditions and reusable contracts

Automatic framing retains the current precondition across a prover call; checked-type,
witness and traversal specs compose without operational states or reading-transport premises.
-/

namespace Snarky.Prover

open Std.WP

/-! ## Automatic framing -/

open Lean.Elab.Tactic.VCGen

/-- Retain the entire precondition at calls interpreted by the boxed prover transformer. -/
@[frameproc] private def persistentFrameProc : FrameProc where
  prog := ``Snarky.CircuitM
  opHead := ``Lean.Order.meet
  mkOpAppM info := Lean.Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]
  mkResourceTy info := pure info.Pred
  proc info := do
    let app := info.unframedApp
    let prog ← Lean.Meta.whnfR app.Prog
    if prog.isAppOfArity ``CircuitM 3 then
      let field := prog.getAppArgs[0]!
      let tag ← Lean.Meta.whnfR prog.getAppArgs[1]!
      if tag.isAppOf ``Snarky.Prover then
        if ← Lean.Meta.isDefEq app.Pred (Lean.mkApp (Lean.mkConst ``Pred) field) then
          let expected ← Lean.Meta.mkAppOptM ``instStdWP
            #[field, tag.getAppArgs[0]!, app.Value, none, none]
          if ← Lean.Meta.withTransparency .default (Lean.Meta.isDefEq app.instWP expected) then
            return .ofFrame info info.pre
    defaultFrameInferenceProc info

/-! ## Checked types and witness allocation

`CheckSpec` is the check interface: a checked type's check keeps a reading of an admissible
value. The witness law uses only this interface, with validity and successful advice as its
premises.
-/

section Witness

/-- A check preserves a scoped reading of an admissible value and satisfies its constraints. -/
class CheckSpec (F c val var : Type) [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F val var] [CheckedType F (Prover c) val var] : Prop where
  /-- The check's persistent contract; no entry-state parameter is required. -/
  check : ∀ (r : var) (v : val),
    CheckedType.Valid (F := F) (c := Prover c) (var := var) v →
    ⦃Reads r v⦄ CheckedType.check (F := F) (c := Prover c) (val := val) r
    ⦃fun _ ↦ Reads r v⦄

/-- Apply a checked type's assertion contract directly. -/
@[spec] theorem Spec.check [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F val var] [CheckedType F (Prover c) val var] [CheckSpec F c val var]
    (r : var) (v : val) (hv : CheckedType.Valid (F := F) (c := Prover c) (var := var) v) :
    ⦃Reads r v⦄ CheckedType.check (F := F) (c := Prover c) (val := val) r
    ⦃fun _ ↦ Reads r v⦄ := CheckSpec.check r v hv

/-- Freshly allocated fields decode to the value that was assigned to them. -/
private theorem Reads.allocated [Field F] [CircuitType F val var] (s : ProverState F) (v : val) :
    Reads (CircuitType.fieldsToVar (F := F) (val := val)
      (mapVec CVar.var (allocRange s.nv (CircuitType.size F val)))) v
      (s.alloc (CircuitType.valueToFields (F := F) v)) := by
  have hscope : CircuitType.Scoped (val := val)
      (s.alloc (CircuitType.valueToFields (F := F) v))
      (CircuitType.fieldsToVar (F := F) (val := val)
        (mapVec CVar.var (allocRange s.nv (CircuitType.size F val)))) := by
    intro cv hcv
    rw [CircuitType.var_roundTrip, toList_mapVec, List.mem_map] at hcv
    obtain ⟨w, hw, rfl⟩ := hcv
    exact show w < s.nv + CircuitType.size F val from (List.mem_range'_1.mp hw).2
  have hreads : CircuitType.Reads (s.alloc (CircuitType.valueToFields (F := F) v)).env.get
      (CircuitType.fieldsToVar (F := F) (val := val)
        (mapVec CVar.var (allocRange s.nv (CircuitType.size F val)))) v := by
    unfold CircuitType.Reads
    rw [CircuitType.var_roundTrip]
    ext i hi
    simp only [getElem_mapVec, getElem_allocRange, CVar.val, ProverState.get_alloc]
    simp [Assignments.get, Assignments.extendList_get
      (show i < (CircuitType.valueToFields (F := F) v).toList.length by simpa using hi)]
  exact ⟨hscope, hreads⟩

/-- Successful advice for an admissible value allocates a scoped bundle reading that value. -/
@[spec] theorem Spec.witness [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F val var] [CheckedType F (Prover c) val var] [CheckSpec F c val var]
    (compute : AsProver F val) (v : val)
    (hv : CheckedType.Valid (F := F) (c := Prover c) (var := var) v) :
    ⦃Advice compute v⦄ Snarky.witness (c := Prover c) compute ⦃fun r ↦ Reads r v⦄ := by
  rw [triple_iff]
  intro s hs
  have hmap : (CircuitType.valueToFields (F := F) <$> compute).run s.env =
      .ok (CircuitType.valueToFields (F := F) v) := by
    change compute.run s.env = .ok v at hs
    simp [AsProver.map_eq, AsProver.run_bind, hs, Except.bind, AsProver.run_pure]
  unfold raw
  simp only [Snarky.witness, proverWP, hmap, proverWP_bind]
  exact (triple_iff _ _ _ _).mp (CheckSpec.check _ v hv) _ (Reads.allocated s v)

end Witness

/-! ## Traversals

Input facts and earlier output facts survive later iterations by the general frame law.
The accumulator's mathematical value is separate from its circuit bundle; no operational
state appears in the traversal contracts.
-/

section Traverse

/-- Pointwise readings of a concrete list against its mathematical values. -/
noncomputable def All₂ (R : α → β → Pred F) : List α → List β → Pred F
  | [], [] => ⊤
  | x :: xs, y :: ys => R x y ⊓ All₂ R xs ys
  | _, _ => ⊥

/-- The mathematical outputs of an accumulating traversal. -/
def scan (g : A → X → A) (h : A → X → Y) : A → List X → List Y
  | _, [] => []
  | a, x :: xs => h a x :: scan g h (g a x) xs

/-- Universal quantification over the entries of a list, inside the assertion language. -/
noncomputable def Every (P : α → Pred F) : List α → Pred F
  | [] => ⊤
  | x :: xs => P x ⊓ Every P xs

/-- Evaluating a paired assertion includes the lengths as well as each pair's fact. -/
theorem All₂.apply (R : α → β → Pred F) (xs : List α) (ys : List β)
    (s : ProverState F) :
    All₂ R xs ys s ↔ List.Forall₂ (fun x y ↦ R x y s) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [All₂]
  | cons x xs ih => cases ys <;> simp [All₂, ih]

/-- Evaluating the input conjunction requires every entry's assertion. -/
theorem Every.apply (P : α → Pred F) (xs : List α) (s : ProverState F) :
    Every P xs s ↔ ∀ x ∈ xs, P x s := by
  induction xs with
  | nil => simp [Every]
  | cons x xs ih => simp [Every, ih]

/-- On equal-length vectors the paired assertion is exactly the indexed assertion. -/
theorem All₂.vector_eq (R : α → β → Pred F) (xs : Vector α n) (ys : Vector β n) :
    All₂ R xs.toList ys.toList = ⨅ i : Fin n, R xs[i] ys[i] := by
  apply Pred.ext
  intro s
  simp only [All₂.apply, Pred.iInf_apply, List.forall₂_iff_get]
  constructor
  · rintro ⟨_, h⟩ i
    exact h i.val (by simp) (by simp)
  · intro h
    exact ⟨by simp, fun i hi _ ↦ h ⟨i, by simpa using hi⟩⟩

variable {F c : Type} [Zero F] [ConstraintHolds F c]

private theorem impossible (x : CircuitM F (Prover c) α) (Q : α → Pred F) :
    ⦃(⊥ : Pred F)⦄ x ⦃Q⦄ := ⟨fun _ h ↦ h.elim⟩

/-- No trace of machine states: the result contains all output readings and the final fold. -/
theorem Spec.mapAccumM {σ α β A X Y : Type}
    (f : σ → α → CircuitM F (Prover c) (β × σ))
    (Acc : σ → A → Pred F) (Input : α → X → Pred F)
    (Output : β → Y → Pred F) (g : A → X → A) (h : A → X → Y)
    (step : ∀ acc a x v,
      ⦃Acc acc a ⊓ Input x v⦄ f acc x ⦃fun p ↦ Output p.1 (h a v) ⊓ Acc p.2 (g a v)⦄) :
    ∀ init a xs vs,
      ⦃Acc init a ⊓ All₂ Input xs vs⦄ Snarky.mapAccumM f init xs
      ⦃fun p ↦ All₂ Output p.1 (scan g h a vs) ⊓ Acc p.2 (vs.foldl g a)⦄ := by
  intro init a xs
  induction xs generalizing init a with
  | nil =>
    intro vs
    cases vs with
    | nil =>
      simp only [Snarky.mapAccumM, All₂, scan, List.foldl_nil]
      vcgen
      simp only [All₂]
      prover_assert
    | cons v vs =>
      simp only [All₂, inf_bot_eq]
      exact impossible _ _
  | cons x xs ih =>
    intro vs
    cases vs with
    | nil =>
      simp only [All₂, inf_bot_eq]
      exact impossible _ _
    | cons v vs =>
      have hs := fun acc ↦ step acc a x v
      have ht := fun acc ↦ ih acc (g a v) vs
      simp only [Snarky.mapAccumM, All₂, scan, List.foldl_cons]
      vcgen [hs, ht] <;> (try simp only [All₂]) <;> prover_assert

/-- Traversal without result collection retains each iteration's persistent postcondition. -/
theorem Spec.forM (f : α → CircuitM F (Prover c) PUnit) (P Q : α → Pred F)
    (step : ∀ x, ⦃P x⦄ f x ⦃fun _ ↦ Q x⦄)
    (xs : List α) :
    ⦃Every P xs⦄ xs.forM f ⦃fun _ ↦ Every Q xs⦄ := by
  induction xs with
  | nil =>
    rw [List.forM, Every]
    vcgen
    simp only [Every]
    prover_assert
  | cons x xs ih =>
    rw [List.forM, Every]
    have hs := step x
    vcgen [hs, ih] <;> (try simp only [Every]) <;> prover_assert

/-- Paired vector traversal retains every input condition and every earlier output fact. -/
theorem Spec.zipWithVecM {α β γ : Type} {n : Nat}
    (f : α → β → CircuitM F (Prover c) γ) (P : α → β → Pred F)
    (Q : α → β → γ → Pred F)
    (step : ∀ x y, ⦃P x y⦄ f x y ⦃Q x y⦄)
    (xs : Vector α n) (ys : Vector β n) :
    ⦃⨅ i : Fin n, P xs[i] ys[i]⦄ Snarky.zipWithVecM f xs ys
    ⦃fun rs ↦ ⨅ i : Fin n, Q xs[i] ys[i] rs[i]⦄ := by
  induction n with
  | zero =>
    rw [Snarky.zipWithVecM_zero]
    vcgen
    all_goals prover_assert
  | succ n ih =>
    have hinit := ih (Vector.ofFn fun i ↦ xs[i.castSucc])
      (Vector.ofFn fun i ↦ ys[i.castSucc])
    have hlast := step xs[Fin.last n] ys[Fin.last n]
    rw [Snarky.zipWithVecM_succ]
    vcgen [hinit, hlast]
    all_goals prover_assert with
      simp [Fin.forall_fin_succ'] at *
      grind

end Traverse

/-! ## Bundle readings under vector layouts -/

/-- A vector reading is the conjunction of its entries' readings, including their scope. -/
theorem Reads.vector_eq [Add F] [Mul F] [Zero F] [CircuitType F val var]
    (xs : Vector var n) (vs : Vector val n) :
    Reads (F := F) xs vs = ⨅ i : Fin n, Reads xs[i] vs[i] := by
  apply Pred.ext
  intro s
  rw [Pred.iInf_apply]
  change CircuitType.ReadsAs s xs vs ↔ ∀ i : Fin n, CircuitType.ReadsAs s xs[i] vs[i]
  simp only [CircuitType.ReadsAs, CircuitType.scoped_vector, CircuitType.reads_vector]
  constructor
  · rintro ⟨hs, hr⟩ i
    exact ⟨hs i.val i.isLt, hr i.val i.isLt⟩
  · intro h
    exact ⟨fun i hi ↦ (h ⟨i, hi⟩).1, fun i hi ↦ (h ⟨i, hi⟩).2⟩

/-- Bundle encoding equivalences preserve the persistent reading assertion. -/
theorem Reads.ofEquiv {F a va b vb : Type} [Add F] [Mul F] [Zero F] [CircuitType F a va]
    (ev : b ≃ a) (ew : vb ≃ va) (r : vb) (v : b) :
    @Reads F b vb _ _ _ (CircuitType.ofEquiv ev ew) r v = Reads (ew r) (ev v) := by
  apply Pred.ext
  intro s
  change @CircuitType.ReadsAs F b vb _ _ _ (CircuitType.ofEquiv ev ew) s r v ↔ _
  simp only [CircuitType.ReadsAs, CircuitType.scoped_ofEquiv, CircuitType.reads_ofEquiv]
  rfl

/-- Chunking preserves all the readings required by a block traversal. -/
theorem Reads.chunk [Add F] [Mul F] [Zero F] {m n : Nat}
    (xs : Vector (FVar F) (m * n)) (vs : Vector F (m * n)) :
    Reads (F := F) xs vs ≤ All₂ (Reads (F := F)) (chunkVec xs).toList (chunkVec vs).toList := by
  intro st hs
  change Reads xs vs st at hs
  change All₂ (Reads (F := F)) (chunkVec xs).toList (chunkVec vs).toList st
  rw [All₂.apply, List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i h1 h2
  simp only [List.get_eq_getElem, Vector.getElem_toList]
  constructor
  · apply CircuitType.scoped_vector.mpr
    intro j hj
    rw [getElem_chunkVec]
    exact CircuitType.scoped_vector.mp hs.1 _ _
  · apply CircuitType.reads_vector.mpr
    intro j hj
    rw [getElem_chunkVec, getElem_chunkVec]
    exact CircuitType.reads_vector.mp hs.2 _ _

/-! ## The checked types' contracts

The concrete types' checks keep a reading: a field element and an unchecked bundle emit
nothing, a bit emits its `boolean` row, and the formers compose their components' contracts.
-/

section CheckSpecInstances

variable {F c : Type} [Field F] [BasicSystem F c] [ConstraintHolds F c]

instance instCheckSpecFVar : CheckSpec F c F (FVar F) where
  check r v _ := by
    show ⦃Reads r v⦄ (pure PUnit.unit : CircuitM F (Prover c) PUnit) ⦃fun _ ↦ Reads r v⦄
    vcgen

instance instCheckSpecBool [DecidableEq F] [NeZero (1 : F)] [LawfulBasicSystem F c] :
    CheckSpec F c Bool (BoolVar F) where
  check r v _ := by
    show ⦃Reads r v⦄
      addConstraint (F := F) (c := Prover c) (BasicSystem.boolean (c := Prover c) r.toCVar)
      ⦃fun _ ↦ Reads r v⦄
    vcgen
    all_goals prover_assert with
      (cases v <;> simp_all [Reads.boolVar_apply, Checked.apply,
        LawfulBasicSystem.holds_boolean, LawfulBasicSystem.cells_boolean, bit])

instance instCheckSpecUnChecked {val var : Type} [CircuitType F val var] :
    CheckSpec F c (UnChecked val) (UnChecked var) where
  check r v _ := by
    show ⦃Reads r v⦄ (pure PUnit.unit : CircuitM F (Prover c) PUnit) ⦃fun _ ↦ Reads r v⦄
    vcgen

instance instCheckSpecProd {a va b vb : Type} [CircuitType F a va] [CircuitType F b vb]
    [CheckedType F (Prover c) a va] [CheckedType F (Prover c) b vb] [CheckSpec F c a va]
    [CheckSpec F c b vb] : CheckSpec F c (a × b) (va × vb) where
  check p v hv := by
    have h1 := CheckSpec.check (c := c) p.1 v.1 (valid_prod.mp hv).1
    have h2 := CheckSpec.check (c := c) p.2 v.2 (valid_prod.mp hv).2
    show ⦃Reads p v⦄ (do CheckedType.check (c := Prover c) (val := a) p.1
                         CheckedType.check (c := Prover c) (val := b) p.2) ⦃fun _ ↦ Reads p v⦄
    vcgen [h1, h2]
    all_goals prover_assert with (intros; simp_all [Reads.prod_apply])

/-- The entries' checks in turn keep every entry's reading. -/
private theorem Spec.checkAll {a va : Type} [CircuitType F a va] [CheckedType F (Prover c) a va]
    [CheckSpec F c a va] :
    ∀ (l : List va) (vs : List a),
      (∀ v ∈ vs, CheckedType.Valid (F := F) (c := Prover c) (var := va) v) →
      ⦃All₂ Reads l vs⦄ checkAll (F := F) (c := Prover c) (a := a) l ⦃fun _ ↦ All₂ Reads l vs⦄
  | [], [], _ => by
    simp only [All₂]
    change ⦃(⊤ : Pred F)⦄ (pure PUnit.unit : CircuitM F (Prover c) PUnit) ⦃fun _ ↦ (⊤ : Pred F)⦄
    vcgen
  | [], _ :: _, _ => by
    simp only [All₂]
    exact impossible _ _
  | _ :: _, [], _ => by
    simp only [All₂]
    exact impossible _ _
  | r :: l, v :: vs, hv => by
    have h := CheckSpec.check (c := c) r v (hv v (List.mem_cons_self ..))
    have ih := Spec.checkAll l vs fun w hw ↦ hv w (List.mem_cons_of_mem _ hw)
    simp only [All₂]
    change ⦃Reads r v ⊓ All₂ Reads l vs⦄
      (do CheckedType.check (c := Prover c) (val := a) r
          Snarky.checkAll (F := F) (c := Prover c) (a := a) l)
        ⦃fun _ ↦ Reads r v ⊓ All₂ Reads l vs⦄
    vcgen [h, ih]
    all_goals prover_assert

instance instCheckSpecVector {a va : Type} [CircuitType F a va] [CheckedType F (Prover c) a va]
    [CheckSpec F c a va] {n : Nat} : CheckSpec F c (Vector a n) (Vector va n) where
  check vs xs hv := by
    have h := Spec.checkAll (c := c) vs.toList xs.toList fun v hv' ↦ by
      obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hv')
      exact valid_vector.mp hv i hi
    show ⦃Reads vs xs⦄ checkAll (F := F) (c := Prover c) (a := a) vs.toList ⦃fun _ ↦ Reads vs xs⦄
    rwa [Reads.vector_eq, ← All₂.vector_eq]

instance instCheckSpecOfEquiv {a va b vb : Type} [CircuitType F a va]
    [S : CheckedType F (Prover c) a va] [CheckSpec F c a va] (ev : b ≃ a) (ew : vb ≃ va) :
    @CheckSpec F c b vb _ _ _ (CircuitType.ofEquiv ev ew) (CheckedType.ofEquiv ev ew) :=
  letI : CircuitType F b vb := CircuitType.ofEquiv ev ew
  letI : CheckedType F (Prover c) b vb := CheckedType.ofEquiv ev ew
  ⟨fun v x hv ↦ by
    rw [Reads.ofEquiv]
    exact CheckSpec.check (c := c) (ew v) (ev x) ((valid_ofEquiv ev ew).mp hv)⟩

end CheckSpecInstances

end Snarky.Prover
