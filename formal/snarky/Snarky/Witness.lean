import Snarky.Prover

/-!
# The witness combinator

`CheckedType` pairs an encoding with the constraint circuit enforcing its
well-formedness; `witness` allocates a bundle, runs the prover's advice, and emits the
check. Its laws — the soundness contract, the run equation, and the completeness law —
are the leaf interface every gadget builds on.
-/

namespace Snarky

/-- Variable bundles whose well-formedness is enforced by constraints: `check` is
emitted by `witness` under both interpreters, with what its rows force about the
bundle (`post`, `check_sound`), that the check is passive at the prover
(`check_runs`), and that an honest encoding satisfies its rows (`check_sat`). The
value type is a parameter because the laws speak of the encoding. -/
class CheckedType (F c val var : Type) [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [CircuitType F val var] where
  /-- The circuit that constrains the bundle to well-formed values (PS `check`). -/
  check : var → CircuitM F c PUnit
  /-- What the check's rows force about the bundle under a valuation. -/
  post : Valuation F → var → Prop
  /-- The rows of `check v`, satisfied at `V`, force `post V v`. -/
  check_sound : ∀ [ConstraintHolds F c] [LawfulBasicSystem F c] (V : Valuation F) (v : var)
    (nv : Nat),
    (∀ con ∈ (build (check v) nv).constraints, ConstraintHolds.Holds V con) → post V v
  /-- The check runs at the prover from any state: it never fails. It MAY allocate
  auxiliaries of its own — the on-curve check witnesses `x²` and `x³` — and, since every
  run only extends the table (`Runs.le`), what was allocated before the check still reads
  the same after it. -/
  check_runs : ∀ (st : ProverState F) (v : var), ∃ st', Runs (check v) st PUnit.unit st'
  /-- A scoped bundle that reads as the encoding of a value satisfies its check's rows,
  at the total reading of any extension of the state the check itself runs to. The run is
  a hypothesis because a check that allocates constrains variables that only its own run
  assigns. -/
  check_sat : ∀ [ConstraintHolds F c] [LawfulBasicSystem F c] {st st' stf : ProverState F}
    (v : var) (a : val), Runs (check v) st PUnit.unit st' →
    st'.nv ≤ stf.nv → st'.env.Le stf.env →
    CircuitType.Scoped (val := val) st v → CircuitType.Reads st.env.get v a →
    Sat (check v) st stf

section Instances

variable {F c : Type}

/-- A field element carries no well-formedness constraint (PS `CheckedType` instance for
`FVar`: `check = const (pure unit)`). -/
instance instCheckedTypeFVar [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] :
    CheckedType F c F (FVar F) where
  check _ := .pure PUnit.unit
  post _ _ := True
  check_sound := by intros; trivial
  check_runs st _ := ⟨st, rfl⟩
  check_sat _ _ _ _ _ _ _ := Sat.pure

/-- A freshly witnessed boolean must be constrained to `{0, 1}`: one `boolean` row, whose
reading is the booleanity every consumer of the bundle assumes. -/
instance instCheckedTypeBool [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [NeZero (1 : F)] [BasicSystem F c] : CheckedType F c Bool (BoolVar F) where
  check b := addConstraint (BasicSystem.boolean b.toCVar)
  post V b := ∃ bb : Bool, (↑b : CVar F).val V = bit bb
  check_sound V b nv hsat := by
    rcases (LawfulBasicSystem.holds_boolean V (↑b)).mp
        (hsat (BasicSystem.boolean b.toCVar) (by simp [Snarky.addConstraint, build])) with h | h
    · exact ⟨false, by simpa [bit] using h⟩
    · exact ⟨true, by simpa [bit] using h⟩
  check_runs st _ := ⟨st, Runs.addConstraint⟩
  check_sat := by
    intro _ _ st _ _ b a hrun _ hle'
    intro hs hr
    have hle := hrun.le.trans hle'
    intro con hcon
    simp [Snarky.addConstraint, build] at hcon
    subst hcon
    refine (LawfulBasicSystem.holds_boolean _ _).mpr ?_
    have hv : (↑b : CVar F).val st.env.get = bit a :=
      congrArg (fun v : Vector F (CircuitType.size F Bool) =>
        v[0]'(show 0 < CircuitType.size F Bool from Nat.one_pos)) hr
    rw [CVar.val_of_le hle (hs _ (List.mem_cons_self ..)), hv]
    cases a <;> simp [bit]

/-- The empty bundle needs no check. -/
instance instCheckedTypeUnit [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] :
    CheckedType F c Unit Unit where
  check _ := .pure PUnit.unit
  post _ _ := True
  check_sound := by intros; trivial
  check_runs st _ := ⟨st, rfl⟩
  check_sat _ _ _ _ _ _ _ := Sat.pure

section Product

variable {a va b vb : Type}

/-- A product is checked factor by factor; its rows concatenate. -/
instance instCheckedTypeProd [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
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
  check_runs st p := by
    obtain ⟨st₁, h₁⟩ := CheckedType.check_runs (c := c) (val := a) st p.1
    obtain ⟨st₂, h₂⟩ := CheckedType.check_runs (c := c) (val := b) st₁ p.2
    exact ⟨st₂, h₁.bind h₂⟩
  check_sat p x hrun hnv hle hs hr := by
    obtain ⟨v, w⟩ := p
    obtain ⟨x, y⟩ := x
    rw [CircuitType.scoped_prod] at hs
    rw [CircuitType.reads_prod] at hr
    obtain ⟨_, st₁, hrun₁, hrun₂⟩ := hrun.bind_inv
    exact Sat.bind hrun₁
      (CheckedType.check_sat v x hrun₁ (Nat.le_trans hrun₂.nv_le hnv)
        (hrun₂.le.trans hle) hs.1 hr.1)
      (CheckedType.check_sat w y hrun₂ hnv hle (hs.2.mono hrun₁.nv_le)
        (hr.2.of_le hs.2 hrun₁.le))

end Product

section VectorFormer

variable {a va : Type}

/-- Check each bundle in turn. -/
def checkAll [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] [CircuitType F a va]
    [CheckedType F c a va] : List va → CircuitM F c PUnit
  | [] => pure PUnit.unit
  | v :: vs => do
    CheckedType.check (c := c) (val := a) v
    checkAll vs

section Laws

variable [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] [CircuitType F a va]
  [CheckedType F c a va]

private theorem checkAll_sound [ConstraintHolds F c] [LawfulBasicSystem F c] (V : Valuation F) :
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

private theorem checkAll_runs : ∀ (l : List va) (st : ProverState F),
    ∃ st', Runs (checkAll (F := F) (c := c) (a := a) l) st PUnit.unit st'
  | [], st => ⟨st, rfl⟩
  | v :: l, st => by
    obtain ⟨st₁, h₁⟩ := CheckedType.check_runs (c := c) (val := a) st v
    obtain ⟨st₂, h₂⟩ := checkAll_runs l st₁
    exact ⟨st₂, h₁.bind h₂⟩

private theorem checkAll_sat [ConstraintHolds F c] [LawfulBasicSystem F c] :
    ∀ (l : List va) {st st' stf : ProverState F},
      Runs (checkAll (F := F) (c := c) (a := a) l) st PUnit.unit st' →
      st'.nv ≤ stf.nv → st'.env.Le stf.env →
      (∀ v ∈ l, CircuitType.Scoped (val := a) st v ∧ ∃ x : a, CircuitType.Reads st.env.get v x) →
      Sat (checkAll (F := F) (c := c) (a := a) l) st stf
  | [], _, _, _, _, _, _, _ => Sat.pure
  | v :: l, st, _, stf, hrun, hnv, hle, hall => by
    obtain ⟨_, st₁, hrun₁, hrun₂⟩ := hrun.bind_inv
    obtain ⟨hs, x, hr⟩ := hall v (List.mem_cons_self ..)
    refine Sat.bind hrun₁
      (CheckedType.check_sat v x hrun₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle) hs hr)
      (checkAll_sat l hrun₂ hnv hle fun w hw => ?_)
    obtain ⟨hsw, y, hrw⟩ := hall w (List.mem_cons_of_mem _ hw)
    exact ⟨hsw.mono hrun₁.nv_le, y, hrw.of_le hsw hrun₁.le⟩

end Laws

/-- A vector is checked entry by entry; its rows concatenate. -/
instance instCheckedTypeVector [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [CircuitType F a va] [CheckedType F c a va] {n : Nat} :
    CheckedType F c (Vector a n) (Vector va n) where
  check vs := checkAll (F := F) (c := c) (a := a) vs.toList
  post V vs := ∀ v ∈ vs.toList, CheckedType.post (c := c) (val := a) V v
  check_sound V vs nv hsat := checkAll_sound V vs.toList nv hsat
  check_runs st vs := checkAll_runs vs.toList st
  check_sat vs xs hrun hnv hle hs hr := by
    rw [CircuitType.scoped_vector] at hs
    rw [CircuitType.reads_vector] at hr
    refine checkAll_sat vs.toList hrun hnv hle fun v hv => ?_
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hv)
    exact ⟨hs i hi, xs[i], hr i hi⟩

end VectorFormer

section UnChecked

variable {val var : Type}

/-- An `UnChecked` bundle emits no check: it grants nothing, which is what the wrapper
is for. -/
instance instCheckedTypeUnChecked [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [CircuitType F val var] : CheckedType F c (UnChecked val) (UnChecked var) where
  check _ := pure PUnit.unit
  post _ _ := True
  check_sound _ _ _ _ := trivial
  check_runs st _ := ⟨st, rfl⟩
  check_sat _ _ _ _ _ _ _ := Sat.pure

end UnChecked

section Equiv

variable {a va b vb : Type}

/-- A type isomorphic to a checked type is checked through the isomorphism. -/
@[reducible] def CheckedType.ofEquiv [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [CircuitType F a va] [S : CheckedType F c a va] (ev : b ≃ a) (ew : vb ≃ va) :
    @CheckedType F c b vb _ _ _ _ _ (CircuitType.ofEquiv ev ew) :=
  letI : CircuitType F b vb := CircuitType.ofEquiv ev ew
  { check := fun v => S.check (ew v)
    post := fun V v => S.post V (ew v)
    check_sound := fun V v nv h => S.check_sound V (ew v) nv h
    check_runs := fun st v => S.check_runs st (ew v)
    check_sat := fun v x hrun hnv hle hs hr => S.check_sat (ew v) (ev x) hrun hnv hle hs hr }

/-- A shape's check, through its decomposition at the value and at the bundle. -/
@[reducible] def CheckedType.ofShape [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    {S T : Type → Type} {val var : Type} [CircuitType F (T val) (T var)]
    [CheckedType F c (T val) (T var)] (e : ∀ a, S a ≃ T a) :
    @CheckedType F c (S val) (S var) _ _ _ _ _ (CircuitType.ofShape e) :=
  CheckedType.ofEquiv (e val) (e var)

end Equiv

end Instances

section Combinators

variable {F c val var : Type}

/-- Witness a typed value — the existential introduction of prover-supplied data, the
circuit model's nondeterminism primitive (OCaml `exists`; o1js `Provable.witness`).
The circuit asserts "there exist `size` field values for this bundle": the builder
allocates the variables and emits the type's `check` constraints; only prover runs
execute `compute`, whose output is — in the NP sense — the witness justifying the
existential. Renamed because `exists` is Lean's `∃` keyword. -/
def witness [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] [inst : CircuitType F val var]
    [CheckedType F c val var] (compute : AsProver F val) : CircuitM F c var :=
  .existsOp inst.size (inst.valueToFields <$> compute) fun vs => do
    let v := inst.fieldsToVar (mapVec CVar.var vs)
    CheckedType.check (c := c) (val := val) v
    pure v

/-- Read a typed variable bundle back to its value during a prover run. The
length check is dynamic (it always succeeds) to keep the definition kernel-reducible
without a `mapM`-length lemma. -/
def readVar [Add F] [Mul F] [inst : CircuitType F val var] (v : var) : AsProver F val := do
  let fields ← (inst.varToFields v).toList.mapM AsProver.readCVar
  if h : fields.length = inst.size then
    pure (inst.fieldsToValue ⟨⟨fields⟩, by simpa using h⟩)
  else
    AsProver.throw "readVar: size mismatch"

open Std.Do in
/-- A witness grants its type's contract. -/
@[spec] theorem witness_spec {V : Valuation F} [Add F] [Mul F] [Zero F] [One F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    [CircuitType F val var] [S : CheckedType F (Builder V c) val var] (compute : AsProver F val) :
    ⦃⌜True⌝⦄
    (witness (val := val) compute : CircuitM F (Builder V c) var)
    ⦃⇓ r _ => ⌜S.post V r⌝⦄ := by
  intro nv _ hsat
  simp only [witness, build, build_bind, List.append_nil] at hsat ⊢
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

/-- A scoped bundle reads as its reading. -/
@[simp] theorem readVar_run [Add F] [Mul F] [Zero F] [CircuitType F val var] {st : ProverState F}
    {v : var} (hs : CircuitType.Scoped (val := val) st v) :
    (readVar (val := val) v).run st.env = .ok (CircuitType.readVal st.env.get v) := by
  simp only [readVar, AsProver.bind_eq, AsProver.run_bind, run_mapM_readCVar hs, Except.bind]
  rw [dif_pos (by simp)]
  rfl

/-- The honest run of a witness: the computation runs, the bundle is allocated at the
counter with the value's encoding, and the run closes wherever the type's check — of a
fresh, honest allocation — closes. The check may allocate, so its landing state is a
hypothesis rather than a computation. -/
private theorem runs_witness [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [inst : CircuitType F val var] [CheckedType F c val var]
    (compute : AsProver F val) {st st' : ProverState F} {v : val}
    (h : compute.run st.env = .ok v)
    (hcheck : Runs (CheckedType.check (c := c) (val := val)
        (inst.fieldsToVar (mapVec CVar.var (allocRange st.nv inst.size))))
      (st.alloc (inst.valueToFields v)) PUnit.unit st') :
    Runs (witness (c := c) (val := val) compute) st
      (inst.fieldsToVar (mapVec CVar.var (allocRange st.nv inst.size))) st' := by
  show prove _ st.nv st.env = _
  simp only [witness, prove, AsProver.map_eq, AsProver.run_bind, h, Except.bind,
    AsProver.run_pure, prove_bind]
  rw [show prove (CheckedType.check (c := c) (val := val)
      (inst.fieldsToVar (mapVec CVar.var (allocRange st.nv inst.size))))
      (st.nv + inst.size) (st.env.extendList st.nv (inst.valueToFields v).toList)
      = .ok (st'.out PUnit.unit) from hcheck]

/-- The witness leaf's completeness law — the one place the representation stack is
crossed. A witness computation that runs to a value yields a run to the allocated
state whose fresh bundle is scoped and reads as that value, whose rows are the type's
check rows, satisfied at any extension, and which only grows the table. -/
theorem witness_complete [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] [inst : CircuitType F val var]
    [CheckedType F c val var] (compute : AsProver F val) {st : ProverState F} {v : val}
    (h : compute.run st.env = .ok v) :
    ∃ (r : var) (st' : ProverState F), Runs (witness (c := c) (val := val) compute) st r st' ∧
      (∀ {stf : ProverState F}, st'.nv ≤ stf.nv → st'.env.Le stf.env →
        Sat (witness (c := c) (val := val) compute) st stf) ∧
      st.nv ≤ st'.nv ∧ st.env.Le st'.env ∧
      CircuitType.Scoped (val := val) st' r ∧ CircuitType.Reads st'.env.get r v := by
  have hscope : CircuitType.Scoped (val := val) (st.alloc (inst.valueToFields v))
      (inst.fieldsToVar (mapVec CVar.var (allocRange st.nv inst.size))) := by
    intro cv hcv
    rw [inst.var_roundTrip, toList_mapVec, List.mem_map] at hcv
    obtain ⟨w, hw, rfl⟩ := hcv
    have := List.mem_range'_1.mp hw
    exact show w < st.nv + inst.size from this.2
  have hreads : CircuitType.Reads (st.alloc (inst.valueToFields v)).env.get
      (inst.fieldsToVar (mapVec CVar.var (allocRange st.nv inst.size))) v := by
    unfold CircuitType.Reads
    rw [inst.var_roundTrip]
    ext i hi
    simp only [getElem_mapVec, getElem_allocRange, CVar.val, ProverState.get_alloc]
    simp [Assignments.get, Assignments.extendList_get
      (show i < (inst.valueToFields v).toList.length by simpa using hi)]
  obtain ⟨st', hcheck⟩ :=
    CheckedType.check_runs (c := c) (val := val) (st.alloc (inst.valueToFields v))
      (inst.fieldsToVar (mapVec CVar.var (allocRange st.nv inst.size)))
  have hrun := runs_witness compute h hcheck
  refine ⟨_, st', hrun, ?_, hrun.nv_le, hrun.le,
    hscope.mono hcheck.nv_le, hreads.of_le hscope hcheck.le⟩
  intro stf hnv' hle' con hcon
  simp only [witness, build, build_bind, List.append_nil] at hcon
  exact CheckedType.check_sat _ v hcheck hnv' hle' hscope hreads con hcon

end Combinators

/-- Witnessing an unchecked bundle emits no rows — the wrapper's whole content. -/
example {val var : Type} [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [CircuitType F val var] (compute : AsProver F (UnChecked val)) (nv : Nat) :
    (build (witness (c := c) (val := UnChecked val) compute) nv).constraints = [] := by
  simp [witness, build, build_bind]

end Snarky
