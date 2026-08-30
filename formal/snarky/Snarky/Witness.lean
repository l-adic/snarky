import Snarky.Prover

/-!
# The witness combinator

`CheckedType` pairs an encoding with the constraint circuit enforcing its
well-formedness; `witness` allocates a bundle, runs the prover's advice, and emits the
check. Its laws — the soundness contract and the completeness law, the two directions of
one statement about the same rows — are the leaf interface every gadget builds on.
-/

namespace Snarky

/-- Variable bundles whose well-formedness is enforced by constraints: `check` is
emitted by `witness` under both interpreters, with what its rows force about the bundle
(`post`, `check_sound`) and that a bundle whose reading already satisfies them can be
completed to a run that does (`check_complete`). The value type is a parameter because
the laws speak of the encoding. -/
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
  /-- The prover's law: from a scoped bundle reading as an admissible value — one whose
  every reading already satisfies `post`, the hypothesis spelled out because the class
  cannot name `CheckedType.Valid` from inside itself — the check runs, and its rows are
  satisfied at every extension of the state it runs to. The check MAY allocate
  auxiliaries of its own, which is why its landing state is part of the conclusion. -/
  check_complete : ∀ [ConstraintHolds F c] [LawfulBasicSystem F c] (v : var) (a : val),
    (∀ (V : Valuation F) (w : var), CircuitType.Reads V w a → post V w) →
    Complete (F := F) (c := c) (fun st => CircuitType.ReadsAs (val := val) st v a)
      (check v) fun _ _ => True

/-- The values a check admits: those whose every bundle reading satisfies what the rows
force. Not a field but a definition — `post` pulled back along the reading — so a type's
admissible values can never be fewer than its own constraints allow, and no completeness
law can rest on anything a verifier does not itself check. -/
def CheckedType.Valid {F c val var : Type} [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [CircuitType F val var] [CheckedType F c val var] (a : val) : Prop :=
  ∀ (V : Valuation F) (w : var), CircuitType.Reads V w a →
    CheckedType.post (c := c) (val := val) V w

section Instances

variable {F c : Type}

/-- A field element carries no well-formedness constraint (PS `CheckedType` instance for
`FVar`: `check = const (pure unit)`). -/
instance instCheckedTypeFVar [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] :
    CheckedType F c F (FVar F) where
  check _ := .pure PUnit.unit
  post _ _ := True
  check_sound := by intros; trivial
  check_complete _ _ _ := Complete.pure

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
  check_complete := by
    intro _ _ b a _ st ⟨hs, hr⟩
    refine ⟨PUnit.unit, st, Runs.addConstraint, ?_, trivial⟩
    intro stf _ hle
    refine Sat.addConstraint ((LawfulBasicSystem.holds_boolean _ _).mpr ?_)
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
  check_complete _ _ _ := Complete.pure

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
  check_complete := by
    rintro _ _ ⟨v, w⟩ ⟨x, y⟩ hv st ⟨hs, hr⟩
    have hx : ∀ (V : Valuation F) (u : va), CircuitType.Reads V u x →
        CheckedType.post (c := c) (val := a) V u := fun V u hu =>
      (hv V (u, CircuitType.constVar y) (CircuitType.reads_prod.mpr
        ⟨hu, CircuitType.reads_constVar V y⟩)).1
    have hy : ∀ (V : Valuation F) (u : vb), CircuitType.Reads V u y →
        CheckedType.post (c := c) (val := b) V u := fun V u hu =>
      (hv V (CircuitType.constVar x, u) (CircuitType.reads_prod.mpr
        ⟨CircuitType.reads_constVar V x, hu⟩)).2
    rw [CircuitType.scoped_prod] at hs
    rw [CircuitType.reads_prod] at hr
    obtain ⟨_, st₁, hrun₁, hsat₁, _⟩ :=
      CheckedType.check_complete (c := c) (val := a) v x hx st ⟨hs.1, hr.1⟩
    obtain ⟨_, st₂, hrun₂, hsat₂, _⟩ :=
      CheckedType.check_complete (c := c) (val := b) w y hy st₁
        ⟨hs.2.mono hrun₁.nv_le, hr.2.of_le hs.2 hrun₁.le⟩
    refine ⟨PUnit.unit, st₂, hrun₁.bind hrun₂, ?_, trivial⟩
    intro stf hnv hle
    exact Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
      (hsat₂ hnv hle)

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

private theorem checkAll_complete [ConstraintHolds F c] [LawfulBasicSystem F c] :
    ∀ l : List va, Complete (F := F) (c := c)
      (fun st => ∀ v ∈ l, ∃ x : a, CheckedType.Valid (F := F) (c := c) (var := va) x ∧
        CircuitType.ReadsAs (val := a) st v x)
      (checkAll (F := F) (c := c) (a := a) l) fun _ _ => True
  | [] => Complete.pure
  | v :: l => by
    intro st hall
    obtain ⟨x, hx, hs, hr⟩ := hall v (List.mem_cons_self ..)
    obtain ⟨_, st₁, hrun₁, hsat₁, _⟩ :=
      CheckedType.check_complete (c := c) (val := a) v x hx st ⟨hs, hr⟩
    obtain ⟨_, st₂, hrun₂, hsat₂, _⟩ := checkAll_complete l st₁ fun w hw => by
      obtain ⟨y, hy, hsw, hrw⟩ := hall w (List.mem_cons_of_mem _ hw)
      exact ⟨y, hy, hsw.mono hrun₁.nv_le, hrw.of_le hsw hrun₁.le⟩
    refine ⟨PUnit.unit, st₂, hrun₁.bind hrun₂, ?_, trivial⟩
    intro stf hnv hle
    exact Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
      (hsat₂ hnv hle)

end Laws

/-- A vector is checked entry by entry; its rows concatenate. -/
instance instCheckedTypeVector [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [CircuitType F a va] [CheckedType F c a va] {n : Nat} :
    CheckedType F c (Vector a n) (Vector va n) where
  check vs := checkAll (F := F) (c := c) (a := a) vs.toList
  post V vs := ∀ v ∈ vs.toList, CheckedType.post (c := c) (val := a) V v
  check_sound V vs nv hsat := checkAll_sound V vs.toList nv hsat
  check_complete vs xs hv := by
    intro st ⟨hs, hr⟩
    rw [CircuitType.scoped_vector] at hs
    rw [CircuitType.reads_vector] at hr
    refine checkAll_complete vs.toList st fun v hv' => ?_
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hv')
    exact ⟨xs[i], valid_getElem hv hi, hs i hi, hr i hi⟩

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
  check_complete _ _ _ := Complete.pure

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
    check_complete := fun v x hx st hpre =>
      S.check_complete (ew v) (ev x)
        (fun V w hw => by
          have h := hx V (ew.symm w)
            (by rwa [CircuitType.reads_ofEquiv, Equiv.apply_symm_apply])
          rwa [Equiv.apply_symm_apply] at h) st hpre }

/-- A shape's check, through its decomposition at the value and at the bundle. -/
@[reducible] def CheckedType.ofShape [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    {S T : Type → Type} {val var : Type} [CircuitType F (T val) (T var)]
    [CheckedType F c (T val) (T var)] (e : ∀ a, S a ≃ T a) :
    @CheckedType F c (S val) (S var) _ _ _ _ _ (CircuitType.ofShape e) :=
  CheckedType.ofEquiv (e val) (e var)

end Equiv

end Instances

/-! ## Admissibility, at the concrete types and the formers

Every type below admits every value — their checks force nothing about the decoded
value, only that the wires lie in the encoding's image. A type whose rows do constrain
the value (a curve point's on-curve rows) proves its own characterization instead. -/

section Valid

variable {F c : Type}

@[simp] theorem valid_fvar [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] {x : F} :
    CheckedType.Valid (F := F) (c := c) (var := FVar F) x := fun _ _ _ => trivial

@[simp] theorem valid_bool [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)]
    [BasicSystem F c] {b : Bool} :
    CheckedType.Valid (F := F) (c := c) (var := BoolVar F) b :=
  fun _ _ h => ⟨b, CircuitType.reads_boolVar.mp h⟩

@[simp] theorem valid_unchecked {val var : Type} [Add F] [Mul F] [Zero F] [One F]
    [BasicSystem F c] [CircuitType F val var] {x : UnChecked val} :
    CheckedType.Valid (F := F) (c := c) (var := UnChecked var) x := fun _ _ _ => trivial

variable {a va b vb : Type}

@[simp] theorem valid_prod [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
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

@[simp] theorem valid_vector [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [CircuitType F a va] [CheckedType F c a va] {n : Nat} {xs : Vector a n} :
    CheckedType.Valid (F := F) (c := c) (var := Vector va n) xs ↔
      ∀ (i : Nat) (hi : i < n), CheckedType.Valid (F := F) (c := c) (var := va) xs[i] := by
  constructor
  · exact fun h _ hi => valid_getElem h hi
  · rintro h V ws hws w hw
    rw [CircuitType.reads_vector] at hws
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hw)
    exact h i hi V ws[i] (hws i hi)

/-- Admissibility travels through a decomposition. -/
@[simp] theorem valid_ofEquiv [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [CircuitType F a va] [S : CheckedType F c a va] (ev : b ≃ a) (ew : vb ≃ va) {x : b} :
    @CheckedType.Valid F c b vb _ _ _ _ _ (CircuitType.ofEquiv ev ew)
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
crossed. A witness computation that runs to an admissible value yields a run to the
allocated state whose fresh bundle is scoped and reads as that value, whose rows are the
type's check rows, satisfied at any extension, and which only grows the table.
Admissibility is what the type's own rows force (`CheckedType.Valid`), so the hypothesis
restricts the honest prover's domain to exactly what the circuit accepts. -/
theorem witness_complete [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] [inst : CircuitType F val var]
    [CheckedType F c val var] (compute : AsProver F val) {st : ProverState F} {v : val}
    (hv : CheckedType.Valid (F := F) (c := c) (var := var) v)
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
  obtain ⟨_, st', hcheck, hsat, _⟩ :=
    CheckedType.check_complete (c := c) (val := val)
      (inst.fieldsToVar (mapVec CVar.var (allocRange st.nv inst.size))) v hv
      (st.alloc (inst.valueToFields v)) ⟨hscope, hreads⟩
  have hrun := runs_witness compute h hcheck
  refine ⟨_, st', hrun, ?_, hrun.nv_le, hrun.le,
    hscope.mono hcheck.nv_le, hreads.of_le hscope hcheck.le⟩
  intro stf hnv' hle' con hcon
  simp only [witness, build, build_bind, List.append_nil] at hcon
  exact hsat hnv' hle' con hcon

/-- **The witness rule**, at the completeness abstraction: the computation succeeds at the
entry table, and the fresh cells read as its value. `witness_complete`'s two order facts
are what a caller used to transport its own context across the allocation; `Complete.frame`
does that now, so they are not part of the rule. -/
theorem Complete.witness [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] [CircuitType F val var]
    [CheckedType F c val var] (compute : AsProver F val) (v : val)
    (hv : CheckedType.Valid (F := F) (c := c) (var := var) v) :
    Complete (F := F) (c := c) (fun st => compute.run st.env = .ok v)
      (witness (c := c) (val := val) compute)
      (fun r st' => CircuitType.ReadsAs st' r v) := fun _ h =>
  let ⟨r, st', hrun, hsat, _, _, hsc, hrd⟩ := witness_complete compute hv h
  ⟨r, st', hrun, hsat, hsc, hrd⟩

end Combinators

/-- Witnessing an unchecked bundle emits no rows — the wrapper's whole content. -/
example {val var : Type} [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [CircuitType F val var] (compute : AsProver F (UnChecked val)) (nv : Nat) :
    (build (witness (c := c) (val := UnChecked val) compute) nv).constraints = [] := by
  simp [witness, build, build_bind]

end Snarky
