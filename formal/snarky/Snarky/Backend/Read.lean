import Snarky.Circuit.Types
import Snarky.Backend.Assignments
import Snarky.Backend.Prover

/-!
# Reading circuit types off a table

The generic reading vocabulary over `CircuitType`: a variable bundle flattens to its
underlying `CVar`s (`varToFields`), each is read — totally under a `Valuation`,
partially on the prover table — and the read fields decode as the declared value
(`fieldsToValue`). Gadget laws quote this vocabulary instead of spelling per-cell
readings:

- `readVal` — the builder-side reading, a total function (`CVar.val` lifted through
  the encoding);
- `Readable` — the one-predicate `Complete` precondition: every cell of the bundle
  evaluates on the table;
- `Reads` — the prover-side reading: the bundle is readable and the completed table
  (`Assignments.toValuation`) decodes it to the value;
- `ReadsAll` — the elementwise lift of `Reads` to input lists (an unsized input has
  no `CircuitType` encoding of its own).

The `_fvar`/`_prod` lemmas compute the vocabulary at the base and pair instances —
how a proof decomposes a bundle reading into the per-cell facts the gate models
consume. The `.le` lemmas transport every prover-side reading along table extension
(`Assignments.Le`), and `exists_reads`/`exists_readsAll` name the value a readable
hypothesis promises, for use inside a proof.
-/

namespace Snarky

variable {F val var : Type}

/-! ## The readings -/

/-- The builder-side reading of a variable bundle: every underlying `CVar` read under
the valuation, the fields decoded as the declared value. -/
def readVal [Add F] [Mul F] [CircuitType F val var] (V : Valuation F) (cv : var) :
    val :=
  CircuitType.fieldsToValue (var := var)
    ((CircuitType.varToFields (val := val) cv).map (·.val V))

/-- Every `CVar` in the bundle's flattening evaluates — the one-predicate `Complete`
precondition of a gadget that consumes the bundle. The value is not named here
(`exists_reads` recovers it inside a proof), for the reason `Complete` records. -/
def Readable (val : Type) [Add F] [Mul F] [CircuitType F val var]
    (env : Assignments F) (cv : var) : Prop :=
  ∀ i (hi : i < CircuitType.size F val),
    ((CircuitType.varToFields (val := val) cv)[i].eval env).isOk

/-- The prover-side reading of a variable bundle: the bundle is readable, and the
completed table decodes it to the value. On readable cells the completion agrees with
the pinned evaluations (`CVar.val_toValuation`), so this is exactly "every cell
evaluates, and the read fields decode to `v`". -/
def Reads [Add F] [Mul F] [Zero F] [CircuitType F val var] (env : Assignments F)
    (cv : var) (v : val) : Prop :=
  Readable val env cv ∧ readVal env.toValuation cv = v

/-- The prover-side reading of an input list: elementwise `Reads`, in the order
given. -/
def ReadsAll [Add F] [Mul F] [Zero F] [CircuitType F val var] (env : Assignments F)
    (xs : List var) (vs : List val) : Prop :=
  List.Forall₂ (Reads env) xs vs

/-- Name the value behind a successful evaluation — `Except.isOk` destructed, for the
readings below. -/
private theorem exists_of_isOk {ε α : Type} {e : Except ε α} (h : e.isOk = true) :
    ∃ w, e = .ok w := by
  cases e with
  | error _ => cases h
  | ok w => exact ⟨w, rfl⟩

/-! ## Computing the vocabulary at the base instance -/

/-- A single field variable reads as its `CVar.val`. -/
@[circuitVal] theorem readVal_fvar [Add F] [Mul F] (V : Valuation F) (x : FVar F) :
    readVal V x = x.val V := by
  show ((#v[x]).map (·.val V))[0] = x.val V
  simp

/-- A single field variable is readable iff its evaluation succeeds. -/
theorem readable_fvar_iff [Add F] [Mul F] {env : Assignments F} {x : FVar F} :
    Readable F env x ↔ (x.eval env).isOk := by
  constructor
  · intro h
    exact h 0 Nat.zero_lt_one
  · intro h i hi
    have hi' : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    exact h

/-- A single field variable's prover-side reading is its pinned evaluation. -/
theorem reads_fvar_iff [Add F] [Mul F] [Zero F] {env : Assignments F} {x : FVar F}
    {v : F} : Reads env x v ↔ x.eval env = .ok v := by
  constructor
  · rintro ⟨hok, hval⟩
    obtain ⟨w, hw⟩ := exists_of_isOk (readable_fvar_iff.mp hok)
    rw [readVal_fvar, CVar.val_toValuation hw] at hval
    rw [hw, hval]
  · intro h
    exact ⟨readable_fvar_iff.mpr (by rw [h]; rfl),
      by rw [readVal_fvar, CVar.val_toValuation h]⟩

/-! ## Computing the vocabulary at the pair instance -/

section Prod

variable {a b av bv : Type}

/-- The pair instance's dimension, named for the index arithmetic below. -/
private theorem size_prod [A : CircuitType F a av] [B : CircuitType F b bv] :
    CircuitType.size F (a × b) (var := av × bv)
      = CircuitType.size F a (var := av) + CircuitType.size F b (var := bv) := rfl

/-- A pair reads as the pair of its components' readings. -/
@[circuitVal] theorem readVal_prod [Add F] [Mul F] [A : CircuitType F a av]
    [B : CircuitType F b bv] (V : Valuation F) (p : av × bv) :
    readVal (val := a × b) V p = (readVal V p.1, readVal V p.2) := by
  show (A.fieldsToValue ((((A.varToFields p.1 ++ B.varToFields p.2).map
        (·.val V)).take A.size).cast (by omega)),
      B.fieldsToValue ((((A.varToFields p.1 ++ B.varToFields p.2).map
        (·.val V)).drop A.size).cast (by omega)))
    = (A.fieldsToValue ((A.varToFields p.1).map (·.val V)),
      B.fieldsToValue ((B.varToFields p.2).map (·.val V)))
  rw [Vector.map_append, cast_take_append, cast_drop_append]

/-- A pair is readable iff its components are. -/
theorem readable_prod_iff [Add F] [Mul F] [A : CircuitType F a av]
    [B : CircuitType F b bv] {env : Assignments F} {p : av × bv} :
    Readable (a × b) env p ↔ Readable a env p.1 ∧ Readable b env p.2 := by
  constructor
  · intro h
    constructor
    · intro i hi
      have h' := h i (by rw [size_prod]; omega)
      rwa [show (CircuitType.varToFields (val := a × b) p)[i]'(by
            rw [size_prod]; omega)
          = (A.varToFields p.1)[i]
        from Vector.getElem_append_left hi] at h'
    · intro i hi
      have h' := h (A.size + i) (by rw [size_prod]; omega)
      have heq : (CircuitType.varToFields (val := a × b) p)[A.size + i]'(by
            rw [size_prod]; omega)
          = (B.varToFields p.2)[i] := by
        show (A.varToFields p.1 ++ B.varToFields p.2)[A.size + i]'(by omega)
          = (B.varToFields p.2)[i]
        rw [Vector.getElem_append_right (by omega) (by omega)]
        simp
      rwa [heq] at h'
  · rintro ⟨ha, hb⟩ i hi
    have hi' : i < A.size + B.size := hi
    show (((A.varToFields p.1 ++ B.varToFields p.2))[i].eval env).isOk
    by_cases hia : i < A.size
    · rw [Vector.getElem_append_left hia]
      exact ha i hia
    · rw [Vector.getElem_append_right (by omega) (by omega)]
      exact hb (i - A.size) (by omega)

/-- A pair's prover-side reading is the conjunction of its components'. -/
theorem reads_prod_iff [Add F] [Mul F] [Zero F] [CircuitType F a av]
    [CircuitType F b bv] {env : Assignments F} {p : av × bv} {v : a × b} :
    Reads env p v ↔ Reads env p.1 v.1 ∧ Reads env p.2 v.2 := by
  simp only [Reads, readable_prod_iff, readVal_prod, Prod.ext_iff]
  tauto

end Prod

/-! ## Computing the vocabulary at a presented instance -/

section OfEquiv

variable {rep repVar : Type} (R : CircuitType F rep repVar) (e : val ≃ rep) (ev : var ≃ repVar)

/-- A presented bundle reads as its representation's reading, carried back. -/
@[circuitVal] theorem readVal_ofEquiv [Add F] [Mul F] (V : Valuation F) (cv : var) :
    @readVal F val var _ _ (R.ofEquiv e ev) V cv = e.symm (readVal V (ev cv)) := rfl

/-- A presented bundle is readable iff its representation is. -/
theorem readable_ofEquiv_iff [Add F] [Mul F] {env : Assignments F} {cv : var} :
    @Readable F var val _ _ (R.ofEquiv e ev) env cv ↔ Readable rep env (ev cv) :=
  Iff.rfl

/-- A presented bundle's prover-side reading is its representation's, at the carried
value. -/
theorem reads_ofEquiv_iff [Add F] [Mul F] [Zero F] {env : Assignments F} {cv : var}
    {v : val} :
    @Reads F val var _ _ _ (R.ofEquiv e ev) env cv v ↔ Reads env (ev cv) (e v) := by
  simp only [Reads, readable_ofEquiv_iff, readVal_ofEquiv, Equiv.symm_apply_eq]

end OfEquiv

/-! ## Transport along table extension -/

/-- The readability survives table extension. -/
theorem Readable.le [Add F] [Mul F] [CircuitType F val var]
    {env env' : Assignments F} (hle : env.Le env') {cv : var}
    (h : Readable val env cv) : Readable val env' cv := by
  intro i hi
  obtain ⟨w, hw⟩ := exists_of_isOk (h i hi)
  rw [CVar.eval_le hle hw]
  rfl

/-- The reading survives table extension. -/
theorem Reads.le [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {env env' : Assignments F} (hle : env.Le env') {cv : var} {v : val}
    (h : Reads env cv v) : Reads env' cv v := by
  obtain ⟨hok, hval⟩ := h
  refine ⟨hok.le hle, ?_⟩
  rw [← hval]
  show CircuitType.fieldsToValue (var := var) _ = CircuitType.fieldsToValue _
  congr 1
  ext i hi
  simp only [Vector.getElem_map]
  obtain ⟨w, hw⟩ := exists_of_isOk (hok i hi)
  rw [CVar.val_toValuation hw, CVar.val_toValuation (CVar.eval_le hle hw)]

/-- The list reading survives table extension. -/
theorem ReadsAll.le [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {env env' : Assignments F} (hle : env.Le env') {xs : List var} {vs : List val}
    (h : ReadsAll env xs vs) : ReadsAll env' xs vs := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (hx.le hle) ih

/-! ## Naming the read values -/

/-- A readable bundle reads as SOME value — names the value a `Readable` hypothesis
promises, for use inside a proof. -/
theorem exists_reads [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {env : Assignments F} {cv : var} (h : Readable val env cv) :
    ∃ v : val, Reads env cv v :=
  ⟨readVal env.toValuation cv, h, rfl⟩

/-- The reading's precondition half, extracted. -/
theorem Reads.readable [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {env : Assignments F} {cv : var} {v : val} (h : Reads env cv v) :
    Readable val env cv :=
  h.1

/-- A bundle reads as at most one value: the reading is a partial function of the
table. -/
theorem Reads.unique [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {env : Assignments F} {cv : var} {v w : val} (hv : Reads env cv v)
    (hw : Reads env cv w) : v = w :=
  hv.2.symm.trans hw.2

/-- Readable inputs read as SOME value list — names the list the complete laws'
`ReadsAll` hypotheses quantify over, for use inside a proof. -/
theorem exists_readsAll [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {env : Assignments F} :
    ∀ {xs : List var}, (∀ x ∈ xs, Readable val env x) →
      ∃ vs : List val, ReadsAll env xs vs
  | [], _ => ⟨[], .nil⟩
  | x :: xs, h => by
    obtain ⟨v, hv⟩ := exists_reads (h x (by simp))
    obtain ⟨vs, hvs⟩ := exists_readsAll (xs := xs) fun y hy => h y (by simp [hy])
    exact ⟨v :: vs, .cons hv hvs⟩

/-! ## Scope

The prover-side precondition of a gadget law is that its operands are in scope
(`ProverState`'s `∈`, lifted to expressions and bundles): then every read is total,
and the law's values are `val`/`readVal` at the completed table, `st.env.toValuation`.
`eval_eq_val` is the one bridge from the partial `eval` to the total reading; the
`_fvar`/`_prod`/`_ofEquiv` lemmas compute scope at the base, pair and presented
instances, as the `readVal_*` lemmas compute the reading; and `readVal_extendMany_new`
is what a witness leaf grants — the allocated bundle reads as the value the block
computed, by the round trips. -/

/-- `x.Scoped st`: every variable of the expression is in scope. -/
def CVar.Scoped (st : ProverState F) : CVar F → Prop
  | .var v => v ∈ st
  | .const _ => True
  | .add a b => a.Scoped st ∧ b.Scoped st
  | .scale _ y => y.Scoped st

@[simp] theorem CVar.scoped_var (st : ProverState F) (v : Variable) :
    (CVar.var v : CVar F).Scoped st ↔ v ∈ st := Iff.rfl

@[simp] theorem CVar.scoped_const (st : ProverState F) (k : F) :
    (CVar.const k).Scoped st := trivial

@[simp] theorem CVar.scoped_add (st : ProverState F) (a b : CVar F) :
    (CVar.add a b).Scoped st ↔ a.Scoped st ∧ b.Scoped st := Iff.rfl

@[simp] theorem CVar.scoped_scale (st : ProverState F) (k : F) (y : CVar F) :
    (CVar.scale k y).Scoped st ↔ y.Scoped st := Iff.rfl

/-- Scope survives table extension. -/
theorem CVar.Scoped.of_le {st st' : ProverState F} (hle : st.env.Le st'.env) :
    ∀ {x : CVar F}, x.Scoped st → x.Scoped st'
  | .var _, h => ProverState.mem_of_le hle h
  | .const _, _ => trivial
  | .add _ _, ⟨ha, hb⟩ => ⟨ha.of_le hle, hb.of_le hle⟩
  | .scale _ y, h => CVar.Scoped.of_le hle (x := y) h

/-- Reading an in-scope expression is a scoped block. -/
theorem AsProver.Scoped.readCVar [Add F] [Mul F] {st : ProverState F} :
    ∀ {x : CVar F}, x.Scoped st → (readCVar x).Scoped st
  | .var _, hv => ⟨hv, fun _ => trivial⟩
  | .const _, _ => trivial
  | .add _ _, ⟨ha, hb⟩ =>
    AsProver.Scoped.bind (readCVar ha) fun _ => AsProver.Scoped.bind (readCVar hb) fun _ => trivial
  | .scale _ y, hy => AsProver.Scoped.bind (readCVar (x := y) hy) fun _ => trivial

/-- Scope passes through `add_`. -/
theorem CVar.Scoped.add_ [Add F] {st : ProverState F} {a b : CVar F} (ha : a.Scoped st)
    (hb : b.Scoped st) : (CVar.add_ a b).Scoped st := by
  cases a <;> cases b <;> trivial

/-- Scope passes through `scale_`. -/
theorem CVar.Scoped.scale_ [Zero F] [One F] [DecidableEq F] {st : ProverState F} {x : CVar F}
    (k : F) (hx : x.Scoped st) : (CVar.scale_ k x).Scoped st := by
  unfold CVar.scale_
  split_ifs <;> trivial

/-- Scope passes through `sub_`. -/
theorem CVar.Scoped.sub_ [Add F] [Sub F] [Zero F] [One F] [Neg F] [DecidableEq F]
    {st : ProverState F} {a b : CVar F} (ha : a.Scoped st) (hb : b.Scoped st) :
    (CVar.sub_ a b).Scoped st := by
  cases a <;> cases b <;> first | trivial | exact ha.add_ (hb.scale_ _)

/-- `List.mapM`'s loop over in-scope expressions is a scoped block. -/
private theorem AsProver.Scoped.mapM_loop [Add F] [Mul F] {st : ProverState F} :
    ∀ (xs : List (CVar F)) (acc : List F), (∀ x ∈ xs, x.Scoped st) →
      (List.mapM.loop AsProver.readCVar xs acc).Scoped st
  | [], _, _ => trivial
  | x :: xs, acc, h =>
    AsProver.Scoped.bind (readCVar (h x (List.mem_cons_self ..))) fun v =>
      mapM_loop xs (v :: acc) fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- Reading a list of in-scope expressions is a scoped block. -/
theorem AsProver.Scoped.mapM_readCVar [Add F] [Mul F] {st : ProverState F} {xs : List (CVar F)}
    (h : ∀ x ∈ xs, x.Scoped st) : (xs.mapM AsProver.readCVar).Scoped st :=
  mapM_loop xs [] h

/-- The typed read of a boolean variable is a scoped block when its expression is. -/
theorem AsProver.Scoped.readVar_bool [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {st : ProverState F} {b : BoolVar F} (hb : b.toCVar.Scoped st) :
    (readVar (val := Bool) b).Scoped st :=
  AsProver.Scoped.bind (AsProver.Scoped.mapM_readCVar fun x hx => by
    have hx' : x ∈ [b.toCVar] := hx
    rw [List.mem_singleton.mp hx']
    exact hb) fun _ => by
    split <;> trivial

/-- The typed read of a boolean variable evaluates to whether its expression is
nonzero. -/
theorem AsProver.eval_readVar_bool [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    (V : Valuation F) (b : BoolVar F) :
    (readVar (val := Bool) b).eval V = .ok (decide (b.toCVar.val V ≠ 0)) := by
  simp [readVar, Except.bind]
  show decide (b.toCVar.val V ≠ 0) = _
  exact decide_not

/-- An in-scope expression evaluates, to its total reading at the completed table. -/
theorem CVar.eval_eq_val [Add F] [Mul F] [Zero F] {st : ProverState F} :
    ∀ {x : CVar F}, x.Scoped st → x.eval st.env = .ok (x.val st.env.toValuation)
  | .var v, hv => by simp [CVar.eval, CVar.val, st.get_eq hv]
  | .const _, _ => rfl
  | .add a b, ⟨ha, hb⟩ => by simp [CVar.eval, CVar.val, eval_eq_val ha, eval_eq_val hb]
  | .scale _ y, hy => by simp [CVar.eval, CVar.val, eval_eq_val (x := y) hy]

/-- In-scope expressions evaluate, elementwise, to their total readings. -/
theorem CVar.mapM_eval_eq_val [Add F] [Mul F] [Zero F] {st : ProverState F} :
    ∀ {xs : List (CVar F)}, (∀ x ∈ xs, x.Scoped st) →
      xs.mapM (CVar.eval · st.env) = .ok (xs.map (·.val st.env.toValuation))
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, CVar.eval_eq_val (h x (List.mem_cons_self ..)),
      CVar.mapM_eval_eq_val fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- An in-scope reading survives table extension. -/
theorem CVar.val_of_le [Add F] [Mul F] [Zero F] {st st' : ProverState F}
    (hle : st.env.Le st'.env) {x : CVar F} (hs : x.Scoped st) :
    x.val st'.env.toValuation = x.val st.env.toValuation := by
  have h := CVar.eval_le hle (CVar.eval_eq_val hs)
  rw [CVar.eval_eq_val (hs.of_le hle)] at h
  injection h

/-- A one-cell allocation, read back: the field variable at the counter. -/
@[simp] theorem fieldsToVar_fvar_alloc (nv : Nat) :
    CircuitType.fieldsToVar (F := F) (val := F)
      (mapVec CVar.var (allocRange nv (CircuitType.size F F))) = .var nv := by
  show (mapVec CVar.var (allocRange nv 1))[0] = _
  simp [allocRange]

/-- A field value's encoding, as the list an allocation writes. -/
@[simp] theorem valueToFields_fvar_toList (v : F) :
    (CircuitType.valueToFields (F := F) (var := FVar F) v).toList = [v] := rfl

/-- A boolean variable reads as whether its expression is nonzero. -/
@[circuitVal] theorem readVal_bool [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    (V : Valuation F) (b : BoolVar F) : readVal V b = decide (b.toCVar.val V ≠ 0) := by
  show decide (((#v[b.toCVar]).map (·.val V))[0] ≠ 0) = _
  simp

/-- A one-cell boolean allocation, read back: the bit at the counter. -/
@[simp] theorem fieldsToVar_bool_alloc [Zero F] [One F] [DecidableEq F] (nv : Nat) :
    CircuitType.fieldsToVar (F := F) (val := Bool)
      (mapVec CVar.var (allocRange nv (CircuitType.size F Bool))) = .unchecked (.var nv) := by
  show BoolVar.unchecked (mapVec CVar.var (allocRange nv 1))[0] = _
  simp [allocRange]

/-- A bit's encoding, as the list an allocation writes. -/
@[simp] theorem valueToFields_bool_toList [Zero F] [One F] [DecidableEq F] (b : Bool) :
    (CircuitType.valueToFields (F := F) (var := BoolVar F) b).toList = [bit b] := rfl

/-- A three-cell allocation, read back: the three variables at the counter. -/
@[simp] theorem fieldsToVar_triple_alloc (nv : Nat) :
    CircuitType.fieldsToVar (F := F) (val := F × F × F)
      (mapVec CVar.var (allocRange nv (CircuitType.size F (F × F × F))))
      = (.var nv, .var (nv + 1), .var (nv + 2)) := rfl

/-- A triple's encoding, as the list an allocation writes. -/
@[simp] theorem valueToFields_triple_toList (a b c : F) :
    (CircuitType.valueToFields (F := F) (var := FVar F × FVar F × FVar F) (a, b, c)).toList
      = [a, b, c] := rfl

/-- The base instance's dimension. -/
@[simp] theorem size_fvar : CircuitType.size F F (var := FVar F) = 1 := rfl

/-- An allocation's prefix is the shorter allocation at the same counter. -/
private theorem take_alloc (nv m k : Nat) :
    ((mapVec (CVar.var (F := F)) (allocRange nv (m + k))).take m).cast (by omega)
      = mapVec CVar.var (allocRange nv m) :=
  Vector.ext fun i hi => by
    rw [Vector.getElem_cast, Vector.take_eq_extract, Vector.getElem_extract (by omega)]
    simp [allocRange]

/-- An allocation's suffix is the allocation at the advanced counter. -/
private theorem drop_alloc (nv m k : Nat) :
    ((mapVec (CVar.var (F := F)) (allocRange nv (m + k))).drop m).cast (by omega)
      = mapVec CVar.var (allocRange (nv + m) k) :=
  Vector.ext fun i hi => by simp [allocRange, Nat.add_assoc]

/-- A pair's allocation is its components' allocations, the second at the counter
advanced past the first. -/
@[simp] theorem fieldsToVar_prod_alloc {a b av bv : Type} [A : CircuitType F a av]
    [B : CircuitType F b bv] (nv : Nat) :
    CircuitType.fieldsToVar (F := F) (val := a × b)
        (mapVec CVar.var (allocRange nv (CircuitType.size F (a × b) (var := av × bv))))
      = (CircuitType.fieldsToVar (F := F) (val := a)
            (mapVec CVar.var (allocRange nv (CircuitType.size F a (var := av)))),
         CircuitType.fieldsToVar (F := F) (val := b)
            (mapVec CVar.var (allocRange (nv + CircuitType.size F a (var := av))
              (CircuitType.size F b (var := bv))))) := by
  show (A.fieldsToVar (((mapVec CVar.var (allocRange nv (A.size + B.size))).take A.size).cast _),
      B.fieldsToVar (((mapVec CVar.var (allocRange nv (A.size + B.size))).drop A.size).cast _))
    = _
  rw [take_alloc, drop_alloc]

/-- A pair's encoding is its components' encodings, first component first. -/
@[simp] theorem valueToFields_prod_toList {a b av bv : Type} [A : CircuitType F a av]
    [B : CircuitType F b bv] (p : a × b) :
    (CircuitType.valueToFields (F := F) (var := av × bv) p).toList
      = (CircuitType.valueToFields (F := F) (var := av) p.1).toList
        ++ (CircuitType.valueToFields (F := F) (var := bv) p.2).toList := by
  show (A.valueToFields p.1 ++ B.valueToFields p.2).toList = _
  simp

/-- An unchecked-bit allocation, read back: the retagged variable at the counter. -/
@[simp] theorem fieldsToVar_uncheckedBool_alloc [Zero F] [One F] [DecidableEq F] (nv : Nat) :
    CircuitType.fieldsToVar (F := F) (val := UnChecked Bool)
      (mapVec CVar.var (allocRange nv (CircuitType.size F (UnChecked Bool))))
      = ⟨.unchecked (.var nv)⟩ := rfl

/-- An unchecked bit's encoding, as the list an allocation writes. -/
@[simp] theorem valueToFields_uncheckedBool_toList [Zero F] [One F] [DecidableEq F] (b : Bool) :
    (CircuitType.valueToFields (F := F) (var := UnChecked (BoolVar F))
      (⟨b⟩ : UnChecked Bool)).toList = [bit b] := rfl

/-- A bundle is in scope when every cell of its flattening is. -/
def CircuitType.Scoped (val : Type) [CircuitType F val var] (st : ProverState F)
    (cv : var) : Prop :=
  ∀ i (hi : i < CircuitType.size F val), ((CircuitType.varToFields (val := val) cv)[i]).Scoped st

/-- A single field variable is in scope iff its expression is. -/
theorem scoped_fvar_iff {st : ProverState F} {x : FVar F} :
    CircuitType.Scoped F st x ↔ x.Scoped st := by
  constructor
  · intro h
    exact h 0 Nat.zero_lt_one
  · intro h i hi
    have hi' : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    exact h

section ScopeProd

variable {a b av bv : Type}

/-- A pair is in scope iff its components are. -/
theorem scoped_prod_iff [A : CircuitType F a av] [B : CircuitType F b bv]
    {st : ProverState F} {p : av × bv} :
    CircuitType.Scoped (a × b) st p ↔
      CircuitType.Scoped a st p.1 ∧ CircuitType.Scoped b st p.2 := by
  constructor
  · intro h
    constructor
    · intro i hi
      have h' := h i (by show i < A.size + B.size; omega)
      rwa [show (CircuitType.varToFields (val := a × b) p)[i]'(by
            show i < A.size + B.size; omega)
          = (A.varToFields p.1)[i]
        from Vector.getElem_append_left hi] at h'
    · intro i hi
      have h' := h (A.size + i) (by show A.size + i < A.size + B.size; omega)
      have heq : (CircuitType.varToFields (val := a × b) p)[A.size + i]'(by
            show A.size + i < A.size + B.size; omega)
          = (B.varToFields p.2)[i] := by
        show (A.varToFields p.1 ++ B.varToFields p.2)[A.size + i]'(by omega)
          = (B.varToFields p.2)[i]
        rw [Vector.getElem_append_right (by omega) (by omega)]
        simp
      rwa [heq] at h'
  · rintro ⟨ha, hb⟩ i hi
    have hi' : i < A.size + B.size := hi
    show ((A.varToFields p.1 ++ B.varToFields p.2))[i].Scoped st
    by_cases hia : i < A.size
    · rw [Vector.getElem_append_left hia]
      exact ha i hia
    · rw [Vector.getElem_append_right (by omega) (by omega)]
      exact hb (i - A.size) (by omega)

end ScopeProd

section ScopeOfEquiv

variable {rep repVar : Type} (R : CircuitType F rep repVar) (e : val ≃ rep) (ev : var ≃ repVar)

/-- A presented bundle is in scope iff its representation is. -/
theorem scoped_ofEquiv_iff {st : ProverState F} {cv : var} :
    @CircuitType.Scoped F var val (R.ofEquiv e ev) st cv ↔ CircuitType.Scoped rep st (ev cv) :=
  Iff.rfl

end ScopeOfEquiv

/-! ## What a run grants

A run equation names the state after as a term (`mulRun st x y`); `Grants` is that
term's reading, for a consumer composing the run: the table grew, the result is in
scope at the state after, and it reads there as `v`. -/

/-- The reading of a run's result: the table grew, the result is in scope at the state
after, and it reads there as `v`. -/
structure Grants (val : Type) [Add F] [Mul F] [Zero F] [CircuitType F val var]
    (st : ProverState F) (p : ProverState F × var) (v : val) : Prop where
  /-- The table grew. -/
  le : st.env.Le p.1.env
  /-- The result is in scope at the state after. -/
  scope : CircuitType.Scoped val p.1 p.2
  /-- The result reads as `v` at the state after. -/
  read : readVal (val := val) p.1.env.toValuation p.2 = v

/-- A field result: in scope, reading as `v`. -/
theorem Grants.fvar [Add F] [Mul F] [Zero F] {st st' : ProverState F} {x : FVar F} {v : F}
    (hle : st.env.Le st'.env) (hs : x.Scoped st') (hv : x.val st'.env.toValuation = v) :
    Grants F st (st', x) v :=
  ⟨hle, scoped_fvar_iff.mpr hs, by rw [readVal_fvar]; exact hv⟩

/-- A field result is in scope at the state after. -/
theorem Grants.fvar_scoped [Add F] [Mul F] [Zero F] {st : ProverState F}
    {p : ProverState F × FVar F} {v : F} (h : Grants F st p v) : p.2.Scoped p.1 :=
  scoped_fvar_iff.mp h.scope

/-- A field result reads as `v` at the state after. -/
theorem Grants.fvar_val [Add F] [Mul F] [Zero F] {st : ProverState F}
    {p : ProverState F × FVar F} {v : F} (h : Grants F st p v) :
    p.2.val p.1.env.toValuation = v := by
  rw [← readVal_fvar]
  exact h.read

/-- A boolean result, read through its expression: in scope at the state after. -/
theorem Grants.bool_scoped [Add F] [Mul F] [Zero F] {st st' : ProverState F} {b : BoolVar F}
    {v : F} (h : Grants F st (st', (↑b : CVar F)) v) : (↑b : CVar F).Scoped st' :=
  h.fvar_scoped

/-- A boolean result, read through its expression: reads as `v` at the state after. -/
theorem Grants.bool_val [Add F] [Mul F] [Zero F] {st st' : ProverState F} {b : BoolVar F}
    {v : F} (h : Grants F st (st', (↑b : CVar F)) v) : (↑b : CVar F).val st'.env.toValuation = v :=
  h.fvar_val

/-- Scope survives table extension. -/
theorem CircuitType.Scoped.of_le [CircuitType F val var] {st st' : ProverState F}
    (hle : st.env.Le st'.env) {cv : var} (h : CircuitType.Scoped val st cv) :
    CircuitType.Scoped val st' cv :=
  fun i hi => (h i hi).of_le hle

/-- An in-scope bundle's reading survives table extension. -/
theorem readVal_of_le [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {st st' : ProverState F} (hle : st.env.Le st'.env) {cv : var}
    (hs : CircuitType.Scoped val st cv) :
    readVal (val := val) st'.env.toValuation cv = readVal (val := val) st.env.toValuation cv := by
  unfold readVal
  congr 1
  ext i hi
  simp only [Vector.getElem_map]
  exact CVar.val_of_le hle (hs i hi)

/-- An expression that evaluates is in scope. -/
theorem CVar.Scoped.of_eval [Add F] [Mul F] {st : ProverState F} :
    ∀ {x : CVar F} {v : F}, x.eval st.env = .ok v → x.Scoped st
  | .var w, v, h => by
    simp only [CVar.eval] at h
    split at h
    · next y hy => exact ProverState.mem_of_assigned hy
    · cases h
  | .const _, _, _ => trivial
  | .add a b, v, h => by
    simp only [CVar.eval] at h
    split at h
    · cases h
    · next xa hxa =>
      split at h
      · cases h
      · next xb hxb => exact ⟨CVar.Scoped.of_eval hxa, CVar.Scoped.of_eval hxb⟩
  | .scale _ y, v, h => by
    simp only [CVar.eval] at h
    split at h
    · cases h
    · next z hz => exact CVar.Scoped.of_eval (x := y) hz

/-! ## Encodings

What a witness leaf grants is stronger than a reading: the allocated cells *are* the
value's encoding. `Encodes` says so at a valuation; it computes at the base, boolean,
pair and vector instances as the readings do, decodes to `readVal` by the round trip,
and holds at the state an allocation lands on. -/

/-- The bundle's cells, read at `V`, are `v`'s encoding. -/
def CircuitType.Encodes (val : Type) [Add F] [Mul F] [CircuitType F val var]
    (V : Valuation F) (cv : var) (v : val) : Prop :=
  (CircuitType.varToFields (val := val) cv).map (·.val V)
    = CircuitType.valueToFields (var := var) v

/-- A single field variable encodes `k` iff it reads as `k`. -/
theorem encodes_fvar_iff [Add F] [Mul F] {V : Valuation F} {x : FVar F} {k : F} :
    CircuitType.Encodes F V x k ↔ x.val V = k := by
  constructor
  · intro h
    have := congrArg (fun w : Vector F 1 => w[0]) h
    simpa using this
  · intro h
    ext i hi
    have hi' : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    simpa [CircuitType.varToFields, CircuitType.valueToFields] using h

/-- A boolean variable is in scope iff its expression is. -/
theorem scoped_bool_iff [Zero F] [One F] [DecidableEq F] {st : ProverState F} {b : BoolVar F} :
    CircuitType.Scoped Bool st b ↔ (b.toCVar).Scoped st := by
  constructor
  · intro h
    exact h 0 Nat.zero_lt_one
  · intro h i hi
    have hi' : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    exact h

/-- A boolean variable encodes `v` iff its expression reads as `bit v`. -/
theorem encodes_bool_iff [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] {V : Valuation F}
    {b : BoolVar F} {v : Bool} :
    CircuitType.Encodes Bool V b v ↔ b.toCVar.val V = bit v := by
  constructor
  · intro h
    have := congrArg (fun w : Vector F 1 => w[0]) h
    simpa using this
  · intro h
    ext i hi
    have hi' : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    simpa [CircuitType.varToFields, CircuitType.valueToFields] using h

section EncodesProd

variable {a b av bv : Type}

/-- A pair encodes a pair iff its components encode the components. -/
theorem encodes_prod_iff [Add F] [Mul F] [A : CircuitType F a av] [B : CircuitType F b bv]
    {V : Valuation F} {p : av × bv} {v : a × b} :
    CircuitType.Encodes (a × b) V p v ↔
      CircuitType.Encodes a V p.1 v.1 ∧ CircuitType.Encodes b V p.2 v.2 := by
  show (A.varToFields p.1 ++ B.varToFields p.2).map (·.val V)
      = A.valueToFields v.1 ++ B.valueToFields v.2 ↔ _
  rw [Vector.map_append]
  exact ⟨fun h => Vector.append_inj h, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩

end EncodesProd

section EncodesVector

/-- Block `i`, cell `l` of a flattening sits at `l + i * k`. -/
private theorem block_lt {i l k n : Nat} (hi : i < n) (hl : l < k) : l + i * k < n * k :=
  calc l + i * k < k + i * k := Nat.add_lt_add_right hl _
    _ = (i + 1) * k := by rw [Nat.succ_mul, Nat.add_comm]
    _ ≤ n * k := Nat.mul_le_mul_right k hi

/-- A property of corresponding flattened cells is a property of corresponding cells
of corresponding blocks. -/
private theorem block_iff {β γ : Type} {k n : Nat} (P : β → γ → Prop)
    (xss : Vector (Vector β k) n) (yss : Vector (Vector γ k) n) :
    (∀ j (hj : j < n * k), P xss.flatten[j] yss.flatten[j]) ↔
      ∀ i (hi : i < n), ∀ l (hl : l < k), P xss[i][l] yss[i][l] := by
  constructor
  · intro h i hi l hl
    have := h (l + i * k) (block_lt hi hl)
    simp only [Vector.getElem_flatten] at this
    have hd : (l + i * k) / k = i := by
      rw [Nat.add_mul_div_right _ _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hl),
        Nat.div_eq_of_lt hl, Nat.zero_add]
    have hm : (l + i * k) % k = l := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
    simp only [hd, hm] at this
    exact this
  · intro h j hj
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp at hj
      · exact hk
    simp only [Vector.getElem_flatten]
    exact h (j / k) (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hj)) (j % k)
      (Nat.mod_lt _ hk)

/-- A vector is in scope iff its elements are. -/
theorem scoped_vector_iff [A : CircuitType F val var] {st : ProverState F} {n : Nat}
    {bs : Vector var n} :
    CircuitType.Scoped (Vector val n) st bs ↔
      ∀ i (hi : i < n), CircuitType.Scoped val st bs[i] := by
  show (∀ j (hj : j < n * A.size), ((bs.map A.varToFields).flatten[j]).Scoped st) ↔ _
  rw [block_iff (fun x (_ : CVar F) => x.Scoped st) (bs.map A.varToFields)
    (bs.map A.varToFields)]
  simp only [Vector.getElem_map]
  rfl

/-- A vector encodes a vector iff its elements encode the elements. -/
theorem encodes_vector_iff [Add F] [Mul F] [A : CircuitType F val var] {V : Valuation F}
    {n : Nat} {bs : Vector var n} {vs : Vector val n} :
    CircuitType.Encodes (Vector val n) V bs vs ↔
      ∀ i (hi : i < n), CircuitType.Encodes val V bs[i] vs[i] := by
  show ((bs.map A.varToFields).flatten).map (·.val V) = (vs.map A.valueToFields).flatten ↔ _
  have hpt : ∀ {m : Nat} (u w : Vector F m), u = w ↔ ∀ j (hj : j < m), u[j] = w[j] :=
    fun u w => ⟨fun h j hj => by rw [h], fun h => Vector.ext h⟩
  rw [hpt]
  simp only [Vector.getElem_map]
  rw [block_iff (fun x y => x.val V = y) (bs.map A.varToFields) (vs.map A.valueToFields)]
  simp only [Vector.getElem_map]
  constructor
  · intro h i hi
    exact Vector.ext fun l hl => by simpa using h i hi l hl
  · intro h i hi l hl
    have := congrArg (fun w : Vector F A.size => w[l]) (h i hi)
    simpa using this

end EncodesVector

section EncodesOfEquiv

variable {rep repVar : Type} (R : CircuitType F rep repVar) (e : val ≃ rep) (ev : var ≃ repVar)

/-- A presented bundle encodes a value iff its representation encodes the mapped value. -/
theorem encodes_ofEquiv_iff [Add F] [Mul F] {V : Valuation F} {cv : var} {v : val} :
    @CircuitType.Encodes F var val _ _ (R.ofEquiv e ev) V cv v ↔
      CircuitType.Encodes rep V (ev cv) (e v) :=
  Iff.rfl

end EncodesOfEquiv

/-- An encoding decodes to its value. -/
theorem readVal_of_encodes [Add F] [Mul F] [CircuitType F val var] [LawfulCircuitType F val var]
    {V : Valuation F} {cv : var} {v : val} (h : CircuitType.Encodes val V cv v) :
    readVal (val := val) V cv = v := by
  unfold readVal
  rw [h, LawfulCircuitType.value_roundTrip]

/-- What a witness leaf grants: the bundle allocated at the counter encodes, on the
extended table, the value whose encoding was written — `vars_roundTrip` to the cells,
then the batch's slots. -/
theorem encodes_extendMany_new [Add F] [Mul F] [Zero F] [CircuitType F val var]
    [LawfulCircuitType F val var] (st : ProverState F) (v : val) :
    CircuitType.Encodes val
      (st.extendMany (CircuitType.valueToFields (F := F) (var := var) v).toList).env.toValuation
      (CircuitType.fieldsToVar (F := F) (val := val)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F val)))) v := by
  unfold CircuitType.Encodes
  rw [LawfulCircuitType.vars_roundTrip (F := F) (val := val)]
  ext i hi
  simp only [Vector.getElem_map, getElem_mapVec, allocRange, Vector.getElem_ofFn, CVar.val]
  rw [ProverState.get_extendMany_new st (by simpa using hi)]
  simp

/-- The allocated bundle reads as the value whose encoding was written. -/
theorem readVal_extendMany_new [Add F] [Mul F] [Zero F] [CircuitType F val var]
    [LawfulCircuitType F val var] (st : ProverState F) (v : val) :
    readVal (val := val)
      (st.extendMany (CircuitType.valueToFields (F := F) (var := var) v).toList).env.toValuation
      (CircuitType.fieldsToVar (F := F) (val := val)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F val)))) = v :=
  readVal_of_encodes (encodes_extendMany_new st v)

/-- What a witness leaf allocates is in scope at the extended state. -/
theorem scoped_extendMany_new [CircuitType F val var] [LawfulCircuitType F val var]
    (st : ProverState F) (v : val) :
    CircuitType.Scoped val
      (st.extendMany (CircuitType.valueToFields (F := F) (var := var) v).toList)
      (CircuitType.fieldsToVar (F := F) (val := val)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F val)))) := by
  intro i hi
  rw [LawfulCircuitType.vars_roundTrip (F := F) (val := val)]
  simp only [getElem_mapVec, allocRange, Vector.getElem_ofFn, CVar.scoped_var]
  exact st.new_mem_extendMany (by simpa using hi)

/-- The witness leaf's grant: the bundle allocated at the counter reads as the value
whose encoding was written. -/
theorem Grants.alloc [Add F] [Mul F] [Zero F] [CircuitType F val var]
    [LawfulCircuitType F val var] (st : ProverState F) (v : val) :
    Grants val st
      (st.extendMany (CircuitType.valueToFields (F := F) (var := var) v).toList,
        CircuitType.fieldsToVar (F := F) (val := val)
          (mapVec CVar.var (allocRange st.nv (CircuitType.size F val)))) v :=
  ⟨st.le_extendMany _, scoped_extendMany_new st v, readVal_extendMany_new st v⟩

/-- An element of an allocated vector reads as the element written. -/
theorem Grants.alloc_vector_get [Add F] [Mul F] [Zero F] [CircuitType F val var]
    [LawfulCircuitType F val var] {n : Nat} (st : ProverState F) (xs : Vector val n)
    (i : Nat) (hi : i < n) :
    Grants val st
      (st.extendMany (CircuitType.valueToFields (F := F) (var := Vector var n) xs).toList,
        (CircuitType.fieldsToVar (F := F) (val := Vector val n)
          (mapVec CVar.var (allocRange st.nv (CircuitType.size F (Vector val n)))))[i]) xs[i] :=
  ⟨st.le_extendMany _, scoped_vector_iff.mp (scoped_extendMany_new st xs) i hi,
    readVal_of_encodes (encodes_vector_iff.mp (encodes_extendMany_new st xs) i hi)⟩

end Snarky
