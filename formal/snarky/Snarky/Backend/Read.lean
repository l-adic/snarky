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

/-- An in-scope expression evaluates, to its total reading at the completed table. -/
theorem CVar.eval_eq_val [Add F] [Mul F] [Zero F] {st : ProverState F} :
    ∀ {x : CVar F}, x.Scoped st → x.eval st.env = .ok (x.val st.env.toValuation)
  | .var v, hv => by simp [CVar.eval, CVar.val, st.get_eq hv]
  | .const _, _ => rfl
  | .add a b, ⟨ha, hb⟩ => by simp [CVar.eval, CVar.val, eval_eq_val ha, eval_eq_val hb]
  | .scale _ y, hy => by simp [CVar.eval, CVar.val, eval_eq_val (x := y) hy]

/-- An in-scope reading survives table extension. -/
theorem CVar.val_of_le [Add F] [Mul F] [Zero F] {st st' : ProverState F}
    (hle : st.env.Le st'.env) {x : CVar F} (hs : x.Scoped st) :
    x.val st'.env.toValuation = x.val st.env.toValuation := by
  have h := CVar.eval_le hle (CVar.eval_eq_val hs)
  rw [CVar.eval_eq_val (hs.of_le hle)] at h
  injection h

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

/-- What a witness leaf grants: the bundle allocated at the counter reads, on the
extended table, as the value whose encoding was written — `vars_roundTrip` to the
cells, the batch's slots, `value_roundTrip` back. -/
theorem readVal_extendMany_new [Add F] [Mul F] [Zero F] [CircuitType F val var]
    [LawfulCircuitType F val var] (st : ProverState F) (v : val) :
    readVal (val := val)
      (st.extendMany (CircuitType.valueToFields (F := F) (var := var) v).toList).env.toValuation
      (CircuitType.fieldsToVar (F := F) (val := val)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F val)))) = v := by
  unfold readVal
  rw [LawfulCircuitType.vars_roundTrip (F := F) (val := val)]
  set st' := st.extendMany (CircuitType.valueToFields (F := F) (var := var) v).toList with hst'
  have hcells : (mapVec CVar.var (allocRange st.nv (CircuitType.size F val))).map
      (·.val st'.env.toValuation)
      = CircuitType.valueToFields (F := F) (var := var) v := by
    ext i hi
    simp only [Vector.getElem_map, getElem_mapVec, allocRange, Vector.getElem_ofFn, CVar.val]
    rw [ProverState.get_extendMany_new st (by simpa using hi)]
    simp
  rw [hcells, LawfulCircuitType.value_roundTrip]

end Snarky
