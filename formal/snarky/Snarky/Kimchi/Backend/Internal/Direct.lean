import Snarky.Kimchi.Backend.IndexSpec
import Snarky.Kimchi.Backend.Internal.Receipts
import Snarky.Kimchi.Backend.Internal.Wiring
import Kimchi.Index.Basic
import Kimchi.Index.Satisfies
import Kimchi.Columns

/-!
# The direct fragment

The source constraints the lowering places directly: a Boolean on a bare variable, or a
complete addition over bare variables. Their reduction allocates no variable and asserts no
equality, so the union-find, the constant cache and the pinning rows stay untouched, and
every generic equation comes from a Boolean. The fragment still exercises generic batching
across custom blocks, the final flush, repeated wired operands, single-use unwired operands,
and the public rows.

## Main definitions

- `KimchiConstraint.Direct`: membership in the fragment.
- `KimchiConstraint.Direct.Scoped`: the scoping condition on a source list and its public
  variables: every constraint direct, and every operand of an unwired column occurring once.
- `classGates`: the assembled gate list with the class-based wiring.
- `lowering`, `directRows`, `directRoots`: the recorded lowering, its rows and roots; the
  wired fragment reuses them.

## Main results

- `record_boolean_var`, `record_addComplete_direct`: the recorded reduction of each fragment
  constraint in closed form: a Boolean's one generic event, a complete addition's empty log
  and its row over the operands.
- `KimchiConstraint.Direct.events_generic`, `steps_generic_of_direct`: a direct constraint's
  events are generic with no coefficient on an absent cell.
- `KimchiConstraint.Direct.holds_of_satisfies`: any table satisfying an index of the
  fragment's lowering yields a valuation satisfying every source constraint and reading the
  public variables as the public input.
- `directGates_eq_classGates`: the assembled gates are the class-based ones.
- `indexOf_of_classTarget`: an index matching the lowering's rows and the class-based wiring
  agrees with the assembly, so `IndexOf` is decided on concrete data.
- `IndexOf.rows_le`, `IndexOf.typ_eq`, `IndexOf.coeffs_eq`, `IndexOf.classCells_eq`: what an
  index of the lowering says row by row, and that a satisfying table reads alike on every
  cell of a wiring class; the wired fragment reuses them.
- `directRows_gateRow`: a row of a step's gate block, located among the lowering's rows.

## Implementation notes

`Scoped` restricts the fragment enough to recover a valuation from any table satisfying the
index: an operand in a wired column is forced equal across its occurrences by the copy
constraints, and an operand in an unwired column occurs once, so its one cell names its
value. It is a sufficient restriction for this fragment, not a condition the production
circuits meet.

The assembly's wiring goes through a hash map the kernel cannot evaluate; `classGates` is the
same list computed from the classes, so a concrete instance is decided by rewriting with
`directGates_eq_classGates` and evaluating the rest unchanged.
-/

open Kimchi

namespace Snarky

variable {F : Type}

namespace Kimchi

/-- A constraint the lowering places directly: a Boolean on a bare variable, or a complete
addition whose eleven operands are bare variables. Its reduction allocates no variable and
asserts no equality. -/
def KimchiConstraint.Direct : KimchiConstraint F → Prop
  | .basic (.boolean (.var _)) => True
  | .addComplete c => ∀ x ∈ c.operands.toList, x.var?.isSome
  | _ => False

instance KimchiConstraint.decidableDirect (c : KimchiConstraint F) : Decidable c.Direct := by
  unfold KimchiConstraint.Direct
  split <;> infer_instance

/-- The variables a direct constraint names, in gate-column order; empty off the fragment. -/
private def KimchiConstraint.directVars : KimchiConstraint F → List Variable
  | .basic (.boolean x) => x.var?.toList
  | .addComplete c => c.operands.toList.filterMap CVar.var?
  | _ => []

/-- Every variable the source and the public variables name, with repetition. -/
private def directOccurrences (source : List (KimchiConstraint F)) (publicVars : List Variable) :
    List Variable :=
  source.flatMap KimchiConstraint.directVars ++ publicVars

/-- The scoping condition under which any table satisfying the fragment's index determines
a valuation: every constraint is direct, and every operand of an unwired column occurs
exactly once among the operand occurrences and the public variables. -/
structure KimchiConstraint.Direct.Scoped (source : List (KimchiConstraint F))
    (publicVars : List Variable) : Prop where
  /-- Every constraint is in the fragment. -/
  direct : ∀ c ∈ source, c.Direct
  /-- Every operand of an unwired column occurs exactly once among the operand occurrences
  and the public variables. -/
  unwiredOnce : ∀ c ∈ source, ∀ v ∈ c.unwiredVars, (directOccurrences source publicVars).count v = 1

instance (source : List (KimchiConstraint F)) (publicVars : List Variable) :
    Decidable (KimchiConstraint.Direct.Scoped source publicVars) :=
  decidable_of_iff
    ((∀ c ∈ source, c.Direct) ∧
      ∀ c ∈ source, ∀ v ∈ c.unwiredVars, (directOccurrences source publicVars).count v = 1)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

variable [Field F] [DecidableEq F]

/-! ## The fragment's recorded lowering -/

/-- A Boolean on a bare variable records one generic event, its Booleanity equation on the
variable in the left and right cells. -/
theorem record_boolean_var (nv : Variable) (aux : AuxState F) (v : Variable) :
    (recordReduction nv aux
      (KimchiConstraint.reduce (F := F) (.basic (.boolean (.var v))))).events =
      [.generic { cl := -1, vl := some v, cr := 0, vr := some v, co := 0, vo := none,
                  m := 1, c := 0 }] := by
  refine Eq.trans (b := [.generic { cl := -1, vl := some v, cr := 0, vr := some v, co := 0,
                                     vo := none, m := 1 * 1, c := 0 }]) rfl ?_
  simp

/-- A direct complete addition records no event, and its result is the one row labelled by
its operands in gate-column order. -/
theorem record_addComplete_direct (nv : Variable) (aux : AuxState F) {c : AddComplete F}
    (hc : (KimchiConstraint.addComplete c).Direct) :
    (recordReduction nv aux (KimchiConstraint.reduce (.addComplete c))).events = [] ∧
    (recordReduction nv aux (KimchiConstraint.reduce (.addComplete c))).result =
      .addComplete ⟨{ kind := .completeAdd,
                      vars := ⟨⟨c.operands.toList.map CVar.var? ++ List.replicate 4 none⟩,
                        by simp⟩,
                      coeffs := [] }⟩ := by
  obtain ⟨⟨x1, y1⟩, ⟨x2, y2⟩, ⟨x3, y3⟩, inf, sameX, s, infZ, x21Inv⟩ := c
  simp only [KimchiConstraint.Direct, AddComplete.operands] at hc
  obtain ⟨v1, rfl⟩ := CVar.var?_isSome (hc x1 (by simp))
  obtain ⟨w1, rfl⟩ := CVar.var?_isSome (hc y1 (by simp))
  obtain ⟨v2, rfl⟩ := CVar.var?_isSome (hc x2 (by simp))
  obtain ⟨w2, rfl⟩ := CVar.var?_isSome (hc y2 (by simp))
  obtain ⟨v3, rfl⟩ := CVar.var?_isSome (hc x3 (by simp))
  obtain ⟨w3, rfl⟩ := CVar.var?_isSome (hc y3 (by simp))
  obtain ⟨u1, rfl⟩ := CVar.var?_isSome (hc inf (by simp))
  obtain ⟨u2, rfl⟩ := CVar.var?_isSome (hc sameX (by simp))
  obtain ⟨u3, rfl⟩ := CVar.var?_isSome (hc s (by simp))
  obtain ⟨u4, rfl⟩ := CVar.var?_isSome (hc infZ (by simp))
  obtain ⟨u5, rfl⟩ := CVar.var?_isSome (hc x21Inv (by simp))
  simp [recordReduction, KimchiConstraint.reduce, AddComplete.reduce, reduceAffinePoint,
    reduceToVariable, CVar.reduceToAffineExpression, reduceAffineExpression, bind, StateT.bind,
    pure, StateT.pure, Functor.map, StateT.map, AddComplete.operands, CVar.var?]

/-- A direct constraint's recorded events are generic, each carrying no coefficient on an
absent cell. -/
theorem KimchiConstraint.Direct.events_generic {c : KimchiConstraint F} (hc : c.Direct)
    (nv : Variable) (aux : AuxState F) :
    ∀ e ∈ (recordReduction nv aux c.reduce).events, ∃ g, e = .generic g ∧ g.AbsentZero := by
  unfold KimchiConstraint.Direct at hc
  split at hc
  · rw [record_boolean_var]
    intro e he
    rw [List.mem_singleton] at he
    exact ⟨_, he, by simp [GenericPlonkConstraint.AbsentZero]⟩
  · rw [(record_addComplete_direct nv aux hc).1]
    simp
  · exact hc.elim

/-- Every event of a direct list's recorded lowering is generic, with no coefficient on an
absent cell. -/
theorem steps_generic_of_direct {source : List (KimchiConstraint F)}
    (hs : ∀ c ∈ source, c.Direct) (nv : Variable) (aux : AuxState F) :
    ∀ s ∈ (recordGates source nv aux).steps, ∀ e ∈ s.events,
      ∃ g, e = .generic g ∧ g.AbsentZero := by
  induction source generalizing nv aux with
  | nil => simp [recordGates]
  | cons con cons ih =>
    intro s hs' e he
    simp only [recordGates, List.mem_cons] at hs'
    rcases hs' with rfl | hs'
    · exact (hs con (List.mem_cons_self ..)).events_generic nv aux e he
    · exact ih (fun c hc => hs c (List.mem_cons_of_mem _ hc)) _ _ s hs' e he

/-! ## The lowering's rows -/

/-- The fragment's recorded lowering from the initial auxiliary state. -/
abbrev lowering (source : List (KimchiConstraint F)) (nv : Variable) :
    RecordedGates F :=
  recordGates source nv initialAuxState

/-- The rows the fragment's assembly wires: the public rows, then the recorded lowering's
rows with the final flush. -/
def directRows (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) : List (KimchiRow F) :=
  makePublicInputRows publicVars ++ (lowering source nv).allRows

/-- The roots the fragment's assembly wires through. -/
def directRoots (source : List (KimchiConstraint F)) (nv : Variable) : Array Variable :=
  UnionFind.rootOf (directBuilt source nv).aux.wireState.unionFind

/-- The fragment's assembled gates are the production assembly of its rows through its
roots. -/
private theorem directGates_eq (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) :
    directGates source publicVars nv =
      assembleGates (directRoots source nv) (directRows source publicVars nv) := by
  have h := recordBuilt_bodyRows (⟨(), nv, source⟩ : Built (KimchiConstraint F) Unit)
  rw [recordBuilt_erase] at h
  simp only [directGates, directBuilt, gateDataOf, makeGateData, directRows, directRoots, h]
  rfl

/-- The gate list with the class-based wiring: the production assembly, each wire target read
from the classes rather than the hash map. -/
def classGates (roots : Array Variable) (rows : List (KimchiRow F)) : List (AssembledGate F) :=
  rows.zipIdx.map fun (row, i) =>
    { kind := row.kind,
      wires := ⟨⟨[classTarget roots rows i 0, classTarget roots rows i 1,
                  classTarget roots rows i 2, classTarget roots rows i 3,
                  classTarget roots rows i 4, classTarget roots rows i 5,
                  classTarget roots rows i 6]⟩, by simp⟩,
      coeffs := row.coeffs }

/-- The assembled gates are the class-based ones. -/
theorem directGates_eq_classGates (source : List (KimchiConstraint F))
    (publicVars : List Variable) (nv : Variable) :
    directGates source publicVars nv =
      classGates (directRoots source nv) (directRows source publicVars nv) := by
  rw [directGates_eq]
  unfold assembleGates classGates
  simp only [wireTarget_eq]

/-- The roots the assembly wires through are the recorded lowering's union-find roots. -/
theorem directRoots_eq (source : List (KimchiConstraint F)) (nv : Variable) :
    directRoots source nv = UnionFind.rootOf (lowering source nv).aux.wireState.unionFind := by
  have h := recordBuilt_erase (⟨(), nv, source⟩ : Built (KimchiConstraint F) Unit)
  simp only [directRoots, directBuilt, ← h, recordBuilt]

/-- The fragment's gate table has one row per row of the lowering. -/
theorem length_directGates (source : List (KimchiConstraint F))
    (publicVars : List Variable) (nv : Variable) :
    (directGates source publicVars nv).length = (directRows source publicVars nv).length := by
  rw [directGates_eq, length_assembleGates]

/-- An assembled row of the fragment: its row's tag and coefficients, and the wire map's
targets at its permutation cells. -/
theorem getElem_directGates (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) (r : Nat) (hr : r < (directRows source publicVars nv).length) :
    (directGates source publicVars nv)[r]'((length_directGates source publicVars nv).symm ▸ hr) =
      { kind := (directRows source publicVars nv)[r].kind,
        wires := ⟨⟨[wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv))
            r 0,
          wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv)) r 1,
          wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv)) r 2,
          wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv)) r 3,
          wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv)) r 4,
          wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv)) r 5,
          wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv)) r 6]⟩,
          by simp⟩,
        coeffs := (directRows source publicVars nv)[r].coeffs } := by
  rw [List.getElem_of_eq (directGates_eq source publicVars nv)]
  exact getElem_assembleGates _ _ r hr

/-- An index agrees with the fragment's assembly when its rows carry the lowering's tags and
coefficients and the class-based wiring targets, which compute where the assembly's hash map
does not. -/
theorem indexOf_of_classTarget {n : ℕ} (source : List (KimchiConstraint F))
    (publicVars : List Variable) (nv : Variable) (idx : Index F n)
    (hpub : idx.publicCount = publicVars.length)
    (hparams : ∀ c ∈ source, c.ParamsAgree idx.mds idx.endoBase)
    (hfits : (directRows source publicVars nv).length ≤ n - idx.zkRows)
    (htyp : ∀ (i : Fin n) (hi : i.val < (directRows source publicVars nv).length),
      (idx.gates i).typ = (directRows source publicVars nv)[i.val].kind)
    (hcoeffs : ∀ (i : Fin n) (hi : i.val < (directRows source publicVars nv).length)
      (c : Fin coeffCols),
      (idx.gates i).coeffs c = (directRows source publicVars nv)[i.val].coeffs.getD c.val 0)
    (hwires : ∀ (i : Fin n) (_hi : i.val < (directRows source publicVars nv).length)
      (c : Fin permCols),
      (((idx.gates i).wires c).1 : ℕ) =
          (classTarget (directRoots source nv) (directRows source publicVars nv) i.val c.val).col ∧
        (((idx.gates i).wires c).2 : ℕ) =
          (classTarget (directRoots source nv) (directRows source publicVars nv) i.val c.val).row) :
    IndexOf source publicVars nv idx where
  publicCount := hpub
  params := hparams
  fits := by
    rw [length_directGates]
    exact hfits
  typ i hi := by
    have hi' : i.val < (directRows source publicVars nv).length := by
      rwa [length_directGates] at hi
    rw [getElem_directGates source publicVars nv i.val hi']
    exact htyp i hi'
  coeffs i hi c := by
    have hi' : i.val < (directRows source publicVars nv).length := by
      rwa [length_directGates] at hi
    rw [getElem_directGates source publicVars nv i.val hi']
    exact hcoeffs i hi' c
  wires i hi c := by
    have hi' : i.val < (directRows source publicVars nv).length := by
      rwa [length_directGates] at hi
    rw [getElem_directGates source publicVars nv i.val hi']
    obtain ⟨h1, h2⟩ := hwires i hi' c
    fin_cases c <;> simp only [wireTarget_eq] <;> exact ⟨h1, h2⟩

/-! ## The index at the lowering -/

/-- A cell's value in a table: zero outside it. -/
def cellVal {n : ℕ} (wTab : Fin n → Fin wCols → F) (c : Nat × Nat) : F :=
  if h : c.1 < n ∧ c.2 < wCols then wTab ⟨c.1, h.1⟩ ⟨c.2, h.2⟩ else 0

/-- The lowering's rows fit before the index's masked rows. -/
theorem IndexOf.rows_le {n : ℕ} {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} {idx : Index F n} (h : IndexOf source publicVars nv idx) :
    (directRows source publicVars nv).length ≤ n := by
  have h1 := h.fits
  have h2 := idx.zk_le
  rw [length_directGates] at h1
  omega

/-- At a row of the lowering, the index's gate type is the row's. -/
theorem IndexOf.typ_eq {n : ℕ} {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} {idx : Index F n} (h : IndexOf source publicVars nv idx) (r : Nat)
    (hr : r < (directRows source publicVars nv).length) :
    (idx.gates ⟨r, lt_of_lt_of_le hr h.rows_le⟩).typ = (directRows source publicVars nv)[r].kind :=
  (h.typ ⟨r, lt_of_lt_of_le hr h.rows_le⟩
    ((length_directGates source publicVars nv).symm ▸ hr)).trans
    (congrArg AssembledGate.kind (getElem_directGates source publicVars nv r hr))

/-- At a row of the lowering, the index's coefficients are the row's, zero-extended. -/
theorem IndexOf.coeffs_eq {n : ℕ} {source : List (KimchiConstraint F)}
    {publicVars : List Variable} {nv : Variable} {idx : Index F n}
    (h : IndexOf source publicVars nv idx) (r : Nat)
    (hr : r < (directRows source publicVars nv).length) (c : Fin coeffCols) :
    (idx.gates ⟨r, lt_of_lt_of_le hr h.rows_le⟩).coeffs c =
      (directRows source publicVars nv)[r].coeffs.getD c.val 0 :=
  (h.coeffs ⟨r, lt_of_lt_of_le hr h.rows_le⟩
    ((length_directGates source publicVars nv).symm ▸ hr) c).trans
    (congrArg (fun g : AssembledGate F => g.coeffs.getD c.val 0)
      (getElem_directGates source publicVars nv r hr))

/-- Under a satisfying table, the cells of one class of the lowering's wiring read alike: the
index's wires link them in one cycle, and the table carries one value around it. -/
theorem IndexOf.classCells_eq {n : ℕ} [NeZero n] {source : List (KimchiConstraint F)}
    {publicVars : List Variable} {nv : Variable} {idx : Index F n}
    (h : IndexOf source publicVars nv idx) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (hsat : idx.Satisfies pub wTab) (k : Variable)
    {c c' : Nat × Nat}
    (hc : c ∈ classCells (directRoots source nv) (directRows source publicVars nv) k)
    (hc' : c' ∈ classCells (directRoots source nv) (directRows source publicVars nv) k) :
    cellVal wTab c = cellVal wTab c' := by
  have hrows_le := h.rows_le
  have hlenG := length_directGates source publicVars nv
  have hgate := getElem_directGates source publicVars nv
  have hwire : ∀ (r : Nat) (hr : r < (directRows source publicVars nv).length) (c : Fin permCols),
      (((idx.gates ⟨r, by omega⟩).wires c).1 : ℕ) =
          (wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv)) r c).col ∧
        (((idx.gates ⟨r, by omega⟩).wires c).2 : ℕ) =
          (wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv)) r c).row
      := by
    intro r hr c
    have hw := h.wires ⟨r, by omega⟩ (hlenG ▸ hr) c
    simp only [hgate r hr] at hw
    fin_cases c <;> exact hw
  refine classCells_values_eq (directRoots source nv) (directRows source publicVars nv) k
    (cellVal wTab) ?_ hc hc'
  intro c hc
  obtain ⟨hr, hj⟩ := classCells_bounds hc
  obtain ⟨h1, h2⟩ := hwire c.1 hr ⟨c.2, hj⟩
  have hs2 := hsat.2.1 (⟨c.2, hj⟩, ⟨c.1, by omega⟩)
  have hwm : idx.wiringMap (⟨c.2, hj⟩, ⟨c.1, by omega⟩) =
      (idx.gates ⟨c.1, by omega⟩).wires ⟨c.2, hj⟩ := rfl
  rw [hwm] at hs2
  simp only [Index.cellValue] at hs2
  have hb1 : (wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv)) c.1
      c.2).row < n := h2 ▸ ((idx.gates ⟨c.1, by omega⟩).wires ⟨c.2, hj⟩).2.isLt
  have hb2 : (wireTarget (wireMap (directRoots source nv) (directRows source publicVars nv)) c.1
      c.2).col < wCols := by
    rw [← h1]
    exact lt_trans ((idx.gates ⟨c.1, by omega⟩).wires ⟨c.2, hj⟩).1.isLt (by decide)
  simp only [cellVal, dif_pos (And.intro hb1 hb2), dif_pos (And.intro (lt_of_lt_of_le hr hrows_le)
    (lt_trans hj (by decide : 7 < wCols)))]
  refine Eq.trans ?_ hs2
  congr 1
  · exact Fin.ext h2.symm
  · exact Fin.ext h1.symm

/-! ## Provenance of the rows -/

/-- The Booleanity equation on a variable. -/
private def booleanGate (v : Variable) : GenericPlonkConstraint F :=
  { cl := -1, vl := some v, cr := 0, vr := some v, co := 0, vo := none, m := 1, c := 0 }

/-- The queued constraint, if any, has the property. -/
def QueueFrom (P : GenericPlonkConstraint F → Prop) (aux : AuxState F) : Prop :=
  ∀ g, aux.queuedGenericGate = some g → P g

private theorem replayEvent_generic (s : BuilderReductionState F) (g : GenericPlonkConstraint F) :
    replayEvent s (.generic g) = match s.aux.queuedGenericGate with
      | none => { s with aux.queuedGenericGate := some g }
      | some queued =>
        { s with constraints := emitDoubleGateRow queued g :: s.constraints,
                 aux.queuedGenericGate := none } := by
  show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2 = _
  rw [addGenericPlonkConstraint_apply]
  rfl

/-- Replaying generic events with the property from a queue with it: every new row packs two
such constraints, the queue keeps it, and the wiring and counter are untouched. -/
private theorem replay_generic (P : GenericPlonkConstraint F → Prop) :
    ∀ (es : List (ReductionEvent F)) (s : BuilderReductionState F),
      (∀ e ∈ es, ∃ g, e = .generic g ∧ P g) → QueueFrom P s.aux →
      (∀ row ∈ (replay s es).constraints,
        row ∈ s.constraints ∨ ∃ q g, P q ∧ P g ∧ row = emitDoubleGateRow q g) ∧
      QueueFrom P (replay s es).aux ∧ (replay s es).aux.wireState = s.aux.wireState ∧
      (replay s es).nextVariable = s.nextVariable
  | [], _, _, hq => ⟨fun _ h => Or.inl h, hq, rfl, rfl⟩
  | e :: es, s, hes, hq => by
    obtain ⟨g, rfl, hg⟩ := hes e (List.mem_cons_self ..)
    have hes' := fun e he => hes e (List.mem_cons_of_mem _ he)
    have hstep : replay s (.generic g :: es) = replay (replayEvent s (.generic g)) es := rfl
    rw [hstep, replayEvent_generic]
    cases hqg : s.aux.queuedGenericGate with
    | none =>
      exact replay_generic P es { s with aux.queuedGenericGate := some g } hes'
        fun g' hg' => by
          simp only [Option.some.injEq] at hg'
          exact hg' ▸ hg
    | some queued =>
      obtain ⟨h1, h2, h3, h4⟩ := replay_generic P es
        { s with constraints := emitDoubleGateRow queued g :: s.constraints,
                 aux.queuedGenericGate := none } hes' fun _ h => by simp at h
      refine ⟨fun row hrow => ?_, h2, h3, h4⟩
      rcases h1 row hrow with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨queued, g, hq queued hqg, hg, rfl⟩
        · exact Or.inl h
      · exact Or.inr h

/-- A direct constraint's recorded reduction, from a queue with the property, when its generic
events have it: every flushed row packs two such constraints, the queue keeps it, and the
wiring and counter are untouched. -/
private theorem record_direct_rows (P : GenericPlonkConstraint F → Prop) {c : KimchiConstraint F}
    (hc : c.Direct) (nv : Variable) (aux : AuxState F)
    (hP : ∀ g, .generic g ∈ (recordReduction nv aux c.reduce).events → P g)
    (hq : QueueFrom P aux) :
    (∀ r ∈ (recordReduction nv aux c.reduce).rows,
      ∃ q g, P q ∧ P g ∧ r.row = emitDoubleGateRow q g) ∧
    QueueFrom P (recordReduction nv aux c.reduce).aux ∧
    (recordReduction nv aux c.reduce).aux.wireState = aux.wireState ∧
    (recordReduction nv aux c.reduce).nextVariable = nv := by
  have hrep := record_constraint_replays nv aux c
  have hes : ∀ e ∈ (recordReduction nv aux c.reduce).events, ∃ g, e = .generic g ∧ P g :=
    fun e he => by
      obtain ⟨g, rfl, -⟩ := hc.events_generic nv aux e he
      exact ⟨g, rfl, hP g he⟩
  obtain ⟨h1, h2, h3, h4⟩ := replay_generic P _ ⟨[], nv, aux⟩ hes hq
  rw [← hrep] at h1 h2 h3 h4
  simp only [RecordedReduction.finish] at h1 h2 h3 h4
  refine ⟨fun r hr => ?_, h2, h3, h4⟩
  rcases h1 r.row (by simp only [List.mem_reverse, List.mem_map]; exact ⟨r, hr, rfl⟩) with h | h
  · exact (List.not_mem_nil h).elim
  · exact h

theorem length_steps (source : List (KimchiConstraint F)) (nv : Variable)
    (aux : AuxState F) : (recordGates source nv aux).steps.length = source.length := by
  induction source generalizing nv aux with
  | nil => rfl
  | cons con cons ih => simp [recordGates, ih]

/-- The recorded fold over a direct list from a queue with the property, when every
constraint's generic events have it: each step is one constraint's recording from a queue
with the property, and the queue handed back keeps it. -/
private theorem recordGates_direct (P : GenericPlonkConstraint F → Prop)
    (source : List (KimchiConstraint F)) (hs : ∀ c ∈ source, c.Direct)
    (hP : ∀ c ∈ source, ∀ nv aux g, .generic g ∈ (recordReduction nv aux c.reduce).events →
      P g) :
    ∀ nv aux, QueueFrom P aux →
      (∀ p (hp : p < source.length), ∃ nv' aux', QueueFrom P aux' ∧
        (recordGates source nv aux).steps[p]'((length_steps source nv aux).symm ▸ hp) =
          ⟨(recordReduction nv' aux' source[p].reduce).rows,
            (recordReduction nv' aux' source[p].reduce).result,
            (recordReduction nv' aux' source[p].reduce).events⟩) ∧
      QueueFrom P (recordGates source nv aux).aux := by
  induction source with
  | nil => exact fun nv aux hq => ⟨fun p hp => absurd hp (Nat.not_lt_zero _), hq⟩
  | cons con cons ih =>
    intro nv aux hq
    have hcon := hs con (List.mem_cons_self ..)
    have hs' := fun c hc => hs c (List.mem_cons_of_mem _ hc)
    have hP' := fun c hc => hP c (List.mem_cons_of_mem _ hc)
    obtain ⟨-, hq', -, -⟩ := record_direct_rows P hcon nv aux
      (hP con (List.mem_cons_self ..) nv aux) hq
    obtain ⟨ih1, ih2⟩ := ih hs' hP' _ _ hq'
    refine ⟨fun p hp => ?_, ih2⟩
    cases p with
    | zero => exact ⟨nv, aux, hq, rfl⟩
    | succ p =>
      obtain ⟨nv', aux', hq'', hstep⟩ := ih1 p (Nat.lt_of_succ_lt_succ hp)
      exact ⟨nv', aux', hq'', hstep⟩

/-- A Booleanity equation of the source: a Boolean on a bare variable among its constraints. -/
private def BoolGate (source : List (KimchiConstraint F)) (g : GenericPlonkConstraint F) : Prop :=
  ∃ v, KimchiConstraint.basic (.boolean (.var v)) ∈ source ∧ g = booleanGate v

private theorem boolGate_of_events (source : List (KimchiConstraint F)) {c : KimchiConstraint F}
    (hc : c ∈ source) (hd : c.Direct) (nv : Variable) (aux : AuxState F)
    (g : GenericPlonkConstraint F) (hg : .generic g ∈ (recordReduction nv aux c.reduce).events) :
    BoolGate source g := by
  unfold KimchiConstraint.Direct at hd
  split at hd
  · rw [record_boolean_var, List.mem_singleton, ReductionEvent.generic.injEq] at hg
    exact ⟨_, hc, hg⟩
  · rw [(record_addComplete_direct nv aux hd).1] at hg
    exact (List.not_mem_nil hg).elim
  · exact hd.elim

/-- The one row of a direct complete addition. -/
private def addRow (c : AddComplete F) : KimchiRow F :=
  { kind := .completeAdd,
    vars := ⟨⟨c.operands.toList.map CVar.var? ++ List.replicate 4 none⟩, by simp⟩,
    coeffs := [] }

/-- The final flush's row for a queued constraint. -/
def flushRow (g : GenericPlonkConstraint F) : KimchiRow F :=
  { kind := .generic,
    vars := ⟨⟨[g.vl, g.vr, g.vo] ++ List.replicate 12 none⟩, by simp⟩,
    coeffs := constraintToCoeffs g }

/-- The row of a step's gate among the lowering's rows: after the public rows, at the step's
gate span. -/
def gateRowOf (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) (p : Nat) (hp : p < source.length) : Nat :=
  publicVars.length + ((lowering source nv).placements[p]'(by
    rw [RecordedGates.length_placements, length_steps]; exact hp)).customRows.first

/-- A row of a step's gate block, read among the lowering's rows after the public prefix. -/
theorem directRows_gateRow (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) (p : Nat) (hp : p < source.length) (k : Nat)
    (hk : k < ((lowering source nv).steps[p]'((length_steps source nv initialAuxState).symm ▸
      hp)).gateRows.length) :
    (directRows source publicVars nv)[gateRowOf source publicVars nv p hp + k]? =
      some (((lowering source nv).steps[p]'((length_steps source nv initialAuxState).symm ▸
        hp)).gateRows[k]) := by
  have hi : p < (lowering source nv).steps.length :=
    (length_steps source nv initialAuxState).symm ▸ hp
  have hip : p < (lowering source nv).placements.length := by
    rw [RecordedGates.length_placements]
    exact hi
  have hlenPub : (makePublicInputRows (F := F) publicVars).length = publicVars.length := by
    simp [makePublicInputRows]
  have hle := placements_customRows_le (lowering source nv) p hi
  rw [placements_customRows_count _ _ hi] at hle
  have hle' : ((lowering source nv).placements[p]'hip).customRows.first +
      (lowering source nv).steps[p].gateRows.length ≤ (lowering source nv).bodyRows.length := hle
  have hb : ((lowering source nv).placements[p]'hip).customRows.first + k <
      (lowering source nv).bodyRows.length := by omega
  have hrow := getElem_bodyRows_gate (lowering source nv) p hi k hk hb
  show (makePublicInputRows publicVars ++ ((lowering source nv).bodyRows ++
    ((finalizeGateQueue (lowering source nv).aux.queuedGenericGate).map (·.row)).toList))[
      publicVars.length + ((lowering source nv).placements[p]'hip).customRows.first + k]? = _
  rw [List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)]
  have hidx : publicVars.length + ((lowering source nv).placements[p]'hip).customRows.first + k -
      (makePublicInputRows (F := F) publicVars).length =
      ((lowering source nv).placements[p]'hip).customRows.first + k := by omega
  rw [hidx, List.getElem?_eq_getElem hb]
  exact congrArg some hrow

/-- Where each row of the fragment's lowering comes from: a public row, a packed pair of
Booleanity equations, the flushed Booleanity equation, or a direct complete addition's row at
its step's gate span. -/
private theorem directRows_cases {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} (hs : ∀ c ∈ source, c.Direct) (r : Nat)
    (hr : r < (directRows source publicVars nv).length) :
    (∃ (h : r < publicVars.length), (directRows source publicVars nv)[r] =
        (makePublicInputRows (F := F) publicVars)[r]'(by simpa [makePublicInputRows] using h)) ∨
    (∃ q g, BoolGate source q ∧ BoolGate source g ∧
      (directRows source publicVars nv)[r] = emitDoubleGateRow q g) ∨
    (∃ g, BoolGate source g ∧ (directRows source publicVars nv)[r] = flushRow g) ∨
    (∃ (p : Nat) (hp : p < source.length) (c : AddComplete F), source[p] = .addComplete c ∧
      r = gateRowOf source publicVars nv p hp ∧ (directRows source publicVars nv)[r] = addRow c)
    := by
  have hlen : (makePublicInputRows (F := F) publicVars).length = publicVars.length := by
    simp [makePublicInputRows]
  have hfold := recordGates_direct (BoolGate source) source hs
    (fun c hc => boolGate_of_events source hc (hs c hc)) nv initialAuxState
    (fun _ h => by simp [initialAuxState] at h)
  by_cases hpub : r < publicVars.length
  · exact Or.inl ⟨hpub, List.getElem_append_left (hlen ▸ hpub)⟩
  right
  have hk : r - publicVars.length < (lowering source nv).allRows.length := by
    simp only [directRows, List.length_append, hlen] at hr
    omega
  have e : (directRows source publicVars nv)[r] =
      (lowering source nv).allRows[r - publicVars.length] := by
    simp only [directRows]
    rw [List.getElem_append_right (hlen ▸ Nat.le_of_not_lt hpub)]
    simp only [hlen]
  rw [e]
  by_cases hb : r - publicVars.length < (lowering source nv).bodyRows.length
  · have e2 : (lowering source nv).allRows[r - publicVars.length] =
        (lowering source nv).bodyRows[r - publicVars.length] :=
      List.getElem_append_left hb
    rw [e2]
    obtain ⟨i, hi, hc⟩ := bodyRows_placed (lowering source nv) (r - publicVars.length) hb
    have hi' : i < source.length := (length_steps source nv initialAuxState) ▸ hi
    have hip : i < (lowering source nv).placements.length := by
      rw [RecordedGates.length_placements]; exact hi
    obtain ⟨nv', aux', hq', hstep⟩ := hfold.1 i hi'
    have hd := hs _ (List.getElem_mem hi')
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [placements_genericRows_count _ _ hi] at h2
      have h1' : ((lowering source nv).placements[i]'hip).genericRows.first ≤
        r - publicVars.length := h1
      have h2' : r - publicVars.length <
        ((lowering source nv).placements[i]'hip).genericRows.first +
          (lowering source nv).steps[i].rows.length := h2
      have hj : r - publicVars.length - ((lowering source nv).placements[i]'hip).genericRows.first <
        (lowering source nv).steps[i].rows.length := by omega
      have hrow := getElem_bodyRows_generic (lowering source nv) i hi _ hj
        (show ((lowering source nv).placements[i]'hip).genericRows.first +
          (r - publicVars.length - ((lowering source nv).placements[i]'hip).genericRows.first) <
          (lowering source nv).bodyRows.length by omega)
      have eidx : ((lowering source nv).placements[i]'hip).genericRows.first +
          (r - publicVars.length - ((lowering source nv).placements[i]'hip).genericRows.first) =
          r - publicVars.length := by omega
      have hstep' : (lowering source nv).steps[i] =
          ⟨(recordReduction nv' aux' source[i].reduce).rows,
            (recordReduction nv' aux' source[i].reduce).result,
            (recordReduction nv' aux' source[i].reduce).events⟩ := hstep
      rw [(getElem_congr_idx eidx).symm.trans hrow]
      simp only [hstep']
      obtain ⟨hrows, -, -, -⟩ := record_direct_rows (BoolGate source) hd nv' aux'
        (boolGate_of_events source (List.getElem_mem hi') hd nv' aux') hq'
      exact hrows _ (List.getElem_mem _)
    · right; right
      rw [placements_customRows_count _ _ hi] at h2
      have h1' : ((lowering source nv).placements[i]'hip).customRows.first ≤
        r - publicVars.length := h1
      have h2' : r - publicVars.length <
        ((lowering source nv).placements[i]'hip).customRows.first +
          (lowering source nv).steps[i].gateRows.length := h2
      unfold KimchiConstraint.Direct at hd
      split at hd
      · exfalso
        have hgr : (lowering source nv).steps[i].gateRows = [] := by
          rw [hstep, ‹source[i] = _›]
          rfl
        rw [hgr] at h2'
        simp at h2'
        omega
      · obtain ⟨c, hsrc⟩ : ∃ c, source[i] = KimchiConstraint.addComplete c := ⟨_, ‹source[i] = _›⟩
        have hd' : (KimchiConstraint.addComplete c).Direct := hsrc ▸ hs _ (List.getElem_mem hi')
        have hgr : (lowering source nv).steps[i].gateRows = [addRow c] := by
          rw [hstep, hsrc]
          show toKimchiRows (recordReduction nv' aux'
            (KimchiConstraint.reduce (.addComplete c))).result = _
          rw [(record_addComplete_direct nv' aux' hd').2]
          rfl
        rw [hgr, List.length_singleton] at h2'
        refine ⟨i, hi', c, hsrc, ?_, ?_⟩
        · show r = publicVars.length + ((lowering source nv).placements[i]'hip).customRows.first
          omega
        · have hrow := getElem_bodyRows_gate (lowering source nv) i hi 0 (by simp [hgr])
            (show ((lowering source nv).placements[i]'hip).customRows.first + 0 <
              (lowering source nv).bodyRows.length by omega)
          have eidx : ((lowering source nv).placements[i]'hip).customRows.first + 0 =
              r - publicVars.length := by omega
          rw [(getElem_congr_idx eidx).symm.trans hrow]
          simp only [hgr, List.getElem_cons_zero]
      · exact hd.elim
  · right; left
    cases hq : (lowering source nv).aux.queuedGenericGate with
    | none =>
      exfalso
      simp [RecordedGates.allRows, finalizeGateQueue, hq] at hk
      omega
    | some g =>
      refine ⟨g, hfold.2 g hq, ?_⟩
      have e3 : (lowering source nv).allRows = (lowering source nv).bodyRows ++ [flushRow g] := by
        simp only [RecordedGates.allRows, finalizeGateQueue, hq, Option.map_some,
          Option.toList_some]
        rfl
      simp only [e3]
      rw [List.getElem_append_right (Nat.le_of_not_lt hb)]
      simp only [e3, List.length_append, List.length_singleton] at hk
      have : r - publicVars.length - (lowering source nv).bodyRows.length = 0 := by omega
      simp only [this, List.getElem_cons_zero]

/-! ## Labels -/

/-- A label among a labelled prefix padded with absent cells is in the prefix. -/
theorem label_of_append_replicate {l : List (Option Variable)} {m j : Nat} {w : Variable}
    (hj : j < (l ++ List.replicate m none).length)
    (h : (l ++ List.replicate m none)[j] = some w) : ∃ hj' : j < l.length, l[j] = some w := by
  by_cases hl : j < l.length
  · exact ⟨hl, by rwa [List.getElem_append_left hl] at h⟩
  · rw [List.getElem_append_right (Nat.le_of_not_lt hl), List.getElem_replicate] at h
    exact absurd h (by simp)

omit [DecidableEq F] in
/-- A public row's label is in its first seven cells and is a public variable. -/
theorem label_public (l : List Variable) (i : Nat) (hi : i < l.length) (j : Nat)
    (hj : j < wCols) (w : Variable)
    (h : ((makePublicInputRows (F := F) l)[i]'(by simpa [makePublicInputRows] using hi)).vars[j] =
      some w) : j < 7 ∧ w ∈ l := by
  simp only [makePublicInputRows, List.getElem_map] at h
  have h' : ([some l[i]] ++ List.replicate 14 none)[j]'(by simpa using hj) = some w := h
  obtain ⟨hj', h''⟩ := label_of_append_replicate _ h'
  have hmem := h'' ▸ List.getElem_mem hj'
  simp only [List.length_singleton] at hj'
  simp only [List.mem_singleton, Option.some.injEq] at hmem
  exact ⟨by omega, hmem ▸ List.getElem_mem hi⟩

omit [DecidableEq F] in
private theorem label_double {source : List (KimchiConstraint F)} {q g : GenericPlonkConstraint F}
    (hq : BoolGate source q) (hg : BoolGate source g) (j : Nat) (hj : j < wCols) (w : Variable)
    (h : (emitDoubleGateRow q g).vars[j] = some w) :
    j < 7 ∧ KimchiConstraint.basic (.boolean (.var w)) ∈ source := by
  obtain ⟨a, ha, rfl⟩ := hq
  obtain ⟨b, hb, rfl⟩ := hg
  have h' : ([some b, some b, none, some a, some a, none] ++ List.replicate 9 none)[j]'(by
    simpa using hj) = some w := h
  obtain ⟨hj', h''⟩ := label_of_append_replicate _ h'
  have hmem := h'' ▸ List.getElem_mem hj'
  simp only [List.length_cons, List.length_nil] at hj'
  simp at hmem
  refine ⟨by omega, ?_⟩
  rcases hmem with rfl | rfl
  · exact hb
  · exact ha

omit [DecidableEq F] in
private theorem label_flush {source : List (KimchiConstraint F)} {g : GenericPlonkConstraint F}
    (hg : BoolGate source g) (j : Nat) (hj : j < wCols) (w : Variable)
    (h : (flushRow g).vars[j] = some w) :
    j < 7 ∧ KimchiConstraint.basic (.boolean (.var w)) ∈ source := by
  obtain ⟨a, ha, rfl⟩ := hg
  have h' : ([some a, some a, none] ++ List.replicate 12 none)[j]'(by simpa using hj) = some w :=
    h
  obtain ⟨hj', h''⟩ := label_of_append_replicate _ h'
  have hmem := h'' ▸ List.getElem_mem hj'
  simp only [List.length_cons, List.length_nil] at hj'
  simp at hmem
  exact ⟨by omega, hmem ▸ ha⟩

omit [Field F] [DecidableEq F] in
private theorem map_var?_eq (l : List (CVar F)) (hl : ∀ x ∈ l, x.var?.isSome) :
    l.map CVar.var? = (l.filterMap CVar.var?).map some := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨v, rfl⟩ := CVar.var?_isSome (hl x (List.mem_cons_self ..))
    rw [List.map_cons, List.filterMap_cons_some (l := l) (rfl : CVar.var? (CVar.var v) = some v),
      List.map_cons, ih fun y hy => hl y (List.mem_cons_of_mem _ hy)]
    rfl

omit [Field F] [DecidableEq F] in
private theorem directVars_length {c : AddComplete F}
    (hc : (KimchiConstraint.addComplete c).Direct) :
    (KimchiConstraint.addComplete c).directVars.length = 11 := by
  have := congrArg List.length (map_var?_eq c.operands.toList hc)
  simp only [List.length_map, Vector.length_toList] at this
  exact this.symm

omit [Field F] [DecidableEq F] in
private theorem label_add {c : AddComplete F} (hc : (KimchiConstraint.addComplete c).Direct)
    (j : Nat) (hj : j < wCols) (w : Variable) (h : (addRow c).vars[j] = some w) :
    ∃ hj' : j < 11,
      (KimchiConstraint.addComplete c).directVars[j]'(by rw [directVars_length hc]; exact hj') = w
    := by
  have h' : (((KimchiConstraint.addComplete c).directVars.map some) ++ List.replicate 4 none)[j]'(by
    simp only [List.length_append, List.length_map, List.length_replicate, directVars_length hc]
    omega) = some w := by
    have h0 : (c.operands.toList.map CVar.var? ++ List.replicate 4 none)[j]'(by simpa using hj) =
      some w := h
    simpa only [map_var?_eq c.operands.toList hc] using h0
  obtain ⟨hj', h''⟩ := label_of_append_replicate _ h'
  simp only [List.length_map, directVars_length hc] at hj'
  refine ⟨hj', ?_⟩
  rw [List.getElem_map, Option.some.injEq] at h''
  exact h''

omit [Field F] [DecidableEq F] in
private theorem filterMap_eq_of_map (l : List (CVar F)) (vs : List Variable)
    (h : l.map CVar.var? = vs.map some) : l.filterMap CVar.var? = vs := by
  induction l generalizing vs with
  | nil =>
    cases vs with
    | nil => rfl
    | cons => simp at h
  | cons x l ih =>
    cases vs with
    | nil => simp at h
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [List.filterMap_cons, h.1, ih vs h.2]

omit [Field F] [DecidableEq F] in
private theorem unwiredVars_of_label {c : AddComplete F}
    (hc : (KimchiConstraint.addComplete c).Direct) {j : Nat} (hj : j < 11) (h7 : 7 ≤ j)
    {v : Variable}
    (hv : (KimchiConstraint.addComplete c).directVars[j]'(by rw [directVars_length hc]; exact hj)
      = v) : v ∈ (KimchiConstraint.addComplete c).unwiredVars := by
  have hdrop : (c.operands.toList.drop 7).filterMap CVar.var? =
      (KimchiConstraint.addComplete c).directVars.drop 7 := by
    have hm : (c.operands.toList.drop 7).map CVar.var? =
        ((KimchiConstraint.addComplete c).directVars.drop 7).map some := by
      rw [List.map_drop, List.map_drop]
      exact congrArg (List.drop 7) (map_var?_eq c.operands.toList hc)
    exact filterMap_eq_of_map _ _ hm
  rw [addComplete_unwiredVars]
  show v ∈ (c.operands.toList.drop 7).filterMap CVar.var?
  rw [hdrop]
  have hl := directVars_length hc
  have hidx : ((KimchiConstraint.addComplete c).directVars.drop 7).length = 4 := by
    rw [List.length_drop, hl]
  have hget : ((KimchiConstraint.addComplete c).directVars.drop 7)[j - 7]'(by rw [hidx]; omega) =
      (KimchiConstraint.addComplete c).directVars[7 + (j - 7)]'(by rw [hl]; omega) :=
    List.getElem_drop
  simp only [show 7 + (j - 7) = j by omega] at hget
  exact (hget.trans hv) ▸ List.getElem_mem _

/-! ## Counting occurrences -/

omit [Field F] [DecidableEq F] in
private theorem two_le_count_of_ne {l : List Variable} {v : Variable} {j j' : Nat}
    (hj : j < l.length) (hj' : j' < l.length) (hne : j ≠ j') (h1 : l[j] = v) (h2 : l[j'] = v) :
    2 ≤ l.count v := by
  induction l generalizing j j' with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons x rest ih =>
    rw [List.count_cons]
    cases j with
    | zero =>
      cases j' with
      | zero => exact absurd rfl hne
      | succ j' =>
        simp only [List.getElem_cons_zero] at h1
        simp only [List.getElem_cons_succ] at h2
        subst h1
        have : 1 ≤ rest.count x :=
          List.one_le_count_iff.mpr (h2 ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj'))
        simp only [beq_self_eq_true, ite_true]
        omega
    | succ j =>
      cases j' with
      | zero =>
        simp only [List.getElem_cons_zero] at h2
        simp only [List.getElem_cons_succ] at h1
        subst h2
        have : 1 ≤ rest.count x :=
          List.one_le_count_iff.mpr (h1 ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj))
        simp only [beq_self_eq_true, ite_true]
        omega
      | succ j' =>
        simp only [List.getElem_cons_succ] at h1 h2
        have := ih (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hj')
          (fun h => hne (h ▸ rfl)) h1 h2
        omega

omit [Field F] [DecidableEq F] in
theorem two_le_count_flatMap {α : Type} (f : α → List Variable) {v : Variable}
    {source : List α} {p p' : Nat} (hp : p < source.length)
    (hp' : p' < source.length) (hne : p ≠ p') (h1 : v ∈ f source[p]) (h2 : v ∈ f source[p']) :
    2 ≤ (source.flatMap f).count v := by
  induction source generalizing p p' with
  | nil => exact absurd hp (Nat.not_lt_zero _)
  | cons c rest ih =>
    rw [List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases p' with
      | zero => exact absurd rfl hne
      | succ p' =>
        simp only [List.getElem_cons_zero] at h1
        simp only [List.getElem_cons_succ] at h2
        have ha : 1 ≤ (f c).count v := List.one_le_count_iff.mpr h1
        have hb : 1 ≤ (rest.flatMap f).count v :=
          List.one_le_count_iff.mpr (List.mem_flatMap.mpr ⟨_, List.getElem_mem _, h2⟩)
        omega
    | succ p =>
      cases p' with
      | zero =>
        simp only [List.getElem_cons_zero] at h2
        simp only [List.getElem_cons_succ] at h1
        have ha : 1 ≤ (f c).count v := List.one_le_count_iff.mpr h2
        have hb : 1 ≤ (rest.flatMap f).count v :=
          List.one_le_count_iff.mpr (List.mem_flatMap.mpr ⟨_, List.getElem_mem _, h1⟩)
        omega
      | succ p' =>
        simp only [List.getElem_cons_succ] at h1 h2
        have := ih (Nat.lt_of_succ_lt_succ hp) (Nat.lt_of_succ_lt_succ hp')
          (fun h => hne (h ▸ rfl)) h1 h2
        omega

omit [Field F] [DecidableEq F] in
theorem two_le_count_flatMap_same {α : Type} (f : α → List Variable) {v : Variable}
    {source : List α} {p : Nat} (hp : p < source.length)
    (h : 2 ≤ (f source[p]).count v) : 2 ≤ (source.flatMap f).count v := by
  induction source generalizing p with
  | nil => exact absurd hp (Nat.not_lt_zero _)
  | cons c rest ih =>
    rw [List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      simp only [List.getElem_cons_zero] at h
      omega
    | succ p =>
      simp only [List.getElem_cons_succ] at h
      have := ih (Nat.lt_of_succ_lt_succ hp) h
      omega

/-- A label in an unwired column names a cell no other cell carries. -/
private theorem unwired_unique {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} (hscope : KimchiConstraint.Direct.Scoped source publicVars)
    (r j r' j' : Nat) (hr : r < (directRows source publicVars nv).length) (hj : j < wCols)
    (hr' : r' < (directRows source publicVars nv).length) (hj' : j' < wCols) (v : Variable)
    (h7 : 7 ≤ j) (hv : (directRows source publicVars nv)[r].vars[j] = some v)
    (hv' : (directRows source publicVars nv)[r'].vars[j'] = some v) : r' = r ∧ j' = j := by
  have hs := hscope.direct
  rcases directRows_cases hs r hr with ⟨hp, e⟩ | ⟨q, g, hq, hg, e⟩ | ⟨g, hg, e⟩ |
    ⟨p, hp, c, hsrc, hgr, e⟩
  · rw [e] at hv
    have := (label_public publicVars r hp j hj v hv).1
    omega
  · rw [e] at hv
    have := (label_double hq hg j hj v hv).1
    omega
  · rw [e] at hv
    have := (label_flush hg j hj v hv).1
    omega
  rw [e] at hv
  have hd : (KimchiConstraint.addComplete c).Direct := hsrc ▸ hs _ (List.getElem_mem hp)
  obtain ⟨hj11, hvj⟩ := label_add hd j hj v hv
  have hunw := unwiredVars_of_label hd hj11 h7 hvj
  have hcount := hscope.unwiredOnce _ (hsrc ▸ List.getElem_mem hp) v hunw
  simp only [directOccurrences, List.count_append] at hcount
  have hmem : v ∈ source[p].directVars := by
    rw [hsrc]
    exact hvj ▸ List.getElem_mem _
  have hflat : 1 ≤ (source.flatMap KimchiConstraint.directVars).count v :=
    List.one_le_count_iff.mpr (List.mem_flatMap.mpr ⟨_, List.getElem_mem hp, hmem⟩)
  rcases directRows_cases hs r' hr' with ⟨hp', e'⟩ | ⟨q', g', hq', hg', e'⟩ | ⟨g', hg', e'⟩ |
    ⟨p', hp', c', hsrc', hgr', e'⟩
  · exfalso
    rw [e'] at hv'
    have hpubv := (label_public publicVars r' hp' j' hj' v hv').2
    have := List.one_le_count_iff.mpr hpubv
    omega
  · exfalso
    rw [e'] at hv'
    obtain ⟨p', hp', hsrc'⟩ := List.mem_iff_getElem.mp (label_double hq' hg' j' hj' v hv').2
    have hne : p ≠ p' := fun h => by
      subst h
      rw [hsrc] at hsrc'
      cases hsrc'
    have := two_le_count_flatMap KimchiConstraint.directVars hp hp' hne hmem
      (by rw [hsrc']; exact List.mem_singleton_self _)
    omega
  · exfalso
    rw [e'] at hv'
    obtain ⟨p', hp', hsrc'⟩ := List.mem_iff_getElem.mp (label_flush hg' j' hj' v hv').2
    have hne : p ≠ p' := fun h => by
      subst h
      rw [hsrc] at hsrc'
      cases hsrc'
    have := two_le_count_flatMap KimchiConstraint.directVars hp hp' hne hmem
      (by rw [hsrc']; exact List.mem_singleton_self _)
    omega
  · rw [e'] at hv'
    have hd' : (KimchiConstraint.addComplete c').Direct := hsrc' ▸ hs _ (List.getElem_mem hp')
    obtain ⟨hj11', hvj'⟩ := label_add hd' j' hj' v hv'
    by_cases hpp : p = p'
    · subst hpp
      have hcc : c = c' := by
        rw [hsrc] at hsrc'
        exact KimchiConstraint.addComplete.inj hsrc'
      subst hcc
      refine ⟨by rw [hgr, hgr'], ?_⟩
      by_contra hne
      have h2 := two_le_count_of_ne (by rw [directVars_length hd]; exact hj11')
        (by rw [directVars_length hd]; exact hj11) hne hvj' hvj
      have := two_le_count_flatMap_same KimchiConstraint.directVars hp (by rw [hsrc]; exact h2)
      omega
    · exfalso
      have hmem' : v ∈ source[p'].directVars := by
        rw [hsrc']
        exact hvj' ▸ List.getElem_mem _
      have := two_le_count_flatMap KimchiConstraint.directVars hp hp' hpp hmem hmem'
      omega

/-! ## The valuation -/

/-- The value at a cell labelled by the variable, zero when none is. -/
private noncomputable def recover (rows : List (KimchiRow F)) (val : Nat × Nat → F)
    (v : Variable) : F :=
  if h : ∃ c : Fin rows.length × Fin wCols, rows[c.1].vars[c.2] = some v then
    val ((Classical.choose h).1, (Classical.choose h).2)
  else 0

omit [DecidableEq F] in
/-- Every labelled cell reads its variable's recovered value, when wired cells labelled alike
agree and an unwired label is unique. -/
private theorem recover_spec (rows : List (KimchiRow F)) (val : Nat × Nat → F)
    (hwired : ∀ (r j r' j' : Nat) (hr : r < rows.length) (hj : j < 7) (hr' : r' < rows.length)
      (hj' : j' < 7) (v : Variable), rows[r].vars[j]'(by omega) = some v →
      rows[r'].vars[j']'(by omega) = some v → val (r, j) = val (r', j'))
    (huniq : ∀ (r j r' j' : Nat) (hr : r < rows.length) (hj : j < wCols) (hr' : r' < rows.length)
      (hj' : j' < wCols) (v : Variable), 7 ≤ j → rows[r].vars[j] = some v →
      rows[r'].vars[j'] = some v → r' = r ∧ j' = j)
    (r j : Nat) (hr : r < rows.length) (hj : j < wCols) (v : Variable)
    (hv : rows[r].vars[j] = some v) : val (r, j) = recover rows val v := by
  have hex : ∃ c : Fin rows.length × Fin wCols, rows[c.1].vars[c.2] = some v :=
    ⟨(⟨r, hr⟩, ⟨j, hj⟩), hv⟩
  simp only [recover, dif_pos hex]
  have hc := Classical.choose_spec hex
  generalize Classical.choose hex = c at hc ⊢
  by_cases h7 : j < 7
  · by_cases h7' : c.2.val < 7
    · exact hwired r j c.1 c.2 hr h7 c.1.isLt h7' v hv hc
    · obtain ⟨h1, h2⟩ := huniq c.1 c.2 r j c.1.isLt c.2.isLt hr hj v (Nat.le_of_not_lt h7') hc hv
      subst h1 h2
      rfl
  · obtain ⟨h1, h2⟩ := huniq r j c.1 c.2 hr hj c.1.isLt c.2.isLt v (Nat.le_of_not_lt h7) hv hc
    have : c = (⟨r, hr⟩, ⟨j, hj⟩) := Prod.ext (Fin.ext h1) (Fin.ext h2)
    subst this
    rfl

omit [DecidableEq F] in
/-- Folding a zero public input into a generic gate changes nothing. -/
theorem withPublic_zero (g : Kimchi.Gate.Generic F) : g.withPublic 0 = g := by
  simp [Kimchi.Gate.Generic.withPublic]

/-- **The direct fragment's closed theorem.** Any table satisfying an index of the fragment's
lowering, at a public input, yields a valuation satisfying every source constraint and
reading each public variable as its public input. -/
theorem KimchiConstraint.Direct.holds_of_satisfies {n : ℕ} [NeZero n]
    {source : List (KimchiConstraint F)} {publicVars : List Variable} {nv : Variable}
    {idx : Index F n} (hscope : KimchiConstraint.Direct.Scoped source publicVars)
    (hindex : IndexOf source publicVars nv idx) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (hsat : idx.Satisfies pub wTab) :
    ∃ V : Valuation F, (∀ c ∈ source, KimchiConstraint.Holds V c) ∧
      ∀ i : Fin publicVars.length, V publicVars[i] = pub (hindex.publicIndex i) := by
  have hs := hscope.direct
  have hrows_le := hindex.rows_le
  have hlenPub : (makePublicInputRows (F := F) publicVars).length = publicVars.length := by
    simp [makePublicInputRows]
  have hpub_le : publicVars.length ≤ (directRows source publicVars nv).length := by
    simp [directRows, hlenPub]
  have htyp := hindex.typ_eq
  have hcoeff := hindex.coeffs_eq
  have hcopy := hindex.classCells_eq pub wTab hsat
  -- the valuation
  let V : Valuation F := recover (directRows source publicVars nv) (cellVal wTab)
  have hreal : ∀ (r j : Nat) (hr : r < (directRows source publicVars nv).length) (hj : j < wCols)
      (v : Variable), (directRows source publicVars nv)[r].vars[j] = some v →
      cellVal wTab (r, j) = V v := by
    intro r j hr hj v hv
    refine recover_spec _ _ ?_ ?_ r j hr hj v hv
    · intro r j r' j' hr hj hr' hj' v hv hv'
      exact hcopy _ (mem_classCells_of_label hr hj hv) (mem_classCells_of_label hr' hj' hv')
    · intro r j r' j' hr hj hr' hj' v h7 hv hv'
      exact unwired_unique hscope r j r' j' hr hj hr' hj' v h7 hv hv'
  have hval : ∀ (r j : Nat) (hr : r < (directRows source publicVars nv).length) (hj : j < wCols)
      (v : Variable), (directRows source publicVars nv)[r].vars[j] = some v →
      wTab ⟨r, by omega⟩ ⟨j, hj⟩ = V v := by
    intro r j hr hj v hv
    rw [← hreal r j hr hj v hv]
    simp only [cellVal, dif_pos (And.intro (lt_of_lt_of_le hr hrows_le) hj)]
  refine ⟨V, ?_, ?_⟩
  · intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hc
    have hfold := recordGates_direct (BoolGate source) source hs
      (fun c hc => boolGate_of_events source hc (hs c hc)) nv initialAuxState
      (fun _ h => by simp [initialAuxState] at h)
    have hi : p < (lowering source nv).steps.length :=
      (length_steps source nv initialAuxState).symm ▸ hp
    obtain ⟨nv', aux', hq', hstep⟩ := hfold.1 p hp
    have hstep' : (lowering source nv).steps[p] =
        ⟨(recordReduction nv' aux' source[p].reduce).rows,
          (recordReduction nv' aux' source[p].reduce).result,
          (recordReduction nv' aux' source[p].reduce).events⟩ := hstep
    have hd := hs _ (List.getElem_mem hp)
    unfold KimchiConstraint.Direct at hd
    split at hd
    · -- a Boolean on a bare variable
      obtain ⟨v, hsrc⟩ : ∃ v, source[p] = KimchiConstraint.basic (.boolean (.var v)) :=
        ⟨_, ‹source[p] = _›⟩
      have hq0 : (initialAuxState : AuxState F).queuedGenericGate = none := rfl
      have hev : ReductionEvent.generic (booleanGate v) ∈ (lowering source nv).steps[p].events := by
        rw [hstep', hsrc]
        show ReductionEvent.generic (booleanGate v) ∈ (recordReduction nv' aux'
          (KimchiConstraint.reduce (F := F) (.basic (.boolean (.var v))))).events
        rw [record_boolean_var]
        exact List.mem_singleton_self _
      obtain ⟨rc, hrc, hrcg⟩ := receipts_complete source nv initialAuxState hq0 _
        (List.getElem_mem hi) _ ⟨_, hev, rfl⟩
      have hloc := receipts_located source nv initialAuxState hq0 rc hrc
      obtain ⟨row, hrow, hkind, -, -⟩ := id hloc
      obtain ⟨hrowlt, hrow'⟩ := List.getElem?_eq_some_iff.mp hrow
      have hrowlt' : rc.row < (lowering source nv).allRows.length := hrowlt
      have hi' : publicVars.length + rc.row < (directRows source publicVars nv).length := by
        simp only [directRows, List.length_append, hlenPub]
        omega
      have hrowi : (directRows source publicVars nv)[publicVars.length + rc.row] = row := by
        simp only [directRows]
        rw [List.getElem_append_right (by omega)]
        simp only [hlenPub, Nat.add_sub_cancel_left]
        exact hrow'
      have hgen := hsat.1 ⟨publicVars.length + rc.row, by omega⟩
      have htyp' : (idx.gates ⟨publicVars.length + rc.row, by omega⟩).typ = .generic := by
        rw [htyp _ hi', hrowi, hkind]
      unfold Index.rowSatisfies at hgen
      rw [htyp'] at hgen
      simp only at hgen
      have hpub0 : Index.pubAt idx pub ⟨publicVars.length + rc.row, by omega⟩ = 0 := by
        unfold Index.pubAt
        rw [dif_neg (by
          rw [hindex.publicCount]
          show ¬ publicVars.length + rc.row < publicVars.length
          omega)]
      rw [hpub0, withPublic_zero] at hgen
      have hq : (⟨idx.coeffTable ⟨publicVars.length + rc.row, by omega⟩,
          wTab ⟨publicVars.length + rc.row, by omega⟩⟩ : Kimchi.Gate.Generic F) =
          genericAt row (wTab ⟨publicVars.length + rc.row, by omega⟩) := by
        simp only [genericAt]
        congr 1
        funext k
        rw [Index.coeffTable, hcoeff _ hi' k, hrowi]
      rw [hq] at hgen
      have hw : ∀ (k : Fin wCols) (w : Variable), row.vars[k] = some w →
          wTab ⟨publicVars.length + rc.row, by omega⟩ k = V w := by
        intro k w hk
        have := hval _ k.val hi' k.isLt w (by rw [hrowi]; exact hk)
        simpa using this
      have hz := genericValue_of_located hloc hrow _ V hw (by simp [hrcg, booleanGate,
        GenericPlonkConstraint.AbsentZero]) hgen
      rw [hrcg] at hz
      have hfacts : ReductionFacts V (recordReduction nv' aux'
          (Snarky.Kimchi.reduce (F := F) (Basic.boolean (.var v)))).events := by
        have e : (recordReduction nv' aux'
            (Snarky.Kimchi.reduce (F := F) (Basic.boolean (.var v)))).events =
            (recordReduction nv' aux' (KimchiConstraint.reduce (F := F)
              (.basic (.boolean (.var v))))).events := rfl
        rw [e, record_boolean_var]
        intro e he
        rw [List.mem_singleton] at he
        subst he
        exact hz
      rw [hsrc]
      exact boolean_of_reductionFacts nv' aux' (.var v) V hfacts
    · -- a direct complete addition
      obtain ⟨c, hsrc⟩ : ∃ c, source[p] = KimchiConstraint.addComplete c := ⟨_, ‹source[p] = _›⟩
      have hd' : (KimchiConstraint.addComplete c).Direct := hsrc ▸ hs _ (List.getElem_mem hp)
      have hgr : (lowering source nv).steps[p].gateRows = [addRow c] := by
        rw [hstep', hsrc]
        show toKimchiRows (recordReduction nv' aux'
          (KimchiConstraint.reduce (.addComplete c))).result = _
        rw [(record_addComplete_direct nv' aux' hd').2]
        rfl
      have hip : p < (lowering source nv).placements.length := by
        rw [RecordedGates.length_placements]
        exact hi
      have hle := placements_customRows_le (lowering source nv) p hi
      rw [placements_customRows_count _ _ hi, hgr, List.length_singleton] at hle
      have hle' : ((lowering source nv).placements[p]'hip).customRows.first + 1 ≤
        (lowering source nv).bodyRows.length := hle
      have hi' : publicVars.length + ((lowering source nv).placements[p]'hip).customRows.first <
          (directRows source publicVars nv).length := by
        simp only [directRows, List.length_append, hlenPub, RecordedGates.allRows]
        omega
      have hrow := getElem_bodyRows_gate (lowering source nv) p hi 0 (by simp [hgr])
        (show ((lowering source nv).placements[p]'hip).customRows.first + 0 <
          (lowering source nv).bodyRows.length by omega)
      have hrowi : (directRows source publicVars nv)[publicVars.length +
          ((lowering source nv).placements[p]'hip).customRows.first] = addRow c := by
        simp only [directRows]
        rw [List.getElem_append_right (by omega)]
        simp only [hlenPub, Nat.add_sub_cancel_left, RecordedGates.allRows]
        rw [List.getElem_append_left (by omega)]
        refine ((getElem_congr_idx (Nat.add_zero _)).symm.trans hrow).trans ?_
        simp only [hgr, List.getElem_cons_zero]
      have hadd := hsat.1 ⟨publicVars.length +
        ((lowering source nv).placements[p]'hip).customRows.first, by omega⟩
      have htyp' : (idx.gates ⟨publicVars.length +
          ((lowering source nv).placements[p]'hip).customRows.first, by omega⟩).typ =
          .completeAdd := by
        rw [htyp _ hi', hrowi]
        rfl
      unfold Index.rowSatisfies at hadd
      rw [htyp'] at hadd
      simp only at hadd
      have hcells : ∀ k : Fin wCols, k.val < 11 → wTab ⟨publicVars.length +
          ((lowering source nv).placements[p]'hip).customRows.first, by omega⟩ k =
          rowValues V (addRow c) k := by
        intro k hk
        have hlab : (addRow c).vars[k] = some
            ((KimchiConstraint.addComplete c).directVars[k.val]'(by
              rw [directVars_length hd']; exact hk)) := by
          have e : (addRow c).vars[k] = ((KimchiConstraint.addComplete c).directVars.map some ++
              List.replicate 4 none)[k.val]'(by
                simp only [List.length_append, List.length_map, List.length_replicate,
                  directVars_length hd']
                omega) := by
            show (c.operands.toList.map CVar.var? ++ List.replicate 4 none)[k.val]'(by simp) = _
            simp only [map_var?_eq c.operands.toList hd']
            rfl
          rw [e, List.getElem_append_left (by
            simp only [List.length_map, directVars_length hd']; exact hk), List.getElem_map]
        rw [hval _ k.val hi' k.isLt _ (by rw [hrowi]; exact hlab)]
        simp only [rowValues, hlab, Option.map_some, Option.getD_some]
      have hmap : Lift.Gate.AddComplete.cellMap (wTab ⟨publicVars.length +
          ((lowering source nv).placements[p]'hip).customRows.first, by omega⟩) =
          Lift.Gate.AddComplete.cellMap (rowValues V (addRow c)) := by
        simp only [Lift.Gate.AddComplete.cellMap]
        congr 1 <;> exact hcells _ (by decide)
      have hres : (recordReduction nv' aux' c.reduce).result.row = addRow c := by
        have e : (recordReduction nv' aux' (KimchiConstraint.reduce (.addComplete c))).result =
            KimchiGate.addComplete (recordReduction nv' aux' c.reduce).result := rfl
        rw [(record_addComplete_direct nv' aux' hd').2] at e
        exact congrArg Rows.row (KimchiGate.addComplete.inj e).symm
      have hfacts : ReductionFacts V (recordReduction nv' aux' c.reduce).events := by
        have e : (recordReduction nv' aux' c.reduce).events =
            (recordReduction nv' aux' (KimchiConstraint.reduce (.addComplete c))).events := rfl
        rw [e, (record_addComplete_direct nv' aux' hd').1]
        intro e he
        exact (List.not_mem_nil he).elim
      rw [hsrc]
      refine addComplete_holds_of_reductionFacts nv' aux' c V hfacts ?_
      rw [hres, ← hmap]
      exact hadd
    · exact hd.elim
  · intro i
    have hi : i.val < (directRows source publicVars nv).length := by
      have := i.isLt
      omega
    have hrowi : (directRows source publicVars nv)[i.val] =
        (makePublicInputRows publicVars)[i.val]'(by simp [hlenPub]) :=
      List.getElem_append_left (by simp [hlenPub])
    have hlab : (directRows source publicVars nv)[i.val].vars[0] = some publicVars[i] := by
      rw [hrowi]
      simp only [makePublicInputRows, List.getElem_map]
      rfl
    have h1 := hval i.val 0 hi (by decide) _ hlab
    have h2 := hsat.2.2 (hindex.publicIndex i)
    rw [← h1]
    exact h2.symm ▸ rfl

end Kimchi

end Snarky
