import Snarky.Kimchi.Backend.Compile
import Snarky.Kimchi.Backend.Receipts
import Kimchi.Index.Basic
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
  variables: every variable below the initial counter, and every operand of an unwired
  column occurring once.
- `IndexOf`: an index whose gate table is the fragment's actual lowering and assembly.

## Main results

- `record_boolean_var`, `record_addComplete_direct`: the recorded reduction of each fragment
  constraint in closed form: a Boolean's one generic event, a complete addition's empty log
  and its row over the operands.
- `KimchiConstraint.Direct.events_generic`, `steps_generic_of_direct`,
  `receipts_isSome_of_direct`: a direct constraint's events are generic with no coefficient
  on an absent cell, so the fragment's recorded lowering has receipts.

## Implementation notes

`Scoped` restricts the fragment enough to recover a valuation from any table satisfying the
index: an operand in a wired column is forced equal across its occurrences by the copy
constraints, and an operand in an unwired column occurs once, so its one cell names its
value. It is a sufficient restriction for this fragment, not a condition the production
circuits meet.
-/

open Kimchi

namespace Snarky

variable {F : Type}

/-- The variable a bare-variable operand names; `none` for any other form. -/
def CVar.var? : CVar F → Option Variable
  | .var v => some v
  | _ => none

private theorem CVar.var?_isSome {x : CVar F} (h : x.var?.isSome) : ∃ v, x = .var v := by
  cases x with
  | var v => exact ⟨v, rfl⟩
  | _ => exact absurd h (by simp [CVar.var?])

namespace Kimchi

/-- The payload's eleven operands in gate-column order. -/
def AddComplete.operands (c : AddComplete F) : Vector (FVar F) 11 :=
  #v[c.p1.x, c.p1.y, c.p2.x, c.p2.y, c.p3.x, c.p3.y, c.inf, c.sameX, c.s, c.infZ, c.x21Inv]

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

/-- The operands of a direct complete addition in the unwired columns `7` to `10`: `sameX`,
`s`, `infZ`, `x21Inv`. Empty for any other constraint. -/
private def KimchiConstraint.unwiredVars : KimchiConstraint F → List Variable
  | .addComplete c => (c.operands.toList.drop permCols).filterMap CVar.var?
  | _ => []

/-- Every variable the source and the public variables name, with repetition. -/
private def occurrences (source : List (KimchiConstraint F)) (publicVars : List Variable) :
    List Variable :=
  source.flatMap KimchiConstraint.directVars ++ publicVars

/-- The scoping condition under which any table satisfying the fragment's index determines
a valuation: every constraint is direct, every operand and public variable lies below the
initial counter `nv`, and every operand of an unwired column occurs exactly once among the
operand occurrences and the public variables. -/
structure KimchiConstraint.Direct.Scoped (nv : Variable) (source : List (KimchiConstraint F))
    (publicVars : List Variable) : Prop where
  /-- Every constraint is in the fragment. -/
  direct : ∀ c ∈ source, c.Direct
  /-- Every operand and public variable lies below the initial counter. -/
  below : ∀ v ∈ occurrences source publicVars, v < nv
  /-- Every operand of an unwired column occurs exactly once among the operand occurrences
  and the public variables. -/
  unwiredOnce : ∀ c ∈ source, ∀ v ∈ c.unwiredVars, (occurrences source publicVars).count v = 1

instance (nv : Variable) (source : List (KimchiConstraint F)) (publicVars : List Variable) :
    Decidable (KimchiConstraint.Direct.Scoped nv source publicVars) :=
  decidable_of_iff
    ((∀ c ∈ source, c.Direct) ∧ (∀ v ∈ occurrences source publicVars, v < nv) ∧
      ∀ c ∈ source, ∀ v ∈ c.unwiredVars, (occurrences source publicVars).count v = 1)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

variable [Field F] [DecidableEq F]

/-- The fragment's lowering: the builder's reduction folded over `source` from the counter
`nv`, the queue flushed. -/
private def directBuilt (source : List (KimchiConstraint F)) (nv : Variable) : KimchiBuilt F Unit :=
  reduceBuilt ⟨(), nv, source⟩

/-- The assembled gate table of the fragment's lowering at the given public variables: the
public rows, then the body rows, wired through the reduction's union-find. -/
def directGates (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) : List (AssembledGate F) :=
  (gateDataOf (directBuilt source nv) publicVars).2.1

/-- An index whose gate table is the fragment's lowering and assembly: the public count is
the public variables', the assembled rows fit before the masked rows, and at each assembled
row the gate type, the zero-extended coefficients and the seven wire targets are the
assembly's. The remaining rows are left to the index's own laws. -/
structure IndexOf {n : ℕ} (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) (idx : Index F n) : Prop where
  /-- The public rows are the public variables'. -/
  publicCount : idx.publicCount = publicVars.length
  /-- The assembled rows fit before the masked rows. -/
  fits : (directGates source publicVars nv).length ≤ n - idx.zkRows
  /-- Each assembled row's gate type. -/
  typ : ∀ (i : Fin n) (hi : i.val < (directGates source publicVars nv).length),
    (idx.gates i).typ = (directGates source publicVars nv)[i.val].kind
  /-- Each assembled row's coefficients, zero beyond the emitted list. -/
  coeffs : ∀ (i : Fin n) (hi : i.val < (directGates source publicVars nv).length)
    (c : Fin coeffCols),
    (idx.gates i).coeffs c = (directGates source publicVars nv)[i.val].coeffs.getD c.val 0
  /-- Each assembled row's wire targets, column then row. -/
  wires : ∀ (i : Fin n) (hi : i.val < (directGates source publicVars nv).length)
    (c : Fin permCols),
    (((idx.gates i).wires c).1 : ℕ) = ((directGates source publicVars nv)[i.val].wires[c]).col ∧
    (((idx.gates i).wires c).2 : ℕ) = ((directGates source publicVars nv)[i.val].wires[c]).row

/-- A public variable's position as a public row of the index. -/
def IndexOf.publicIndex {n : ℕ} {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} {idx : Index F n} (h : IndexOf source publicVars nv idx)
    (i : Fin publicVars.length) : Fin idx.publicCount :=
  ⟨i, by have := h.publicCount; omega⟩

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

/-- A direct list's recorded lowering has receipts. -/
theorem receipts_isSome_of_direct {source : List (KimchiConstraint F)}
    (hs : ∀ c ∈ source, c.Direct) (nv : Variable) (aux : AuxState F) :
    (receipts (recordGates source nv aux)).isSome :=
  receipts_isSome _ fun s hs' e he =>
    let ⟨g, hg, _⟩ := steps_generic_of_direct hs nv aux s hs' e he
    ⟨g, hg⟩

end Kimchi

end Snarky
