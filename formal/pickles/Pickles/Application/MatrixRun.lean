import Pickles.Application.CheckedCompile
import Pickles.Application.Run

/-!
# Satisfying tables give typed application executions

A `StepTable` is a witness table accepted by a branch's index at a typed step statement, the
statement's encoding its public input; a `WrapTable` the same for the wrap circuit. Neither
carries a valuation or source satisfaction. For a checked application, every such table has
an execution of the circuit reading its statement (`CheckedApplication.lift_step`,
`CheckedApplication.lift_wrap`): the backend lifts the table to a valuation satisfying the
canonical compilation at the public input, the compiled layout reads that input as the typed
statement, and the execution is that valuation at inert advice, every execution compiling to
the canonical compilation. The execution's retained cells are the canonical compilation's
(`StepRun.cells_eq`, `WrapRun.cells_eq`), the body's statement among them.

The valuation is existential: nothing here recovers it, and nothing identifies it with any
prover's. A table relates to its execution only through the public statement.

## Main definitions

- `StepTable`, `WrapTable`: tables accepted at typed statements.

## Main results

- `CheckedApplication.lift_step`, `CheckedApplication.lift_wrap`: every accepted table has an
  execution at its statement.
- `StepRun.cells_eq`, `WrapRun.cells_eq`: every execution's retained cells are the canonical
  compilation's.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta
open scoped Kimchi

variable {D : Shape} {L : Layout D}

/-- A table accepted at a typed step statement: the branch's index is satisfied at the
statement's encoding, the index's public rows cast to the encoding's fields. -/
structure StepTable (I : ApplicationIndices D) (b : D.Branch) where
  /-- The statement. -/
  statement : StepPublic D
  /-- The witness table, on the branch's domain. -/
  table : Fin (I.stepSize b) → Fin wCols → Fp
  /-- The index accepts the table at the statement. -/
  holds : (I.step b).SatisfiesVec (CircuitType.valueToFields statement) (I.stepPublicCount b)
    table

/-- A table accepted at a typed wrap statement. -/
structure WrapTable (I : ApplicationIndices D) where
  /-- The statement. -/
  statement : WrapPublic
  /-- The witness table, on the wrap domain. -/
  table : Fin I.wrapSize → Fin wCols → Fq
  /-- The index accepts the table at the statement. -/
  holds : I.wrap.SatisfiesVec (CircuitType.valueToFields statement) I.wrapPublicCount table

/-! ## Executions and the canonical compilation -/

/-- Every step execution's retained cells are the canonical compilation's. -/
theorem StepRun.cells_eq {C : Circuits D L} {b : D.Branch} (r : StepRun C b) :
    r.cells = (stepCompilation C b).result.1.2 :=
  congrArg (fun x => x.result.1.2) (C.stepBuilt_eq r.V b r.advice)

/-- Every wrap execution's retained cells are the canonical compilation's. -/
theorem WrapRun.cells_eq {C : Circuits D L} (r : WrapRun C) :
    r.cells = (wrapCompilation C).result.1.2 :=
  congrArg (fun x => x.result.1.2) (C.wrapBuilt_eq r.V r.advice)

/-- The step circuit's body returns its statement beside the cells that retain it. -/
private theorem stepCompilation_out (C : Circuits D L) (b : D.Branch) :
    (stepCompilation C b).result.1.1 = (stepCompilation C b).result.1.2.out := by
  rw [stepCompilation, Circuits.stepBuilt, compileWith_result]
  unfold Circuits.stepCircuit stepMainCircuit
  simp only [map_eq_pure_bind]
  erw [build_bind]
  rfl

/-- A public input the backend lifts to, pointwise at the public variables, as the compiled
layout's list equation. -/
private theorem map_eq_of_pointwise {F : Type} [Field F] [DecidableEq F]
    {source : List (KimchiConstraint F)} {pubVars : List Variable} {nv n : ℕ}
    (c : CheckedIndex source pubVars nv n) {m : ℕ} (v : Vector F m)
    (h : c.index.publicCount = m) (V : Valuation F)
    (hpub : ∀ i : Fin pubVars.length, V pubVars[i] = v[Fin.cast h (c.publicIndex i)]) :
    pubVars.map V = v.toList := by
  have hlen : pubVars.length = m := c.publicCount_eq.symm.trans h
  refine List.ext_getElem (by simp [hlen]) fun i hi _ => ?_
  have h1 := hpub ⟨i, by simpa using hi⟩
  simp only [Fin.getElem_fin, Fin.val_cast, CheckedIndex.publicIndex_val] at h1
  simp only [List.getElem_map, Vector.getElem_toList]
  exact h1

/-! ## Lifting -/

/-- **An accepted step table has a step execution at its statement.** -/
theorem CheckedApplication.lift_step {C : Circuits D L} (checked : CheckedApplication C)
    (b : D.Branch) (t : StepTable checked.indices b) :
    ∃ r : StepRun C b, CircuitType.Reads r.V r.cells.out t.statement := by
  haveI : NeZero (stepIndexData C b).n :=
    ⟨by have := (checked.step b).index.zk_three; have := (checked.step b).index.zk_le; omega⟩
  obtain ⟨V, hV, hpub⟩ := (checked.step b).lift _ t.table t.holds
  have hlist : (stepPublicVars C b).map V =
      (#v[] : Vector Fp 0).toList ++ (CircuitType.valueToFields (F := Fp) t.statement).toList :=
    map_eq_of_pointwise (checked.step b) _ (checked.indices.stepPublicCount b) V hpub
  obtain ⟨-, hout⟩ := compileWith_reads (a := Unit) (b := StepPublic D)
    (main := C.stepCircuit (fun _ => 0) b inertStepAdvice) hV #v[] _ hlist
  have hread : CircuitType.Reads V (stepCompilation C b).result.1.1 t.statement :=
    (hout t.statement).mpr rfl
  refine ⟨⟨V, inertStepAdvice, ?_⟩, ?_⟩
  · rw [show (C.stepBuilt V b inertStepAdvice).constraints = (stepCompilation C b).constraints
      from congrArg Built.constraints (C.stepBuilt_eq V b inertStepAdvice)]
    exact hV
  · show CircuitType.Reads V (StepRun.cells ⟨V, inertStepAdvice, _⟩).out t.statement
    rw [StepRun.cells_eq, ← stepCompilation_out]
    exact hread

/-- **An accepted wrap table has a wrap execution at its statement.** -/
theorem CheckedApplication.lift_wrap {C : Circuits D L} (checked : CheckedApplication C)
    (t : WrapTable checked.indices) :
    ∃ r : WrapRun C, CircuitType.Reads r.V wrapStatement t.statement := by
  haveI : NeZero (wrapIndexData C).n :=
    ⟨by have := checked.wrap.index.zk_three; have := checked.wrap.index.zk_le; omega⟩
  obtain ⟨V, hV, hpub⟩ := checked.wrap.lift _ t.table t.holds
  have hlist : (wrapPublicVars C).map V =
      (CircuitType.valueToFields (F := Fq) t.statement).toList ++ (#v[] : Vector Fq 0).toList := by
    show _ = _ ++ ([] : List Fq)
    rw [List.append_nil]
    exact map_eq_of_pointwise checked.wrap _ checked.indices.wrapPublicCount V hpub
  obtain ⟨hin, -⟩ := compileWith_reads (a := WrapPublic) (b := Unit)
    (main := C.wrapCircuit (fun _ => 0) inertWrapAdvice) hV _ #v[] hlist
  refine ⟨⟨V, inertWrapAdvice, ?_⟩, (hin t.statement).mpr rfl⟩
  rw [show (C.wrapBuilt V inertWrapAdvice).constraints = (wrapCompilation C).constraints
    from congrArg Built.constraints (C.wrapBuilt_eq V inertWrapAdvice)]
  exact hV

end Pickles.Application
