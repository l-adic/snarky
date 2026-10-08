import Snarky.Kimchi.Backend.Checks.CheckedCompileConsumer
import Snarky.Kimchi.Backend.Checks.WiredFixtures
import Snarky.Kimchi.Backend.Checks.Table
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Checked-compilation checks

The checked compilation decided over a field of 113 elements, in the kernel. The check accepts
the eight accepted sources of the wired-fragment checks. It reports a source out of scope by
the scope checker's failure, at parameters where the index would not be built either, and it
reports the index failure for a source in scope whose index is not built. Each case rewrites
the assembled gates to the class-based ones with `directGates_eq_classGates`, and a lifted
circuit's checked index is identified with that one through `checkBuilt?_index`.

The public-interface consumer's circuit is compiled with `compile`, and with `compileWith`
keeping its first product as a cell; the kept cell is the result's, and the public variables are
the same. Each compilation's checked index comes from `checkBuilt?`, the table the prover's values
fill is decided to satisfy it, and the consumer's `compile_lifts` and `compileWith_lifts` lift
it, with no scope or correspondence argument; `compile_reads_lifts` and `compileWith_reads_lifts`
read the lifted valuation as the inputs `3`, `5` and the output `45`.

`compile_reads` is also decided on three circuits of its own, its premise that the compiled
rows hold decided directly: one whose output is the expression `x + 1`, read through the row
binding it to its fresh public copy, one with no input and a constant output, and one with no
output.

## Main results

- `check_accepts`, `check_accepts'`: the check on the accepted sources.
- `check_rejects_scope`, `check_rejects_index`: the two failures.
- `compileWith_example_layout`: the kept cell and the public variables.
- `compile_example_holds`, `compileWith_example_holds`: the lifted valuations.
- `compile_example_reads`, `compileWith_example_reads`: their typed readings.
- `affine_example_reads`, `constant_example_reads`, `unit_output_example_reads`: the typed
  reading of an expression output, of an empty input bundle and of an empty output bundle.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky WiredFixture

instance : Fact (Nat.Prime 113) := ⟨by norm_num⟩

/-! ## Sources -/

/-- The check accepts the first four accepted sources. -/
theorem check_accepts :
    (CheckedIndex.check? source publicVars 20 16 3 40 0 mds shifts).isOk ∧
    (CheckedIndex.check? endoSource endoPublic 11 16 3 40 0 mds shifts).isOk ∧
    (CheckedIndex.check? chainSource chainPublic 22 16 3 40 0 mds shifts).isOk ∧
    (CheckedIndex.check? scaleSource scalePublic 25 16 3 40 0 mds shifts).isOk := by
  simp only [CheckedIndex.check?_isOk_iff, compiledIndex?, directGates_eq_classGates]
  decide +kernel

/-- The check accepts the other four accepted sources, each at its own parameters. -/
theorem check_accepts' :
    (CheckedIndex.check? scaleChainSource scaleChainPublic 46 16 3 40 0 mds shifts).isOk ∧
    (CheckedIndex.check? endoMulSource endoMulPublic 28 16 3 40 2 mds shifts).isOk ∧
    (CheckedIndex.check? poseidonSource poseidonPublic 32 16 3 40 0 poseidonMds shifts).isOk ∧
    (CheckedIndex.check? padSource padPublic 5 16 3 40 0 mds shifts).isOk := by
  simp only [CheckedIndex.check?_isOk_iff, compiledIndex?, directGates_eq_classGates]
  decide +kernel

/-- A variable at the counter is reported as the scope failure, on a domain of four rows with
three masked, where the index would not be built either. -/
theorem check_rejects_scope :
    (compiledIndex? highSource publicVars 20 4 3 1 0 mds shifts).isNone ∧
    CheckedIndex.check? highSource publicVars 20 4 3 1 0 mds shifts =
      .error (.scope (.outOfRange 5 20)) := by
  refine ⟨?_, ?_⟩
  · simp only [compiledIndex?, directGates_eq_classGates]
    decide +kernel
  · have hs : scopedFailure? 20 highSource publicVars = some (.outOfRange 5 20) := by
      decide +kernel
    unfold CheckedIndex.check?
    split
    · rename_i f hf
      rw [hs] at hf
      cases hf
      rfl
    · rename_i hf
      rw [hs] at hf
      cases hf

/-- A Poseidon block at another matrix is in scope, and the check reports the index failure. -/
theorem check_rejects_index :
    CheckedIndex.check? poseidonSource poseidonPublic 32 16 3 40 0 mds shifts = .error .index := by
  have hs : scopedFailure? 32 poseidonSource poseidonPublic = none := by
    decide +kernel
  have hi : compiledIndex? poseidonSource poseidonPublic 32 16 3 40 0 mds shifts = none := by
    rw [← Option.isNone_iff_eq_none]
    simp only [compiledIndex?, directGates_eq_classGates]
    decide +kernel
  unfold CheckedIndex.check?
  split
  · rename_i f hf
    rw [hs] at hf
    cases hf
  · split
    · rename_i idx hidx
      rw [hi] at hidx
      cases hidx
    · rfl

/-! ## The consumer's circuit -/

open CheckedConsumer

/-- The prover's values: the inputs `3` and `5`, the product `15`, the output `45` and its
public copy. -/
private def V : Valuation K := fun v => [3, 5, 15, 45, 45].getD v 0

/-- The kept cell is the first product, and keeping it adds no public variable: the inputs and
the output's public copy. -/
theorem compileWith_example_layout :
    ((builtWith K).result.1.2 matches .var 2) ∧
      publicVarsOf (builtWith K) = publicVarsOf (built K) ∧
      publicVarsOf (built K) = [0, 1, 4] := by
  decide +kernel

/-- The constructor's index of a compiled circuit, by the class-based gates. -/
private def classIndex? {β : Type} (b : Built (KimchiConstraint K) (β × FVar K)) :
    Option (Index K 16) :=
  indexOfGates? (classGates (directRoots b.constraints b.nextVar)
    (directRows b.constraints (publicVarsOf b) b.nextVar)) b.constraints (publicVarsOf b).length
    16 3 40 0 mds shifts

/-- A compiled circuit the check accepts has a checked index, which the prover's table satisfies
at the prover's public values when it satisfies the class-based index. -/
private theorem checked_of_class {β : Type} (b : Built (KimchiConstraint K) (β × FVar K))
    (hok : (checkBuilt? (a := K × K) (b := K) b 16 3 40 0 mds shifts).isOk = true)
    (hsome : (classIndex? b).isSome = true)
    (hsat : ((classIndex? b).get hsome).Satisfies (fun j => V ((publicVarsOf b).getD j.val 0))
      (tableOf V (directRows b.constraints (publicVarsOf b) b.nextVar))) :
    ∃ c : CheckedIndex b.constraints (publicVarsOf b) b.nextVar 16,
      c.index.Satisfies (fun j => V (publicVarsOf b)[Fin.cast c.publicCount_eq j])
        (tableOf V (directRows b.constraints (publicVarsOf b) b.nextVar)) := by
  obtain ⟨c, hc⟩ : ∃ c, checkBuilt? (a := K × K) (b := K) b 16 3 40 0 mds shifts = .ok c := by
    revert hok
    cases checkBuilt? (a := K × K) (b := K) b 16 3 40 0 mds shifts with
    | ok c => exact fun _ => ⟨c, rfl⟩
    | error _ => simp [Except.isOk, Except.toBool]
  have hidx : c.index = (classIndex? b).get hsome := by
    have h := checkBuilt?_index hc
    rw [gateDataOf_reduceBuilt, directGates_eq_classGates] at h
    exact Option.some_injective _ (h.symm.trans (Option.some_get hsome).symm)
  refine ⟨c, ?_⟩
  have hpub : (fun j : Fin c.index.publicCount => V (publicVarsOf b)[Fin.cast c.publicCount_eq j]) =
      fun j => V ((publicVarsOf b).getD j.val 0) :=
    funext fun j => (congrArg V (List.getD_eq_getElem _ _ (Fin.cast c.publicCount_eq j).isLt)).symm
  rw [hpub, hidx]
  exact hsat

/-- **Lifting a compiled circuit.** The consumer's circuit compiled by `compile`, checked by
`checkBuilt?`, lifts through `compile_lifts` from the prover's table to a valuation satisfying
every compiled constraint and agreeing with the prover's at the public variables. -/
theorem compile_example_holds :
    ∃ W : Valuation K, (∀ c ∈ (built K).constraints, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin (publicVarsOf (built K)).length,
        W (publicVarsOf (built K))[i] = V (publicVarsOf (built K))[i] := by
  obtain ⟨c, hsat⟩ := checked_of_class (built K)
    (by
      simp only [checkBuilt?, CheckedIndex.check?_isOk_iff, compiledIndex?,
        directGates_eq_classGates]
      decide +kernel)
    (by decide +kernel) (by decide +kernel)
  exact compile_lifts c (fun i => V (publicVarsOf (built K))[i]) _ hsat

/-- The same lifting for the circuit compiled by `compileWith` with its kept cell, through
`compileWith_lifts`. -/
theorem compileWith_example_holds :
    ∃ W : Valuation K, (∀ c ∈ (builtWith K).constraints, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin (publicVarsOf (builtWith K)).length,
        W (publicVarsOf (builtWith K))[i] = V (publicVarsOf (builtWith K))[i] := by
  obtain ⟨c, hsat⟩ := checked_of_class (builtWith K)
    (by
      simp only [checkBuilt?, CheckedIndex.check?_isOk_iff, compiledIndex?,
        directGates_eq_classGates]
      decide +kernel)
    (by decide +kernel) (by decide +kernel)
  exact compileWith_lifts c (fun i => V (publicVarsOf (builtWith K))[i]) _ hsat

/-- **Typed lifting of a compiled circuit.** The valuation `compile_reads_lifts` gives reads
the inputs `3`, `5` and the output `45`. -/
theorem compile_example_reads :
    ∃ W : Valuation K, (∀ c ∈ (built K).constraints, KimchiConstraint.Holds W c) ∧
      CircuitType.Reads W (inputVar (F := K) (a := K × K)) ((3, 5) : K × K) ∧
      CircuitType.Reads W (built K).result.1 (45 : K) := by
  obtain ⟨c, hsat⟩ := checked_of_class (built K)
    (by
      simp only [checkBuilt?, CheckedIndex.check?_isOk_iff, compiledIndex?,
        directGates_eq_classGates]
      decide +kernel)
    (by decide +kernel) (by decide +kernel)
  obtain ⟨W, hW, hin, hout⟩ := compile_reads_lifts c (fun i => V (publicVarsOf (built K))[i]) _
    hsat #v[3, 5] #v[45] (by decide +kernel)
  exact ⟨W, hW, (hin _).mpr (by decide +kernel), (hout _).mpr (by decide +kernel)⟩

/-- The same typed reading for the circuit compiled with its kept cell. -/
theorem compileWith_example_reads :
    ∃ W : Valuation K, (∀ c ∈ (builtWith K).constraints, KimchiConstraint.Holds W c) ∧
      CircuitType.Reads W (inputVar (F := K) (a := K × K)) ((3, 5) : K × K) ∧
      CircuitType.Reads W (builtWith K).result.1.1 (45 : K) := by
  obtain ⟨c, hsat⟩ := checked_of_class (builtWith K)
    (by
      simp only [checkBuilt?, CheckedIndex.check?_isOk_iff, compiledIndex?,
        directGates_eq_classGates]
      decide +kernel)
    (by decide +kernel) (by decide +kernel)
  obtain ⟨W, hW, hin, hout⟩ := compileWith_reads_lifts c
    (fun i => V (publicVarsOf (builtWith K))[i]) _ hsat #v[3, 5] #v[45] (by decide +kernel)
  exact ⟨W, hW, (hin _).mpr (by decide +kernel), (hout _).mpr (by decide +kernel)⟩

/-! ## Typed readings of other outputs -/

/-- A circuit whose output is the expression `x + 1`, not a variable. -/
private def offset (x : FVar K) : CircuitM K (KimchiConstraint K) (FVar K) :=
  pure (CVar.add_ x (.const 1))

/-- The input `4` and its public copy of the output, `5`. -/
private def offsetV : Valuation K := fun v => [4, 5].getD v 0

/-- The body's output `x + 1` reads as `5` through the row binding it to the public copy. -/
theorem affine_example_reads :
    CircuitType.Reads offsetV (inputVar (F := K) (a := K)) (4 : K) ∧
      CircuitType.Reads offsetV (compile (a := K) (b := K) offset).result.1 (5 : K) := by
  have hsat : ∀ c ∈ (compile (a := K) (b := K) offset).constraints,
      KimchiConstraint.Holds offsetV c := by
    decide +kernel
  obtain ⟨hin, hout⟩ := compile_reads hsat #v[4] #v[5] (by decide +kernel)
  exact ⟨(hin _).mpr rfl, (hout _).mpr rfl⟩

/-- A circuit with no input and the constant output `7`. -/
private def seven (_ : Unit) : CircuitM K (KimchiConstraint K) (FVar K) :=
  pure (.const 7)

/-- The empty input bundle reads as `()`, and the constant output as `7`. -/
theorem constant_example_reads :
    CircuitType.Reads (fun _ => (7 : K)) (inputVar (F := K) (a := Unit)) () ∧
      CircuitType.Reads (fun _ => (7 : K)) (compile (a := Unit) (b := K) seven).result.1
        (7 : K) := by
  have hsat : ∀ c ∈ (compile (a := Unit) (b := K) seven).constraints,
      KimchiConstraint.Holds (fun _ => (7 : K)) c := by
    decide +kernel
  obtain ⟨hin, hout⟩ := compile_reads hsat #v[] #v[7] (by decide +kernel)
  exact ⟨(hin _).mpr rfl, (hout _).mpr rfl⟩

/-- A circuit with no output. -/
private def discard (_ : FVar K) : CircuitM K (KimchiConstraint K) Unit :=
  pure ()

/-- The input reads as `4`, and the empty output bundle as `()`. -/
theorem unit_output_example_reads :
    CircuitType.Reads (fun _ => (4 : K)) (inputVar (F := K) (a := K)) (4 : K) ∧
      CircuitType.Reads (fun _ => (4 : K)) (compile (a := K) (b := Unit) discard).result.1 () := by
  have hsat : ∀ c ∈ (compile (a := K) (b := Unit) discard).constraints,
      KimchiConstraint.Holds (fun _ => (4 : K)) c := by
    decide +kernel
  obtain ⟨hin, hout⟩ := compile_reads hsat #v[4] #v[] (by decide +kernel)
  exact ⟨(hin _).mpr rfl, (hout _).mpr rfl⟩

end Snarky.Kimchi
