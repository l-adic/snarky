import Snarky.Kimchi.Backend.CheckedCompile
import Snarky.Kimchi.Backend.WiredFixtures
import Snarky.DSL.Field
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Checked-compilation checks

The checked compilation decided over a field of 113 elements, in the kernel. The check accepts
the eight accepted sources of the wired-fragment checks. It reports a source out of scope by
the scope checker's failure, at parameters where the index would not be built either, and it
rejects a source in scope whose index is not built. Each case rewrites the assembled gates to
the class-based ones with `directGates_eq_classGates`, and a lifted circuit's checked index is
identified with that one through `checkBuilt?_index`.

A small circuit multiplies its two inputs and the product by the first input. It is compiled
with `compile`, and with `compileWith` keeping the first product as a cell; the kept cell is the
result's, and the public variables are the same. Each compilation is checked by `checkBuilt?`
and lifted by `CheckedIndex.lift` from the table the prover's values fill, with no scope or
correspondence argument.

## Main results

- `check_accepts`, `check_accepts'`: the check on the accepted sources.
- `check_rejects_scope`, `check_rejects_index`: the two failures.
- `compileWith_example_layout`: the kept cell and the public variables.
- `compile_example_holds`, `compileWith_example_holds`: the lifted valuations.
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

/-- The failure a check reports. -/
private def failureOf {α : Type} : Except CheckFailure α → Option CheckFailure
  | .error e => some e
  | .ok _ => none

/-- A variable at the counter is reported as the scope failure, on a domain of four rows with
three masked, where the index would not be built either. -/
theorem check_rejects_scope :
    (compiledIndex? highSource publicVars 20 4 3 1 0 mds shifts).isNone ∧
    failureOf (CheckedIndex.check? highSource publicVars 20 4 3 1 0 mds shifts) =
      some (.scope (.outOfRange 5 20)) := by
  refine ⟨?_, by decide +kernel⟩
  simp only [compiledIndex?, directGates_eq_classGates]
  decide +kernel

/-- A Poseidon block at another matrix is in scope, and the check rejects it. -/
theorem check_rejects_index :
    checkScoped 32 poseidonSource poseidonPublic = true ∧
    (CheckedIndex.check? poseidonSource poseidonPublic 32 16 3 40 0 mds shifts).isOk = false := by
  simp only [← Bool.not_eq_true, CheckedIndex.check?_isOk_iff, compiledIndex?,
    directGates_eq_classGates]
  decide +kernel

/-! ## A compiled circuit -/

/-- The circuit's body: the product of the inputs, kept as a cell, times the first input. -/
private def circuitWith (p : FVar K × FVar K) :
    CircuitM K (KimchiConstraint K) (FVar K × FVar K) := do
  let z ← mul p.1 p.2
  let w ← mul z p.1
  pure (w, z)

/-- The circuit without the kept cell. -/
private def circuit (p : FVar K × FVar K) : CircuitM K (KimchiConstraint K) (FVar K) :=
  Prod.fst <$> circuitWith p

private def built : Built (KimchiConstraint K) (FVar K × FVar K) :=
  compile (a := K × K) (b := K) circuit

private def builtWith : Built (KimchiConstraint K) ((FVar K × FVar K) × FVar K) :=
  compileWith (a := K × K) (b := K) circuitWith

/-- A compiled circuit's public variables. -/
private abbrev pvOf {β : Type} (b : Built (KimchiConstraint K) (β × FVar K)) : List Variable :=
  compiledPublicVars (F := K) (a := K × K) (b := K) b

/-- The prover's values: the inputs `3` and `5`, the product `15`, the output `45` and its
public copy. -/
private def V : Valuation K := fun v => [3, 5, 15, 45, 45].getD v 0

/-- The kept cell is the first product, and keeping it adds no public variable: the inputs and
the output's public copy. -/
theorem compileWith_example_layout :
    (builtWith.result.1.2 matches .var 2) ∧ pvOf builtWith = pvOf built ∧
      pvOf built = [0, 1, 4] := by
  decide +kernel

/-- The constructor's index of a compiled circuit, by the class-based gates. -/
private def classIndex? {β : Type} (b : Built (KimchiConstraint K) (β × FVar K)) :
    Option (Index K 16) :=
  indexOfGates? (classGates (directRoots b.constraints b.nextVar)
    (directRows b.constraints (pvOf b) b.nextVar)) b.constraints (pvOf b).length 16 3 40 0 mds
    shifts

/-- A compiled circuit the check accepts lifts from the prover's table on its index: a
valuation satisfying every compiled constraint and agreeing with the prover's at the public
variables. -/
private theorem lifts {β : Type} (b : Built (KimchiConstraint K) (β × FVar K))
    (hok : (checkBuilt? (a := K × K) (b := K) b 16 3 40 0 mds shifts).isOk = true)
    (hsome : (classIndex? b).isSome = true)
    (hsat : ((classIndex? b).get hsome).Satisfies (fun i => V ((pvOf b).getD i.val 0))
      (tableOf V (directRows b.constraints (pvOf b) b.nextVar))) :
    ∃ W : Valuation K, (∀ c ∈ b.constraints, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin (pvOf b).length, W (pvOf b)[i] = V (pvOf b)[i] := by
  obtain ⟨c, hc⟩ : ∃ c, checkBuilt? (a := K × K) (b := K) b 16 3 40 0 mds shifts = .ok c := by
    revert hok
    cases checkBuilt? (a := K × K) (b := K) b 16 3 40 0 mds shifts with
    | ok c => exact fun _ => ⟨c, rfl⟩
    | error _ => simp [Except.isOk, Except.toBool]
  have hidx : c.index = (classIndex? b).get hsome := by
    have h := checkBuilt?_index hc
    rw [gateDataOf_reduceBuilt, directGates_eq_classGates] at h
    exact Option.some_injective _ (h.symm.trans (Option.some_get hsome).symm)
  obtain ⟨W, hW, hpub⟩ :=
    c.lift (fun i => V ((pvOf b).getD i.val 0)) (tableOf V (directRows b.constraints (pvOf b)
      b.nextVar)) (by rw [hidx]; exact hsat)
  refine ⟨W, hW, fun i => ?_⟩
  rw [hpub i]
  exact congrArg V (List.getD_eq_getElem _ _ i.isLt)

/-- **Lifting a compiled circuit.** The circuit compiled by `compile`, checked by
`checkBuilt?`, lifts from the prover's table to a valuation satisfying every compiled
constraint and agreeing with the prover's at the public variables. -/
theorem compile_example_holds :
    ∃ W : Valuation K, (∀ c ∈ built.constraints, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin (pvOf built).length, W (pvOf built)[i] = V (pvOf built)[i] := by
  refine lifts built ?_ (by decide +kernel) (by decide +kernel)
  simp only [checkBuilt?, CheckedIndex.check?_isOk_iff, compiledIndex?, directGates_eq_classGates]
  decide +kernel

/-- The same lifting for the circuit compiled by `compileWith` with its kept cell. -/
theorem compileWith_example_holds :
    ∃ W : Valuation K, (∀ c ∈ builtWith.constraints, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin (pvOf builtWith).length, W (pvOf builtWith)[i] = V (pvOf builtWith)[i] := by
  refine lifts builtWith ?_ (by decide +kernel) (by decide +kernel)
  simp only [checkBuilt?, CheckedIndex.check?_isOk_iff, compiledIndex?, directGates_eq_classGates]
  decide +kernel

end Snarky.Kimchi
