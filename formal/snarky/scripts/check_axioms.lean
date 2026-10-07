/-
Axiom-closure gate for the Snarky DSL library: the interpreter laws, the leaf witness
interface, and every gadget's soundness and completeness law must be proved from the
standard logical axioms alone — the deep embedding is pure core Lean, so nothing else
(no `sorryAx`, no `native_decide`, no curve axioms) may appear in their closures. The sole
exception is the deployed endo dictionaries (`deployedRoots`): their fields may carry the
certified `native_decide` witnesses of the Pasta trust base, so every law theorem stays
pure core Lean and the deployed trust is localized in exactly those values.

The root list is a deletion guard as well as an axiom guard: a name absent from the environment
fails with `axiom-check root not in environment`, so removing a listed declaration — even
together with its `roots.txt` line — cannot pass silently.

Run from `formal/snarky/`:  lake env lean scripts/check_axioms.lean
-/
import Snarky
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.Poseidon
import Snarky.Kimchi.Circuit.RangeCheck
import Snarky.Kimchi.Circuit.Sponge
import Snarky.Kimchi.Circuit.RandomOracle
import Snarky.Kimchi.Circuit.EndoScalar
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Snarky.Kimchi.Circuit.GroupMap
import Snarky.Kimchi.Backend.Compile
import Snarky.Kimchi.Backend.Trace
import Snarky.Kimchi.Backend.TraceChecks
import Snarky.Kimchi.Backend.TraceSemantics
import Snarky.Kimchi.Backend.RowCorrespondence
import Snarky.Kimchi.Backend.Receipts
import Snarky.Kimchi.Backend.Direct
import Snarky.Kimchi.Backend.Wiring
import Snarky.Kimchi.Backend.DirectChecks
import Snarky.Kimchi.Backend.Wired
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Snarky.CheckAxioms

/-- The headline laws: the two interpreters and their composition, the reading vocabulary
every completeness law is stated in, the `witness` leaf interface, the traversal
combinators, the DSL operations, the whole-circuit layer, and the Kimchi gadgets. -/
def roots : List Name :=
  -- The interpreters, their composition, and the lockstep between them.
  [ `Snarky.build_bind,
    `Snarky.prove_pure,
    `Snarky.prove_bind,
    `Snarky.prove_addConstraint,
    `Snarky.prove_build_agrees,
    `Snarky.builder_spec_iff,
    `Snarky.addConstraint_spec,

    -- The completeness vocabulary: a run's reach, the rows it leaves satisfied, and the
    -- reading that survives a later run.
    `Snarky.Complete.bind,
    `Snarky.Complete.frame,
    `Snarky.Complete.imp,
    `Snarky.Complete.seq,
    `Snarky.Complete.pure,
    `Snarky.Complete.pure_of,
    `Snarky.Complete.addConstraint,
    `Snarky.Complete.of_false,
    `Snarky.Complete.instantiate,
    `Snarky.Complete.post,
    `Snarky.runs_post,
    `Snarky.run_le,
    `Snarky.CVar.val_of_le,
    `Snarky.CircuitType.Reads.of_le,
    `Snarky.CircuitType.Scoped.mono,
    `Snarky.CircuitType.monotone_readsAs,

    -- The leaf interface every gadget builds on.
    `Snarky.witness_spec,
    `Snarky.Complete.witness,

    -- The traversal combinators, whose laws the ladders' transports go through.
    `Snarky.forM_spec,
    `Snarky.forM_complete,
    `Snarky.mapAccumM_spec,
    `Snarky.mapAccumM_complete,
    `Snarky.zipWithVecM_spec,
    `Snarky.zipWithVecM_complete,

    -- The DSL: field operations.
    `Snarky.equals_spec, `Snarky.equals_complete,
    `Snarky.isZero_spec, `Snarky.isZero_complete,
    `Snarky.neq_spec, `Snarky.neq_complete,
    `Snarky.mul_spec, `Snarky.mul_complete,
    `Snarky.inv_spec, `Snarky.inv_complete,
    `Snarky.div_spec, `Snarky.div_complete,
    `Snarky.square_spec, `Snarky.square_complete,
    `Snarky.pow_spec, `Snarky.pow_complete,

    -- The DSL: boolean operations.
    `Snarky.and_spec, `Snarky.and_complete,
    `Snarky.or_spec, `Snarky.or_complete,
    `Snarky.xor_spec, `Snarky.xor_complete,
    `Snarky.any_spec, `Snarky.any_complete,
    `Snarky.all_spec, `Snarky.all_complete,
    `Snarky.selectField_spec, `Snarky.selectField_complete,
    `Snarky.LawfulIfThenElse.select_complete,

    -- The DSL: assertions.
    `Snarky.assert_spec, `Snarky.assert_complete,
    `Snarky.assertEq_spec, `Snarky.assertEq_complete,
    `Snarky.assertEqual_spec, `Snarky.assertEqual_complete,
    `Snarky.assertNonZero_spec, `Snarky.assertNonZero_complete,
    `Snarky.assertNotEqual_spec, `Snarky.assertNotEqual_complete,
    `Snarky.assertSquare_spec, `Snarky.assertSquare_complete,
    `Snarky.assertAny_spec, `Snarky.assertAny_complete,
    `Snarky.assertAll_spec, `Snarky.assertAll_complete,
    `Snarky.assertExactlyOne_spec, `Snarky.assertExactlyOne_complete,

    -- The DSL: bit decomposition and the seal.
    `Snarky.unpack_spec, `Snarky.unpack_complete,
    `Snarky.sealVar_spec, `Snarky.sealVar_complete,

    -- The whole-circuit layer: the public interface's reading, and the payoff.
    `Snarky.scoped_inputVar,
    `Snarky.reads_inputVar,
    `Snarky.solve_complete,

    -- The backends' reading of the `BasicSystem` primitives.
    `Snarky.instLawfulBasicSystemBasic,
    `Snarky.instLawfulBasicSystemBuilder,
    `Snarky.Kimchi.KimchiConstraint.instLawfulBasicSystem,

    -- The lowering trace: a recorded reduction erases to the existing reduction.
    `Snarky.Kimchi.record_reduceToVariable_erases,
    `Snarky.Kimchi.record_basic_erases,
    `Snarky.Kimchi.record_addComplete_erases,
    `Snarky.Kimchi.record_constraint_erases,
    `Snarky.Kimchi.recordGates_erase,
    `Snarky.Kimchi.recordBuilt_erase,
    `Snarky.Kimchi.recordBuilt_bodyRows,
    `Snarky.Kimchi.getElem_bodyRows_generic,
    `Snarky.Kimchi.getElem_bodyRows_gate,
    `Snarky.Kimchi.record_constraint_replays,
    `Snarky.Kimchi.record_constraint_allocates,
    `Snarky.Kimchi.record_constraint_decides,
    `Snarky.Kimchi.replayEvent_equal,
    `Snarky.Kimchi.outcomeOf_cached_mem,
    `Snarky.Kimchi.cache_replay,
    `Snarky.Kimchi.cached_mem,
    `Snarky.Kimchi.equalsHolds_of_merge,
    `Snarky.Kimchi.equalsHolds_of_cached,
    `Snarky.Kimchi.equalsHolds_of_pinned,
    `Snarky.Kimchi.equalsHolds_of_row,
    `Snarky.Kimchi.equalsHolds_of_trivial,
    `Snarky.Kimchi.mem_pinsOf,
    `Snarky.Kimchi.inv_replay,
    `Snarky.Kimchi.same_replay_mono,
    `Snarky.Kimchi.same_replay,
    `Snarky.Kimchi.directRoots_eq,
    `Snarky.Kimchi.KimchiConstraint.Wired.Scoped,
    `Snarky.Kimchi.fusion_root_eq,
    `Snarky.Kimchi.pinned_of_cached,
    `Snarky.Kimchi.unwired_not_named,
    `Snarky.Kimchi.unwired_of_cell,
    `Snarky.Kimchi.unwired_cell_unique,
    `Snarky.Kimchi.KimchiConstraint.Wired.holds_of_satisfies,
    `Snarky.Kimchi.receipts_located,
    `Snarky.Kimchi.receipts_complete,
    `Snarky.Kimchi.genericValue_of_located,
    `Snarky.Kimchi.record_boolean_var,
    `Snarky.Kimchi.record_addComplete_direct,
    `Snarky.Kimchi.KimchiConstraint.Direct.events_generic,
    `Snarky.Kimchi.steps_generic_of_direct,
    `Snarky.Kimchi.wireMap_getElem?,
    `Snarky.Kimchi.getElem_assembleGates,
    `Snarky.Kimchi.classCells_values_eq,
    `Snarky.Kimchi.length_assembleGates,
    `Snarky.Kimchi.classCells_bounds,
    `Snarky.Kimchi.mem_classCells_of_label,
    `Snarky.Kimchi.RecordedGates.length_placements,
    `Snarky.Kimchi.bodyRows_placed,
    `Snarky.Kimchi.placements_genericRows_count,
    `Snarky.Kimchi.placements_customRows_count,
    `Snarky.Kimchi.placements_customRows_le,
    `Snarky.Kimchi.KimchiConstraint.Direct.holds_of_satisfies,
    `Snarky.Kimchi.label_of_mem_classCells,
    `Snarky.Kimchi.wireMap_getElem?_eq_none,
    `Snarky.Kimchi.wireTarget_eq,
    `Snarky.Kimchi.length_directGates,
    `Snarky.Kimchi.getElem_directGates,
    `Snarky.Kimchi.indexOf_of_classTarget,
    `Snarky.Kimchi.direct_example_built,
    `Snarky.Kimchi.direct_example_scoped,
    `Snarky.Kimchi.direct_example_indexOf,
    `Snarky.Kimchi.direct_example_satisfies,
    `Snarky.Kimchi.direct_example_holds,
    `Snarky.Kimchi.direct_rejections,
    `Snarky.Kimchi.direct_rejections_index,
    -- The union-find's class view.
    `Snarky.Kimchi.UnionFind.empty_inv,
    `Snarky.Kimchi.UnionFind.find_inv,
    `Snarky.Kimchi.UnionFind.same_find_mono,
    `Snarky.Kimchi.UnionFind.union_inv,
    `Snarky.Kimchi.UnionFind.same_union_self,
    `Snarky.Kimchi.UnionFind.same_union_mono,
    `Snarky.Kimchi.UnionFind.rootOf_getD_eq,
    `Snarky.Kimchi.recorded_batching,
    `Snarky.Kimchi.recorded_wiring,
    `Snarky.Kimchi.recorded_constantCache,
    `Snarky.Kimchi.recorded_allocation,
    `Snarky.Kimchi.recorded_equalities,
    `Snarky.Kimchi.reduceToVariable_reads,
    `Snarky.Kimchi.boolean_of_reductionFacts,
    `Snarky.Kimchi.addComplete_read_eq,
    `Snarky.Kimchi.addComplete_holds_of_reductionFacts,

    -- The Kimchi gadgets.
    `Snarky.Kimchi.sealPoint_spec, `Snarky.Kimchi.sealPoint_complete,
    `Snarky.Kimchi.infColumn_spec,
    `Snarky.Kimchi.addFast_spec, `Snarky.Kimchi.addFast_complete,
    `Snarky.Kimchi.Poseidon.poseidon_spec, `Snarky.Kimchi.Poseidon.poseidon_complete,
    `Snarky.Kimchi.SpongeVar.absorb_spec, `Snarky.Kimchi.SpongeVar.absorb_complete,
    `Snarky.Kimchi.SpongeVar.squeeze_spec, `Snarky.Kimchi.SpongeVar.squeeze_complete,
    `Snarky.Kimchi.RandomOracle.update_spec, `Snarky.Kimchi.RandomOracle.update_complete,
    `Snarky.Kimchi.RandomOracle.hash2_spec, `Snarky.Kimchi.RandomOracle.hash2_complete,
    `Snarky.Kimchi.RandomOracle.hashVec_spec, `Snarky.Kimchi.RandomOracle.hashVec_complete,
    `Snarky.Kimchi.EndoScalar.toField_spec, `Snarky.Kimchi.EndoScalar.toField_complete,
    `Snarky.Kimchi.EndoMul.endoMul_spec, `Snarky.Kimchi.EndoMul.endoMul_complete,
    `Snarky.Kimchi.EndoMul.endoInv_spec, `Snarky.Kimchi.EndoMul.endoInv_complete,
    `Snarky.Kimchi.varBaseMul_spec, `Snarky.Kimchi.varBaseMul_complete,
    `Snarky.Kimchi.varBaseMul_spec_scalar,
    `Snarky.Kimchi.scaleFast1_spec, `Snarky.Kimchi.scaleFast1_complete,
    `Snarky.Kimchi.scaleFast2_spec, `Snarky.Kimchi.scaleFast2_complete,
    `Snarky.Kimchi.scaleFast2_spec_scalar,
    `Snarky.Kimchi.scaleFast2'_spec, `Snarky.Kimchi.scaleFast2'_complete,
    `Snarky.Kimchi.scaleFast2'_spec_scalar,
    `Snarky.Kimchi.splitFieldVar_spec, `Snarky.Kimchi.splitFieldVar_complete,
    `Snarky.Kimchi.rangeCheck128_spec, `Snarky.Kimchi.rangeCheck128_complete,
    `Snarky.Kimchi.lowest128Bits'_spec, `Snarky.Kimchi.lowest128Bits'_complete,
    `Snarky.Kimchi.groupMapCircuit_spec, `Snarky.Kimchi.groupMapCircuit_complete,
    `Snarky.Kimchi.groupMapCircuit_onCurve_spec,
    `Snarky.Kimchi.groupMapCircuit_toGroup_complete,
    `Snarky.Kimchi.groupMapPure_toGroup,

    -- The deployed dictionaries.
    `Snarky.Kimchi.HasEndo.pallas,
    `Snarky.Kimchi.HasEndo.vesta ]

/-- Pure core Lean: only the three standard logical axioms are permitted. -/
def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The deployed dictionaries — the only roots whose closures may additionally
    contain the certified `native_decide` witnesses (`isTrustedNativeDecide`): their
    fields discharge the curve facts at the concrete Pasta curves, whose trust base
    (the certified orders and eigenvalue anchors) carries those certificates. Every
    LAW stays pure core Lean — the whole native_decide trust of this package is
    localized in these two values. -/
def deployedRoots : List Name :=
  [ `Snarky.Kimchi.HasEndo.pallas,
    `Snarky.Kimchi.HasEndo.vesta ]

/-- A trusted `native_decide` certificate, discriminated by DEFINING MODULE rather than
    by name prefix (the kimchi gate's convention: the name is forgeable from inside a
    `namespace CompElliptic` block, the defining module is not): an upstream
    CompElliptic module, or `Pasta/Endo.lean` — the one tree file declared to hold the
    two GLV eigenvalue anchors. -/
def isTrustedNativeDecide (env : Environment) (ax : Name) : Bool :=
  (ax.toString.splitOn "native_decide").length > 1 &&
    match env.getModuleFor? ax with
    | some m => (`CompElliptic).isPrefixOf m || m == `Pasta.Endo
    | none => false

end Snarky.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Snarky.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Snarky.CheckAxioms.allowed.contains ax ||
          (Snarky.CheckAxioms.deployedRoots.contains root &&
            Snarky.CheckAxioms.isTrustedNativeDecide env ax) do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Snarky.CheckAxioms.roots.length} Snarky roots reduce to \
      {Snarky.CheckAxioms.allowed} (deployed dictionaries + certified native_decide)"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"

-- The soundness-tag invariant (`WP.lean`): a program enters the soundness reading by
-- NAMING the tag. `Builder V c` is `c` under a name instance search will not unfold, so
-- `WP (CircuitM F (Builder V c))` must resolve and `WP (CircuitM F c)` must not — a
-- generic instance at the untagged carrier would make the reading ambiguous. Checked at
-- a concrete carrier; a violating instance would be declared generically and land here.
run_cmd liftTermElabM do
  let resolves (ty : Lean.TSyntax `term) : Lean.Elab.TermElabM Bool := do
    let e ← Lean.instantiateMVars (← Lean.Elab.Term.elabType ty)
    return (← Lean.Meta.synthInstance? e).isSome
  unless ← resolves (← `(Std.Do.WP
      (Snarky.CircuitM Nat (Snarky.Builder (fun _ => (0 : Nat)) (Snarky.Basic Nat)))
      (Std.Do.PostShape.arg Nat Std.Do.PostShape.pure))) do
    throwError "no WP instance at the soundness tag — the tagged reading (WP.lean) is broken"
  IO.println "✓ WP resolves at the soundness tag"
  if ← resolves (← `(Std.Do.WP (Snarky.CircuitM Nat (Snarky.Basic Nat))
      (Std.Do.PostShape.arg Nat Std.Do.PostShape.pure))) then
    throwError "WP instance found at the untagged carrier — the soundness-tag \
      resolution invariant (WP.lean) is broken"
  IO.println "✓ no WP instance at the untagged carrier"
