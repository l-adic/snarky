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
import Snarky.Kimchi.Backend.Internal.Trace
import Snarky.Kimchi.Backend.Checks.TraceChecks
import Snarky.Kimchi.Backend.Internal.TraceSemantics
import Snarky.Kimchi.Backend.Internal.RowCorrespondence
import Snarky.Kimchi.Backend.Internal.Receipts
import Snarky.Kimchi.Backend.Internal.Direct
import Snarky.Kimchi.Backend.Internal.Wiring
import Snarky.Kimchi.Backend.Checks.DirectChecks
import Snarky.Kimchi.Backend.Internal.Wired
import Snarky.Kimchi.Backend.Checks.WiredChecks
import Snarky.Kimchi.Backend.Checks.ScopedCheckChecks
import Snarky.Kimchi.Backend.Checks.CompiledIndexChecks
import Snarky.Kimchi.Backend.Checks.CheckedCompileChecks
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
    `Snarky.length_compiledPublicVars_compile,
    `Snarky.length_compiledPublicVars_compileWith,
    `Snarky.compile_reads,
    `Snarky.compileWith_reads,

    -- The backends' reading of the `BasicSystem` primitives.
    `Snarky.instLawfulBasicSystemBasic,
    `Snarky.instLawfulBasicSystemBuilder,
    `Snarky.Kimchi.KimchiConstraint.instLawfulBasicSystem,

    -- Checked compilation, the supported interface: the checks, whose results carry the scope
    -- and correspondence proofs, and lifting, whose closure is the whole lifting proof.
    `Snarky.Kimchi.CheckedIndex.«check?»,
    `Snarky.Kimchi.«checkBuilt?»,
    `Snarky.Kimchi.CheckedIndex.lift,
    `Snarky.Kimchi.CheckedIndex.publicCount_eq,
    `Snarky.Kimchi.CheckedIndex.publicIndex_val,
    `Snarky.Kimchi.«checkBuilt?_index»,
    `Snarky.Kimchi.CheckedIndex.«check?_index»,
    `Snarky.Kimchi.CheckedIndex.«check?_isOk_iff»,
    `Snarky.Kimchi.«gateTable?_isSome_iff»,
    `Snarky.Kimchi.«gateTable?_padding»,
    `Snarky.Kimchi.checkScoped_eq_true_iff,

    -- Regression checks: the facade-only consumer and the decided acceptances, rejections
    -- and recordings, each by its endpoint.
    `Snarky.Kimchi.CheckedConsumer.compile_lifts,
    `Snarky.Kimchi.CheckedConsumer.compileWith_lifts,
    `Snarky.Kimchi.CheckedConsumer.compile_reads_lifts,
    `Snarky.Kimchi.CheckedConsumer.compileWith_reads_lifts,
    `Snarky.Kimchi.direct_example_holds,
    `Snarky.Kimchi.direct_rejections,
    `Snarky.Kimchi.direct_rejections_index,
    `Snarky.Kimchi.wired_example_holds,
    `Snarky.Kimchi.wired_rejections_scope,
    `Snarky.Kimchi.wired_rejections_table,
    `Snarky.Kimchi.wired_rejections_index,
    `Snarky.Kimchi.endo_example_holds,
    `Snarky.Kimchi.endo_example_layout,
    `Snarky.Kimchi.chain_example_holds,
    `Snarky.Kimchi.chain_example_layout,
    `Snarky.Kimchi.endo_rejections,
    `Snarky.Kimchi.scale_example_holds,
    `Snarky.Kimchi.scale_example_layout,
    `Snarky.Kimchi.scaleChain_example_holds,
    `Snarky.Kimchi.scaleChain_example_layout,
    `Snarky.Kimchi.scale_rejections,
    `Snarky.Kimchi.endoMul_example_holds,
    `Snarky.Kimchi.endoMul_example_layout,
    `Snarky.Kimchi.endoMul_rejections,
    `Snarky.Kimchi.endoMul_rejections_index,
    `Snarky.Kimchi.poseidon_example_holds,
    `Snarky.Kimchi.poseidon_example_layout,
    `Snarky.Kimchi.poseidon_rejections,
    `Snarky.Kimchi.poseidon_rejections_index,
    `Snarky.Kimchi.pad_example_holds,
    `Snarky.Kimchi.pad_example_layout,
    `Snarky.Kimchi.pad_rejections,
    `Snarky.Kimchi.checkScoped_accepts,
    `Snarky.Kimchi.scopedFailure_range,
    `Snarky.Kimchi.scopedFailure_notWired,
    `Snarky.Kimchi.scopedFailure_reused,
    `Snarky.Kimchi.scopedFailure_precedence,
    `Snarky.Kimchi.compiledIndex_accepts,
    `Snarky.Kimchi.«compiledIndex_accepts'»,
    `Snarky.Kimchi.compiledIndex_rejects,
    `Snarky.Kimchi.gateTable_rejects,
    `Snarky.Kimchi.gateTable_padding,
    `Snarky.Kimchi.wired_example_holds_compiled,
    `Snarky.Kimchi.check_accepts,
    `Snarky.Kimchi.«check_accepts'»,
    `Snarky.Kimchi.check_rejects_scope,
    `Snarky.Kimchi.check_rejects_index,
    `Snarky.Kimchi.compileWith_example_layout,
    `Snarky.Kimchi.compile_example_holds,
    `Snarky.Kimchi.compileWith_example_holds,
    `Snarky.Kimchi.compile_example_reads,
    `Snarky.Kimchi.compileWith_example_reads,
    `Snarky.Kimchi.compile_example_rejects_altered,
    `Snarky.Kimchi.affine_example_reads,
    `Snarky.Kimchi.constant_example_reads,
    `Snarky.Kimchi.unit_output_example_reads,
    `Snarky.Kimchi.recorded_batching,
    `Snarky.Kimchi.recorded_wiring,
    `Snarky.Kimchi.recorded_constantCache,
    `Snarky.Kimchi.recorded_allocation,
    `Snarky.Kimchi.recorded_equalities,

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
