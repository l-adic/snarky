/-
Axiom-closure gate for the Snarky DSL library: the interpreter laws must be proved from
the standard logical axioms alone — the deep embedding is pure core Lean, so nothing else
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
import Snarky.Kimchi.Circuit.CurvePoint
import Snarky.Kimchi.Backend.Compile
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Snarky.CheckAxioms

/-- The headline interpreter and gadget laws (beside their interpreters and gadgets). -/
def roots : List Name :=
  [ `Snarky.build_eraseWitness,
    `Snarky.prove_assignments_le,
    `Snarky.prove_build_agrees,
    `Snarky.prove_complete,
    `Snarky.CVar.eval_le,
    `Snarky.build_bind,
    `Snarky.prove_bind,
    `Snarky.equals_spec,
    `Snarky.equals_complete_spec,
    `Snarky.mul_spec,
    `Snarky.mul_complete_spec,
    `Snarky.inv_spec,
    `Snarky.inv_complete_spec,
    `Snarky.div_spec,
    `Snarky.div_complete_spec,
    `Snarky.square_spec,
    `Snarky.square_complete_spec,
    `Snarky.pow_spec,
    `Snarky.pow_complete_spec,
    `Snarky.sum_eval,
    `Snarky.not_eval,
    `Snarky.neq_spec,
    `Snarky.neq_complete_spec,
    `Snarky.and_spec,
    `Snarky.and_complete_spec,
    `Snarky.or_spec,
    `Snarky.or_complete_spec,
    `Snarky.xor_spec,
    `Snarky.xor_complete_spec,
    `Snarky.select_spec,
    `Snarky.select_complete_spec,
    `Snarky.assertEqual_spec,
    `Snarky.assertEqual_complete_spec,
    `Snarky.assertNonZero_spec,
    `Snarky.assertNonZero_complete_spec,
    `Snarky.assertNotEqual_spec,
    `Snarky.assertNotEqual_complete_spec,
    `Snarky.assertSquare_spec,
    `Snarky.assertSquare_complete_spec,
    `Snarky.assert_spec,
    `Snarky.assert_complete_spec,
    `Snarky.invCore_spec,
    `Snarky.any_spec,
    `Snarky.any_complete_spec,
    `Snarky.all_spec,
    `Snarky.all_complete_spec,
    `Snarky.allBools_spec,
    `Snarky.allBools_complete_spec,
    `Snarky.assertAny_spec,
    `Snarky.assertAny_complete_spec,
    `Snarky.assertAll_spec,
    `Snarky.assertAll_complete_spec,
    `Snarky.assertExactlyOne_spec,
    `Snarky.assertExactlyOne_complete_spec,
    `Snarky.pack_eval,
    `Snarky.pack_val,
    `Snarky.packPure_unpackPure,
    `Snarky.unpack_spec,
    `Snarky.unpack_complete_spec,
    `Snarky.ltBitstringValue_spec,
    `Snarky.ltBitstringValue_complete_spec,
    `Snarky.assertBitsBelow_spec,
    `Snarky.assertBitsBelow_complete_spec,
    `Snarky.unpackFull_spec,
    `Snarky.unpackFull_complete_spec,
    `Snarky.sealVar_spec,
    `Snarky.sealVar_complete_spec,
    `Snarky.Kimchi.AddFast.addFast_spec,
    `Snarky.Kimchi.AddFast.addFast_checkFinite_spec,
    `Snarky.Kimchi.Poseidon.poseidon_spec,
    `Snarky.Kimchi.Poseidon.poseidon_complete_spec,
    `Snarky.Kimchi.SpongeVar.absorb_spec,
    `Snarky.Kimchi.SpongeVar.squeeze_spec,
    `Snarky.Kimchi.SpongeVar.absorb_complete_spec,
    `Snarky.Kimchi.SpongeVar.squeeze_complete_spec,
    `Snarky.Kimchi.SpongeVar.vals_init,
    `Snarky.Kimchi.SpongeVar.vals_ofConstants,
    `Snarky.Kimchi.SpongeVar.reads_init,
    `Snarky.Kimchi.SpongeVar.reads_ofConstants,
    `Snarky.Kimchi.SpongeVar.Reads.le,
    `Snarky.Kimchi.RandomOracle.update_spec,
    `Snarky.Kimchi.RandomOracle.update_complete_spec,
    `Snarky.Kimchi.RandomOracle.hash2_spec,
    `Snarky.Kimchi.RandomOracle.hash2_complete_spec,
    `Snarky.Kimchi.RandomOracle.hashVec_spec,
    `Snarky.Kimchi.RandomOracle.hashVec_complete_spec,
    `Snarky.readVal_fvar,
    `Snarky.readVal_prod,
    `Snarky.readable_fvar_iff,
    `Snarky.readable_prod_iff,
    `Snarky.reads_fvar_iff,
    `Snarky.reads_prod_iff,
    `Snarky.Readable.le,
    `Snarky.Reads.le,
    `Snarky.ReadsAll.le,
    `Snarky.Reads.readable,
    `Snarky.Reads.unique,
    `Snarky.exists_reads,
    `Snarky.exists_readsAll,
    `Snarky.Kimchi.AddFast.addFast_complete_spec,
    `Snarky.Kimchi.EndoScalar.toFieldChecked'_spec,
    `Snarky.Kimchi.EndoScalar.toField_spec,
    `Snarky.Kimchi.EndoScalar.toFieldChecked'_complete_spec,
    `Snarky.Kimchi.EndoScalar.toField_complete_spec,
    `Snarky.Kimchi.EndoMul.endoMul_spec,
    `Snarky.Kimchi.EndoMul.endoMul_complete_spec,
    `Snarky.Kimchi.EndoMul.endoInv_spec,
    `Snarky.Kimchi.EndoMul.endoInv_complete_spec,
    `Snarky.Kimchi.varBaseMul_spec,
    `Snarky.Kimchi.varBaseMul_complete_spec,
    `Snarky.Kimchi.scaleFast1_complete_spec,
    `Snarky.Kimchi.scaleFast2_complete_spec,
    `Snarky.Kimchi.scaleFast2'_complete_spec,
    `Snarky.Kimchi.splitFieldVar_complete_spec,
    `Snarky.Kimchi.rangeCheck128_spec, `Snarky.Kimchi.rangeCheck128_complete_spec,
    `Snarky.Kimchi.lowest128Bits'_spec,
    `Snarky.Kimchi.lowest128Bits'_complete_spec,
    `Snarky.Kimchi.scaleFast1_spec,
    `Snarky.Kimchi.splitFieldVar_spec,
    `Snarky.Kimchi.scaleFast2_spec,
    `Snarky.Kimchi.scaleFast2'_spec,
    `Snarky.Kimchi.groupMapCircuit_spec,
    `Snarky.Kimchi.groupMapCircuit_complete_spec,
    `Snarky.Kimchi.groupMapPure_toGroup,
    `Snarky.Kimchi.groupMapCircuit_onCurve_spec,
    `Snarky.Kimchi.groupMapCircuit_toGroup_complete_spec,
    `Snarky.Kimchi.CurvePoint.check_spec,
    `Snarky.Kimchi.CurvePoint.check_complete_spec,
    `Snarky.Kimchi.HasEndo.pallas,
    `Snarky.Kimchi.HasEndo.vesta,
    `Snarky.Kimchi.HasEndo.vesta_crumbs_eq,
    `Snarky.Kimchi.HasEndo.vesta_endoExpand,
    `Snarky.Kimchi.HasCurve.pallas,
    `Snarky.Kimchi.HasCurve.vesta,
    `Snarky.Kimchi.vesta_ladderRegime,
    `Snarky.post_of_prove,

    `Snarky.addConstraint_spec,
    `Snarky.addConstraint_complete_spec,
    `Snarky.witnessBool_spec,
    `Snarky.witness_complete_spec,
    `Snarky.generateVec_spec,
    `Snarky.generateVec_complete_spec,
    `Snarky.sound_spec_iff,
    `Snarky.complete_spec_iff,
    `Snarky.Example.cubic_spec,
    `Snarky.Example.cubic_complete_spec,
    `Snarky.Example.cubic_sound,
    `Snarky.Example.cubic_complete,
    `Snarky.solve_complete,
    `Snarky.proveWith_compileBody_slots,
    `Snarky.Kimchi.kimchiOps_lockstep,
    `Snarky.Kimchi.kimchiOps_proveExtends,
    `Snarky.Kimchi.kimchiCompile_solve_nextVar,
    `Snarky.Kimchi.kimchiSolve_publicSlots,
    `Snarky.readVar_le,
    `Snarky.CVar.reduce_eval,
    `Snarky.fvar_value_roundTrip,
    `Snarky.fvar_var_roundTrip,
    `Snarky.boolVar_value_roundTrip,
    `Snarky.boolVar_var_roundTrip,
    `Snarky.build_eq_of_eraseWitness,
    `Snarky.CircuitM.instLawfulMonad,
    `Snarky.Basic.instLawfulBasicSystem,
    `Snarky.Basic.instLawfulChecker,
    `Snarky.Kimchi.KimchiConstraint.instLawfulBasicSystem,
    `Snarky.Kimchi.KimchiConstraint.instLawfulChecker,
    `Snarky.instLawfulCircuitTypeF,
    `Snarky.instLawfulCircuitTypeBool,
    `Snarky.instLawfulCircuitTypeUnChecked,
    `Snarky.instLawfulCircuitTypeProd,
    `Snarky.instLawfulCircuitTypeVector,
    `Snarky.instLawfulCheckedTypeF,
    `Snarky.instLawfulCheckedTypeUnChecked,
    `Snarky.instLawfulCheckedTypeBool,
    `Snarky.instLawfulCheckedTypeProd,
    `Snarky.instLawfulCheckedTypeVector,
    `Snarky.instWitnessReadsF,
    `Snarky.instWitnessReadsBool,
    `Snarky.instWitnessReadsUnChecked,
    `Snarky.instWitnessReadsProd,
    `Snarky.instWitnessReadsVector,
    `Snarky.CircuitType.ofEquiv,
    `Snarky.LawfulCircuitType.ofEquiv,
    `Snarky.CheckedType.ofEquiv,
    `Snarky.LawfulCheckedType.ofEquiv,
    `Snarky.WitnessReads.ofEquiv ]

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
    `Snarky.Kimchi.HasEndo.vesta,
    `Snarky.Kimchi.HasEndo.vesta_crumbs_eq,
    `Snarky.Kimchi.HasEndo.vesta_endoExpand,
    `Snarky.Kimchi.HasCurve.pallas,
    `Snarky.Kimchi.HasCurve.vesta,
    `Snarky.Kimchi.vesta_ladderRegime ]

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

-- The prover-tag invariant (`Backend/WP.lean`): the prover carriers must carry no
-- `ConstraintHolds` instance — one would make the two `WP` instances on `CircuitM`
-- ambiguous at the tag. Checked at a concrete field; a violating instance would be
-- declared generically and land here.
run_cmd liftTermElabM do
  for carrier in [``Snarky.ProverC, ``Snarky.Kimchi.KimchiProverC] do
    let ty := Lean.mkApp2 (Lean.mkConst ``Snarky.ConstraintHolds)
      (Lean.mkConst ``Snarky.Example.F17)
      (Lean.mkApp (Lean.mkConst carrier) (Lean.mkConst ``Snarky.Example.F17))
    if (← Lean.Meta.synthInstance? ty).isSome then
      throwError "ConstraintHolds instance found at {carrier} — the prover WP \
        resolution invariant (Backend/WP.lean) is broken"
    IO.println s!"✓ no ConstraintHolds instance at {carrier}"
