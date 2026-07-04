/-
Axiom-closure gate for the Kimchi formalization.

`lake build` succeeds even with `sorry` (it is only a warning), so this script gates the headline
theorems explicitly: it collects the full axiom closure of each root and fails unless every axiom
is in the allowlist below — the three standard logical axioms, the two trusted Pasta Hasse-bound
axioms (`Kimchi.Pasta.{pallas_hasse, vesta_hasse}`, from which the group orders are *derived* via
CompElliptic), `Lean.ofReduceBool` (inherited from CompElliptic's `native_decide` order witness),
and the Pasta GLV endomorphism inputs. This subsumes the old `sorryAx` grep: a `sorry` shows up as
`sorryAx`, which is not in the allowlist, and any *other* stray axiom that slips in is caught too.

Run from `formal/`:  lake env lean scripts/check_axioms.lean   (or: scripts/check_axioms.sh)
-/
import Kimchi

open Lean Lean.Elab.Command

namespace Kimchi.CheckAxioms

/-- The headline theorems whose axiom closure must stay clean. -/
def roots : List Name :=
  [ `Kimchi.Gate.Generic.sound, `Kimchi.Gate.Generic.complete,
    `Kimchi.Gate.AddComplete.sound_noninf, `Kimchi.Gate.AddComplete.complete_noninf,
    `Kimchi.Gate.AddComplete.sound_point_noninf, `Kimchi.Gate.AddComplete.sound_point_inf,
    `Kimchi.Gate.AddComplete.ok_iff, `Kimchi.Gate.AddComplete.inf_boolean,
    `Kimchi.Gate.AddComplete.complete_inf, `Kimchi.Gate.AddComplete.complete,
    `Kimchi.Gate.AddComplete.sound,
    `Kimchi.Gate.VarBaseMul.sound, `Kimchi.Gate.VarBaseMul.complete,
    `WeierstrassCurve.Affine.zsmul_mod, `WeierstrassCurve.Affine.order_smul,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_forbidden_correct,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_subwrap_correct,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_scaleFast1,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_scaleFast2,
    -- EndoScalar gate + circuit soundness (#173).
    `Kimchi.Gate.EndoScalar.sound, `Kimchi.Gate.EndoScalar.complete,
    `Kimchi.Circuit.EndoScalar.chain_toField,
    `Kimchi.Circuit.EndoScalar.chain_complete,
    `Kimchi.Circuit.EndoScalar.endoScalar_unique,
    `Kimchi.Gate.EndoMul.sound, `Kimchi.Gate.EndoMul.complete,
    `Kimchi.Circuit.EndoMul.endoMul,
    `Kimchi.Circuit.EndoMul.pallas_endoMul, `Kimchi.Circuit.EndoMul.vesta_endoMul,
    `Kimchi.Circuit.EndoMul.pallas_combo_off_targets,
    `Kimchi.Circuit.EndoMul.vesta_combo_off_targets,
    `Kimchi.Commitment.IPA.ipa_soundness,
    `Kimchi.Commitment.IPA.commitmentBinding_iff_no_relation,
    `Kimchi.Commitment.IPA.ipaRelation_unique,
    `Kimchi.Commitment.IPA.vandermondeN,
    `Kimchi.Commitment.IPA.batch_soundness,
    `Kimchi.Quotient.zH_dvd_iff,
    `Kimchi.Quotient.genericRows_iff_dvd,
    -- The ingested-constraint-system checker: its faithfulness reflection and the
    -- completeAdd bridge into the AddComplete soundness suite.
    `Kimchi.Circuit.check_iff, `Kimchi.Circuit.rowHolds_completeAdd,
    -- The checker-facing custom-gate constraint reflections.
    `Kimchi.Checker.Generic.ok_iff, `Kimchi.Checker.VarBaseMul.ok_iff,
    `Kimchi.Checker.EndoScalar.ok_iff,
    `Kimchi.Checker.EndoMul.ok_iff, `Kimchi.Gate.Poseidon.ok_iff,
    -- Composing gates into circuits: the checker↔algebraic-gate bridge, the abstract chained
    -- soundness (threading assumed), and the gold-standard circuit soundness (threading + gate
    -- identities derived from the reconstructed circuit's `Satisfies`).
    `Kimchi.Gate.VarBaseMul.checker_holds_iff, `Kimchi.Circuit.VarBaseMul.chain_sound,
    `Kimchi.Circuit.VarBaseMul.circuit_sound,
    -- EndoMul: the checker↔gate bridge (up to the distinct-point non-degeneracy the dumped gate
    -- omits) and the gold-standard circuit soundness.
    `Kimchi.Gate.EndoMul.checker_holds_iff, `Kimchi.Circuit.EndoMul.circuit_sound,
    -- EndoScalar: the checker↔gate bridge (up to the `6·`-scaling / char precondition) and the
    -- gold-standard circuit soundness.
    `Kimchi.Gate.EndoScalar.checker_holds_iff, `Kimchi.Circuit.EndoScalar.circuit_sound,
    -- Pasta specializations of the circuit-composition proofs: routing `Satisfies` through the
    -- deployed Pasta roots discharges the curve non-degeneracy / char / order side conditions.
    `Kimchi.Circuit.VarBaseMul.varBaseMul_circuit_scaleFast1,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_circuit_scaleFast2,
    `Kimchi.Circuit.EndoMul.pallas_endoMul_circuit,
    -- Scalar-field lifts (#6): the integer output scalar reduced to its canonical residue in
    -- [0, order) — an element of the 2-cycle sister curve's base field.
    `WeierstrassCurve.Affine.exists_canonical_scalar,
    `Kimchi.Circuit.EndoMul.pallas_endoMul_circuit_scalar,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_circuit_scaleFast1_scalar,
    `Kimchi.Circuit.EndoScalar.pallas_circuit_sound,
    `Kimchi.Circuit.EndoScalar.vesta_circuit_sound,
    -- Poseidon: the per-row round-function bridge and the chained-permutation soundness (the
    -- chain computes the 5m-round Poseidon permutation of the initial state).
    `Kimchi.Gate.Poseidon.holds_rowPerm, `Kimchi.Circuit.Poseidon.circuit_sound,
    -- The concrete Pallas/Vesta endo constants are machine-checked to be primitive cube roots.
    `Kimchi.Pasta.pallas_endo_cube, `Kimchi.Pasta.vesta_endo_cube,
    -- Heterogeneous gate-combination examples: every unordered pair of the five custom kinds
    -- composes in one circuit, its Satisfies yielding both gates' algebraic facts.
    `Kimchi.Circuit.Combinations.exCA_VB_sound, `Kimchi.Circuit.Combinations.exCA_EM_sound,
    `Kimchi.Circuit.Combinations.exCA_ES_sound, `Kimchi.Circuit.Combinations.exCA_PO_sound,
    `Kimchi.Circuit.Combinations.exVB_EM_sound, `Kimchi.Circuit.Combinations.exVB_ES_sound,
    `Kimchi.Circuit.Combinations.exVB_PO_sound, `Kimchi.Circuit.Combinations.exEM_ES_sound,
    `Kimchi.Circuit.Combinations.exEM_PO_sound, `Kimchi.Circuit.Combinations.exES_PO_sound,
    -- Init grounding (#4): the chain's initial state sourced from setup rows — constant-pinning
    -- (EndoMulScalar) and CompleteAdd-doubling dataflow (VarBaseMul's [2]·T).
    `Kimchi.Circuit.InitGrounding.esSetup_pins_init,
    `Kimchi.Circuit.InitGrounding.completeAdd_doubles,
    -- Fully-grounded EndoMulScalar: init derived from trailing setup rows, no init hypotheses.
    `Kimchi.Circuit.EndoScalar.esCircuitGrounded_sound,
    -- VarBaseMul init from a CompleteAdd doubling (dataflow): P₀ = [2]·T derived, not assumed —
    -- the adapter, and the fully reconstructed circuit deriving the wiring from copyHolds.
    `Kimchi.Circuit.VarBaseMul.varBaseMul_scaleFast1_grounded,
    `Kimchi.Circuit.VarBaseMul.vbmCircuitGrounded_scaleFast1,
    -- Verifier sub-circuit: the IPA scale-and-combine MSM term p' = acc + [s]·T (VarBaseMul chain
    -- output fed into a CompleteAdd by dataflow), with the FULL complete-add disjunction.
    `Kimchi.Circuit.VarBaseMul.scaleCombine_sound,
    -- Rung 1: the fully-public statement — the whole dumped circuit reconstructed (public rows +
    -- init doubling + embedded chain + combine + inf assert), conclusion over pub alone.
    `Kimchi.Circuit.VarBaseMul.gateRegister_cast,
    `Kimchi.Circuit.VarBaseMul.scaleCombinePub_sound,
    -- Rung 3b: EndoScalar↔EndoMul sibling consistency — the scalar multiplied onto the point is
    -- the very field element the scalar run computed, joined at the shared crumb stream.
    `Kimchi.Circuit.EndoSibling.pallas_sibling_consistency,
    -- Rung 3a: the endo scale-and-combine MSM term (EndoMul chain output fed into a CompleteAdd),
    -- full complete-add disjunction.
    `Kimchi.Circuit.EndoMul.endoCombine_sound,
    -- Rung 2: the parametric n-term MSM — scale-and-combine blocks folded through their
    -- CompleteAdds (structural induction over the recursively-built circuit).
    `Kimchi.Circuit.VarBaseMul.blockStep, `Kimchi.Circuit.VarBaseMul.msm_sound,
    -- Rung 4: Fiat-Shamir — the transcript-derived challenge feeds the endo decode; the public
    -- output is the effective scalar of a challenge the circuit computes from its own inputs.
    `Kimchi.Circuit.FiatShamir.fiatShamir_sound,
    -- Rungs 5-6: the circuit ↔ commitment-layer IPA bridge. msm_recombine lands the circuit's
    -- MSM on the verifier's recombined commitment; circuit_ipa_soundness composes through
    -- VerifierAccepts into ipa_soundness — circuit satisfaction becomes knowledge soundness.
    `Kimchi.Circuit.IpaBridge.msm_recombine,
    `Kimchi.Circuit.IpaBridge.circuit_ipa_soundness,
    -- The fully circuit-grounded capstone: the Schnorr sides derived from circuits too.
    `Kimchi.Circuit.IpaBridge.circuit_ipa_soundness',
    -- The emission-monad semantics: elaborating the Poseidon gadget IS posCircuit, for all m —
    -- the generic replacement for the per-fixture reconstruction tie.
    `Kimchi.Circuit.Elab.elabPoseidon_eq_posCircuit,
    `Kimchi.Circuit.Elab.elabPoseidon_seq,
    -- The wire layer: cycle-pointer wires (kimchi's sigma) are extensionally class-constancy,
    -- and recovering the DSL's union-event specification from the cycle encoding is lossless.
    `Kimchi.Circuit.Elab.class_const_of_cycle,
    `Kimchi.Circuit.Elab.cycle_of_class_const,
    `Kimchi.Circuit.Elab.linksHold_of_cycles,
    -- End-to-end wired gadget: Satisfies of the realized circuit recovers the DSL's
    -- union-event specification — emission, wiring, realization, semantics, all theorems.
    `Kimchi.Circuit.Elab.pairCircuit_linksHold,
    -- copyHolds discharged from Ironwood's permutation kernel: the extensional copy constraints
    -- are a consequence of the grand-product multiset identity, not a modeling choice.
    `Kimchi.Circuit.Permutation.copyHolds_of_multiset,
    `Kimchi.Circuit.Permutation.cell_eq_of_sameCycle ]

/-- The only axioms the roots may depend on: the standard logical axioms; the Pasta Hasse bounds
    (`{pallas,vesta}_hasse`); `Lean.ofReduceBool`; and the Pasta CM eigenvalue relations
    (`{pallas,vesta}_eigen`). The endo coefficients `{pallas,vesta}_endo` are now concrete defs
    (machine-checked cube roots), no longer axioms. CompElliptic `native_decide` witnesses are
    permitted separately by
    `isTrustedNativeDecide`. -/
def allowed : List Name :=
  [ `propext, `Classical.choice, `Quot.sound, `Lean.ofReduceBool,
    `Kimchi.Pasta.pallas_hasse, `Kimchi.Pasta.vesta_hasse,
    `Kimchi.Pasta.pallas_eigen, `Kimchi.Pasta.vesta_eigen, ]

/-- A CompElliptic `native_decide` witness: an axiom under the `CompElliptic` namespace carrying the
    `native_decide` marker (these back CompElliptic's point counts). A `native_decide` in our own
    tree is not `CompElliptic`-namespaced, so it is still rejected. -/
def isTrustedNativeDecide (ax : Name) : Bool :=
  let s := ax.toString
  "CompElliptic.".isPrefixOf s && (s.splitOn "native_decide").length > 1

/-- An axiom is permitted if it is in the explicit allowlist or is a CompElliptic `native_decide`
    witness. -/
def isAllowed (ax : Name) : Bool := allowed.contains ax || isTrustedNativeDecide ax

end Kimchi.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Kimchi.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Kimchi.CheckAxioms.isAllowed ax do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Kimchi.CheckAxioms.roots.length} roots reduce to the allowed axiom set \
      {Kimchi.CheckAxioms.allowed}"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
