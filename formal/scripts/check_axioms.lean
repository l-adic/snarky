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
    `Kimchi.Quotient.identity_of_evals,
    `Kimchi.Quotient.dvd_separation,
    `Kimchi.Quotient.rows_iff_dvd_of,
    `Kimchi.Quotient.rowsSel_iff_dvd,
    `Kimchi.Quotient.AddComplete.rows_iff_dvd,
    `Kimchi.Quotient.VarBaseMul.rows_iff_dvd,
    `Kimchi.Quotient.EndoMul.rows_iff_dvd,
    `Kimchi.Quotient.AddComplete.soundness,
    `Kimchi.Quotient.VarBaseMul.soundness,
    `Kimchi.Quotient.EndoMul.soundness,
    `Kimchi.Quotient.Argument.rows_iff_dvd,
    `Kimchi.Quotient.Argument.soundness,
    `Kimchi.Quotient.EndoScalar.rows_iff_dvd,
    `Kimchi.Quotient.EndoScalar.soundness,
    `Kimchi.Gate.Poseidon.sound, `Kimchi.Gate.Poseidon.complete,
    `Kimchi.Quotient.Poseidon.rows_iff_dvd,
    `Kimchi.Quotient.Poseidon.soundness,
    `Kimchi.Quotient.multiset_eq_of_pairFactor_prod_eq,
    `Kimchi.Quotient.identity_of_grid_evals,
    `Kimchi.Quotient.multiset_eq_of_grid_prod_evals,
    `Kimchi.Verifier.verify_reflects, `Kimchi.Verifier.ipaVesta_sound,
    `Kimchi.Verifier.ipaPallas_sound ]

/-- The only axioms the roots may depend on: the standard logical axioms; the Pasta Hasse bounds
    (`{pallas,vesta}_hasse`); `Lean.ofReduceBool`; and the Pasta CM eigenvalue relations
    (`{pallas,vesta}_eigen` — the endomorphism coefficients `β` and eigenvalues `λ` themselves
    are concrete, proved definitions in `Kimchi/Pasta/Constants.lean`). CompElliptic
    `native_decide` witnesses are permitted separately by `isTrustedNativeDecide`. -/
def allowed : List Name :=
  [ `propext, `Classical.choice, `Quot.sound, `Lean.ofReduceBool,
    `Kimchi.Pasta.pallas_hasse, `Kimchi.Pasta.vesta_hasse,
    -- The declared Fiat-Shamir assumption: Poseidon-accepted runs admit de-blinded
    -- accepting transcript trees (`Kimchi/Verifier/Reflection.lean`). One per Pasta curve.
    `Kimchi.Verifier.poseidon_fiat_shamir_vesta, `Kimchi.Verifier.poseidon_fiat_shamir_pallas,
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
