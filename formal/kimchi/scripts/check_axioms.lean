/-
Axiom-closure gate for the Kimchi formalization.

`lake build` succeeds even with `sorry` (it is only a warning), so this script gates the headline
theorems explicitly: it collects the full axiom closure of each root and fails unless every axiom
is in the allowlist below — the three standard logical axioms and the trusted `native_decide`
certificates (the Pasta group orders are *unconditional*, derived via
CompElliptic's fibre-bound argument) — `Lean.ofReduceBool` plus the named certificate
declarations. This subsumes the old `sorryAx` grep: a `sorry` shows up as
`sorryAx`, which is not in the allowlist, and any *other* stray axiom that slips in is caught too.

Run from `formal/kimchi/`:  lake env lean scripts/check_axioms.lean
(or from `formal/`:         lake env lean kimchi/scripts/check_axioms.lean)
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
    `Kimchi.Gate.VarBaseMul.varBaseMul_forbidden_correct,
    `Kimchi.Gate.VarBaseMul.varBaseMul_subwrap_correct,
    `Kimchi.Gate.VarBaseMul.varBaseMul_scaleFast1,
    `Kimchi.Gate.VarBaseMul.varBaseMul_scaleFast2,
    `Kimchi.Gate.EndoScalar.sound, `Kimchi.Gate.EndoScalar.complete,
    `Kimchi.Gate.EndoScalar.chain_toField,
    `Kimchi.Gate.EndoScalar.chain_complete,
    `Kimchi.Gate.EndoScalar.endoScalar_unique,
    `Kimchi.Gate.EndoMul.sound, `Kimchi.Gate.EndoMul.complete,
    `Kimchi.Gate.EndoMul.endoMul,
    `Kimchi.Gate.EndoMul.pallas_endoMul, `Kimchi.Gate.EndoMul.vesta_endoMul,
    `Kimchi.Quotient.zH_dvd_iff,
    `Kimchi.Quotient.dvd_separation,
    `Kimchi.Quotient.rowsSel_iff_dvd,
    `Kimchi.Quotient.Argument.soundness,
    `Kimchi.Gate.Poseidon.sound, `Kimchi.Gate.Poseidon.complete,
    `Kimchi.Quotient.prod_eq_of_accumulator,
    `Kimchi.Quotient.Permutation.soundness,
    `Kimchi.Quotient.copy_soundness, `Kimchi.Quotient.Permutation.copy_soundness,
    `Kimchi.Quotient.Permutation.copy_soundness_wired,
    `Kimchi.Index.rowSatisfies_of_evalCheck,
    `Kimchi.Index.satisfies_of_evalCheck,
    `Kimchi.Index.gateMember_dvd_of_rowSatisfies,
    `Kimchi.Index.satisfies_iff_fullFamily_dvd,
    `Kimchi.Quotient.multiset_eq_of_prod_eval,
    `Kimchi.Verifier.kimchiVerify_reflects, `Kimchi.Verifier.barycentricPubEval_eq,
    `Kimchi.Protocol.Equation.verifierEquation_iff,
    `Kimchi.Protocol.Equation.satisfies_of_verifierEquation,
    `Kimchi.Protocol.kimchiProof_sound_of_openings,
    `Kimchi.Verifier.kimchiVesta_run_sound, `Kimchi.Verifier.kimchiPallas_run_sound,
    `Kimchi.Verifier.kimchiProof_sound_algebraic,
    `Kimchi.Verifier.kimchiProof_sound_algebraic_ft,
    `Kimchi.Verifier.ft_opening_of_reflected,
    `Kimchi.Verifier.ft_opening_of_reflected_vesta,
    `Kimchi.Verifier.ft_opening_of_reflected_pallas,
    `Kimchi.Verifier.kimchiVesta_run_sound_algebraic_ft,
    `Kimchi.Verifier.kimchiPallas_run_sound_algebraic_ft ]

/-- The only axioms the roots may depend on: the standard logical axioms and
    `Lean.ofReduceBool`. The pasta package declares NO axioms — the group orders are
    unconditional (CompElliptic's fibre-bound argument) and the CM eigenvalue relations are
    THEOREMS (homomorphism + prime-order cyclicity + `native_decide` anchors at the
    generators). The `native_decide` witnesses are permitted separately by
    `isTrustedNativeDecide`. -/
def allowed : List Name :=
  [ `propext, `Classical.choice, `Quot.sound, `Lean.ofReduceBool,
    -- The declared Fiat-Shamir assumption: Poseidon-accepted runs admit de-blinded
    -- accepting transcript trees (`Kimchi/Verifier/Reflection.lean`). One per Pasta curve.
    `Bulletproof.poseidon_fiat_shamir_vesta, `Bulletproof.poseidon_fiat_shamir_pallas,
    -- The deployed-run Fiat–Shamir assumption, anchored on the warm reflected run
    -- (`Ipa.verifyFrom (runWarm) (runInput)`) rather than the cold `Ipa.verify`. One per curve;
    -- the residue-free ft opening (`ft_opening_of_reflected_*`) is stated over this.
    `Kimchi.Verifier.kimchi_fiat_shamir_vesta, `Kimchi.Verifier.kimchi_fiat_shamir_pallas,
 ]

/-- A trusted `native_decide` witness: CompElliptic's point counts, or pasta's two GLV
    eigenvalue anchors (`Pasta.{pallas,vesta}_lam_nsmul_Gpt`, `pasta/Pasta/Endo.lean`) —
    exactly those declarations, by name. Any other `native_decide` in our tree is still
    rejected. -/
def isTrustedNativeDecide (ax : Name) : Bool :=
  let s := ax.toString
  (s.splitOn "native_decide").length > 1 &&
    ("CompElliptic.".isPrefixOf s
      || "Pasta.pallas_lam_nsmul_Gpt.".isPrefixOf s
      || "Pasta.vesta_lam_nsmul_Gpt.".isPrefixOf s)

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
