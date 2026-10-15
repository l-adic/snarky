import PicklesFixture.TerminalData
import PicklesFixture.Certification
import PicklesFixture.ApplicationFromShape
import PicklesFixture.Verdicts

/-!
Check terminal verification on cached real Step/Wrap proofs. Reconstruct and certify the selected
applications from their sidecars, rebuild the carried terminal data, and check both premises of
`terminal_requiredProofs` without running either circuit or supplying witness matrices.
`APPS` defaults to HeterogeneousPrevs; `PICKLES_DUMP_DIR` and `PICKLES_PROOF_CACHE_DIR` select
the existing sidecars and caches. Mutated scalar data, commitments and messages must be rejected.
-/

open Lean Snarky Snarky.Kimchi Pickles Pickles.Application PicklesFixture
open PicklesFixture.Application Bulletproof CompElliptic.Fields.Pasta
open Kimchi.Fixture Kimchi.Fixture.PS Kimchi.Verifier

private def rejectChecks {D : Shape} {C : Circuits D} (name : String) (d : TerminalData C) :
    IO Unit := do
  match d.check? with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{name}: altered terminal data passed Checks")

private def checkMutations {D : Shape} {C : Circuits D}
    (p : KimchiProof CW 1 WrapIPARounds) (d : TerminalData C) : IO Unit := do
  rejectChecks "deferred scalar"
    { d with deferred := { d.deferred with b := d.deferred.b + 1 } }
  rejectChecks "Step evaluations"
    { d with evals := { d.evals with ftEval1 := d.evals.ftEval1 + 1 } }
  rejectChecks "Step commitment"
    { d with message := { d.message with challengePolynomialCommitment := ⟨0, 0⟩ } }
  if h : 0 < D.width then
    let old := d.message.oldBulletproofChallenges[0]
    let altered : TerminalData C := { d with message := { d.message with
      oldBulletproofChallenges := d.message.oldBulletproofChallenges.set 0
        (old.set 0 (old[0] + 1)) } }
    let _ ← IO.ofExcept altered.check?
    unless !kimchiVerify CW C.setup.wrapSrs C.wiring.backend.wrapKey
        { p with olds := altered.wrapAccumulators.toArray }
        (CircuitType.valueToFields altered.statement).toArray do
      throw (IO.userError "altered Wrap accumulator challenges passed terminal verification")

private def checkProof {D : Shape} {C : Circuits D} (cert : ApplicationCertified C)
    (p : KimchiProof CW 1 WrapIPARounds) (d : TerminalData C) := show IO _ from do
  let ⟨checks⟩ ← IO.ofExcept d.check?
  let ⟨haccept⟩ ← requireProof
    (kimchiVerify CW C.setup.wrapSrs C.wiring.backend.wrapKey
      { p with olds := d.wrapAccumulators.toArray }
      (CircuitType.valueToFields d.statement).toArray = true)
    (IO.userError "final Wrap proof rejected with reconstructed terminal accumulators")
  return PLift.up (terminal_requiredProofs cert p d haccept checks)

private def checkApplicationProofs (name : String) (A : ImportedApplication)
    (wraps : Array (Cache.Entry CW)) (steps : Array (Cache.Entry CS)) : IO Unit := do
  let cert ← certifyApplication name A
  let C := A.assembled.circuits A.setup (fun _ => none)
  let mut count := 0
  for w in wraps.filter (·.vkDigest == toString C.wiring.backend.wrapKey.digest.val) do
    let some link := w.step | throw (IO.userError s!"{name}: Wrap proof has no Step reference")
    let some s := steps.find? (fun s => (s.vkDigest, s.publicInputKey) == link)
      | throw (IO.userError s!"{name}: no cached Step proof for final Wrap")
    let some b := (List.finRange A.shape.branches).find?
      (fun b => s.vkDigest == toString C.wiring.backend.stepKeys[b].digest.val)
      | throw (IO.userError s!"{name}: final Step key is not an application branch")
    let (_, p) ← IO.ofExcept (w.checkedAt WrapIPARounds 1)
    let d ← IO.ofExcept (terminalDataOf A b s w)
    unless (CircuitType.valueToFields d.statement).toArray == w.publicInput do
      throw (IO.userError s!"{name}: reconstructed terminal statement differs from cached input")
    unless d.wrapAccumulators.toArray.map (fun a => (a.sg, a.u)) ==
        p.olds.map (fun a => (a.sg, a.u)) do
      throw (IO.userError s!"{name}: reconstructed terminal accumulators differ from cached olds")
    let _ ← checkProof cert p d
    checkMutations p d
    count := count + 1
    IO.println s!"✓ {name}/{b.val}: terminal Checks, Wrap acceptance and required-proof theorem; \
      mutations rejected"
    (← IO.getStdout).flush
  unless count > 0 do throw (IO.userError s!"{name}: no terminal proofs checked")

def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let apps ← IO.ofExcept (Manifest.select ((← IO.getEnv "APPS").or (some "HeterogeneousPrevs")))
  let wrap ← srsAt CW "pallas" pallasBase.sqrt? (← IO.mkRef []) WrapIPARounds
  let step ← srsAt CS "vesta" vestaBase.sqrt? (← IO.mkRef []) StepIPARounds
  let cacheDir := (← IO.getEnv "PICKLES_PROOF_CACHE_DIR").getD
    "../packages/pickles/test/fixtures/proof-cache"
  loadApplications dir apps wrap step fun imported => do
    for app in apps do
      let raw ← IO.FS.readFile (System.FilePath.mk cacheDir / s!"{app.name}.json")
      let (wraps, _) ← IO.ofExcept (Cache.parseFile CW fqSide.endo pallasBase.sqrt? raw)
      let (steps, _) ← IO.ofExcept (Cache.parseFile CS fpSide.endo vestaBase.sqrt? raw)
      for (name, A) in imported.filter (fun (name, _) => name.startsWith (app.name ++ "/")) do
        checkApplicationProofs name A wraps steps
