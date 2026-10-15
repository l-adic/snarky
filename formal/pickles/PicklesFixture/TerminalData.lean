import PicklesFixture.ApplicationImport
import Pickles.Application.Terminal

/-!
# Terminal data from cached proofs

Recover the data carried alongside a final Wrap proof from the existing proof cache and rule
dump. No satisfying circuit execution is used: the cached Step proof supplies evaluations and
old challenges, the Wrap proof supplies its public statement and old accumulators, and the
recorded rule witness supplies the application statement.
-/

namespace PicklesFixture.Application

open Snarky Snarky.Kimchi Pickles Pickles.Application Bulletproof
open CompElliptic.Fields.Pasta Kimchi.Fixture Kimchi.Verifier

private def prechallengeOf (x : SizedF 128 Fp) : Except String (SizedF 128 Prechallenge) :=
  if h : x.val.val < 2 ^ 128 then .ok ⟨⟨x.val.val, h⟩⟩
  else .error "terminal prechallenge exceeds 128 bits"

private def deferredOf (d : DeferredValues StepIPARounds Fp (Type1 Fp)) :
    Except String (DeferredValues StepIPARounds Prechallenge Fp) := do
  let unshift (x : Type1 Fp) := Pasta.Shifted.unshiftType1 255 x.val
  return {
    plonk := {
      alpha := ← prechallengeOf d.plonk.alpha
      beta := ← prechallengeOf d.plonk.beta
      gamma := ← prechallengeOf d.plonk.gamma
      zeta := ← prechallengeOf d.plonk.zeta
      perm := unshift d.plonk.perm
      zetaToSrsLength := unshift d.plonk.zetaToSrsLength
      zetaToDomainSize := unshift d.plonk.zetaToDomainSize }
    combinedInnerProduct := unshift d.combinedInnerProduct
    xi := ← prechallengeOf d.xi
    bulletproofChallenges := ← d.bulletproofChallenges.mapM prechallengeOf
    b := unshift d.b }

/-- Decode terminal carried data from a cached Step/Wrap pair, without running either circuit.
The caller checks the reconstructed public statement and old accumulators against the cache. -/
def terminalDataOf (A : ImportedApplication) (b : A.shape.Branch)
    (S : Cache.Entry CS) (W : Cache.Entry CW) :
    Except String (TerminalData (A.assembled.circuits A.setup (fun _ ↦ none))) := do
  let D := A.shape
  let C := A.assembled.circuits A.setup (fun _ ↦ none)
  let (_, cpS) ← S.checkedAt StepIPARounds C.wiring.backend.stepChunks
  let (_, cpW) ← W.checkedAt WrapIPARounds 1
  unless cpS.olds.size = D.slots b do
    throw "terminal Step proof has the wrong number of old accumulators"
  unless cpW.olds.size = MaxProofsVerified do
    throw "terminal Wrap proof has the wrong number of old accumulators"
  let statement ← wrapStatementOf toStep StepIPARounds W.publicInput
  let packed ← wrapInputOf W
  let some witness := S.rule | throw "terminal Step proof has no rule witness"
  let rule := (A.assembled.rules b).dump
  unless witness.input.size = rule.inputSize && witness.values.size = rule.allocated do
    throw "terminal rule witness dimensions differ from the rule dump"
  let values := witness.input ++ witness.values
  let app := witness.input ++ rule.publicOutput.map (fun e ↦ e.val (values.getD · 0))
  let appState : Vector Fp D.schema.size ←
    if h : app.size = D.schema.size then pure ⟨app, h⟩
    else throw "terminal application statement has the wrong size"
  let width : Fin (D.width + 1) := ⟨D.slots b, Nat.lt_succ_of_le (D.slots_le_width b)⟩
  return {
    deferred := ← deferredOf statement.proofState.deferredValues.toDeferredValues
    spongeDigest := statement.proofState.spongeDigestBeforeEvaluations
    evals := ← chunkedEvalsOf CS cpS
    oldChallenges := ← lastPadded D.width (Vector.replicate StepIPARounds 0)
      (cpS.olds.map (·.u))
    width
    appState
    prevSgs := ← lastPadded width.val ⟨C.setup.dummySg.x, C.setup.dummySg.y⟩
      (cpW.olds.map fun a ↦ ⟨a.sg.x, a.sg.y⟩)
    message := {
      challengePolynomialCommitment := ⟨cpS.opening.sg.x, cpS.opening.sg.y⟩
      oldBulletproofChallenges := ← lastPadded D.width C.setup.dummy (cpW.olds.map (·.u)) }
    branchData := packed.branchData }

end PicklesFixture.Application
