import PicklesFixture.ApplicationImport
import Pickles.Application.CheckedCompile

/-!
# Certification of reconstructed applications

Compile each reconstructed application's circuits once and certify the supplied keys against
those Lean indices and the shared SRSs. The result is `ApplicationCertified`; independent
constraint-system dumps and proof caches are not inputs to this operation.
-/

namespace PicklesFixture.Application

open Snarky.Kimchi Pickles Pickles.Application

/-- A circuit's check failure, for the report. -/
private def describeCheck : CheckFailure → String
  | .scope (.outOfRange i v) => s!"scope: variable {v} at or above the counter, in constraint {i}"
  | .scope (.publicOutOfRange v) => s!"scope: public variable {v} at or above the counter"
  | .scope (.notWired i) => s!"scope: constraint {i} is not wired"
  | .scope (.reused i v) => s!"scope: unwired operand {v} of constraint {i} occurs again"
  | .index => "index: the constructor built no index"

/-- An application's check failure, located at its circuit. -/
def located {D : Shape} : ApplicationFailure D → String
  | .step b f => s!"step {b.val}: {describeCheck f}"
  | .wrap f => s!"wrap: {describeCheck f}"
  | .stepKey b f => s!"key: step {b.val}: {f.describe}"
  | .wrapKey f => s!"key: wrap: {f.describe}"

/-- Certify the reconstructed circuits and their supplied keys, without foreign circuit dumps.
Each circuit is compiled once; a failure is located at its stage and circuit. -/
def certifyApplication (name : String) (A : ImportedApplication) :
    IO (ApplicationCertified (A.assembled.circuits A.setup (fun _ => none))) := do
  let C := A.assembled.circuits A.setup (fun _ => none)
  let t0 ← IO.monoMsNow
  let steps ← finSequence fun b => IO.lazyPure fun _ => canonicalStep C b
  let wrap ← IO.lazyPure fun _ => canonicalWrap C
  let t1 ← IO.monoMsNow
  let cert ← match ← IO.lazyPure fun _ => checkApplicationWith C steps wrap with
    | .error f => throw (IO.userError s!"{name}: {located f}")
    | .ok cert => pure cert
  let t2 ← IO.monoMsNow
  let I := cert.indices
  for b in List.finRange A.shape.branches do
    IO.println s!"✓ {name} step {b.val}: checked index on a domain of {I.stepSize b}, \
      {(I.step b).zkRows} masked rows, {(I.step b).publicCount} public rows"
  IO.println s!"✓ {name} wrap: checked index on a domain of {I.wrapSize}, {I.wrap.zkRows} \
    masked rows, {I.wrap.publicCount} public rows (compile {t1 - t0} ms, check {t2 - t1} ms)"
  IO.println s!"✓ {name}: all step and wrap keys derived from the Lean indices and SRSs"
  (← IO.getStdout).flush
  return cert

end PicklesFixture.Application
