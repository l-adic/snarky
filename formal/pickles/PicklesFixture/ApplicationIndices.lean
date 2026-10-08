import PicklesFixture.ApplicationRun

/-!
# Checked indices of reconstructed applications

Compile each reconstructed application's circuits once, compare them with the independent
dump, check them at their keys' index data (`checkApplication`'s check on the compilations in
hand), reporting every branch's and the wrap circuit's domain, masked rows and public rows,
then reject the same compilations at index data a key could not have supplied: a domain of
eight rows, two masked rows, the generator `1`, equal shifts, a zero endomorphism coefficient
and a zero Poseidon matrix. Every rejection must be the index stage, located at the circuit
whose data changed: the first branch takes the domain data, and the wrap circuit, whose gates
read both parameters, the gate data.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi Pickles Pickles.Application CompElliptic.Fields.Pasta

/-- A circuit's failure, for the report. -/
private def describe : CheckFailure → String
  | .scope (.outOfRange i v) => s!"scope: variable {v} at or above the counter, in constraint {i}"
  | .scope (.publicOutOfRange v) => s!"scope: public variable {v} at or above the counter"
  | .scope (.notWired i) => s!"scope: constraint {i} is not wired"
  | .scope (.reused i v) => s!"scope: unwired operand {v} of constraint {i} occurs again"
  | .index => "index: the constructor built no index"

/-- An application's failure, for the report. -/
private def located {D : Shape} : ApplicationFailure D → String
  | .step b f => s!"step {b.val}: {describe f}"
  | .wrap f => s!"wrap: {describe f}"

/-- Domain data a key could not have supplied, each one change from the given data. -/
private def domainCorruptions {F : Type} [Zero F] [One F] (d : IndexData F) :
    List (String × IndexData F) :=
  [ ("a domain of eight rows", { d with n := 8 }),
    ("two masked rows", { d with zkRows := 2 }),
    ("the generator 1", { d with omega := 1 }),
    ("equal shifts", { d with shifts := fun _ => 1 }) ]

/-- Gate data no field environment supplies, each one change from the given data. -/
private def gateCorruptions {F : Type} [Zero F] (d : IndexData F) :
    List (String × IndexData F) :=
  [ ("a zero endomorphism coefficient", { d with endoBase := 0 }),
    ("a zero Poseidon matrix", { d with mds := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ }) ]

/-- Require a check to fail where expected. -/
private def requireRejected {D : Shape} {α : Type} (name what : String)
    (expected : ApplicationFailure D → Bool) : Except (ApplicationFailure D) α → IO Unit
  | .error f =>
    if expected f then IO.println s!"✓ {name}: {what} rejected at the {located f}"
    else throw (IO.userError s!"{name}: {what} rejected elsewhere: {located f}")
  | .ok _ => throw (IO.userError s!"{name}: {what} was accepted")

/-- Compile an application's circuits once; compare them with the dump, check them at their
keys' index data, report the checked indices, then require each corruption of the data to be
rejected at its circuit. -/
def checkIndices (name : String) (A : ImportedApplication) (tag : Json) : IO Unit := do
  let C := A.assembled.circuits A.setup (fun _ => none)
  let t0 ← IO.monoMsNow
  let steps ← finSequence fun b => IO.lazyPure fun _ => canonicalStep C b
  let wrap ← IO.lazyPure fun _ => canonicalWrap C
  let t1 ← IO.monoMsNow
  compareCompilations C steps wrap name tag
  let t2 ← IO.monoMsNow
  let checked ← match ← IO.lazyPure fun _ =>
      checkApplicationAt C steps wrap (stepIndexData C) (wrapIndexData C) with
    | .error f => throw (IO.userError s!"{name}: {located f}")
    | .ok checked => pure checked
  let t3 ← IO.monoMsNow
  let I := checked.indices
  for b in List.finRange A.shape.branches do
    IO.println s!"✓ {name} step {b.val}: checked index on a domain of {I.stepSize b}, \
      {(I.step b).zkRows} masked rows, {(I.step b).publicCount} public rows"
  IO.println s!"✓ {name} wrap: checked index on a domain of {I.wrapSize}, {I.wrap.zkRows} \
    masked rows, {I.wrap.publicCount} public rows (compile {t1 - t0} ms, compare {t2 - t1} ms, \
    check {t3 - t2} ms)"
  (← IO.getStdout).flush
  let first : A.shape.Branch := ⟨0, A.shape.branches_pos⟩
  for (what, bad) in domainCorruptions (stepIndexData C first) do
    requireRejected name s!"step 0 at {what}" (fun | .step b .index => b.val = 0 | _ => false)
      (← IO.lazyPure fun _ => checkApplicationAt C steps wrap
        (fun b => if b.val = 0 then bad else stepIndexData C b) (wrapIndexData C))
  for (what, bad) in gateCorruptions (wrapIndexData C) do
    requireRejected name s!"the wrap circuit at {what}" (fun | .wrap .index => true | _ => false)
      (← IO.lazyPure fun _ => checkApplicationAt C steps wrap (stepIndexData C) bad)
  (← IO.getStdout).flush

end PicklesFixture.Application
