import PicklesFixture.ImportedIndices
import PicklesFixture.KeyChecks
import Pickles.Application.MatrixRun

/-!
# Checked indices of reconstructed applications

Compile each reconstructed application's circuits once and check them at their keys' index
data (`checkApplication`'s check on the compilations in hand), reporting every branch's and
the wrap circuit's domain, masked rows and public rows. Then the dumps' path: the indices
imported from the independent dump certified against the checked application, a disagreement
located at its datum, before the compilations are required to match the dump datum by datum.
A dump corrupted before that path must fail at its datum, and each change to the imported
side alone must be rejected where it is. Then reject the same compilations at index data a
key could not have supplied: a domain of eight rows, two masked rows, the generator `1`,
equal shifts, a zero endomorphism coefficient and a zero Poseidon matrix. Every rejection
must be the index stage, located at the circuit whose data changed: the first branch takes
the domain data, and the wrap circuit, whose gates read both parameters, the gate data.

Then, from the application's cached proofs, construct the tables the lifting theorems take
(`PicklesFixture.Application.checkTables`): each cached execution's rendered witness rows laid
out on the checked index's domain, its public values, required to be the cached proof's, read
as the typed statement, and the checked index's acceptance of the table at that statement
decided. The cached prover is
evidence that such tables exist; it is a premise of nothing.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi Pickles Pickles.Application PicklesFixture
open Bulletproof CompElliptic.Fields.Pasta Kimchi.Fixture Kimchi.Fixture.PS
open scoped Kimchi

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

/-- Send an application down the certification path, then require the compilations to match
the dumps datum by datum, a corrupted dump to fail at its datum, each change to the imported
side to be rejected where it is, and each corruption of the key data to be rejected at its
circuit. One compilation per circuit and one parse per dump. -/
def checkIndices (name : String) (A : ImportedApplication) (tag : Json) :
    IO (CheckedApplication (A.assembled.circuits A.setup (fun _ => none))) := do
  let C := A.assembled.circuits A.setup (fun _ => none)
  let r ← certifyApplication name A tag
  if name == "NoRecursionReturn/nrr" then rejectWrongKeys name A r
  compareCompilations C r.steps r.wrap name r.stepDump r.wrapDump
  rejectCorruptedDump name C r.steps r.wrap r.checked r.stepDump r.wrapDump
  rejectImportedChanges name C r.checked r.stepDump r.wrapDump
  let first : A.shape.Branch := ⟨0, A.shape.branches_pos⟩
  for (what, bad) in domainCorruptions (stepIndexData C first) do
    requireRejected name s!"step 0 at {what}" (fun | .step b .index => b.val = 0 | _ => false)
      (← IO.lazyPure fun _ => checkApplicationAt C r.steps r.wrap
        (fun b => if b.val = 0 then bad else stepIndexData C b) (wrapIndexData C))
  for (what, bad) in gateCorruptions (wrapIndexData C) do
    requireRejected name s!"the wrap circuit at {what}" (fun | .wrap .index => true | _ => false)
      (← IO.lazyPure fun _ => checkApplicationAt C r.steps r.wrap (stepIndexData C) bad)
  (← IO.getStdout).flush
  return r.checked

/-! ## Tables from cached executions -/

/-- A cached execution's rendered rows laid out on a domain, zero beyond them. -/
private def tableOn {p : ℕ} (n : ℕ) (rows : Array (Vector (ZMod p) 15)) :
    Fin n → Fin wCols → ZMod p :=
  fun i j => ((rows[i.val]?).map (·[j])).getD 0

/-- A cached execution's public values as the typed statement they encode. -/
private def statementOf {p : ℕ} [Fact p.Prime] (val var : Type) [CircuitType (ZMod p) val var]
    (name : String) (pub : List (ZMod p)) : IO val := do
  if h : pub.length = CircuitType.size (ZMod p) val then
    return CircuitType.fieldsToValue (F := ZMod p) ⟨⟨pub⟩, h⟩
  else throw (IO.userError s!"{name}: {pub.length} public values, the statement has \
    {CircuitType.size (ZMod p) val} fields")

private def cacheKey {C : Ipa.KimchiCurve} (e : Cache.Entry C) :=
  (e.vkDigest, e.publicInputKey)

/-- From the application's cached proofs, construct a `StepTable` and a `WrapTable` against the
checked indices for every cached step execution and the wrap execution wrapping it: the rows
on the checked domain, the public values as the typed statement, acceptance decided. -/
def checkTables (name : String) (A : ImportedApplication)
    (checked : CheckedApplication (A.assembled.circuits A.setup (fun _ => none)))
    (cacheDir : System.FilePath) : IO Unit := do
  let app := (name.splitOn "/").head!
  let raw ← IO.FS.readFile (cacheDir / s!"{app}.json")
  let (wraps, _) ← IO.ofExcept (Cache.parseFile CW fqSide.endo pallasBase.sqrt? raw)
  let (steps, _) ← IO.ofExcept (Cache.parseFile CS fpSide.endo vestaBase.sqrt? raw)
  let (run, _) ← runner A.setup A app name
  let I := checked.indices
  let mut built := 0
  for b in List.finRange A.shape.branches do
    let vk := A.assembled.wiring.backend.stepKeys[b].cvk
    for p in steps.filter (·.vkDigest == toString vk.digest.val) do
      let prevs ← IO.ofExcept (stepPrevsOf (A.shape.slots b) wraps steps p)
      let r ← run.step b.val p prevs.toArray
      unless r.pub == p.publicInput.toList do
        throw (IO.userError s!"{name}/{b.val} step: the public values differ from the cached \
          proof's")
      unless r.rows.size ≤ I.stepSize b do
        throw (IO.userError s!"{name}/{b.val} step: {r.rows.size} rows on a domain of \
          {I.stepSize b}")
      let statement ← statementOf (StepPublic A.shape) _ s!"{name}/{b.val} step" r.pub
      let table := tableOn (I.stepSize b) r.rows
      if h : (I.step b).SatisfiesVec (CircuitType.valueToFields statement)
          (I.stepPublicCount b) table then
        let _ : StepTable I b := ⟨statement, table, h⟩
        IO.println s!"✓ {name}/{b.val} step: a StepTable against the checked index at the \
          cached proof's statement, {r.rows.size} rows on a domain of {I.stepSize b}"
      else throw (IO.userError s!"{name}/{b.val} step: the checked index rejects the cached \
        execution's table at its statement")
      let wrappers := wraps.filter (·.step == some (cacheKey p))
      let some q := wrappers[0]? | throw (IO.userError s!"{name}/{b.val}: no cached wrap")
      let r ← run.wrap b.val p q prevs.toArray
      unless r.pub == q.publicInput.toList do
        throw (IO.userError s!"{name}/{b.val} wrap: the public values differ from the cached \
          proof's")
      unless r.rows.size ≤ I.wrapSize do
        throw (IO.userError s!"{name}/{b.val} wrap: {r.rows.size} rows on a domain of \
          {I.wrapSize}")
      let statement ← statementOf WrapPublic _ s!"{name}/{b.val} wrap" r.pub
      let table := tableOn I.wrapSize r.rows
      if h : I.wrap.SatisfiesVec (CircuitType.valueToFields statement) I.wrapPublicCount table
          then
        let _ : WrapTable I := ⟨statement, table, h⟩
        IO.println s!"✓ {name}/{b.val} wrap: a WrapTable against the checked index at the \
          cached proof's statement, {r.rows.size} rows on a domain of {I.wrapSize}"
      else throw (IO.userError s!"{name}/{b.val} wrap: the checked index rejects the cached \
        execution's table at its statement")
      built := built + 2
  unless built > 0 do throw (IO.userError s!"{name}: no cached executions")
  (← IO.getStdout).flush

end PicklesFixture.Application
