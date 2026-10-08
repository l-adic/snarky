import PicklesFixture.ApplicationRun
import Pickles.Application.Imported

/-!
# Imported indices of reconstructed applications

Build each branch's and the wrap circuit's index from the independent circuit dump alone, at
the key's data the checked compilation uses (`PicklesFixture.Application.importIndices`): the
dump's rows laid out on the key's domain, and `Kimchi.Index.build?` at the key's masked rows,
generator, shifts and endomorphism coefficient and the environment's matrix. The dump is
validated before padding: equal gate array lengths, the public rows among the rows, the rows
before the masked ones, and in each row at most the coefficient columns (a shorter row is zero
beyond its entries, the reading kimchi gives it), seven wire targets inside the table and a
known gate type. Every failure is located at its circuit.

`PicklesFixture.Application.certifyAndCompare` is the path a reconstructed application's dumps
take: the imported indices certified against the checked application, a disagreement located
at its datum, and only then the compilations required to match the dumps datum by datum, the
evidence that also sees variable ids. The certificate's `CertifiedIndices.correct` is the
imported indices' Pickles-correctness. `PicklesFixture.Application.rejectCorruptedDump` sends
a dump with one coefficient changed down that path and requires exactly the located failure.
`PicklesFixture.Application.rejectImportedChanges` requires three changes to the imported side
alone to be rejected where they are, the checked application the same throughout: a
coefficient of the first branch's first row after the public rows, the first wire targets of
that row and the next exchanged, another permutation the constructor accepts, and the wrap
circuit's endomorphism coefficient.

`PicklesFixture.Application.rejectInvalidDumps` is the adapter's own behaviour on small dumps,
before any application: a wellformed dump builds, a wire target outside the table is refused,
and more rows than fit before the masked ones are refused.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi Pickles Pickles.Application PicklesFixture
open Bulletproof CompElliptic.Fields.Pasta Kimchi.Fixture Kimchi.Fixture.PS
open scoped Kimchi

/-! ## The adapter -/

/-- A dump's wire target as a cell of the table. -/
private def targetOf (n i : ℕ) (w : ℕ × ℕ) : Except String (Fin permCols × Fin n) :=
  if h : w.1 < 7 ∧ w.2 < n then pure (⟨w.1, h.1⟩, ⟨w.2, h.2⟩)
  else throw s!"row {i}: wire target ({w.1}, {w.2}) outside the table"

/-- A dump row as a gate row: its type, its coefficients zero beyond the dumped ones and at
most the columns, its seven wire targets. -/
private def rowOf {F : Type} [Zero F] (n : ℕ) (raw : Raw F) (i : ℕ) :
    Except String (Kimchi.Index.GateRow F n) := do
  let some typ := raw.typs[i]? | throw s!"row {i}: no gate type"
  let some coeffs := raw.coeffs[i]? | throw s!"row {i}: no coefficients"
  let some wires := raw.wires[i]? | throw s!"row {i}: no wires"
  unless coeffs.size ≤ 15 do throw s!"row {i}: {coeffs.size} coefficients, 15 columns"
  let ws ← wires.mapM (targetOf n i)
  if h : ws.size = 7 then
    return { typ := typ, coeffs := fun c => coeffs.getD (c : ℕ) 0,
             wires := fun c => ws[(c : ℕ)]'(by omega) }
  else throw s!"row {i}: {ws.size} wire targets, 7 expected"

/-- The table over the converted rows: the array's row where there is one, a zero gate wired
to itself beyond. Never inlined, so that the array is a value the function captures and not
a computation every read repeats. -/
@[noinline] private def tableOver {F : Type} [Zero F] {n : ℕ}
    (arr : Array (Kimchi.Index.GateRow F n)) : Fin n → Kimchi.Index.GateRow F n :=
  fun i => if h : i.val < arr.size then arr[i.val]
    else { typ := .zero, coeffs := fun _ => 0, wires := fun c => (c, i) }

/-- A dump's index at a key's data: the dump validated and each row converted, laid out on
the key's domain, and `Kimchi.Index.build?` at the key's masked rows, generator, shifts and
endomorphism coefficient and the environment's matrix. -/
def importIndex {p : ℕ} [Fact p.Prime] (raw : Raw (ZMod p)) (d : IndexData (ZMod p)) :
    Except String (Kimchi.Index (ZMod p) d.n) := do
  let rows := raw.typs.size
  unless raw.coeffs.size = rows ∧ raw.wires.size = rows do
    throw s!"gate arrays of {rows}, {raw.coeffs.size} and {raw.wires.size} rows"
  unless raw.publicInputSize ≤ rows do
    throw s!"{raw.publicInputSize} public rows among {rows} rows"
  unless rows + d.zkRows ≤ d.n do
    throw s!"{rows} rows and {d.zkRows} masked rows on a domain of {d.n}"
  let arr ← (Array.range rows).mapM (rowOf d.n raw)
  match Kimchi.Index.build? (tableOver arr) raw.publicInputSize d.zkRows d.omega d.endoBase
      d.mds d.shifts with
  | none => throw "the index constructor rejected the dump at the key's data"
  | some idx => return idx

/-- Every branch's and the wrap circuit's index from the dumps at the data, each branch's
public rows required to be its statement's fields, as the wrap circuit's; a failure is
located at its circuit. -/
def importIndicesWith {D : Shape} (stepDump : D.Branch → Raw Fp) (wrapDump : Raw Fq)
    (stepData : D.Branch → IndexData Fp) (wrapData : IndexData Fq) :
    Except String (ApplicationIndices D) := do
  let step ← finSequence (β := fun b => Kimchi.Index Fp (stepData b).n) fun b =>
    (importIndex (stepDump b) (stepData b)).mapError (s!"step {b.val}: " ++ ·)
  let wrap ← (importIndex wrapDump wrapData).mapError ("wrap: " ++ ·)
  let stepFields := CircuitType.size Fp (StepPublic D)
  let wrapFields := CircuitType.size Fq WrapPublic
  if hs : ∀ b, (step b).publicCount = stepFields then
    if hw : wrap.publicCount = wrapFields then
      return { stepSize := fun b => (stepData b).n, step := step, wrapSize := wrapData.n,
               wrap := wrap, stepPublicCount := hs, wrapPublicCount := hw }
    else throw s!"wrap: {wrap.publicCount} public rows, {wrapFields} statement fields"
  else
    match (List.finRange D.branches).find? fun b => (step b).publicCount != stepFields with
    | some b =>
      throw s!"step {b.val}: {(step b).publicCount} public rows, {stepFields} statement fields"
    | none => throw "a branch's public rows are not its statement's fields"

/-- An application's imported indices: every branch's and the wrap circuit's dump at its
key's data. -/
def importIndices {D : Shape} {L : Layout D} (C : Circuits D L) (stepDump : D.Branch → Raw Fp)
    (wrapDump : Raw Fq) : Except String (ApplicationIndices D) :=
  importIndicesWith stepDump wrapDump (stepIndexData C) (wrapIndexData C)

/-! ## Certification and its rejections -/

/-- A datum of an index, for the report. -/
private def describeIndex : Kimchi.Index.IndexDiff → String
  | .publicCount => "the public count"
  | .zkRows => "the masked-row count"
  | .omega => "the generator"
  | .endoBase => "the endomorphism coefficient"
  | .mds => "the matrix"
  | .shifts c => s!"shift {c.val}"
  | .typ i => s!"row {i}, the gate type"
  | .coeff i c => s!"row {i}, coefficient {c.val}"
  | .wire i c => s!"row {i}, wire {c.val}"

/-- A disagreement, located. -/
private def describe {D : Shape} : IndicesDiff D → String
  | .step (.size b) => s!"step {b.val}: the domain size"
  | .step (.member b d) => s!"step {b.val}: {describeIndex d}"
  | .wrapSize => "wrap: the domain size"
  | .wrap d => s!"wrap: {describeIndex d}"

/-- Require certification of imported indices to fail where expected. -/
private def requireDiff {D : Shape} {L : Layout D} {C : Circuits D L} (name what : String)
    (checked : CheckedApplication C) (imported : Except String (ApplicationIndices D))
    (expected : IndicesDiff D → Bool) : IO Unit := do
  let imported ← match imported with
    | .error e => throw (IO.userError s!"{name}: {what} was refused by the import: {e}")
    | .ok i => pure i
  match certifyIndices? checked imported with
  | .error d =>
    if expected d then IO.println s!"✓ {name}: {what} rejected at {describe d}"
    else throw (IO.userError s!"{name}: {what} rejected elsewhere: {describe d}")
  | .ok _ => throw (IO.userError s!"{name}: {what} was certified")

/-- The dump with the first coefficient of row `r` changed. -/
private def coefficientChanged (raw : Raw Fp) (r : ℕ) : Raw Fp :=
  { raw with coeffs := raw.coeffs.modify r fun cs =>
      if cs.isEmpty then #[1] else cs.modify 0 (· + 1) }

/-- The dump with the first wire targets of rows `r` and `r + 1` exchanged: another
permutation of the same cells. -/
private def wiresExchanged (raw : Raw Fp) (r : ℕ) : Raw Fp :=
  let a := (raw.wires.getD r #[]).getD 0 (0, 0)
  let b := (raw.wires.getD (r + 1) #[]).getD 0 (0, 0)
  let wires := raw.wires.modify r (·.modify 0 fun _ => b)
  { raw with wires := wires.modify (r + 1) (·.modify 0 fun _ => a) }

/-- Import an application's indices from its dumps at the keys' data and certify them against
the checked application, a disagreement located at its datum; the certificate's correctness
is read as the theorem states it. -/
def certifyImported {D : Shape} {L : Layout D} (name : String) (C : Circuits D L)
    (checked : CheckedApplication C) (stepDump : D.Branch → Raw Fp) (wrapDump : Raw Fq) :
    IO (CertifiedIndices C) := do
  let t0 ← IO.monoMsNow
  let imported ← match ← IO.lazyPure fun _ => importIndices C stepDump wrapDump with
    | .error e => throw (IO.userError s!"{name}: import: {e}")
    | .ok i => pure i
  let t1 ← IO.monoMsNow
  let cert ← match ← IO.lazyPure fun _ => certifyIndices? checked imported with
    | .error d => throw (IO.userError s!"{name}: the imported indices differ at {describe d}")
    | .ok cert => pure cert
  let t2 ← IO.monoMsNow
  let _correct : PicklesCorrect C cert.indices := cert.correct
  IO.println s!"✓ {name}: imported indices certified against the checked application \
    (import {t1 - t0} ms, compare {t2 - t1} ms)"
  (← IO.getStdout).flush
  return cert

/-- The dumps' path: the imported indices certified against the checked application first,
then the compilations in hand required to match the dumps datum by datum. -/
def certifyAndCompare {D : Shape} {L : Layout D} (name : String) (C : Circuits D L)
    (steps : (b : D.Branch) → StepCompilation C b) (wrap : WrapCompilation C)
    (checked : CheckedApplication C) (stepDump : D.Branch → Raw Fp) (wrapDump : Raw Fq) :
    IO (CertifiedIndices C) := do
  let cert ← certifyImported name C checked stepDump wrapDump
  compareCompilations C steps wrap name stepDump wrapDump
  return cert

/-- The first branch's dump, and its first row after the public rows, which must exist with
the next. -/
private def firstDump {D : Shape} (name : String) (stepDump : D.Branch → Raw Fp) :
    IO (Raw Fp × ℕ) := do
  let raw := stepDump ⟨0, D.branches_pos⟩
  let r := raw.publicInputSize
  unless r + 1 < raw.typs.size do
    throw (IO.userError s!"{name}: too few rows after the public rows for the rejections")
  return (raw, r)

/-- A dump with one coefficient changed, sent down the dumps' path: the failure is exactly
the located one. -/
def rejectCorruptedDump {D : Shape} {L : Layout D} (name : String) (C : Circuits D L)
    (steps : (b : D.Branch) → StepCompilation C b) (wrap : WrapCompilation C)
    (checked : CheckedApplication C) (stepDump : D.Branch → Raw Fp) (wrapDump : Raw Fq) :
    IO Unit := do
  let (raw, r) ← firstDump name stepDump
  let corrupted (b : D.Branch) : Raw Fp :=
    if b.val = 0 then coefficientChanged raw r else stepDump b
  let expected := s!"{name}: the imported indices differ at step 0: row {r}, coefficient 0"
  match ← (certifyAndCompare name C steps wrap checked corrupted wrapDump).toBaseIO with
  | .ok _ => throw (IO.userError s!"{name}: a corrupted dump passed the dumps' path")
  | .error e =>
    if toString e = expected then
      IO.println s!"✓ {name}: a corrupted dump fails the dumps' path at step 0 row {r}, \
        coefficient 0"
    else throw (IO.userError s!"{name}: a corrupted dump failed the dumps' path elsewhere: {e}")

/-- Require each change to the imported side alone to be rejected where it is: a coefficient
of the first branch's first row after the public rows, the first wire targets of that row and
the next exchanged, and the wrap circuit's endomorphism coefficient. -/
def rejectImportedChanges {D : Shape} {L : Layout D} (name : String) (C : Circuits D L)
    (checked : CheckedApplication C) (stepDump : D.Branch → Raw Fp) (wrapDump : Raw Fq) :
    IO Unit := do
  let (raw, r) ← firstDump name stepDump
  let stepDumpWith (bad : Raw Fp) (b : D.Branch) : Raw Fp := if b.val = 0 then bad else stepDump b
  requireDiff name s!"a coefficient of step 0 row {r}" checked
    (importIndicesWith (stepDumpWith (coefficientChanged raw r)) wrapDump (stepIndexData C)
      (wrapIndexData C))
    (fun | .step (.member b (.coeff i c)) => b.val == 0 && i == r && c.val == 0 | _ => false)
  requireDiff name s!"the first wire targets of step 0 rows {r} and {r + 1} exchanged" checked
    (importIndicesWith (stepDumpWith (wiresExchanged raw r)) wrapDump (stepIndexData C)
      (wrapIndexData C))
    (fun | .step (.member b (.wire i c)) => b.val == 0 && i == r && c.val == 0 | _ => false)
  requireDiff name "the wrap circuit's endomorphism coefficient" checked
    (importIndicesWith stepDump wrapDump (stepIndexData C)
      { wrapIndexData C with endoBase := (wrapIndexData C).endoBase + 1 })
    (fun | .wrap .endoBase => true | _ => false)
  (← IO.getStdout).flush

/-! ## The adapter on small dumps -/

/-- Index data of a domain of eight with three masked rows, the generator and shifts the
dump adapter synthesizes. -/
private def smallData : IndexData Fp :=
  { n := 8, zkRows := 3, omega := fpSide.omega 8,
    shifts := fun i => (fpSide.generator : Fp) ^ (i : ℕ), endoBase := 0,
    mds := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ }

/-- A dump of `rows` zero gates wired to themselves, no public rows. -/
private def zeroRows (rows : ℕ) : Raw Fp :=
  { publicInputSize := 0, typs := Array.replicate rows .zero,
    coeffs := Array.replicate rows #[],
    wires := (Array.range rows).map fun i => (Array.range 7).map fun c => (c, i),
    vars := #[], witness := #[], pub := #[] }

/-- A one-row dump, a public generic row, whose last wire target is the row `target`. -/
private def oneRow (target : ℕ) : Raw Fp :=
  { publicInputSize := 1, typs := #[.generic], coeffs := #[#[1]],
    wires := #[#[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, target)]],
    vars := #[], witness := #[], pub := #[] }

/-- The adapter on small dumps at a domain of eight: five zero rows build, a wire target
outside the table is refused by the adapter, and six rows, more than fit before the masked
ones, are refused by it. -/
def rejectInvalidDumps : IO Unit := do
  let require (what : String) (r : Except String (Kimchi.Index Fp smallData.n))
      (expected : String) : IO Unit :=
    match r with
    | .error e =>
      if e.startsWith expected then IO.println s!"✓ adapter: {what} refused: {e}"
      else throw (IO.userError s!"adapter: {what} refused elsewhere: {e}")
    | .ok _ => throw (IO.userError s!"adapter: {what} accepted")
  match importIndex (zeroRows 5) smallData with
  | .error e => throw (IO.userError s!"adapter: five zero rows refused: {e}")
  | .ok _ => IO.println s!"✓ adapter: five zero rows build an index on a domain of {smallData.n}"
  require "a wire target outside the table" (importIndex (oneRow 8) smallData)
    "row 0: wire target"
  require "six rows on a domain of eight with three masked" (importIndex (zeroRows 6) smallData)
    "6 rows and 3 masked rows"

end PicklesFixture.Application
