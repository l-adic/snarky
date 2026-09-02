import Pickles.Linearization.Types
import Lean.Data.Json

/-!
# Decoding linearization token streams

The JSON decoder for kimchi's compiled linearization, reading
`packages/pickles-codegen/rust/output/{pallas,vesta}_scalar_field.json` — the Rust dump
that is the SOURCE OF TRUTH for the token stream. The PureScript modules
`Pickles.Linearization.{Pallas,Vesta}` are generated from the same files by
`pickles-codegen`'s `Generator.purs`, so this decoder and those modules are independent
transcriptions of one origin: neither is derived from the other, and a disagreement is
detectable rather than shared.

This library sits BESIDE the `Pickles` tree rather than inside it, matching `KimchiFixture`
(kimchi), `FixtureKit` (poseidon) and `BulletproofFixture` (bulletproof-pcs): checking
against recorded data is not part of the development, so the proof library never depends on
a decoder. Scripts import it directly.

Imports are deliberately narrow — `Lean.Data.Json` and the token alphabet, nothing more.
`FixtureKit.Parse` is NOT used: its decoders are parameterised over field elements and pull
in Mathlib and CompElliptic, which a token decoder has no use for.

## The wire encoding

Nullary tokens are bare strings; everything else is a single-key object. `SkipIf` and
`SkipIfNot` carry a two-element `[flag, count]` array. The shapes below are the complete
set observed across both deployed streams:

* `"Add" | "Mul" | "Sub" | "Dup" | "Store" | "VanishesOnZeroKnowledgeAndPreviousRows"`
* `{"Constant": "EndoCoefficient" | {"Mds": {…}} | {"Literal": "0x…"}}`
* `{"Challenge": "Alpha" | "Beta" | "Gamma" | "JointCombiner"}`
* `{"Cell": {"col": …, "row": "Curr" | "Next"}}`
* `{"Pow": n}`, `{"Load": n}`
* `{"UnnormalizedLagrangeBasis": {"zk_rows": bool, "offset": int}}` — offset is SIGNED
* `{"SkipIf": [flag, n]}`, `{"SkipIfNot": [flag, n]}`

Unknown tags are rejected rather than dropped. That is stricter than `FixtureKit.Parse`'s
documented hygiene (which drops unknown keys), and deliberately so: a token this decoder
does not understand is a token the interpreter cannot execute, so silently discarding one
would change the program rather than merely widen the input.
-/

namespace Pickles.Fixture

open Lean Pickles.Linearization

/-! ## Small helpers -/

/-- `some v` when `j` is an object carrying key `k`, `none` otherwise. The probe used to
discriminate the single-key object encodings. -/
private def field? (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

/-- The value of a hexadecimal digit. -/
private def hexDigit? (c : Char) : Option Nat :=
  let v := c.toNat
  if 0x30 ≤ v && v ≤ 0x39 then some (v - 0x30)          -- '0'..'9'
  else if 0x61 ≤ v && v ≤ 0x66 then some (v - 0x61 + 10) -- 'a'..'f'
  else if 0x41 ≤ v && v ≤ 0x46 then some (v - 0x41 + 10) -- 'A'..'F'
  else none

/-- One step of the hex fold. An `'x'`/`'X'` RESETS the accumulator, which is how the
leading `"0"` of a `"0x…"` prefix is discarded without a prefix test (`String.startsWith`
lives on `Slice`, not `String`, in this toolchain). The tolerance this buys — a stray `x`
mid-numeral restarts the parse — is harmless here: the input is Rust-generated, and a
misread literal cannot survive the `constant_term` agreement the fixture driver checks. -/
private def hexStep (acc : Except String Nat) (c : Char) : Except String Nat :=
  match acc with
  | .error e => .error e
  | .ok n =>
    if c.toNat = 0x78 || c.toNat = 0x58 then .ok 0
    else match hexDigit? c with
      | some d => .ok (n * 16 + d)
      | none => .error s!"not a hex digit: '{c}'"

/-- A `"0x…"` literal as a natural number. Rejects an empty numeral and any non-hex
character. The deployed streams reach 46 hex digits, so the result is genuinely big. -/
private def parseHexNat (s : String) : Except String Nat :=
  if s.isEmpty then .error "empty hex literal"
  else s.foldl hexStep (.ok 0)

/-! ## The leaf enumerations -/

/-- `"Curr" | "Next"`. -/
private def parseCurrOrNext (j : Json) : Except String CurrOrNext := do
  match ← j.getStr? with
  | "Curr" => return .curr
  | "Next" => return .next
  | s => throw s!"unknown CurrOrNext: {s}"

/-- A gate name, as an `Index` column's payload. -/
private def parseGateType (j : Json) : Except String GateType := do
  match ← j.getStr? with
  | "Generic" => return .generic
  | "Poseidon" => return .poseidon
  | "CompleteAdd" => return .completeAdd
  | "VarBaseMul" => return .varBaseMul
  | "EndoMul" => return .endoMul
  | "EndoMulScalar" => return .endoMulScalar
  | "RangeCheck0" => return .rangeCheck0
  | "RangeCheck1" => return .rangeCheck1
  | "ForeignFieldAdd" => return .foreignFieldAdd
  | "ForeignFieldMul" => return .foreignFieldMul
  | "Xor16" => return .xor16
  | "Rot64" => return .rot64
  | s => throw s!"unknown GateType: {s}"

/-- A lookup family name. -/
private def parseLookupPattern (j : Json) : Except String LookupPattern := do
  match ← j.getStr? with
  | "Lookup" => return .lookup
  | "Xor" => return .xor
  | "RangeCheck" => return .rangeCheck
  | "ForeignFieldMul" => return .foreignFieldMul
  | s => throw s!"unknown LookupPattern: {s}"

/-- A challenge name. -/
private def parseChallengeTerm (j : Json) : Except String ChallengeTerm := do
  match ← j.getStr? with
  | "Alpha" => return .alpha
  | "Beta" => return .beta
  | "Gamma" => return .gamma
  | "JointCombiner" => return .jointCombiner
  | s => throw s!"unknown ChallengeTerm: {s}"

/-! ## The tagged unions -/

/-- A column reference: four bare tags, five single-key objects. -/
private def parseColumn (j : Json) : Except String Column := do
  if let .ok s := j.getStr? then
    match s with
    | "LookupAggreg" => return .lookupAggreg
    | "LookupTable" => return .lookupTable
    | "LookupRuntimeTable" => return .lookupRuntimeTable
    | "LookupRuntimeSelector" => return .lookupRuntimeSelector
    | _ => throw s!"unknown Column tag: {s}"
  if let some v := field? j "Witness" then return .witness (← v.getNat?)
  if let some v := field? j "Coefficient" then return .coefficient (← v.getNat?)
  if let some v := field? j "Index" then return .index (← parseGateType v)
  if let some v := field? j "LookupSorted" then return .lookupSorted (← v.getNat?)
  if let some v := field? j "LookupKindIndex" then return .lookupKindIndex (← parseLookupPattern v)
  throw s!"unrecognised Column: {j.compress}"

/-- A constant: the bare `EndoCoefficient` tag, an MDS entry, or a hex literal. -/
private def parseConstantTerm (j : Json) : Except String ConstantTerm := do
  if let .ok s := j.getStr? then
    match s with
    | "EndoCoefficient" => return .endoCoefficient
    | _ => throw s!"unknown ConstantTerm tag: {s}"
  if let some v := field? j "Mds" then
    return .mds (← (← v.getObjVal? "row").getNat?) (← (← v.getObjVal? "col").getNat?)
  if let some v := field? j "Literal" then return .literal (← parseHexNat (← v.getStr?))
  throw s!"unrecognised ConstantTerm: {j.compress}"

/-- A feature predicate: eight bare tags, three single-key objects. -/
private def parseFeatureFlag (j : Json) : Except String FeatureFlag := do
  if let .ok s := j.getStr? then
    match s with
    | "RangeCheck0" => return .rangeCheck0
    | "RangeCheck1" => return .rangeCheck1
    | "ForeignFieldAdd" => return .foreignFieldAdd
    | "ForeignFieldMul" => return .foreignFieldMul
    | "Xor" => return .xor
    | "Rot" => return .rot
    | "LookupTables" => return .lookupTables
    | "RuntimeLookupTables" => return .runtimeLookupTables
    | _ => throw s!"unknown FeatureFlag tag: {s}"
  if let some v := field? j "LookupPattern" then return .lookupPattern (← parseLookupPattern v)
  if let some v := field? j "TableWidth" then return .tableWidth (← v.getNat?)
  if let some v := field? j "LookupsPerRow" then return .lookupsPerRow (← v.getNat?)
  throw s!"unrecognised FeatureFlag: {j.compress}"

/-- The `[flag, count]` payload shared by `SkipIf` and `SkipIfNot`. -/
private def parseGuard (j : Json) : Except String (FeatureFlag × Nat) := do
  let a ← j.getArr?
  match a[0]?, a[1]? with
  | some fj, some nj => return (← parseFeatureFlag fj, ← nj.getNat?)
  | _, _ => throw s!"expected a [flag, count] pair, got {a.size} entries"

/-! ## Tokens and streams -/

/-- One token. Nullary tokens arrive as bare strings, the rest as single-key objects. -/
private def parseToken (j : Json) : Except String PolishToken := do
  if let .ok s := j.getStr? then
    match s with
    | "Add" => return .add
    | "Mul" => return .mul
    | "Sub" => return .sub
    | "Dup" => return .dup
    | "Store" => return .store
    | "VanishesOnZeroKnowledgeAndPreviousRows" =>
      return .vanishesOnZeroKnowledgeAndPreviousRows
    | _ => throw s!"unknown nullary PolishToken: {s}"
  if let some v := field? j "Constant" then return .constant (← parseConstantTerm v)
  if let some v := field? j "Challenge" then return .challenge (← parseChallengeTerm v)
  if let some v := field? j "Cell" then
    return .cell (← parseColumn (← v.getObjVal? "col")) (← parseCurrOrNext (← v.getObjVal? "row"))
  if let some v := field? j "Pow" then return .pow (← v.getNat?)
  if let some v := field? j "Load" then return .load (← v.getNat?)
  if let some v := field? j "UnnormalizedLagrangeBasis" then
    return .unnormalizedLagrangeBasis (← (← v.getObjVal? "zk_rows").getBool?)
      (← (← v.getObjVal? "offset").getInt?)
  if let some v := field? j "SkipIf" then
    let (f, n) ← parseGuard v
    return .skipIf f n
  if let some v := field? j "SkipIfNot" then
    let (f, n) ← parseGuard v
    return .skipIfNot f n
  throw s!"unrecognised PolishToken: {j.compress}"

/-- A whole dump: the `constant_term` program, with `index_terms` required to be empty.

That requirement is not incidental. Every column of the deployed one-chunk index is
evaluated, so the linearization carries no per-column index terms — the same fact
`kimchi/scripts/check_linearization.lean` asserts of its own fixture before reading the
scalar side. A non-empty `index_terms` means a dump from outside the modelled regime, and
is rejected here rather than quietly ignored. -/
def parseLinearization (j : Json) : Except String (Array PolishToken) := do
  let ct ← (← j.getObjVal? "constant_term").getArr?
  let toks ← ct.mapM parseToken
  let it ← (← j.getObjVal? "index_terms").getArr?
  unless it.isEmpty do
    throw s!"expected an empty index_terms array, got {it.size} entries"
  return toks

/-- Read and decode a dump, reporting the path on failure. -/
def readLinearization (path : String) : IO (Array PolishToken) := do
  let raw ← IO.FS.readFile path
  match Json.parse raw >>= parseLinearization with
  | .ok toks => return toks
  | .error e => throw (IO.userError s!"{path}: {e}")

end Pickles.Fixture
