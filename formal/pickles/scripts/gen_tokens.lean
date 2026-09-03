import Pickles.Linearization.Types
import Lean.Data.Json

/-!
# `gen_tokens` — the linearization token codegen

Reads `pickles-codegen`'s Rust dump of kimchi's compiled linearization and writes
`Pickles/Linearization/{Fp,Fq}.lean`, the Lean counterpart of what `Generator.purs`
does for PureScript. Both read the same JSON, `packages/pickles-codegen/rust/output/`
`{fp,fq}.json`, so the Lean and PureScript token modules are independent transcriptions
of one origin and a disagreement between them is detectable.

The output is committed: formal/'s CI checks out without the mina submodule and cannot
regenerate it. Run `make gen-linearization-lean` at the repo root on a proof-systems bump
and commit the diff.

    LINEARIZATION_JSON_DIR   where fp.json / fq.json live
    LINEARIZATION_LEAN_DIR   where Fp.lean / Fq.lean are written

## The wire encoding

Nullary tokens are bare strings; everything else is a single-key object. `SkipIf` and
`SkipIfNot` carry a two-element `[flag, count]` array.

* `"Add" | "Mul" | "Sub" | "Dup" | "Store" | "VanishesOnZeroKnowledgeAndPreviousRows"`
* `{"Constant": "EndoCoefficient" | {"Mds": {…}} | {"Literal": "0x…"}}`
* `{"Challenge": "Alpha" | "Beta" | "Gamma" | "JointCombiner"}`
* `{"Cell": {"col": …, "row": "Curr" | "Next"}}`
* `{"Pow": n}`, `{"Load": n}`
* `{"UnnormalizedLagrangeBasis": {"zk_rows": bool, "offset": int}}`, offset signed
* `{"SkipIf": [flag, n]}`, `{"SkipIfNot": [flag, n]}`

Unknown tags are rejected rather than dropped: a token the decoder does not understand is
one the interpreter cannot execute.
-/

open Lean Pickles.Linearization

/-! ## Decoding -/

/-! ## Small helpers -/

/-- `some v` when `j` is an object carrying key `k`, `none` otherwise. -/
def field? (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

/-- The value of a hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  let v := c.toNat
  if 0x30 ≤ v && v ≤ 0x39 then some (v - 0x30)          -- '0'..'9'
  else if 0x61 ≤ v && v ≤ 0x66 then some (v - 0x61 + 10) -- 'a'..'f'
  else if 0x41 ≤ v && v ≤ 0x46 then some (v - 0x41 + 10) -- 'A'..'F'
  else none

/-- One step of the hex fold. An `x` resets the accumulator, which discards the leading
`0` of a `0x` prefix. -/
def hexStep (acc : Except String Nat) (c : Char) : Except String Nat :=
  match acc with
  | .error e => .error e
  | .ok n =>
    if c.toNat = 0x78 || c.toNat = 0x58 then .ok 0
    else match hexDigit? c with
      | some d => .ok (n * 16 + d)
      | none => .error s!"not a hex digit: '{c}'"

/-- A `0x…` literal as a natural number. -/
def parseHexNat (s : String) : Except String Nat :=
  if s.isEmpty then .error "empty hex literal"
  else s.foldl hexStep (.ok 0)

/-! ## The leaf enumerations -/

/-- `"Curr" | "Next"`. -/
def parseCurrOrNext (j : Json) : Except String CurrOrNext := do
  match ← j.getStr? with
  | "Curr" => return .curr
  | "Next" => return .next
  | s => throw s!"unknown CurrOrNext: {s}"

/-- A gate name, as an `Index` column's payload. -/
def parseGateType (j : Json) : Except String GateType := do
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
def parseLookupPattern (j : Json) : Except String LookupPattern := do
  match ← j.getStr? with
  | "Lookup" => return .lookup
  | "Xor" => return .xor
  | "RangeCheck" => return .rangeCheck
  | "ForeignFieldMul" => return .foreignFieldMul
  | s => throw s!"unknown LookupPattern: {s}"

/-- A challenge name. -/
def parseChallengeTerm (j : Json) : Except String ChallengeTerm := do
  match ← j.getStr? with
  | "Alpha" => return .alpha
  | "Beta" => return .beta
  | "Gamma" => return .gamma
  | "JointCombiner" => return .jointCombiner
  | s => throw s!"unknown ChallengeTerm: {s}"

/-! ## The tagged unions -/

/-- A column reference: four bare tags, five single-key objects. -/
def parseColumn (j : Json) : Except String Column := do
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
  if let some v := field? j "LookupKindIndex" then
    return .lookupKindIndex (← parseLookupPattern v)
  throw s!"unrecognised Column: {j.compress}"

/-- A constant: the bare `EndoCoefficient` tag, an MDS entry, or a hex literal. -/
def parseConstantTerm (j : Json) : Except String ConstantTerm := do
  if let .ok s := j.getStr? then
    match s with
    | "EndoCoefficient" => return .endoCoefficient
    | _ => throw s!"unknown ConstantTerm tag: {s}"
  if let some v := field? j "Mds" then
    return .mds (← (← v.getObjVal? "row").getNat?) (← (← v.getObjVal? "col").getNat?)
  if let some v := field? j "Literal" then return .literal (← parseHexNat (← v.getStr?))
  throw s!"unrecognised ConstantTerm: {j.compress}"

/-- A feature predicate: eight bare tags, three single-key objects. -/
def parseFeatureFlag (j : Json) : Except String FeatureFlag := do
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
def parseGuard (j : Json) : Except String (FeatureFlag × Nat) := do
  let a ← j.getArr?
  match a[0]?, a[1]? with
  | some fj, some nj => return (← parseFeatureFlag fj, ← nj.getNat?)
  | _, _ => throw s!"expected a [flag, count] pair, got {a.size} entries"

/-! ## Tokens and streams -/

/-- One token. Nullary tokens arrive as bare strings, the rest as single-key objects. -/
def parseToken (j : Json) : Except String PolishToken := do
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
    return .cell (← parseColumn (← v.getObjVal? "col"))
      (← parseCurrOrNext (← v.getObjVal? "row"))
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

/-- The `constant_term` program of a dump. `index_terms` must be empty: every column of
the deployed one-chunk index is evaluated, so there are no per-column terms, as
`kimchi/scripts/check_linearization.lean` also requires of its fixture. -/
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

/-! ## Rendering -/

/-! ## Rendering -/

/-- An `Int` as a Lean literal, parenthesised when negative. -/
def intLit (i : Int) : String := if i < 0 then s!"({i})" else toString i

/-- A row selector. -/
def rowSrc : CurrOrNext → String
  | .curr => ".curr"
  | .next => ".next"

/-- A gate name. -/
def gateSrc : GateType → String
  | .generic => ".generic"          | .poseidon => ".poseidon"
  | .completeAdd => ".completeAdd"  | .varBaseMul => ".varBaseMul"
  | .endoMul => ".endoMul"          | .endoMulScalar => ".endoMulScalar"
  | .rangeCheck0 => ".rangeCheck0"  | .rangeCheck1 => ".rangeCheck1"
  | .foreignFieldAdd => ".foreignFieldAdd"
  | .foreignFieldMul => ".foreignFieldMul"
  | .xor16 => ".xor16"              | .rot64 => ".rot64"

/-- A lookup family. -/
def lpSrc : LookupPattern → String
  | .lookup => ".lookup"          | .xor => ".xor"
  | .rangeCheck => ".rangeCheck"  | .foreignFieldMul => ".foreignFieldMul"

/-- A column reference. -/
def colSrc : Column → String
  | .witness i => s!"(.witness {i})"
  | .coefficient i => s!"(.coefficient {i})"
  | .index g => s!"(.index {gateSrc g})"
  | .lookupSorted i => s!"(.lookupSorted {i})"
  | .lookupAggreg => ".lookupAggreg"
  | .lookupTable => ".lookupTable"
  | .lookupRuntimeTable => ".lookupRuntimeTable"
  | .lookupRuntimeSelector => ".lookupRuntimeSelector"
  | .lookupKindIndex p => s!"(.lookupKindIndex {lpSrc p})"

/-- A constant. -/
def constSrc : ConstantTerm → String
  | .endoCoefficient => ".endoCoefficient"
  | .mds r c => s!"(.mds {r} {c})"
  | .literal v => s!"(.literal {v})"

/-- A challenge. -/
def chalSrc : ChallengeTerm → String
  | .alpha => ".alpha"  | .beta => ".beta"
  | .gamma => ".gamma"  | .jointCombiner => ".jointCombiner"

/-- A feature predicate. -/
def flagSrc : FeatureFlag → String
  | .rangeCheck0 => ".rangeCheck0"  | .rangeCheck1 => ".rangeCheck1"
  | .foreignFieldAdd => ".foreignFieldAdd"
  | .foreignFieldMul => ".foreignFieldMul"
  | .xor => ".xor"                  | .rot => ".rot"
  | .lookupTables => ".lookupTables"
  | .runtimeLookupTables => ".runtimeLookupTables"
  | .lookupPattern p => s!"(.lookupPattern {lpSrc p})"
  | .tableWidth n => s!"(.tableWidth {n})"
  | .lookupsPerRow n => s!"(.lookupsPerRow {n})"

/-- One token as a Lean term. -/
def tokenSrc : PolishToken → String
  | .constant c => s!".constant {constSrc c}"
  | .challenge c => s!".challenge {chalSrc c}"
  | .cell col row => s!".cell {colSrc col} {rowSrc row}"
  | .dup => ".dup"
  | .pow n => s!".pow {n}"
  | .add => ".add"
  | .mul => ".mul"
  | .sub => ".sub"
  | .vanishesOnZeroKnowledgeAndPreviousRows => ".vanishesOnZeroKnowledgeAndPreviousRows"
  | .unnormalizedLagrangeBasis zk off =>
      s!".unnormalizedLagrangeBasis {zk} {intLit off}"
  | .store => ".store"
  | .load i => s!".load {i}"
  | .skipIf f n => s!".skipIf {flagSrc f} {n}"
  | .skipIfNot f n => s!".skipIfNot {flagSrc f} {n}"

/-! ## The module -/

/-- The generated module `Pickles.Linearization.<field>`, exporting `<defName>`, one
token per line. -/
def moduleSrc (defName field : String) (toks : Array PolishToken) : String :=
  let body := toks.toList.map (fun t => "  " ++ tokenSrc t)
  let rows := String.intercalate ",\n" body
  s!"import Pickles.Linearization.Types\n\
     \n\
     /-!\n\
     # The deployed linearization over {field}\n\
     \n\
     Generated by `scripts/gen_tokens.lean` from the Rust dump; do not edit. The\n\
     PureScript counterparts (`Pickles.Linearization.Pallas`/`Vesta`) come from the same\n\
     JSON, so the two are independent transcriptions of one origin.\n\
     -/\n\
     \n\
     namespace Pickles.Linearization\n\
     \n\
     /-- kimchi's compiled linearization over {field}: {toks.size} tokens. -/\n\
     def {defName} : Array PolishToken := #[\n\
     {rows}]\n\
     \n\
     end Pickles.Linearization\n"

/-! ## The driver -/

def emit (jsonDir leanDir file name defName field : String) : IO Unit := do
  let toks ← readLinearization s!"{jsonDir}/{file}.json"
  let path := s!"{leanDir}/{name}.lean"
  IO.FS.writeFile path (moduleSrc defName field toks)
  IO.println s!"wrote {path} ({toks.size} tokens)"

def main : IO Unit := do
  let jsonDir := (← IO.getEnv "LINEARIZATION_JSON_DIR").getD
    "../../packages/pickles-codegen/rust/output"
  let leanDir := (← IO.getEnv "LINEARIZATION_LEAN_DIR").getD "Pickles/Linearization"
  IO.FS.createDirAll leanDir
  emit jsonDir leanDir "fp" "Fp" "fpTokens" "Fp"
  emit jsonDir leanDir "fq" "Fq" "fqTokens" "Fq"
