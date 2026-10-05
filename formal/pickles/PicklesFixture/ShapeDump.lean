import Pickles.Application.Wiring
import Lean.Data.Json

/-!
# Application shapes from PureScript sidecars

Read a tag's small shape file, resolve each imported source against an already assembled
application by its complete wrap key, and construct the Lean application shape. The
schema uses field vectors: rule replay and the verifier observe the flattened fields,
not the source language's value types.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi CompElliptic.Fields.Pasta Pickles.Application

structure FieldLayoutDump where
  inputFields : Nat
  outputFields : Nat
  deriving Repr, DecidableEq, Inhabited

private def FieldLayoutDump.ofJson (j : Json) : Except String FieldLayoutDump := do
  let inputFields ← (← j.getObjVal? "inputFields").getNat?
  let outputFields ← (← j.getObjVal? "outputFields").getNat?
  return ⟨inputFields, outputFields⟩

structure ImportedLayoutDump where
  statement : FieldLayoutDump
  width : Nat
  deriving Repr, DecidableEq, Inhabited

private def ImportedLayoutDump.ofJson (j : Json) : Except String ImportedLayoutDump := do
  let statement ← FieldLayoutDump.ofJson (← j.getObjVal? "statement")
  let width ← (← j.getObjVal? "width").getNat?
  return ⟨statement, width⟩

inductive SlotSourceDump where
  | self
  | external (importIndex : Nat)
  | sideLoaded (layout : ImportedLayoutDump)
  deriving Repr, DecidableEq, Inhabited

private def SlotSourceDump.ofJson (j : Json) : Except String SlotSourceDump := do
  match ← (← j.getObjVal? "kind").getStr? with
  | "self" => return .self
  | "external" => return .external (← (← j.getObjVal? "importIndex").getNat?)
  | "sideLoaded" => return .sideLoaded (← ImportedLayoutDump.ofJson j)
  | kind => throw s!"unknown predecessor source {kind}"

structure ShapeDump where
  statement : FieldLayoutDump
  imports : Array ImportedLayoutDump
  branches : Array (Array SlotSourceDump)
  deriving Repr

def ShapeDump.ofJson (j : Json) : Except String ShapeDump := do
  let statement ← FieldLayoutDump.ofJson (← j.getObjVal? "statement")
  let imports ← (← (← j.getObjVal? "imports").getArr?).mapM ImportedLayoutDump.ofJson
  let branches ← (← (← j.getObjVal? "branches").getArr?).mapM fun b => do
    (← (← b.getObjVal? "slots").getArr?).mapM SlotSourceDump.ofJson
  return ⟨statement, imports, branches⟩

private def fieldSchema (s : FieldLayoutDump) : Schema where
  Input := Vector Fp s.inputFields
  InputVar := Vector (FVar Fp) s.inputFields
  Output := Vector Fp s.outputFields
  OutputVar := Vector (FVar Fp) s.outputFields
  inputEncoding := inferInstance
  outputEncoding := inferInstance
  inputCheck := inferInstance

/-- An application already assembled in compilation order, identified by its exported key. -/
structure KnownTag where
  key : Json
  interface : LayoutInterface
  circuit : CircuitInterface interface

/-- A decoded shape and the already assembled interfaces its slots use. -/
structure LoadedShape where
  shape : Shape
  layout : Layout shape
  imports : (i : Fin shape.imports.size) → CircuitInterface shape.imports[i]

private structure CheckedSources (raw : ShapeDump) where
  rows : Array (Array (SlotRef raw.imports.size))
  importKeys : Array Json

private theorem castRows_size {m n : Nat} (h : m = n)
    (rows : Array (Array (SlotRef m))) : (h ▸ rows).size = rows.size := by
  cases h
  rfl

private def ShapeDump.checkTag (raw : ShapeDump) (tag : Json) :
    Except String (CheckedSources raw) := do
  let wrapMain : Json ← tag.getObjVal? "wrapMain"
  let ownKey : Json ← wrapMain.getObjVal? "key"
  let branchJsons : Array Json ← (← tag.getObjVal? "branches").getArr?
  unless branchJsons.size == raw.branches.size do
    throw "shape branch count differs from the tag"
  let mut sourceRows : Array (Array (SlotRef raw.imports.size)) := #[]
  let mut importKeys : Array (Option Json) := Array.replicate raw.imports.size none
  let mut nextImport := 0
  for b in [:raw.branches.size] do
    let stepMain : Json ← branchJsons[b]!.getObjVal? "stepMain"
    let constants : Json ← stepMain.getObjVal? "constants"
    let keyedSlots : Array Json ← (← constants.getObjVal? "slots").getArr?
    let row := raw.branches[b]!
    unless keyedSlots.size == row.size do
      throw s!"branch {b}: shape slot count differs from the tag"
    let mut sources : Array (SlotRef raw.imports.size) := #[]
    for i in [:row.size] do
      let keyed := keyedSlots[i]!
      let kind ← (← keyed.getObjVal? "kind").getStr?
      let source ← match row[i]! with
        | .self => do
          unless kind == "self" && (← keyed.getObjVal? "key") == ownKey do
            throw s!"branch {b} slot {i}: Self key differs from this tag"
          pure SlotRef.self
        | .external k => do
          unless kind == "external" do
            throw s!"branch {b} slot {i}: expected an External key"
          if h : k < raw.imports.size then
            let key ← keyed.getObjVal? "key"
            match importKeys[k]! with
            | none =>
              unless k == nextImport do
                throw s!"import {k}: indices must follow first-use slot order"
              importKeys := importKeys.set! k (some key)
              nextImport := nextImport + 1
            | some prior => unless prior == key do
                throw s!"import {k}: slots disagree on the source key"
            pure (SlotRef.external ⟨k, h⟩)
          else throw s!"branch {b} slot {i}: import index {k} is out of bounds"
        | .sideLoaded _ => throw "side-loaded application slots are not yet in Lean Shape"
      sources := sources.push source
    sourceRows := sourceRows.push sources
  let mut keys : Array Json := #[]
  for i in [:raw.imports.size] do
    let some key := importKeys[i]! | throw s!"import {i} is unused"
    if keys.contains key then throw "the same source key has two import indices"
    keys := keys.push key
  return ⟨sourceRows, keys⟩

private def ShapeDump.resolveImports (raw : ShapeDump) (keys : Array Json)
    (known : Array KnownTag) : Except String (Array KnownTag) :=
  (keys.zip raw.imports).mapM fun (key, declared) =>
    match known.find? (fun p => p.key == key) with
    | none => .error "an import has no previously assembled producer"
    | some producer =>
      let schema := producer.interface.schema
      if declared.statement.inputFields == CircuitType.size Fp schema.Input &&
          declared.statement.outputFields == CircuitType.size Fp schema.Output &&
          declared.width == producer.interface.width.val then
        .ok producer
      else .error "an import disagrees with its producer's statement or width"

/-- Validate a sidecar against the tag's keyed slots and previously loaded tags, then
construct the shape used for application compilation. -/
def ShapeDump.load (raw : ShapeDump) (tag : Json) (known : Array KnownTag) :
    Except String LoadedShape :=
  match raw.checkTag tag with
  | .error e => .error e
  | .ok checked =>
    match raw.resolveImports checked.importKeys known with
    | .error e => .error e
    | .ok resolved =>
      let interfaces := resolved.map (·.interface)
      if hsize : interfaces.size = raw.imports.size then
        if h : 0 < checked.rows.size then
          let rows : Array (Array (SlotRef interfaces.size)) := hsize.symm ▸ checked.rows
          let D : Shape :=
            { schema := fieldSchema raw.statement
              imports := interfaces
              branches := rows.size
              branches_pos := by
                have hs : rows.size = checked.rows.size := castRows_size hsize.symm checked.rows
                simpa [hs] using h
              slots b := rows[b].size
              source b i := rows[b][i] }
          match Layout.check D with
          | .error e => .error e
          | .ok ⟨L⟩ =>
            let importFn : (i : Fin D.imports.size) → CircuitInterface D.imports[i] :=
              fun i => by
                have hi : i.val < resolved.size := by simpa [D, interfaces] using i.isLt
                simpa [D, interfaces] using (resolved[i.val]'hi).circuit
            .ok ⟨D, L, importFn⟩
        else .error "an application shape must have at least one branch"
      else .error "the resolved import count differs from the shape"

end PicklesFixture.Application
