import Pickles.Application.Wiring
import Lean.Data.Json

/-!
# Application shapes from PureScript sidecars

Read an application shape and attach the already resolved producer interfaces. The
schema uses field vectors: rule replay and the verifier observe the flattened fields,
not the source language's value types.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi CompElliptic.Fields.Pasta Pickles.Application

/-- Field counts of the application's public input and output. -/
structure FieldLayoutDump where
  /-- Number of flattened input fields. -/
  inputFields : Nat
  /-- Number of flattened output fields. -/
  outputFields : Nat
  deriving DecidableEq, Inhabited

private def FieldLayoutDump.ofJson (j : Json) : Except String FieldLayoutDump := do
  let inputFields ← (← j.getObjVal? "inputFields").getNat?
  let outputFields ← (← j.getObjVal? "outputFields").getNat?
  return ⟨inputFields, outputFields⟩

/-- Statement layout and recursion width declared for an imported application. -/
structure ImportedLayoutDump where
  /-- The imported application's flattened statement layout. -/
  statement : FieldLayoutDump
  /-- Maximum predecessor count of the imported application. -/
  width : Nat
  deriving DecidableEq, Inhabited

private def ImportedLayoutDump.ofJson (j : Json) : Except String ImportedLayoutDump := do
  let statement ← FieldLayoutDump.ofJson (← j.getObjVal? "statement")
  let width ← (← j.getObjVal? "width").getNat?
  return ⟨statement, width⟩

/-- Source of a branch's predecessor proof in the serialized shape. -/
inductive SlotSourceDump where
  | self
  | external (importIndex : Nat)
  | sideLoaded (layout : ImportedLayoutDump)
  deriving DecidableEq, Inhabited

private def SlotSourceDump.ofJson (j : Json) : Except String SlotSourceDump := do
  match ← (← j.getObjVal? "kind").getStr? with
  | "self" => return .self
  | "external" => return .external (← (← j.getObjVal? "importIndex").getNat?)
  | "sideLoaded" => return .sideLoaded (← ImportedLayoutDump.ofJson j)
  | kind => throw s!"unknown predecessor source {kind}"

/-- Statement layout, imported interfaces and ordered branch slots from the sidecar. -/
structure ShapeDump where
  /-- The application's flattened statement layout. -/
  statement : FieldLayoutDump
  /-- Imported application layouts in first-use order. -/
  imports : Array ImportedLayoutDump
  /-- Each branch's predecessor sources in slot order. -/
  branches : Array (Array SlotSourceDump)

/-- Decode the statement layout, imports and branch slots before checking their coherence. -/
def ShapeDump.ofJson (j : Json) : Except String ShapeDump := do
  let statement ← FieldLayoutDump.ofJson (← j.getObjVal? "statement")
  let imports ← (← (← j.getObjVal? "imports").getArr?).mapM ImportedLayoutDump.ofJson
  let branches ← (← (← j.getObjVal? "branches").getArr?).mapM fun b => do
    (← (← b.getObjVal? "slots").getArr?).mapM SlotSourceDump.ofJson
  return ⟨statement, imports, branches⟩

/-- Represent a flattened statement with field-vector values and variables. -/
def fieldSchema (s : FieldLayoutDump) : Schema where
  Input := Vector Fp s.inputFields
  InputVar := Vector (FVar Fp) s.inputFields
  Output := Vector Fp s.outputFields
  OutputVar := Vector (FVar Fp) s.outputFields
  inputEncoding := inferInstance
  outputEncoding := inferInstance
  inputCheck := inferInstance

/-- Canonical field-vector schemas retained when loading an application's shape. -/
structure FieldSchemas (D : Shape) where
  /-- The application's flattened input/output layout. -/
  own : FieldLayoutDump
  /-- The shape uses the canonical field encoding. -/
  own_eq : D.schema = fieldSchema own
  /-- Each imported application's flattened layout. -/
  imports : (i : Fin D.imports.size) → FieldLayoutDump
  /-- Imported encodings are canonical too. -/
  imports_eq : ∀ i, D.imports[i].schema = fieldSchema (imports i)

/-- An application already assembled in compilation order, identified by its exported key. -/
structure KnownTag where
  /-- The producer's checked wrap key. -/
  key : Pickles.Key Bulletproof.IpaPallas.curve 1
  /-- The producer's exported statement schema and width. -/
  interface : LayoutInterface
  /-- Backend parameters attached to the exported layout. -/
  circuit : CircuitInterface interface
  /-- The producer's flattened statement layout. -/
  statement : FieldLayoutDump
  /-- The interface uses the canonical encoding of its declared field counts. -/
  schema_eq : interface.schema = fieldSchema statement

/-- A decoded shape and the already assembled interfaces its slots use. -/
structure LoadedShape where
  /-- The decoded application shape with resolved predecessor sources. -/
  shape : Shape
  /-- Checked slot capacities and padding positions. -/
  layout : Layout shape
  /-- Canonical statement encodings for the application and its imports. -/
  schemas : FieldSchemas shape
  /-- Backend parameters of each resolved producer. -/
  imports : (i : Fin shape.imports.size) → CircuitInterface shape.imports[i]

private def checkImportLayouts (raw : ShapeDump) (resolved : Array KnownTag) :
    Except String Unit := do
  unless raw.imports.size = resolved.size do
    throw "the resolved import count differs from the shape"
  for i in [:raw.imports.size] do
    let declared := raw.imports[i]!
    let some producer := resolved[i]? | throw "missing resolved import"
    let schema := producer.interface.schema
    unless declared.statement.inputFields == CircuitType.size Fp schema.Input &&
        declared.statement.outputFields == CircuitType.size Fp schema.Output &&
        declared.width == producer.interface.width.val do
      throw "an import disagrees with its producer's statement or width"

private def sourceRows (raw : ShapeDump) (n : Nat) :
    Except String (Array (Array (SlotRef n))) := do
  let mut nextImport : Nat := 0
  let mut rows : Array (Array (SlotRef n)) := #[]
  for branch in raw.branches do
    let mut row : Array (SlotRef n) := #[]
    for slot in branch do
      let source ← match slot with
        | .self => pure SlotRef.self
        | .external i =>
          if h : i < n then
            if i > nextImport then throw "import indices must follow first-use slot order"
            if i = nextImport then nextImport := nextImport + 1
            pure (SlotRef.external ⟨i, h⟩)
          else throw "an import index is out of bounds"
        | .sideLoaded _ => throw "side-loaded application slots are not yet in Lean Shape"
      row := row.push source
    rows := rows.push row
  unless nextImport = n do throw "an import is unused"
  return rows

/-- Construct a shape from its sidecar and resolved imports, checking field sizes and routing. -/
def ShapeDump.load (raw : ShapeDump) (resolved : Array KnownTag) : Except String LoadedShape :=
  match checkImportLayouts raw resolved with
  | .error e => .error e
  | .ok () => match sourceRows raw resolved.size with
    | .error e => .error e
    | .ok rows =>
      if h : 0 < rows.size then
        let interfaces := resolved.map (·.interface)
        let D : Shape :=
          { schema := fieldSchema raw.statement
            imports := interfaces
            branches := rows.size
            branches_pos := h
            slots b := rows[b].size
            source b i := by simpa [interfaces] using rows[b][i] }
        match Layout.check D with
        | .error e => .error e
        | .ok ⟨L⟩ =>
          let importFn : (i : Fin D.imports.size) → CircuitInterface D.imports[i] := fun i => by
            have hi : i.val < resolved.size := by simpa [D, interfaces] using i.isLt
            simpa [D, interfaces] using (resolved[i.val]'hi).circuit
          let schemas : FieldSchemas D :=
            { own := raw.statement, own_eq := rfl
              imports := fun i => resolved[i.val]'
                (by simpa [D, interfaces] using i.isLt) |>.statement
              imports_eq := fun i => by
                have hi : i.val < resolved.size := by simpa [D, interfaces] using i.isLt
                simpa [D, interfaces] using (resolved[i.val]'hi).schema_eq }
          .ok ⟨D, L, schemas, importFn⟩
      else .error "an application shape must have at least one branch"

end PicklesFixture.Application
