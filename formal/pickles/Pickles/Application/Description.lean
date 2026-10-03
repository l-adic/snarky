import Pickles.Statement
import Snarky.Kimchi.Semantics

/-!
# Application descriptions

One application's schema and branch shapes, with the layout interfaces of its already
compiled imports. A slot refers to Self or one of those imports. Imported applications'
branch descriptions are not needed to compute this application's layout.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

/-- An application's input/output encodings and the input's circuit check. -/
structure Schema where
  /-- Public input values. -/
  Input : Type
  /-- Public input cells. -/
  InputVar : Type
  /-- Public output values. -/
  Output : Type
  /-- Public output cells. -/
  OutputVar : Type
  /-- The input's field encoding. -/
  inputEncoding : CircuitType Fp Input InputVar
  /-- The output's field encoding. -/
  outputEncoding : CircuitType Fp Output OutputVar
  /-- The check emitted when the rule's input is witnessed. -/
  inputCheck : @CheckedType Fp (KimchiConstraint Fp) Input InputVar _ _ _ inputEncoding

attribute [instance] Schema.inputEncoding Schema.outputEncoding Schema.inputCheck

/-- A statement contains its input fields followed by its output fields. -/
private def Schema.size (S : Schema) : Nat :=
  CircuitType.size Fp S.Input + CircuitType.size Fp S.Output

/-- The layout information a checked application exposes to its importers.
Keys and domains belong to the later circuit-construction layer. -/
structure LayoutInterface where
  /-- The imported application's statement encoding. -/
  schema : Schema
  /-- Its maximum predecessor count, already bounded by the protocol. -/
  width : Fin (MaxProofsVerified + 1)

/-- A slot's source: Self, or one of this application's compiled imports. -/
inductive SlotRef (numImports : Nat) where
  /-- The application being compiled, whose wrap key will be witnessed. -/
  | self
  /-- An already compiled application, whose wrap key will be a circuit constant. -/
  | external (tag : Fin numImports)

/-- One application's schema, compiled imports, and ordered branch/slot shapes. -/
structure Shape where
  /-- The application's statement schema, shared by its branches. -/
  schema : Schema
  /-- Layout interfaces of already compiled applications available to External slots. -/
  imports : Array LayoutInterface
  /-- The number of alternative rules. -/
  branches : Nat
  /-- An application has at least one branch. -/
  branches_pos : 0 < branches
  /-- Each branch's predecessor count. -/
  slots : Fin branches → Nat
  /-- Each predecessor's source, in the rule's slot order. -/
  source : (b : Fin branches) → Fin (slots b) → SlotRef imports.size

/-- A branch of a particular application. -/
abbrev Shape.Branch (D : Shape) := Fin D.branches

/-- A predecessor slot of a particular branch. -/
abbrev Shape.Slot (D : Shape) (b : D.Branch) := Fin (D.slots b)

/-- The maximum predecessor count across an application's branches. -/
def Shape.width (D : Shape) : Nat :=
  ((List.finRange D.branches).map D.slots).foldl max 0

/-- A branch slot's source application width, which can be smaller than the capacity
of the shared wrap position it occupies. -/
def Shape.slotWidth (D : Shape) (b : D.Branch) (i : D.Slot b) : Nat :=
  match D.source b i with
  | .self => D.width
  | .external tag => D.imports[tag].width.val

/-- The number of statement fields a slot reads, derived from its target's encoding. -/
def Shape.prevSize (D : Shape) (b : D.Branch) (i : D.Slot b) : Nat :=
  match D.source b i with
  | .self => D.schema.size
  | .external tag => D.imports[tag].schema.size

end Pickles.Application
