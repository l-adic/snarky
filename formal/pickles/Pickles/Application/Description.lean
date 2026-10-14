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
def Schema.size (S : Schema) : Nat :=
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

/-- Every branch fits the maximum width computed from all branches. -/
theorem Shape.slots_le_width (D : Shape) (b : D.Branch) :
    D.slots b ≤ D.width := by
  exact List.le_max_of_mem (List.mem_cons_of_mem 0
    (List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩))

/-- A branch slot's position after front padding to the application's width. -/
def Shape.paddedSlot (D : Shape) (b : D.Branch) (i : D.Slot b) : Fin D.width :=
  ⟨D.width - D.slots b + i.val, by
    have := D.slots_le_width b
    have := i.isLt
    omega⟩

/-- Look up position `j` in branch `b`'s slot list, front-padded to `D.width`.
Return `none` if `j` lies in the leading padding, or `some i` for the branch-local
predecessor slot occupying that position. -/
def Shape.slotAt (D : Shape) (b : D.Branch) (j : Fin D.width) : Option (D.Slot b) :=
  if h : D.width - D.slots b ≤ j.val then
    some ⟨j.val - (D.width - D.slots b), by
      have := D.slots_le_width b
      have := j.isLt
      omega⟩
  else none

/-- Front-padding a live slot and looking it up returns that same slot. -/
theorem Shape.slotAt_paddedSlot (D : Shape) (b : D.Branch)
    (i : D.Slot b) : D.slotAt b (D.paddedSlot b i) = some i := by
  simp [slotAt, paddedSlot]

/-- Branch predecessor counts, at the shape the shared wrap circuit takes. -/
def Shape.widths (D : Shape) : Vector (Fin (D.width + 1)) D.branches :=
  Vector.ofFn fun b => ⟨D.slots b, Nat.lt_succ_of_le (D.slots_le_width b)⟩

/-- Shared capacity: the maximum source width at this wrap position across branches.
An unused position contributes zero; a live width-zero slot remains present in `slotAt`. -/
private def Shape.wrapWidth (D : Shape) (j : Fin D.width) : Nat :=
  ((List.finRange D.branches).map fun b =>
    ((D.slotAt b j).map (D.slotWidth b)).getD 0).foldl max 0

/-- Every live slot's source width fits its shared wrap position's computed capacity. -/
private theorem Shape.slotWidth_le_wrapWidth (D : Shape) (b : D.Branch) (i : D.Slot b) :
    D.slotWidth b i ≤ D.wrapWidth (D.paddedSlot b i) := by
  unfold wrapWidth
  apply List.le_max_of_mem (List.mem_cons_of_mem 0 ?_)
  exact List.mem_map.mpr ⟨b, List.mem_finRange b, by simp [slotAt_paddedSlot]⟩

/-- A checked layout: this application's width fits the protocol.
Imported widths are bounded by their interfaces; shared capacities are derived maxima. -/
structure Layout (D : Shape) : Prop where
  private mk ::
  /-- This application's maximum width fits the protocol. -/
  width_le : D.width ≤ MaxProofsVerified

/-- Self uses this application's checked width; External uses its imported bound. -/
private theorem Layout.slotWidth_le {D : Shape} (L : Layout D) (b : D.Branch) (i : D.Slot b) :
    D.slotWidth b i ≤ MaxProofsVerified := by
  unfold Shape.slotWidth
  cases D.source b i with
  | self => exact L.width_le
  | external tag => exact Nat.le_of_lt_succ D.imports[tag].width.isLt

/-- Each computed shared width fits the protocol when all target widths do. -/
private theorem Layout.wrapWidth_le {D : Shape} (L : Layout D)
    (j : Fin D.width) : D.wrapWidth j ≤ MaxProofsVerified := by
  apply (List.max_le_iff (List.cons_ne_nil 0 _)).mpr
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Nat.zero_le _
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  cases h : D.slotAt b j with
  | none => simp
  | some i => exact L.slotWidth_le b i

/-- Shared slot capacities, at the shape the wrap circuit takes. -/
def Layout.wrapWidths {D : Shape} (L : Layout D) :
    Vector (Fin (MaxProofsVerified + 1)) D.width :=
  Vector.ofFn fun j => ⟨D.wrapWidth j, Nat.lt_succ_of_le (L.wrapWidth_le j)⟩

/-- Every branch slot's source width fits the wrap circuit's allocated capacity. -/
theorem Layout.slotWidth_le_wrapWidths {D : Shape} (L : Layout D)
    (b : D.Branch) (i : D.Slot b) :
    D.slotWidth b i ≤ (L.wrapWidths[D.paddedSlot b i] : Nat) := by
  simpa only [wrapWidths, Fin.getElem_fin, Vector.getElem_ofFn] using
    D.slotWidth_le_wrapWidth b i

/-- Export only the schema and checked width needed by another application's layout. -/
def Layout.export {D : Shape} (L : Layout D) : LayoutInterface where
  schema := D.schema
  width := ⟨D.width, Nat.lt_succ_of_le L.width_le⟩

/-- Assemble the layout, rejecting application widths above the protocol bound.
`PLift` carries the checked proposition through the executable `Except` result. -/
def Layout.check (D : Shape) : Except String (PLift (Layout D)) :=
  if hw : D.width ≤ MaxProofsVerified then
    .ok ⟨⟨hw⟩⟩
  else .error "the application's predecessor count exceeds MaxProofsVerified"

end Pickles.Application
