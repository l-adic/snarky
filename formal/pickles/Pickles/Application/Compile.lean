import Pickles.Application.Description

/-!
# Application layout assembly

Compute branch widths, front-padding positions, and the shared wrap slot capacities.
As in OCaml's max_local_max_proofs_verifieds, each shared slot takes the maximum
source width across branches. A branch's source width can be smaller than that capacity.

This is the layout portion of application compilation. It has no SRS, keys, Lagrange
tables, or execution facts and does not yet build the main circuits.
-/

namespace Pickles.Application

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
def Shape.wrapWidth (D : Shape) (j : Fin D.width) : Nat :=
  ((List.finRange D.branches).map fun b =>
    ((D.slotAt b j).map (D.slotWidth b)).getD 0).foldl max 0

/-- Every live slot's source width fits its shared wrap position's computed capacity. -/
theorem Shape.slotWidth_le_wrapWidth (D : Shape) (b : D.Branch) (i : D.Slot b) :
    D.slotWidth b i ≤ D.wrapWidth (D.paddedSlot b i) := by
  unfold wrapWidth
  apply List.le_max_of_mem (List.mem_cons_of_mem 0 ?_)
  exact List.mem_map.mpr ⟨b, List.mem_finRange b, by simp [slotAt_paddedSlot]⟩

/-- A checked layout: this application's width fits the protocol.
Imported widths are bounded by their interfaces; shared capacities are derived maxima. -/
structure Layout (D : Shape) : Prop where
  /-- This application's maximum width fits the protocol. -/
  width_le : D.width ≤ MaxProofsVerified

/-- Self uses this application's checked width; External uses its imported bound. -/
theorem Layout.slotWidth_le {D : Shape} (L : Layout D) (b : D.Branch) (i : D.Slot b) :
    D.slotWidth b i ≤ MaxProofsVerified := by
  unfold Shape.slotWidth
  cases D.source b i with
  | self => exact L.width_le
  | external tag => exact Nat.le_of_lt_succ D.imports[tag].width.isLt

/-- Each computed shared width fits the protocol when all target widths do. -/
theorem Layout.wrapWidth_le {D : Shape} (L : Layout D)
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

/-- Assembly succeeds exactly when this application has a compatible layout. -/
theorem Layout.check_ok_iff (D : Shape) :
    (∃ L, Layout.check D = .ok ⟨L⟩) ↔ Layout D := by
  constructor
  · rintro ⟨L, _⟩
    exact L
  · intro L
    exact ⟨L, by simp [check, L.width_le]⟩

end Pickles.Application
