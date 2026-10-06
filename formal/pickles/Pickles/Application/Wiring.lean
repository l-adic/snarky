import Pickles.Application.Compile
import Pickles.KeyLayout
import Pickles.StepMain
import Pickles.WrapFinalize

/-!
# Application key and domain wiring

Resolve Self and External slots from one application's backend artifacts and its imported
interfaces. Candidate step domains come from branch keys; wrap-domain pins follow source
keys and front padding. Source chunk counts remain per slot, matching the step circuit's
slot-indexed chunk-count parameter.

Assembly checks key layouts, chunk counts, and supported wrap domains. Lagrange tables
are backend data: this layer neither computes them from an SRS nor asserts that they are
the SRS's commitments. It also makes no claim about a run's witnessed Self key.
-/

namespace Pickles.Application

open Snarky Kimchi.Verifier Bulletproof CompElliptic.Fields.Pasta

/-- The circuit data an application exports without exposing its branch descriptions. -/
structure CircuitInterface (I : LayoutInterface) where
  /-- The source application's checked wrap key. -/
  wrapKey : Key IpaPallas.curve 1
  /-- The key declares the wrap circuit's fixed public and accumulator counts. -/
  wrapLayout : WrapKeyLayout wrapKey.cvk
  /-- Its wrap proof uses one chunk at the deployed SRS size. -/
  wrapChunks : 1 = chunkCount WrapIPARounds wrapKey.cvk.domainLog2
  /-- The source wrap domain has a position in the finalize circuit's domain table. -/
  wrapDomain : wrapKey.cvk.domainLog2 ∈ wrapDomainLog2s
  /-- The source application's step-proof chunk count. -/
  stepChunks : Nat
  /-- The candidate step domains, checked at this source's chunk count. -/
  stepDomains : KnownDomains stepChunks
  /-- The backend's public-input bases for this source's wrap key. -/
  wrapLagrange : SlotLagrange 1 StepIPARounds

/-- The supported wrap-domain index is computed from the key. -/
def CircuitInterface.wrapIndex {I : LayoutInterface} (C : CircuitInterface I) : Nat :=
  wrapDomainLog2s.idxOf C.wrapKey.cvk.domainLog2

/-- The computed index selects the source key's wrap domain. -/
private theorem CircuitInterface.wrapIndex_spec {I : LayoutInterface} (C : CircuitInterface I) :
    wrapDomainLog2s[C.wrapIndex]? = some C.wrapKey.cvk.domainLog2 :=
  List.getElem?_idxOf C.wrapDomain

/-- Backend artifacts for one application, with step keys in the description's branch order. -/
structure BackendArtifacts (D : Shape) where
  /-- The application's wrap key, with the ordinary key invariants already checked. -/
  wrapKey : Key IpaPallas.curve 1
  /-- The application's own step-proof chunk count, independent of its imports' counts. -/
  stepChunks : Nat
  /-- One step key per branch, sharing this application's step-proof chunk count. -/
  stepKeys : Vector (Key IpaVesta.curve stepChunks) D.branches
  /-- The backend's public-input bases for the wrap key. -/
  wrapLagrange : SlotLagrange 1 StepIPARounds

/-- Candidate step domains derived from the application's branch keys, in branch order. -/
def BackendArtifacts.stepDomains {D : Shape} (A : BackendArtifacts D) :
    KnownDomains A.stepChunks where
  log2s := A.stepKeys.toList.map (·.cvk.domainLog2)
  log2s_le := by
    intro d hd
    obtain ⟨K, _, rfl⟩ := List.mem_map.mp hd
    exact K.domainLog2_le
  log2s_zkRows := by
    intro d hd
    obtain ⟨K, _, rfl⟩ := List.mem_map.mp hd
    simpa only [K.zkRows_eq] using K.zkRows_le

/-- A backend's key metadata agrees with this application's layout and deployed SRS sizes. -/
structure BackendValid {D : Shape} (A : BackendArtifacts D) : Prop where
  /-- Branch selection fits the wrap field. -/
  branches_le : D.branches ≤ PALLAS_SCALAR_CARD
  /-- The wrap key has the full statement and padded accumulator counts. -/
  wrapLayout : WrapKeyLayout A.wrapKey.cvk
  /-- The wrap key uses one chunk at the deployed wrap SRS. -/
  wrapChunks : 1 = chunkCount WrapIPARounds A.wrapKey.cvk.domainLog2
  /-- The wrap domain is supported by the finalize circuit. -/
  wrapDomain : A.wrapKey.cvk.domainLog2 ∈ wrapDomainLog2s
  /-- Each step key declares the padded statement and its branch's predecessor count. -/
  stepLayouts : ∀ b : D.Branch, StepKeyLayout A.stepKeys[b].cvk D.width (D.slots b)
  /-- Each step domain uses the declared number of chunks at the deployed step SRS. -/
  stepChunks : ∀ b : D.Branch,
    A.stepChunks = chunkCount StepIPARounds A.stepKeys[b].cvk.domainLog2

/-- A checked application's static wiring and its already compiled imports. -/
structure Wiring (D : Shape) (L : Layout D) where
  /-- The application's own backend artifacts. -/
  backend : BackendArtifacts D
  /-- The checked agreement between those artifacts and the application description. -/
  valid : BackendValid backend
  /-- Each import supplies circuit data at its declared layout interface. -/
  imports : (t : Fin D.imports.size) → CircuitInterface D.imports[t]

/-- Check a proposition and retain its proof, or fail with the supplied error. -/
def requireProof {m : Type → Type} {ε : Type} [Monad m] [MonadExcept ε m]
    (p : Prop) [Decidable p] (error : ε) : m (PLift p) :=
  if h : p then pure ⟨h⟩ else throw error

/-- Validate backend metadata before assembling the configuration; no uniform source-chunk
condition is imposed. Lagrange correspondence remains a later SRS-dependent premise. -/
def Wiring.assemble {D : Shape} (L : Layout D) (A : BackendArtifacts D)
    (imports : (t : Fin D.imports.size) → CircuitInterface D.imports[t]) :
    Except String (Wiring D L) := do
  let ⟨hb⟩ ← requireProof (D.branches ≤ PALLAS_SCALAR_CARD)
    "the branch count exceeds the wrap field"
  let ⟨hw⟩ ← requireProof (WrapKeyLayout A.wrapKey.cvk)
    "the wrap key's layout disagrees with the wrap circuit"
  let ⟨hc⟩ ← requireProof (1 = chunkCount WrapIPARounds A.wrapKey.cvk.domainLog2)
    "the wrap key does not use one chunk"
  let ⟨hd⟩ ← requireProof (A.wrapKey.cvk.domainLog2 ∈ wrapDomainLog2s)
    "the wrap key's domain is not supported"
  let ⟨hs⟩ ← requireProof
    (∀ b : D.Branch, StepKeyLayout A.stepKeys[b].cvk D.width (D.slots b))
    "a step key's layout disagrees with its branch"
  let ⟨hn⟩ ← requireProof (∀ b : D.Branch,
    A.stepChunks = chunkCount StepIPARounds A.stepKeys[b].cvk.domainLog2)
    "a step key's domain disagrees with the declared chunk count"
  return ⟨A, ⟨hb, hw, hc, hd, hs, hn⟩, imports⟩

/-- Export this application's circuit data for later applications. -/
def Wiring.export {D : Shape} {L : Layout D} (W : Wiring D L) : CircuitInterface L.export where
  wrapKey := W.backend.wrapKey
  wrapLayout := W.valid.wrapLayout
  wrapChunks := W.valid.wrapChunks
  wrapDomain := W.valid.wrapDomain
  stepChunks := W.backend.stepChunks
  stepDomains := W.backend.stepDomains
  wrapLagrange := W.backend.wrapLagrange

/-- The source layout attached to a branch-local slot. -/
def Shape.sourceLayout (D : Shape) (L : Layout D) (b : D.Branch) (i : D.Slot b) :
    LayoutInterface :=
  match D.source b i with
  | .self => L.export
  | .external t => D.imports[t]

/-- Resolve the slot's circuit interface from its declared source. -/
def Wiring.source {D : Shape} {L : Layout D} (W : Wiring D L) (b : D.Branch) (i : D.Slot b) :
    CircuitInterface (D.sourceLayout L b i) :=
  SlotRef.casesOn (motive := fun s => CircuitInterface
    (match s with | .self => L.export | .external t => D.imports[t]))
    (D.source b i) W.export W.imports

/-- Each slot finalizes step proofs at its source application's chunk count. -/
def Wiring.sourceChunks {D : Shape} {L : Layout D} (W : Wiring D L)
    (b : D.Branch) (i : D.Slot b) : Nat :=
  (W.source b i).stepChunks

/-- Construct the existing circuit's slot sources: Self keeps a witnessed key, while
External embeds the imported key's commitments and candidate domains as constants. -/
def Wiring.sources {D : Shape} {L : Layout D} (W : Wiring D L)
    (b : D.Branch) (i : D.Slot b) : SlotSource 1 StepIPARounds :=
  match D.source b i with
  | .self => .self W.backend.wrapLagrange
  | .external t =>
    let C := W.imports t
    .external C.wrapKey.cvk.comms C.wrapLagrange D.imports[t].width.val C.stepDomains.list

/-- Resolving a source preserves its declared application width. -/
theorem Wiring.source_width {D : Shape} {L : Layout D} (W : Wiring D L)
    (b : D.Branch) (i : D.Slot b) :
    (W.sources b i).width D.width = D.slotWidth b i := by
  cases h : D.source b i <;> simp [sources, Shape.slotWidth, h]

/-- The resolved circuit source uses exactly its source interface's candidate domains. -/
theorem Wiring.source_domains {D : Shape} {L : Layout D} (W : Wiring D L)
    (b : D.Branch) (i : D.Slot b) :
    (W.sources b i).domains W.backend.stepDomains.list = (W.source b i).stepDomains.list := by
  unfold sources source Shape.sourceLayout
  generalize D.source b i = s
  cases s <;> rfl

/-- The wrap-domain index of a padding position: the one-predecessor wrap domain's place in
`wrapDomainLog2s`, which the wrap circuit pins and its prover supplies. -/
private def paddingWrapIndex : Nat := 1

/-- Each finalization position's wrap-domain index, across branches. Leading padding
uses `paddingWrapIndex`. -/
def Wiring.pins {D : Shape} {L : Layout D} (W : Wiring D L) :
    Vector (Vector (Option Nat) D.branches) D.width :=
  Vector.ofFn fun j => Vector.ofFn fun b =>
    some (((D.slotAt b j).map fun i => (W.source b i).wrapIndex).getD paddingWrapIndex)

/-- A branch's live slot is pinned to its selected source's wrap domain. -/
theorem Wiring.pins_at_slot {D : Shape} {L : Layout D} (W : Wiring D L)
    (b : D.Branch) (i : D.Slot b) :
    W.pins[D.paddedSlot b i][b] = some (W.source b i).wrapIndex := by
  simp [pins, Shape.slotAt_paddedSlot]

/-- Any pin read at a live slot selects that source's actual wrap-key domain. -/
theorem Wiring.pin_domain {D : Shape} {L : Layout D} (W : Wiring D L)
    (b : D.Branch) (i : D.Slot b) (j : Nat)
    (h : W.pins[D.paddedSlot b i][b] = some j) :
    wrapDomainLog2s[j]? = some (W.source b i).wrapKey.cvk.domainLog2 := by
  rw [W.pins_at_slot] at h
  cases Option.some.inj h
  exact (W.source b i).wrapIndex_spec

/-- The branch-key vector the existing wrap circuit takes, in application branch order. -/
def Wiring.stepKeys {D : Shape} {L : Layout D} (W : Wiring D L) :
    Vector (KimchiVK IpaVesta.curve W.backend.stepChunks) D.branches :=
  W.backend.stepKeys.map (·.cvk)

/-- The assembled branch-key table has the layout required by the generic capstones. -/
theorem Wiring.step_key_layout {D : Shape} {L : Layout D} (W : Wiring D L) (b : D.Branch) :
    StepKeyLayout W.stepKeys[b] D.width (D.widths[b] : Nat) := by
  simpa [stepKeys, Shape.widths] using W.valid.stepLayouts b

end Pickles.Application
