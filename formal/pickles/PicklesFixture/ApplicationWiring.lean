import PicklesFixture.Application
import PicklesFixture.Constants

/-!
# Application wiring fixtures

Read backend artifacts independently of the slot routing being checked. The description
selects Self or an imported application; branch keys supply candidate domains. Compare
the resulting circuit configuration with the separately exported slot constants and pins.

The schema exports wrap Lagrange tables only inside slot constants. Collect these backend
tables once by domain and require all copies to agree. Their SRS correspondence is the
existing upstream premise, not an independent result of this fixture check.
-/

namespace PicklesFixture.Application

open Lean Snarky Kimchi.Verifier Bulletproof CompElliptic.Fields.Pasta Pickles
open Pickles.Application

private def keyOf (C : Ipa.KimchiCurve) (k nc : Nat) (j : Json) :
    Except String (Key C nc) := do
  let cvk ← checkedKey C k nc j
  let some key := Key.check cvk | throw "the backend key failed its invariant check"
  return key

private def wrapLagrangeOf (j : Json) : Except String (SlotLagrange 1 StepIPARounds) := do
  let pts ← FixtureKit.parseArrOf (chunksOf IpaPallas.curve 1) j
  if h : pts.size = CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp) then
    return ⟨pts, h⟩
  else throw "a wrap Lagrange table has the wrong number of bases"

/-- The corpus's backend wrap Lagrange tables, indexed by domain; disagreeing copies fail. -/
def wrapTablesOf (tags : Array Json) :
    Except String (List (Nat × SlotLagrange 1 StepIPARounds)) := do
  let mut tables := []
  for tag in tags do
    for branch in ← (← tag.getObjVal? "branches").getArr? do
      let c ← constantsOf "stepMain" (← branch.getObjVal? "stepMain")
      for slot in ← (← c.getObjVal? "slots").getArr? do
        let key ← keyOf IpaPallas.curve WrapIPARounds 1 (← slot.getObjVal? "key")
        let table ← wrapLagrangeOf (← slot.getObjVal? "lagrange")
        let d := key.cvk.domainLog2
        match tables.lookup d with
        | some previous =>
          unless previous == table do throw s!"wrap Lagrange tables disagree at domain {d}"
        | none => tables := (d, table) :: tables
  return tables

/-- Load only the application's own backend keys and its domain's Lagrange table.
Slot routing, source domains, widths, and pins are derived later from the description. -/
def backendOf (D : Shape) (tables : List (Nat × SlotLagrange 1 StepIPARounds)) (tag : Json) :
    Except String (BackendArtifacts D) := do
  let wrap ← tag.getObjVal? "wrapMain"
  let wrapKey ← keyOf IpaPallas.curve WrapIPARounds 1 (← wrap.getObjVal? "key")
  let some wrapLagrange := tables.lookup wrapKey.cvk.domainLog2
    | throw s!"no backend wrap Lagrange table for domain {wrapKey.cvk.domainLog2}"
  let c ← constantsOf "wrapMain" wrap
  let branches ← (← c.getObjVal? "branches").getArr?
  let some first := branches[0]? | throw "the backend has no branch key"
  let bases ← (← first.getObjVal? "lagrange").getArr?
  let some base := bases[0]? | throw "the backend has no step Lagrange base"
  let stepChunks := (← base.getArr?).size
  let keys ← branches.mapM fun branch => do
    keyOf IpaVesta.curve StepIPARounds stepChunks (← branch.getObjVal? "key")
  if h : keys.size = D.branches then
    return { wrapKey, stepChunks, stepKeys := ⟨keys, h⟩, wrapLagrange }
  else throw "the number of backend branch keys differs from the description"

-- Key's invariants fix its generator, shifts, endomorphism, digest and zero-knowledge rows.
-- Compare the remaining metadata and all commitments, rather than only a key digest.
private def sameKey {C : Ipa.KimchiCurve} {nc : Nat} (a b : KimchiVK C nc) : Bool :=
  decide (a.comms = b.comms) && a.domainLog2 == b.domainLog2 &&
    a.publicCount == b.publicCount && a.prevChallenges == b.prevChallenges

/-- Compare derived wiring with the dump's per-slot constants and wrap branch tables.
This reader keeps each slot's chunk count separate, including mixed-chunk descriptions. -/
def checkWiring {D : Shape} {L : Layout D} (W : Wiring D L) (name : String) (tag : Json) :
    Except String Unit := do
  let c ← constantsOf "wrapMain" (← tag.getObjVal? "wrapMain")
  let pins ← FixtureKit.parseArrOf (FixtureKit.parseArrOf fun j =>
    if j.isNull then pure none else some <$> j.getNat?) (← c.getObjVal? "pins")
  let expectedPins := (Vector.ofFn fun b : D.Branch =>
    (W.pins.map fun p => p[b]).toArray).toArray
  unless pins == expectedPins do throw s!"{name}: wrap-domain pins differ from assembly"
  let heights ← FixtureKit.parseArrOf Json.getNat? (← c.getObjVal? "slotWidths")
  unless heights == (L.wrapWidths.map Fin.val).toArray do
    throw s!"{name}: wrap capacities differ from assembly"
  let branches ← (← tag.getObjVal? "branches").getArr?
  let wrapBranches ← (← c.getObjVal? "branches").getArr?
  unless branches.size == D.branches && wrapBranches.size == D.branches do
    throw s!"{name}: branch counts differ from the description"
  for b in List.finRange D.branches do
    let some wb := wrapBranches[b.val]? | throw s!"{name}: missing wrap branch {b.val}"
    unless (← (← wb.getObjVal? "width").getNat?) == (D.widths[b] : Nat) do
      throw s!"{name}: branch width differs from assembly"
    let key ← keyOf IpaVesta.curve StepIPARounds W.backend.stepChunks (← wb.getObjVal? "key")
    unless sameKey key.cvk W.stepKeys[b] do
      throw s!"{name}: branch key differs from assembly"
    let some branch := branches[b.val]? | throw s!"{name}: missing step branch {b.val}"
    let sc ← constantsOf "stepMain" (← branch.getObjVal? "stepMain")
    let slots ← (← sc.getObjVal? "slots").getArr?
    unless slots.size == D.slots b do throw s!"{name}: branch slot count differs from description"
    have _ := W.step_key_layout b
    for i in List.finRange (D.slots b) do
      let some slot := slots[i.val]? | throw s!"{name}: missing slot {i.val}"
      let C := W.source b i
      let source := W.sources b i
      let expectedKind := match source with | .self _ => "self" | .external .. => "external"
      unless (← (← slot.getObjVal? "kind").getStr?) == expectedKind do
        throw s!"{name}/{b.val}/{i.val}: source kind differs from assembly"
      let key ← keyOf IpaPallas.curve WrapIPARounds 1 (← slot.getObjVal? "key")
      unless sameKey key.cvk C.wrapKey.cvk do
        throw s!"{name}/{b.val}/{i.val}: source key differs from assembly"
      match source with
      | .self _ => pure ()
      | .external comms _ _ _ =>
        unless decide (comms = key.cvk.comms) do
          throw s!"{name}/{b.val}/{i.val}: embedded External key differs from the slot's key"
      unless (← (← slot.getObjVal? "numChunks").getNat?) == W.sourceChunks b i do
        throw s!"{name}/{b.val}/{i.val}: source chunk count differs from assembly"
      unless (← (← slot.getObjVal? "width").getNat?) == (W.sources b i).width D.width do
        throw s!"{name}/{b.val}/{i.val}: source width differs from assembly"
      let domains ← FixtureKit.parseArrOf Json.getNat? (← slot.getObjVal? "domains")
      unless domains.toList ==
          ((source.domains W.backend.stepDomains.list).map (·.log2)) do
        throw s!"{name}/{b.val}/{i.val}: source domains differ from branch keys"
      unless (← wrapLagrangeOf (← slot.getObjVal? "lagrange")) == (W.sources b i).lagrange do
        throw s!"{name}/{b.val}/{i.val}: source Lagrange table differs from assembly"
      have _ := W.source_width b i
      have _ := W.source_domains b i
      have _ := W.pin_domain b i C.wrapIndex (W.pins_at_slot b i)

end PicklesFixture.Application
