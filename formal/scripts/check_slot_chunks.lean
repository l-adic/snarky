import PicklesFixture.Advice
import PicklesFixture.Fop

/-!
Construct step circuits with different predecessor step chunk counts in the same rule.
The TwoPhaseChain sidecar supplies the wrap key and blinding base. Lagrange entries,
slot counts and candidate step domains below are synthetic. This checks decoding and circuit
construction, not a mixed-chunk proof or a satisfying witness.

Run from `formal/`: `PICKLES_DUMP_DIR=<dir> lake exe check-slot-chunks`.
-/

open Lean Snarky Snarky.Kimchi Pickles PicklesFixture CompElliptic.Fields.Pasta

private def require (ok : Bool) (message : String) : IO Unit := do
  unless ok do throw (IO.userError message)

private def reject {α : Type} (result : Except String α) (message : String) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError message)
  | .error _ => pure ()

private def withSlots (step : Json) (slots : Array Json) : Except String Json := do
  let c ← step.getObjVal? "constants"
  return step.setObjVal! "constants" (c.setObjVal! "slots" (.arr slots))

private def externalSlot (slot : Json) (nc : Nat) : Json :=
  let slot := (slot.setObjVal! "kind" (toJson "external")).setObjVal! "numChunks" (toJson nc)
  slot.setObjVal! "domains" (toJson [if nc = 1 then 14 else 17])

private def circuitSize (k : StepMainConsts 2) : IO Nat := do
  let built := compileWith (a := Unit) (b := StepStatement (UnfVal 15) Fp 2)
    (stepMainCircuit (c := KimchiConstraint Fp) (w := 2) (ncw := 1) (ncs := k.chunks) (k := 15)
      (ks := StepIPARounds) (inVal := Unit) (outVal := Unit) (ss := fun _ => 1)
      (fun i => k.slots[i].source) (fun i => k.slots[i].width_le (by decide))
      k.h (fun i => fopStepParams (k.chunks i)) k.ownDomains
      (constPt dummyWrapSgPt) dummyUnfN0
      (fun _ => pure ((fun _ =>
        { appState := #v[.const 0], mustVerify := CircuitType.constVar (F := Fp) false }), ()))
      inertStepAdvice)
  let count := built.constraints.length
  require (count > 0) "the step circuit emitted no constraints"
  for i in List.finRange 2 do
    require ((built.result.1.2.slots i).evals.pub.zeta.toArray.size == k.chunks i)
      s!"slot {i}: the allocated evaluations have the wrong chunk count"
  IO.println s!"✓ step circuit: chunks {(k.slots.map (·.chunks)).toArray}, {count} constraints"
  (← IO.getStdout).flush
  return count

/-- Decode heterogeneous slots and build their circuits in both slot orders. -/
def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let tag ← IO.ofExcept (Json.parse (← IO.FS.readFile
    (System.FilePath.mk dir / "TwoPhaseChain" / "shapes" / "two_phase_chain.json")))
  let key ← IO.ofExcept (tag.getObjVal? "resolved" >>= (·.getObjVal? "wrapKey"))
  let h ← IO.ofExcept (tag.getObjVal? "environment" >>= (·.getObjVal? "srs") >>=
    (·.getObjVal? "wrap") >>= (·.getObjVal? "h"))
  let m := CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp)
  let slot := Json.mkObj [("kind", toJson "self"), ("width", toJson (2 : Nat)),
    ("numChunks", toJson (1 : Nat)), ("domains", toJson [14]), ("key", key),
    ("lagrange", Json.arr (Array.replicate m (Json.arr #[h])))]
  let step := Json.mkObj [("constants", Json.mkObj
    [("kind", toJson "stepMain"), ("h", h), ("slots", Json.arr #[slot])])]
  let one := externalSlot slot 1
  let two := externalSlot slot 2
  let read (slots : Array Json) := withSlots step slots >>= stepMainOf 2 2
  let uniform ← IO.ofExcept (read #[one, one])
  let mixed ← IO.ofExcept (read #[one, two])
  let reversed ← IO.ofExcept (read #[two, one])
  require (mixed.chunks 0 == 1 && mixed.chunks 1 == 2 &&
    reversed.chunks 0 == 2 && reversed.chunks 1 == 1)
    "the reader changed a slot's chunk count or order"
  let self := (slot.setObjVal! "width" (toJson (2 : Nat))).setObjVal! "kind" (toJson "self")
  reject (read #[self, self.setObjVal! "numChunks" (toJson (2 : Nat))])
    "accepted Self slots with different chunk counts"
  reject (read #[self, self.setObjVal! "domains" (toJson [15])])
    "accepted Self slots with different candidate domains"
  let selfExternal ← IO.ofExcept (read #[self, two])
  let externalSelf ← IO.ofExcept (read #[two, self])
  require (selfExternal.chunks 0 == 1 && selfExternal.chunks 1 == 2 &&
    selfExternal.ownDomains.map (·.log2) == selfExternal.slots[0].domains.log2s &&
    externalSelf.ownDomains.map (·.log2) == selfExternal.ownDomains.map (·.log2))
    "an External slot changed the Self domains or chunk count"
  let empty ← IO.ofExcept (withSlots step #[] >>= stepMainOf 0 2)
  require (empty.ownDomains.isEmpty) "an empty branch gained candidate domains"
  reject (withSlots step #[one] >>= stepMainOf 2 2) "accepted the wrong slot count"
  let n11 ← circuitSize uniform
  let n12 ← circuitSize mixed
  let n21 ← circuitSize reversed
  require (n12 > n11 && n21 == n12)
    "mixed chunk counts did not change the circuit size consistently"
  IO.println "✓ per-slot chunks: decoding, Self consistency, empty branches, circuit construction"
