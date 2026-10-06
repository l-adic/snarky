import Pickles.Application.Circuit
import PicklesFixture.Rule
import PicklesFixture.Advice

/-!
# Application circuits from checked rule replays

Adapt each rule's flattened encodings to its declared application schema, after checking
all field and predecessor counts. Cached witness advice changes no built cell or constraint.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi Pickles Pickles.Application Bulletproof
open CompElliptic.Fields.Pasta

/-- A dumped rule whose input, output and predecessor schemas match its declared branch. -/
structure CheckedRule (D : Shape) (b : D.Branch) where
  /-- The recorded rule operations and output expressions. -/
  dump : RuleDump
  /-- The input encoding has the declared size. -/
  inputSize : dump.inputSize = CircuitType.size Fp D.schema.Input
  /-- The output encoding has the declared size. -/
  outputSize : dump.publicOutput.size = CircuitType.size Fp D.schema.Output
  /-- The rule returns the declared number of predecessors. -/
  slots : D.slots b = dump.prevs.size
  /-- Each predecessor has its source application's statement size. -/
  prevSizes : ∀ i : D.Slot b, dump.prevs[i.cast slots].1.size = D.prevSize b i

/-- Check a replay against its branch's input, output and predecessor layouts. -/
def CheckedRule.check (D : Shape) (b : D.Branch) (dump : RuleDump) :
    Except String (CheckedRule D b) := do
  let ⟨hi⟩ ← requireProof (dump.inputSize = CircuitType.size Fp D.schema.Input)
    "the rule's input differs from the application schema"
  let ⟨ho⟩ ← requireProof (dump.publicOutput.size = CircuitType.size Fp D.schema.Output)
    "the rule's output differs from the application schema"
  let ⟨hn⟩ ← requireProof (D.slots b = dump.prevs.size)
    "the rule's predecessor count differs from its declared branch"
  let ⟨hs⟩ ← requireProof (∀ i : D.Slot b, dump.prevs[i.cast hn].1.size = D.prevSize b i)
    "a rule predecessor's statement differs from the declared source schema"
  return ⟨dump, hi, ho, hn, hs⟩

/-- Replay a rule through its declared input, output and predecessor encodings. -/
private def CheckedRule.main {D : Shape} {b : D.Branch} (r : CheckedRule D b)
    (vals : Option (Array Fp)) (x : D.schema.InputVar) :
    CircuitM Fp (KimchiConstraint Fp)
      (((i : D.Slot b) → PrevStatement (D.prevSize b i)) × D.schema.OutputVar) := do
  let (prevs, output) ← replayRule r.dump vals
    ((CircuitType.varToFields (F := Fp) (val := D.schema.Input) x).cast r.inputSize.symm)
  return ((fun i =>
    { appState := (prevs (i.cast r.slots)).appState.cast (r.prevSizes i)
      mustVerify := (prevs (i.cast r.slots)).mustVerify }),
    CircuitType.fieldsToVar (F := Fp) (val := D.schema.Output) (output.cast r.outputSize))

private theorem CheckedRule.build_main_irrel {D : Shape} {b : D.Branch}
    (r : CheckedRule D b) (vals vals' : Option (Array Fp)) (x : D.schema.InputVar) (nv : Nat) :
    build (r.main vals x) nv = build (r.main vals' x) nv := by
  simp only [main, build_bind, build_replayRule_irrel r.dump vals vals']

/-- An application assembled from backend artifacts and checked rule dumps. -/
structure Assembled (D : Shape) where
  /-- The checked application layout. -/
  layout : Layout D
  /-- The application and imported backend interfaces. -/
  wiring : Wiring D layout
  /-- Each rule checked against the declared schema and sources. -/
  rules : (b : D.Branch) → CheckedRule D b
  /-- The backend's step-domain public-input bases. -/
  stepLagrange : Nat → Vector (Vector IpaVesta.curve.Point wiring.backend.stepChunks)
    (CircuitType.size Fp (StepStatement (UnfVal WrapIPARounds) Fp D.width))

/-- Construct the application's circuits, with optional cached advice for each fixed rule. -/
def Assembled.circuits {D : Shape} (A : Assembled D) (S : Setup)
    (vals : D.Branch → Option (Array Fp)) : Circuits D A.layout where
  setup := S
  wiring := A.wiring
  rules b := (A.rules b).main (vals b)
  stepLagrange := A.stepLagrange

/-- The replayed application rule stays fixed when its cached witness values change. -/
theorem Assembled.stepBuilt_ruleAdvice_irrel {D : Shape} (A : Assembled D) (S : Setup)
    (vals vals' : D.Branch → Option (Array Fp)) (V : Valuation Fp) (b : D.Branch)
    (adv : (A.circuits S vals).StepAdvice b) :
    (A.circuits S vals).stepBuilt V b adv = (A.circuits S vals').stepBuilt V b adv := by
  exact Circuits.stepBuilt_rules_congr (A.circuits S vals) V
    (fun b => (A.rules b).main (vals' b)) b adv
    (fun x nv => (A.rules b).build_main_irrel _ _ x nv)

end PicklesFixture.Application
