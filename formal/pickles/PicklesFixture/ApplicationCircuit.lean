import PicklesFixture.ApplicationWiring
import PicklesFixture.Application
import Pickles.Application.Circuit
import PicklesFixture.Rule
import PicklesFixture.Advice

/-!
# Application circuits against tag dumps

Assemble circuits from independently declared application shapes, backend keys and tables,
and replayed rules. A rule's dumped field vectors are adapted to the declared schema only
after their sizes have been checked. Cached rule advice changes no built cell or constraint.

The selected corpus covers Self recursion, heterogeneous External statements and a two-chunk
External source. Slot routing and circuit dimensions come from the application declarations.
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

private def checkedRuleOf (D : Shape) (b : D.Branch) (j : Json) :
    Except String (CheckedRule D b) := do
  let dump ← RuleDump.ofJson j
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
  /-- The wrap message's padding challenges. -/
  dummy : Vector Fq WrapIPARounds

/-- Construct the application's circuits, with optional cached advice for each fixed rule. -/
def Assembled.circuits {D : Shape} (A : Assembled D) (S : Setup)
    (vals : D.Branch → Option (Array Fp)) : Circuits D A.layout where
  setup := { S with dummy := A.dummy }
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

private def stepTablesOf {D : Shape} {L : Layout D} (W : Wiring D L) (j : Json) :
    Except String (Nat → Vector (Vector IpaVesta.curve.Point W.backend.stepChunks)
      (CircuitType.size Fp (StepStatement (UnfVal WrapIPARounds) Fp D.width))) := do
  let c ← constantsOf "wrapMain" (← j.getObjVal? "wrapMain")
  let branches ← (← c.getObjVal? "branches").getArr?
  let tables ← branches.mapM fun branch => do
    let table ← FixtureKit.parseArrOf (chunksOf IpaVesta.curve W.backend.stepChunks)
      (← branch.getObjVal? "lagrange")
    if h : table.size = CircuitType.size Fp (StepStatement (UnfVal WrapIPARounds) Fp D.width)
    then return (⟨table, h⟩ : Vector _ _)
    else throw "a step-domain Lagrange table has the wrong public-input size"
  if h : tables.size = D.branches then
    let tables : Vector _ D.branches := ⟨tables, h⟩
    let first : D.Branch := ⟨0, D.branches_pos⟩
    for b in List.finRange D.branches do
      for b' in List.finRange D.branches do
        unless W.stepKeys[b].domainLog2 != W.stepKeys[b'].domainLog2 || tables[b] == tables[b'] do
          throw "step Lagrange tables disagree at the same domain"
    return fun d => tables[(stepDomainLog2s W.stepKeys).toList.idxOf d]?.getD tables[first]
  else throw "the step-domain table count differs from the declared branches"

/-- Assemble one declared application, checking its exported configuration against the dump. -/
def assembleOf (D : Shape)
    (imports : (t : Fin D.imports.size) → CircuitInterface D.imports[t])
    (tables : List (Nat × SlotLagrange 1 StepIPARounds)) (name : String) (j : Json) :
    Except String (Assembled D) := do
  let ⟨layout⟩ ← Layout.check D
  let backend ← backendOf D tables j
  let wiring ← Wiring.assemble layout backend imports
  checkWiring wiring name j
  let branches ← (← j.getObjVal? "branches").getArr?
  let rules ← finSequence fun b : D.Branch => do
    let some branch := branches[b.val]? | throw "a declared branch is missing"
    checkedRuleOf D b (← branch.getObjVal? "rule")
  let c ← constantsOf "wrapMain" (← j.getObjVal? "wrapMain")
  let ds ← FixtureKit.parseArrOf FixtureKit.parseZMod (← c.getObjVal? "dummy")
  let dummy ← if h : ds.size = WrapIPARounds then pure (⟨ds, h⟩ : Vector Fq WrapIPARounds)
    else throw "the wrap padding has the wrong round count"
  return { layout, wiring, rules, stepLagrange := ← stepTablesOf wiring j, dummy }

/-- The five independently described tags in the application fixture corpus. -/
inductive Tag where
  | chain | child | parent | chunks | recurse
  deriving DecidableEq

/-- A fixture tag's fixed application description. -/
def Tag.shape : Tag → Shape
  | .chain => twoPhaseChain
  | .child => heterogeneousChild
  | .parent => heterogeneousPrevs (Layout.export (D := heterogeneousChild) ⟨by decide⟩)
  | .chunks => chunksChild
  | .recurse => recurseOverChunks (Layout.export (D := chunksChild) ⟨by decide⟩)

/-- Assemble the selected fixture applications in import order; missing requested files fail. -/
def selected {α : Type} (dir : System.FilePath) (apps : List String)
    (f : (t : Tag) → Assembled t.shape → String → Json → IO α) : IO (List (String × α)) := do
  let names :=
    (if "TwoPhaseChain" ∈ apps then ["TwoPhaseChain/two_phase_chain"] else []) ++
    (if "HeterogeneousPrevs" ∈ apps then
      ["HeterogeneousPrevs/child", "HeterogeneousPrevs/application"] else []) ++
    (if "RecurseOverChunks" ∈ apps then
      ["RecurseOverChunks/chunks2", "RecurseOverChunks/recurse"] else [])
  let tags ← names.mapM fun name => do
    let tag ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / s!"{name}.json")))
    return (name, tag)
  let tables ← IO.ofExcept (wrapTablesOf (tags.map (·.2)).toArray)
  let get (name : String) : IO Json :=
    match tags.lookup name with
    | some j => pure j
    | none => throw (IO.userError s!"missing selected tag {name}")
  let make (D : Shape) (imports : (t : Fin D.imports.size) → CircuitInterface D.imports[t])
      (name : String) : IO (Assembled D) := do
    IO.ofExcept (assembleOf D imports tables name (← get name))
  let mut result := []
  if "TwoPhaseChain" ∈ apps then
    let name := "TwoPhaseChain/two_phase_chain"
    let A ← make twoPhaseChain (fun t => Fin.elim0 t) name
    result := result ++ [(name, ← f .chain A name (← get name))]
  if "HeterogeneousPrevs" ∈ apps then
    let child ← make heterogeneousChild (fun t => Fin.elim0 t) "HeterogeneousPrevs/child"
    let D := heterogeneousPrevs child.layout.export
    let A ← make D (oneImport child.wiring.export) "HeterogeneousPrevs/application"
    for (name, action) in
        [("HeterogeneousPrevs/child", f .child child),
         ("HeterogeneousPrevs/application", f .parent A)] do
      result := result ++ [(name, ← action name (← get name))]
  if "RecurseOverChunks" ∈ apps then
    let child ← make chunksChild (fun t => Fin.elim0 t) "RecurseOverChunks/chunks2"
    let D := recurseOverChunks child.layout.export
    let A ← make D (oneImport child.wiring.export) "RecurseOverChunks/recurse"
    for (name, action) in
        [("RecurseOverChunks/chunks2", f .chunks child),
         ("RecurseOverChunks/recurse", f .recurse A)] do
      result := result ++ [(name, ← action name (← get name))]
  return result

end PicklesFixture.Application
