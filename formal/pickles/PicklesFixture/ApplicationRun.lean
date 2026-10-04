import PicklesFixture.ApplicationCircuit
import PicklesFixture.Compare
import Pickles.Application.Run

/-!
# Runs of assembled applications

The selected applications generate both circuits through `Application.Circuits`. Cached
advice supplies their witnesses. Each run also supplies the existing capstone harness,
after deciding exact equality of the compiled constraints, variable count and public cells.
Typed satisfying runs are retained for the application capstones and handover checks. The
constraint comparison also connects the declared schema to the flat rule encodings used by
the independent cache checks.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi Pickles Pickles.Application Bulletproof
open CompElliptic.Fields.Pasta Kimchi.Fixture Kimchi.Fixture.PS

deriving instance DecidableEq for CVar
deriving instance DecidableEq for Basic
deriving instance DecidableEq for AffinePoint
deriving instance DecidableEq for AddComplete
deriving instance DecidableEq for PoseidonConstraint
deriving instance DecidableEq for ScaleRound
deriving instance DecidableEq for EndoScalarRound
deriving instance DecidableEq for EndoMulRound
deriving instance DecidableEq for EndoMul
deriving instance DecidableEq for KimchiConstraint

-- Cross-library deriving appends the owning library name to these generated identifiers.
attribute [nolint defsWithUnderscore] instDecidableEqCVar_picklesFixture
  instDecidableEqCVar_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqBasic_picklesFixture
  instDecidableEqBasic_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqAffinePoint_picklesFixture
  instDecidableEqAffinePoint_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqAddComplete_picklesFixture
  instDecidableEqAddComplete_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqPoseidonConstraint_picklesFixture
  instDecidableEqPoseidonConstraint_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqScaleRound_picklesFixture
  instDecidableEqScaleRound_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqEndoScalarRound_picklesFixture
  instDecidableEqEndoScalarRound_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqEndoMulRound_picklesFixture
  instDecidableEqEndoMulRound_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqEndoMul_picklesFixture
  instDecidableEqEndoMul_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqKimchiConstraint_picklesFixture
  instDecidableEqKimchiConstraint_picklesFixture.decEq

/-- A run with its constraint system and public cells, independent of its internal cell type. -/
structure CircuitRun (p : Nat) [Fact p.Prime] where
  /-- The prover's valuation. -/
  V : Valuation (ZMod p)
  /-- The constraints compiled by the application constructor. -/
  constraints : List (KimchiConstraint (ZMod p))
  /-- The decided source satisfaction predicate. -/
  holds : Decidable (∀ con ∈ constraints, ConstraintHolds.Holds V con)
  /-- The final allocation counter. -/
  nextVar : Nat
  /-- Public variable identifiers, in input/output order. -/
  pubVars : List Nat
  /-- Whether the lowered witness satisfies its index. -/
  satisfies : Bool
  /-- The public values read from the witness. -/
  pub : List (ZMod p)

private def fromRun {p : Nat} [Fact p.Prime] {a av b bv α : Type}
    [A : CircuitType (ZMod p) a av]
    [∀ V : Valuation (ZMod p), CheckedType (ZMod p) (Builder V (KimchiConstraint (ZMod p))) a av]
    [CircuitType (ZMod p) b bv]
    {body : (V : Valuation (ZMod p)) → av →
      CircuitM (ZMod p) (Builder V (KimchiConstraint (ZMod p))) (bv × α)}
    (r : MainRun (a := a) (b := b) body) : CircuitRun p :=
  let built := compileWith (a := a) (b := b) (body r.V)
  { V := r.V, constraints := built.constraints, holds := r.holds
    nextVar := built.nextVar
    pubVars := (allocRange 0 A.size).toList ++ bundleVars (F := ZMod p) (b := b) built.result.2
    satisfies := r.satisfies, pub := r.pub }

/-- Transport a run to the capstone's body after checking the complete compiled system. -/
def CircuitRun.atBody {p : Nat} [Fact p.Prime] {a av b bv α : Type}
    [A : CircuitType (ZMod p) a av]
    [∀ V : Valuation (ZMod p), CheckedType (ZMod p) (Builder V (KimchiConstraint (ZMod p))) a av]
    [CircuitType (ZMod p) b bv] (r : CircuitRun p)
    (body : (V : Valuation (ZMod p)) → av →
      CircuitM (ZMod p) (Builder V (KimchiConstraint (ZMod p))) (bv × α)) :
    IO (MainRun (a := a) (b := b) body) := do
  let built := compileWith (a := a) (b := b) (body r.V)
  unless r.nextVar == built.nextVar && r.pubVars ==
      (allocRange 0 A.size).toList ++ bundleVars (F := ZMod p) (b := b) built.result.2 do
    throw (IO.userError "application and capstone body disagree on allocation or public cells")
  if h : r.constraints = built.constraints then
    IO.println "    application circuit = capstone circuit (constraints, allocation, public cells)"
    return {
      V := r.V, holds := h ▸ r.holds, satisfies := r.satisfies, pub := r.pub
      result := built.result, result_eq := rfl }
  else throw (IO.userError "application and capstone body have different constraints")

/-- A canonical satisfying step run and its cache routing information. -/
structure StepEntry {D : Shape} {L : Layout D} (C : Circuits D L) where
  /-- The selected branch. -/
  branch : D.Branch
  /-- The application execution, with rule and main advice erased from its build. -/
  run : Pickles.Application.StepRun C branch
  /-- The proof produced by this step circuit. -/
  proof : Cache.Entry CS
  /-- The ordered predecessor proofs used by this rule. -/
  previous : Vector StepPrev (D.slots branch)

/-- A canonical satisfying wrap run and its cached step/wrap pair. -/
structure WrapEntry {D : Shape} {L : Layout D} (C : Circuits D L) where
  /-- The selected step branch. -/
  branch : D.Branch
  /-- The application execution. -/
  run : Pickles.Application.WrapRun C
  /-- The step proof wrapped by this execution. -/
  step : Cache.Entry CS
  /-- The proof produced by this wrap circuit. -/
  proof : Cache.Entry CW

/-- An assembled fixture application retaining the typed runs generated by its runner. -/
structure Context (S : Setup) (t : Tag) where
  /-- The checked application artifacts. -/
  assembled : Assembled t.shape
  /-- The fixture path used in reports. -/
  name : String
  /-- Satisfying executions of the application branches. -/
  steps : IO.Ref (List (StepEntry (assembled.circuits S (fun _ => none))))
  /-- Satisfying executions of the shared wrap circuit. -/
  wraps : IO.Ref (List (WrapEntry (assembled.circuits S (fun _ => none))))

/-- Executable circuits of a selected application, with its typed description captured. -/
structure Runner where
  /-- Run a declared step branch on its cached proof and predecessors. -/
  step : Nat → Cache.Entry CS → Array StepPrev → IO (CircuitRun PALLAS_BASE_CARD)
  /-- Run the shared wrap circuit on its cached step/wrap pair and predecessors. -/
  wrap : Nat → Cache.Entry CS → Cache.Entry CW → Array StepPrev →
    IO (CircuitRun PALLAS_SCALAR_CARD)

private def checkCompiled {D : Shape} (A : Assembled D) (S : Setup)
    (name : String) (tag : Json) : IO Unit := do
  let C := A.circuits S (fun _ => none)
  let branches ← IO.ofExcept ((tag.getObjVal? "branches") >>= Json.getArr?)
  let report (label : String) (checks : List (String × Bool)) : IO Unit := do
    let bad := checks.filter (!·.2)
    unless bad.isEmpty do
      throw (IO.userError s!"{name} {label}: {String.intercalate ", " (bad.map (·.1))}")
    IO.println s!"✓ {name} {label}: application circuit matches dumped constraint system"
    (← IO.getStdout).flush
  for b in List.finRange D.branches do
    let some branch := branches[b.val]? | throw (IO.userError "a declared branch is missing")
    let raw : Raw Fp ← IO.ofExcept do
      parseGates (← (← branch.getObjVal? "stepMain").getObjVal? "circuit")
    report s!"step {b.val}" (compareWith (a := Unit)
      (b := StepStatement (UnfVal WrapIPARounds) Fp D.width)
      (fun u => Prod.fst <$> C.stepCircuit (fun _ => 0) b inertStepAdvice u) raw)
  let raw : Raw Fq ← IO.ofExcept do
    parseGates (← (← tag.getObjVal? "wrapMain").getObjVal? "circuit")
  report "wrap" (compareWith (a := StatementPacked StepIPARounds (Type1 Fq) Fq) (b := Unit)
    (fun s => Prod.fst <$> C.wrapCircuit (fun _ => 0) inertWrapAdvice s) raw)

private def runStep {D : Shape} (A : Assembled D) (S : Setup) (branch : Nat)
    (proof : Cache.Entry CS) (previous : Array StepPrev)
    (saved : IO.Ref (List (StepEntry (A.circuits S (fun _ => none))))) :
    IO (CircuitRun PALLAS_BASE_CARD) := do
  let b : D.Branch ← if h : branch < D.branches then pure ⟨branch, h⟩
    else throw (IO.userError "step branch outside application")
  let prevs : Vector StepPrev (D.slots b) ←
    if h : previous.size = D.slots b then pure ⟨previous, h⟩
    else throw (IO.userError "predecessor count differs from application branch")
  let some rule := proof.rule | throw (IO.userError "the step proof has no rule witness")
  unless rule.values.size == (A.rules b).dump.allocated do
    throw (IO.userError "the rule's cached allocation count differs from its body")
  let vals := fun _ : D.Branch => some rule.values
  let C := A.circuits S vals
  let advice ← IO.ofExcept (stepAdviceOf D.width (SlotSource.widths D.width (C.wiring.sources b))
    (C.wiring.sourceChunks b) C.wiring.backend.wrapKey.cvk proof prevs)
  let r ← runMain fpSide (a := Unit) (b := StepStatement (UnfVal WrapIPARounds) Fp D.width)
    (fun V => C.stepCircuit V b advice) ()
  -- The executed rule's values and all main advice erase from the canonical build.
  have fixed := (A.stepBuilt_ruleAdvice_irrel S vals (fun _ => none) r.V b advice).trans
    ((A.circuits S (fun _ => none)).stepBuilt_advice_irrel r.V b advice inertStepAdvice)
  let result := fromRun r
  let holds : Decidable (∀ con ∈
      ((A.circuits S (fun _ => none)).stepBuilt r.V b inertStepAdvice).constraints,
      ConstraintHolds.Holds r.V con) := congrArg Built.constraints fixed ▸ result.holds
  match holds with
  | .isFalse _ => throw (IO.userError "application step constraints do not hold")
  | .isTrue h => saved.modify fun rs =>
      { branch := b, run := ⟨r.V, inertStepAdvice, h⟩, proof, previous := prevs } :: rs
  return { result with
    constraints := ((A.circuits S (fun _ => none)).stepBuilt r.V b inertStepAdvice).constraints
    holds := congrArg Built.constraints fixed ▸ result.holds }

private def runWrap {D : Shape} (A : Assembled D) (S : Setup) (pad : WrapPadding)
    (branch : Nat) (proof : Cache.Entry CS) (wrapped : Cache.Entry CW)
    (previous : Array StepPrev)
    (saved : IO.Ref (List (WrapEntry (A.circuits S (fun _ => none))))) :
    IO (CircuitRun PALLAS_SCALAR_CARD) := do
  let b : D.Branch ← if h : branch < D.branches then pure ⟨branch, h⟩
    else throw (IO.userError "wrap branch outside application")
  let prevs : Vector StepPrev (D.slots b) ←
    if h : previous.size = D.slots b then pure ⟨previous, h⟩
    else throw (IO.userError "predecessor count differs from application branch")
  let C := A.circuits S (fun _ => none)
  let pins := (C.wiring.pins.map fun p => p[b]).toList
  let prevs ← IO.ofExcept (wrapPrevsOf D.width pins wrapped prevs)
  let advice ← IO.ofExcept (wrapMainAdviceOf C.wiring.backend.stepChunks branch
    A.layout.wrapWidths pad A.dummy proof prevs)
  let inp ← IO.ofExcept (wrapInputOf wrapped)
  let r ← runMain fqSide (a := StatementPacked StepIPARounds (Type1 Fq) Fq) (b := Unit)
    (fun V => C.wrapCircuit V advice) inp
  have fixed := C.wrapBuilt_advice_irrel r.V advice inertWrapAdvice
  let result := fromRun r
  let holds : Decidable (∀ con ∈ (C.wrapBuilt r.V inertWrapAdvice).constraints,
      ConstraintHolds.Holds r.V con) := congrArg Built.constraints fixed ▸ result.holds
  match holds with
  | .isFalse _ => throw (IO.userError "application wrap constraints do not hold")
  | .isTrue h => saved.modify fun rs =>
      { branch := b, run := ⟨r.V, inertWrapAdvice, h⟩, step := proof, proof := wrapped } :: rs
  return { result with
    constraints := (C.wrapBuilt r.V inertWrapAdvice).constraints
    holds := congrArg Built.constraints fixed ▸ result.holds }

private def checkMixed {D : Shape} (A : Assembled D) (S : Setup) : IO Unit := do
  let domains : KnownDomains 2 :=
    { log2s := [17]
      log2s_le := by simp; decide
      log2s_zkRows := by simp [zkRowsOf] }
  let imports (t : Fin D.imports.size) : CircuitInterface D.imports[t] :=
    { A.wiring.imports t with
      stepChunks := 2, stepDomains := domains
      stepDomains_nonempty := by simp [domains]
      stepChunkDomains := by simp [domains, Kimchi.Verifier.chunkCount, StepIPARounds] }
  let C := A.circuits S (fun _ => none)
  let mixed : Circuits D A.layout := { C with wiring := { A.wiring with imports } }
  let b : D.Branch ← if h : 1 < D.branches then pure ⟨1, h⟩
    else throw (IO.userError "the mixed-chunk example requires the recursive branch")
  let built : Built (KimchiConstraint Fp) ((_ × mixed.StepCells b) × _) :=
    mixed.stepBuilt (fun _ => 0) b inertStepAdvice
  let counts := (List.finRange (D.slots b)).map fun i =>
    ((built.result.1.2.slots i).evals.pub.zeta.toArray.size, mixed.wiring.sourceChunks b i)
  unless counts == [(2, 2), (1, 1)] do
    throw (IO.userError "the application constructor changed mixed source chunk counts")
  unless built.constraints.length > (C.stepBuilt (fun _ => 0) b inertStepAdvice).constraints.length
      do throw (IO.userError "the larger source did not enlarge the assembled step circuit")
  IO.println "✓ synthetic application: mixed 2/1 chunks reach the allocated step cells"
  (← IO.getStdout).flush

/-- Check the assembled systems and retain the typed runs alongside executable runners. -/
def runners (dir : System.FilePath) (apps : List String) (S : Setup) :
    IO (List (String × Runner) × List ((t : Tag) × Context S t)) := do
  let contexts ← selected dir apps fun t A name tag => do
    checkCompiled A S name tag
    if name = "HeterogeneousPrevs/application" then checkMixed A S
    let pad ← IO.ofExcept (WrapPadding.ofJson (← IO.ofExcept (tag.getObjVal? "wrapMain")))
    let steps ← IO.mkRef []
    let wraps ← IO.mkRef []
    let context : Context S t := ⟨A, name, steps, wraps⟩
    let runner : Runner :=
      { step := fun b p ps => runStep A S b p ps steps
        wrap := fun b p q ps => runWrap A S pad b p q ps wraps }
    return (runner, (⟨t, context⟩ : (t : Tag) × Context S t))
  return (contexts.map fun (name, r, _) => (name, r), contexts.map fun (_, _, c) => c)

end PicklesFixture.Application
