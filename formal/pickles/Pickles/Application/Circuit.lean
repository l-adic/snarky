import Pickles.Application.Wiring
import Pickles.WrapMain
import Pickles.Linearization.Fp
import Pickles.Linearization.Fq

/-!
# Application circuit construction

Construct each branch's step circuit and the shared wrap circuit from one application's
checked wiring. Rules belong to the application; executions supply advice. Both constructors
retain their internal cells through `Snarky.compileWith` for the circuit capstones.

The backend supplies the Lagrange tables. Their correspondence to the SRS remains a premise
of the verification results, separate from circuit construction.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta

/-- The application's rule circuits, with predecessor statements at each source's size. -/
abbrev Rules (D : Shape) :=
  (b : D.Branch) → D.schema.InputVar →
    CircuitM Fp (KimchiConstraint Fp)
      (((i : D.Slot b) → PrevStatement (D.prevSize b i)) × D.schema.OutputVar)

/-- The protocol parameters and padding values shared by an application's circuits. -/
structure Setup where
  /-- The SRS for wrap-proof verification. -/
  wrap : Srs IpaPallas.curve
  /-- The SRS for step-proof verification. -/
  step : Srs IpaVesta.curve
  /-- The wrap SRS has the protocol's wrap round count. -/
  wrapRounds : wrap.σ.k = WrapIPARounds
  /-- The step SRS has the protocol's step round count. -/
  stepRounds : step.σ.k = StepIPARounds
  /-- The padding commitment for a slot's old accumulators. -/
  dummySg : IpaPallas.curve.Point
  /-- The padding entry for a branch's step statement. -/
  dummyUnf : UnfVal WrapIPARounds
  /-- The padding challenges for wrap messages. -/
  dummy : Vector Fq WrapIPARounds

/-- One application's circuit data, with a fixed rule for each branch. -/
structure Circuits (D : Shape) (L : Layout D) where
  /-- The SRSs and padding constants. -/
  setup : Setup
  /-- The checked keys, domains and source interfaces. -/
  wiring : Wiring D L
  /-- Each branch's rule, at the application's common input and output schema. -/
  rules : Rules D
  /-- The backend's public-input bases for each step domain. -/
  stepLagrange : Nat →
    Vector (Vector IpaVesta.curve.Point wiring.backend.stepChunks)
      (CircuitType.size Fp (StepStatement (UnfVal WrapIPARounds) Fp D.width))

variable {D : Shape} {L : Layout D}

private instance (D : Shape) : NeZero D.branches := ⟨Nat.ne_of_gt D.branches_pos⟩

private theorem build_bind_congr {F c α β : Type}
    {m m' : CircuitM F c α} {k k' : α → CircuitM F c β}
    (hm : ∀ nv, build m nv = build m' nv)
    (hk : ∀ x nv, build (k x) nv = build (k' x) nv) (nv : Nat) :
    build (m >>= k) nv = build (m' >>= k') nv := by
  simp only [build_bind, hm, hk]

/-- A branch's advice, with widths and chunk counts resolved from its slot sources. -/
abbrev Circuits.StepAdvice (C : Circuits D L) (b : D.Branch) :=
  StepMainAdvice (D.slots b) D.width (SlotSource.widths D.width (C.wiring.sources b))
    1 (C.wiring.sourceChunks b) WrapIPARounds StepIPARounds D.schema.Input

/-- The statement and internal cells retained by a branch's step circuit. -/
abbrev Circuits.StepCells (C : Circuits D L) (b : D.Branch) :=
  StepMainOut (D.slots b) D.width (SlotSource.widths D.width (C.wiring.sources b))
    (D.prevSize b) D.schema.size 1 (C.wiring.sourceChunks b) WrapIPARounds StepIPARounds

/-- The shared wrap circuit's advice, including its witnessed branch selection. -/
abbrev Circuits.WrapAdvice (C : Circuits D L) :=
  WrapMainAdvice D.width C.wiring.backend.stepChunks WrapIPARounds StepIPARounds
    (L.wrapWidths.map Fin.val).sum

/-- The shared wrap circuit's finalization and verification cells. -/
abbrev Circuits.WrapCells (C : Circuits D L) :=
  WrapMainFinalizeOut D.branches D.width C.wiring.backend.stepChunks
    WrapIPARounds L.wrapWidths ×
  WrapMainVerifyOut D.width C.wiring.backend.stepChunks WrapIPARounds StepIPARounds

/-- Every resolved source fits the protocol's accumulator bound. -/
theorem Circuits.source_bound (C : Circuits D L) (b : D.Branch) (i : D.Slot b) :
    SlotSource.widths D.width (C.wiring.sources b) i ≤ MaxProofsVerified := by
  rw [SlotSource.widths, C.wiring.source_width]
  exact (L.slotWidth_le_wrapWidths b i).trans
    (Nat.le_of_lt_succ (L.wrapWidths[D.paddedSlot b i]).isLt)

/-- A branch's step circuit, with its public statement and internal cells retained. -/
def Circuits.stepCircuit (C : Circuits D L) (V : Valuation Fp)
    (b : D.Branch) (advice : C.StepAdvice b) :
    Unit → CircuitM Fp (Builder V (KimchiConstraint Fp))
      (StepStatement (UnfVar WrapIPARounds) (FVar Fp) D.width × C.StepCells b) :=
  haveI : CheckedType Fp (Builder V (KimchiConstraint Fp))
      D.schema.Input D.schema.InputVar := D.schema.inputCheck
  stepMainCircuit (outVal := D.schema.Output)
    (C.wiring.sources b) (C.source_bound b) C.setup.wrap.σ.h
    (fun i => FopParams.of IpaVesta.curve (C.wiring.sourceChunks b i)
      StepIPARounds Linearization.fpTokens)
    C.wiring.backend.stepDomains.list (constPt C.setup.dummySg) C.setup.dummyUnf
    (C.rules b) advice

/-- The shared wrap circuit, with no public output and both blocks' cells retained. -/
def Circuits.wrapCircuit (C : Circuits D L) (V : Valuation Fq)
    (advice : C.WrapAdvice) :
    StatementPacked StepIPARounds (Type1 (FVar Fq)) (FVar Fq) →
      CircuitM Fq (Builder V (KimchiConstraint Fq)) (Unit × C.WrapCells) :=
  wrapMainCircuit (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
    D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
    C.wiring.pins C.stepLagrange C.setup.step.σ.h C.setup.dummy L.wrapWidths advice

/-- Compile a branch's step circuit, keeping its statement and internal cells. -/
def Circuits.stepBuilt (C : Circuits D L) (V : Valuation Fp)
    (b : D.Branch) (advice : C.StepAdvice b) :=
  compileWith (a := Unit) (b := StepStatement (UnfVal WrapIPARounds) Fp D.width)
    (C.stepCircuit V b advice)

/-- Compile the shared wrap circuit, keeping its internal cells. -/
def Circuits.wrapBuilt (C : Circuits D L) (V : Valuation Fq) (advice : C.WrapAdvice) :=
  compileWith (a := StatementPacked StepIPARounds (Type1 Fq) Fq) (b := Unit)
    (C.wrapCircuit V advice)

/-- Changing step advice preserves the compiled constraints, allocation and retained cells. -/
theorem Circuits.stepBuilt_advice_irrel (C : Circuits D L) (V : Valuation Fp)
    (b : D.Branch) (a a' : C.StepAdvice b) :
    C.stepBuilt V b a = C.stepBuilt V b a' := by
  unfold stepBuilt compileWith compileWithBody stepCircuit stepMainCircuit stepMain
  simp only [map_eq_pure_bind]
  repeat' first | rfl | apply build_bind_congr | intro

/-- Replacing a rule by one with the same built body preserves the compiled step circuit. -/
theorem Circuits.stepBuilt_rules_congr (C : Circuits D L) (V : Valuation Fp)
    (rules : Rules D) (b : D.Branch) (advice : C.StepAdvice b)
    (h : ∀ x nv, build (C.rules b x) nv = build (rules b x) nv) :
    C.stepBuilt V b advice = { C with rules }.stepBuilt V b advice := by
  unfold stepBuilt compileWith compileWithBody stepCircuit stepMainCircuit stepMain
  simp only [map_eq_pure_bind]
  repeat' first | exact h _ _ | rfl | apply build_bind_congr | intro

private theorem build_wrapMainFinalize_advice_irrel (C : Circuits D L) (V : Valuation Fq)
    (a a' : C.WrapAdvice) (branchData : FVar Fq) (nv : Nat) :
    build (wrapMainFinalize (c := Builder V (KimchiConstraint Fq))
      (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
      D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.setup.dummy L.wrapWidths a branchData) nv =
    build (wrapMainFinalize (c := Builder V (KimchiConstraint Fq))
      (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
      D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.setup.dummy L.wrapWidths a' branchData) nv := by
  unfold wrapMainFinalize
  repeat' first
    | (apply build_bind_congr (fun _ => rfl); intro _ _)
    | rfl

private theorem build_wrapMainVerify_advice_irrel (C : Circuits D L) (V : Valuation Fq)
    (a a' : C.WrapAdvice)
    (stmt : StatementPacked StepIPARounds (Type1 (FVar Fq)) (FVar Fq))
    (hd : WrapMainFinalizeOut D.branches D.width C.wiring.backend.stepChunks
      WrapIPARounds L.wrapWidths) (nv : Nat) :
    build (wrapMainVerify (c := Builder V (KimchiConstraint Fq))
      (stepDomainLog2s C.wiring.stepKeys) C.stepLagrange C.setup.step.σ.h
      C.setup.dummy L.wrapWidths a stmt hd) nv =
    build (wrapMainVerify (c := Builder V (KimchiConstraint Fq))
      (stepDomainLog2s C.wiring.stepKeys) C.stepLagrange C.setup.step.σ.h
      C.setup.dummy L.wrapWidths a' stmt hd) nv := by
  unfold wrapMainVerify
  repeat' first
    | (apply build_bind_congr (fun _ => rfl); intro _ _)
    | rfl

/-- Changing wrap advice preserves the compiled constraints, allocation and retained cells. -/
theorem Circuits.wrapBuilt_advice_irrel (C : Circuits D L) (V : Valuation Fq)
    (a a' : C.WrapAdvice) :
    C.wrapBuilt V a = C.wrapBuilt V a' := by
  unfold wrapBuilt compileWith compileWithBody wrapCircuit wrapMainCircuit wrapMain
  simp only [map_eq_pure_bind]
  apply build_bind_congr (fun _ => rfl)
  intro _ nv
  apply build_bind_congr ?_ (fun _ _ => rfl)
  intro nv
  apply build_bind_congr ?_ (fun _ _ => rfl)
  intro nv
  apply build_bind_congr (build_wrapMainFinalize_advice_irrel C V a a' _)
  intro hd nv
  exact build_bind_congr (build_wrapMainVerify_advice_irrel C V a a' _ hd)
    (fun _ _ => rfl) nv

end Pickles.Application
