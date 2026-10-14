import Pickles.Application.Circuit
import Pickles.KeyDerivation
import Snarky.Kimchi.Backend.CheckedCompile
import Kimchi.Columns

/-!
# Compilation and key certification of an application

Each circuit of an application has a canonical compilation: a branch's step circuit, or the
shared wrap circuit, with inert advice. Advice changes no part of the build:
every execution's compiled circuit is the canonical one, constraints, allocation and retained
cells included (`Circuits.stepBuilt_eq`, `Circuits.wrapBuilt_eq`).

`checkApplication` checks every canonical compilation through the backend's `checkBuilt?` at
its key's index data, then checks the supplied keys against those indices and the shared SRSs.
It returns one `ApplicationCertified` containing the checked Lean indices and their key
correspondence, or the first failure located at its circuit and stage. No imported constraint
system or index comparison is required. A consumer reads the family of indices through
`ApplicationCertified.indices`.

The index data a circuit is checked at has two origins, kept apart. The domain size, its
generator, the masked-row count and the permutation shifts are the circuit's key's. The gate
parameters are the field's: the endomorphism coefficient is the key's, which `Key.endo_eq`
makes the curve's, and the Poseidon matrix is the one the verifier reads for the curve's
proofs, `Kimchi.Verifier.mdsOfParams` of its sponge parameters.

The checks take each compilation in hand, pinned to the canonical one (`StepCompilation`,
`WrapCompilation`), so a driver compiles each circuit once for comparison, checking and
rejection alike; `checkApplicationWith` takes them in hand and `checkApplication` compiles them
itself.

## Main definitions

- `stepCompilation`, `wrapCompilation`: the canonical compilations; `canonicalStep`,
  `canonicalWrap`: the same in hand.
- `IndexData`, `IndexData.ofKey`: the data an index is built at and the data supplied by a key.
- `ApplicationCertified`: checked Lean indices and correspondence of the supplied keys.
- `checkApplicationWith`, `checkApplication`: the checks.
- `ApplicationIndices`, `ApplicationCertified.indices`: the family of certified indices.
- `ApplicationFailure`: a compilation or key rejection located at its circuit.

## Main results

- `Circuits.stepBuilt_eq`, `Circuits.wrapBuilt_eq`: every execution's compiled circuit is the
  canonical compilation.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier
open scoped Kimchi

variable {D : Shape} {L : Layout D}

/-- A branch's public statement: its step circuit's public output. -/
abbrev StepPublic (D : Shape) := StepStatement (UnfVal WrapIPARounds) Fp D.width

/-- The wrap circuit's public statement: its public input. -/
abbrev WrapPublic := StatementPacked StepIPARounds (Type1 Fq) Fq

/-! ## The canonical compilations -/

/-- The type of a branch's compiled step circuit: its statement and retained cells, then the
statement's public copy. -/
abbrev StepBuilt (C : Circuits D L) (b : D.Branch) :=
  Built (KimchiConstraint Fp)
    ((StepStatement (UnfVar WrapIPARounds) (FVar Fp) D.width × C.StepCells b) ×
      StepStatement (UnfVar WrapIPARounds) (FVar Fp) D.width)

/-- The type of the compiled wrap circuit: its retained cells and no public output. -/
abbrev WrapBuilt (C : Circuits D L) := Built (KimchiConstraint Fq) ((Unit × C.WrapCells) × Unit)

/-- A branch's step circuit compiled with inert advice. -/
def stepCompilation (C : Circuits D L) (b : D.Branch) : StepBuilt C b :=
  C.stepBuilt b inertStepAdvice

/-- The shared wrap circuit compiled with inert advice. -/
def wrapCompilation (C : Circuits D L) : WrapBuilt C :=
  C.wrapBuilt inertWrapAdvice

/-- **Every step execution compiles to the canonical compilation.** Advice changes no
constraint, allocation or retained cell. -/
theorem Circuits.stepBuilt_eq (C : Circuits D L) (b : D.Branch)
    (a : C.StepAdvice b) : C.stepBuilt b a = stepCompilation C b :=
  C.stepBuilt_advice_irrel b a inertStepAdvice

/-- **Every wrap execution compiles to the canonical compilation.** -/
theorem Circuits.wrapBuilt_eq (C : Circuits D L) (a : C.WrapAdvice) :
    C.wrapBuilt a = wrapCompilation C :=
  C.wrapBuilt_advice_irrel a inertWrapAdvice

/-- A branch's compilation in hand, pinned to the canonical one. -/
abbrev StepCompilation (C : Circuits D L) (b : D.Branch) :=
  { built : StepBuilt C b // built = stepCompilation C b }

/-- The wrap circuit's compilation in hand, pinned to the canonical one. -/
abbrev WrapCompilation (C : Circuits D L) := { built : WrapBuilt C // built = wrapCompilation C }

/-- A branch's canonical compilation, in hand. -/
def canonicalStep (C : Circuits D L) (b : D.Branch) : StepCompilation C b :=
  ⟨stepCompilation C b, rfl⟩

/-- The wrap circuit's canonical compilation, in hand. -/
def canonicalWrap (C : Circuits D L) : WrapCompilation C :=
  ⟨wrapCompilation C, rfl⟩

/-- A branch's public variables: no input slot, then its statement's public copy. -/
abbrev stepPublicVars (C : Circuits D L) (b : D.Branch) : List Variable :=
  compiledPublicVars (F := Fp) (a := Unit) (b := StepPublic D) (stepCompilation C b)

/-- The wrap circuit's public variables: its statement's input slots, then no output. -/
abbrev wrapPublicVars (C : Circuits D L) : List Variable :=
  compiledPublicVars (F := Fq) (a := WrapPublic) (b := Unit) (wrapCompilation C)

/-! ## Index data -/

/-- The data an index is built at: the domain size and generator, the masked-row count and
the permutation shifts, and the gate parameters, the endomorphism coefficient and the Poseidon
matrix. -/
structure IndexData (F : Type) where
  /-- The domain size. -/
  n : ℕ
  /-- The masked-row count. -/
  zkRows : ℕ
  /-- The domain generator. -/
  omega : F
  /-- The permutation coset shifts. -/
  shifts : Fin permCols → F
  /-- The endomorphism gate's coefficient. -/
  endoBase : F
  /-- The Poseidon gate's matrix. -/
  mds : Kimchi.Gate.Poseidon.Mds F

/-- A key's index data. The domain, generator, masked rows, shifts and endomorphism coefficient
are the key's, the coefficient being the curve's by `Key.endo_eq`; the matrix is the one the
verifier reads for the curve's proofs, `mdsOfParams` of its sponge parameters. -/
def IndexData.ofKey {C : Ipa.KimchiCurve} {nc : ℕ} (K : Key C nc) : IndexData C.ScalarField where
  n := K.cvk.n
  zkRows := K.cvk.zkRows
  omega := K.cvk.omega
  shifts c := K.cvk.shifts[c]
  endoBase := K.cvk.endo
  mds := mdsOfParams C.frSponge.params

/-- A branch's index data: its step key's. -/
def stepIndexData (C : Circuits D L) (b : D.Branch) : IndexData Fp :=
  .ofKey C.wiring.backend.stepKeys[b]

/-- The wrap circuit's index data: the wrap key's. -/
def wrapIndexData (C : Circuits D L) : IndexData Fq :=
  .ofKey C.wiring.backend.wrapKey

/-! ## Checking -/

section Check

variable {F : Type} [Field F] [DecidableEq F] {a avar b bvar β : Type} [CircuitType F a avar]
  [CircuitType F b bvar]

/-- Check a compilation in hand at the supplied index data. -/
private def checkAt (built : Built (KimchiConstraint F) (β × bvar)) (d : IndexData F) :
    Except CheckFailure (CheckedIndex built.constraints
      (compiledPublicVars (F := F) (a := a) (b := b) built) built.nextVar d.n) :=
  checkBuilt? (a := a) (b := b) built d.n d.zkRows d.omega d.endoBase d.mds d.shifts

end Check

/-- A branch's checked index at given index data, from its compilation in hand. -/
def checkStepAt (C : Circuits D L) (b : D.Branch) (built : StepCompilation C b)
    (d : IndexData Fp) :
    Except CheckFailure (CheckedIndex (stepCompilation C b).constraints (stepPublicVars C b)
      (stepCompilation C b).nextVar d.n) :=
  cast (by rw [built.2]) (checkAt (a := Unit) (b := StepPublic D) built.1 d)

/-- The wrap circuit's checked index at given index data, from its compilation in hand. -/
def checkWrapAt (C : Circuits D L) (built : WrapCompilation C) (d : IndexData Fq) :
    Except CheckFailure (CheckedIndex (wrapCompilation C).constraints (wrapPublicVars C)
      (wrapCompilation C).nextVar d.n) :=
  cast (by rw [built.2]) (checkAt (a := WrapPublic) (b := Unit) built.1 d)

/-- A compilation or key rejection, located at its branch or at the wrap circuit. -/
inductive ApplicationFailure (D : Shape) where
  /-- The branch's step circuit was rejected. -/
  | step (b : D.Branch) (failure : CheckFailure)
  /-- The wrap circuit was rejected. -/
  | wrap (failure : CheckFailure)
  /-- A branch's supplied key does not correspond to its compiled index. -/
  | stepKey (b : D.Branch) (failure : KeyFailure)
  /-- The supplied wrap key does not correspond to its compiled index. -/
  | wrapKey (failure : KeyFailure)

/-- Checked Lean compilations and correspondence of the supplied keys to those same indices.
This certificate makes no claim about an imported constraint system. -/
structure ApplicationCertified (C : Circuits D L) where
  /-- Each branch's checked index. -/
  step : (b : D.Branch) → CheckedIndex (stepCompilation C b).constraints (stepPublicVars C b)
    (stepCompilation C b).nextVar (stepIndexData C b).n
  /-- The wrap circuit's checked index. -/
  wrap : CheckedIndex (wrapCompilation C).constraints (wrapPublicVars C)
    (wrapCompilation C).nextVar (wrapIndexData C).n
  /-- Each branch's supplied key commits to its checked index under the shared Step SRS. -/
  stepKey : ∀ b, KeyCorresponds C.setup.stepSrs.σ (step b).index
    C.wiring.backend.stepKeys[b] (D.slots b)
  /-- The supplied Wrap key commits to its checked index under the shared Wrap SRS. -/
  wrapKey : KeyCorresponds C.setup.wrapSrs.σ wrap.index
    C.wiring.backend.wrapKey MaxProofsVerified

/-- Check the compilations in hand and their supplied keys. Every failure is located at its
circuit and at either compilation checking or key correspondence. -/
def checkApplicationWith (C : Circuits D L) (steps : (b : D.Branch) → StepCompilation C b)
    (wrap : WrapCompilation C) : Except (ApplicationFailure D) (ApplicationCertified C) := do
  let step ← finSequence fun b =>
    (checkStepAt C b (steps b) (stepIndexData C b)).mapError (.step b)
  let wrap ← (checkWrapAt C wrap (wrapIndexData C)).mapError .wrap
  let stepKeys ← finSequence fun b =>
    (checkKey? pastaShapeVesta C.setup.stepSrs.σ (step b).index
      C.wiring.backend.stepKeys[b] (D.slots b)).mapError (.stepKey b)
  let wrapKey ← (checkKey? pastaShapePallas C.setup.wrapSrs.σ wrap.index
    C.wiring.backend.wrapKey MaxProofsVerified).mapError .wrapKey
  return ⟨step, wrap, fun b => (stepKeys b).down, wrapKey.down⟩

/-- Compile the application's circuits and certify their supplied keys against those indices. -/
def checkApplication (C : Circuits D L) :
    Except (ApplicationFailure D) (ApplicationCertified C) :=
  checkApplicationWith C (canonicalStep C) (canonicalWrap C)

/-! ## The indices -/

/-- One application's indices: one per branch and the wrap circuit's, each with one public row
per field of its public statement. -/
structure ApplicationIndices (D : Shape) where
  /-- Each branch's domain size. -/
  stepSize : D.Branch → ℕ
  /-- Each branch's index. -/
  step : (b : D.Branch) → Kimchi.Index Fp (stepSize b)
  /-- The wrap circuit's domain size. -/
  wrapSize : ℕ
  /-- The wrap circuit's index. -/
  wrap : Kimchi.Index Fq wrapSize
  /-- A branch's public rows are its statement's fields. -/
  stepPublicCount : ∀ b, (step b).publicCount = CircuitType.size Fp (StepPublic D)
  /-- The wrap circuit's public rows are its statement's fields. -/
  wrapPublicCount : wrap.publicCount = CircuitType.size Fq WrapPublic

/-- The indices a certificate holds, their public counts from the compiled layout. -/
def ApplicationCertified.indices {C : Circuits D L} (checked : ApplicationCertified C) :
    ApplicationIndices D where
  stepSize b := (stepIndexData C b).n
  step b := (checked.step b).index
  wrapSize := (wrapIndexData C).n
  wrap := checked.wrap.index
  stepPublicCount b := (checked.step b).publicCount_eq.trans (by
    simpa only [show CircuitType.size Fp Unit = 0 from rfl, Nat.zero_add] using
      length_compiledPublicVars_compileWith (a := Unit) (b := StepPublic D)
        (C.stepCircuit b inertStepAdvice))
  wrapPublicCount := checked.wrap.publicCount_eq.trans (by
    simpa only [show CircuitType.size Fq Unit = 0 from rfl, Nat.add_zero] using
      length_compiledPublicVars_compileWith (a := WrapPublic) (b := Unit)
        (C.wrapCircuit inertWrapAdvice))

end Pickles.Application
