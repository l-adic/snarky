import Pickles.Application.Verify
import Kimchi.KeyDerivation
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
It also derives each required Lagrange table once per domain and checks the embedded verifiers'
nondegeneracy premises. It returns one `ApplicationCertified` containing the checked Lean
indices, their key correspondence and the verifier setup, or the first failure located at its
circuit and stage. No imported constraint system or index comparison is required.
A consumer reads the family of indices through
`ApplicationCertified.indices`.

The index data a circuit is checked at has two origins, kept apart. The domain size, its
generator, the masked-row count and the permutation shifts are the circuit's key's. The gate
parameters are the field's: the endomorphism coefficient is the key's, which `KimchiVK.endo_eq`
makes the curve's, and the Poseidon matrix is the one the verifier reads for the curve's
proofs, `Kimchi.Verifier.mdsOfParams` of its sponge parameters.

`checkApplication` takes each compilation in hand, pinned to the canonical one
(`StepCompilation`, `WrapCompilation`), so a driver compiles each circuit once for comparison,
checking and rejection alike.

## Main definitions

- `stepCompilation`, `wrapCompilation`: the canonical compilations; `canonicalStep`,
  `canonicalWrap`: the same in hand.
- `IndexData`: the data an index is built at.
- `ApplicationCertified`: checked Lean indices, supplied keys and embedded-verifier setup.
- `checkApplication`: certify the application from its compilations.
- `ApplicationIndices`, `ApplicationCertified.indices`: the family of certified indices.
- `ApplicationFailure`: a compilation, key or setup rejection located at its circuit or slot.

## Main results

- `Circuits.stepBuilt_eq`, `Circuits.wrapBuilt_eq`: every execution's compiled circuit is the
  canonical compilation.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier
open scoped Kimchi

variable {D : Shape}

/-- A branch's public statement: its step circuit's public output. -/
abbrev StepPublic (D : Shape) := StepStatement (UnfVal WrapIPARounds) Fp D.width

/-- The wrap circuit's public statement: its public input. -/
abbrev WrapPublic := StatementPacked StepIPARounds (Type1 Fq) Fq

/-! ## The canonical compilations -/

/-- The type of a branch's compiled step circuit: its statement and retained cells, then the
statement's public copy. -/
abbrev StepBuilt (C : Circuits D) (b : D.Branch) :=
  Built (KimchiConstraint Fp)
    ((StepStatement (UnfVar WrapIPARounds) (FVar Fp) D.width × C.StepCells b) ×
      StepStatement (UnfVar WrapIPARounds) (FVar Fp) D.width)

/-- The type of the compiled wrap circuit: its retained cells and no public output. -/
abbrev WrapBuilt (C : Circuits D) := Built (KimchiConstraint Fq) ((Unit × C.WrapCells) × Unit)

/-- A branch's step circuit compiled with inert advice. -/
def stepCompilation (C : Circuits D) (b : D.Branch) : StepBuilt C b :=
  C.stepBuilt b inertStepAdvice

/-- The shared wrap circuit compiled with inert advice. -/
def wrapCompilation (C : Circuits D) : WrapBuilt C :=
  C.wrapBuilt inertWrapAdvice

/-- **Every step execution compiles to the canonical compilation.** Advice changes no
constraint, allocation or retained cell. -/
theorem Circuits.stepBuilt_eq (C : Circuits D) (b : D.Branch)
    (a : C.StepAdvice b) : C.stepBuilt b a = stepCompilation C b :=
  C.stepBuilt_advice_irrel b a inertStepAdvice

/-- **Every wrap execution compiles to the canonical compilation.** -/
theorem Circuits.wrapBuilt_eq (C : Circuits D) (a : C.WrapAdvice) :
    C.wrapBuilt a = wrapCompilation C :=
  C.wrapBuilt_advice_irrel a inertWrapAdvice

/-- A branch's compilation in hand, pinned to the canonical one. -/
abbrev StepCompilation (C : Circuits D) (b : D.Branch) :=
  { built : StepBuilt C b // built = stepCompilation C b }

/-- The wrap circuit's compilation in hand, pinned to the canonical one. -/
abbrev WrapCompilation (C : Circuits D) := { built : WrapBuilt C // built = wrapCompilation C }

/-- A branch's canonical compilation, in hand. -/
def canonicalStep (C : Circuits D) (b : D.Branch) : StepCompilation C b :=
  ⟨stepCompilation C b, rfl⟩

/-- The wrap circuit's canonical compilation, in hand. -/
def canonicalWrap (C : Circuits D) : WrapCompilation C :=
  ⟨wrapCompilation C, rfl⟩

/-- A branch's public variables: no input slot, then its statement's public copy. -/
abbrev stepPublicVars (C : Circuits D) (b : D.Branch) : List Variable :=
  compiledPublicVars (F := Fp) (a := Unit) (b := StepPublic D) (stepCompilation C b)

/-- The wrap circuit's public variables: its statement's input slots, then no output. -/
abbrev wrapPublicVars (C : Circuits D) : List Variable :=
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
are the key's, the coefficient being the curve's by `KimchiVK.endo_eq`; the matrix is the one the
verifier reads for the curve's proofs, `mdsOfParams` of its sponge parameters. -/
private def IndexData.ofKey {C : Ipa.KimchiCurve} {nc : ℕ} (K : KimchiVK C nc) :
    IndexData C.ScalarField where
  n := K.n
  zkRows := K.zkRows
  omega := K.omega
  shifts c := K.shifts[c]
  endoBase := K.endo
  mds := mdsOfParams C.frSponge.params

/-- A branch's index data: its step key's. -/
def stepIndexData (C : Circuits D) (b : D.Branch) : IndexData Fp :=
  .ofKey C.wiring.backend.stepKeys[b]

/-- The wrap circuit's index data: the wrap key's. -/
def wrapIndexData (C : Circuits D) : IndexData Fq :=
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
def checkStepAt (C : Circuits D) (b : D.Branch) (built : StepCompilation C b)
    (d : IndexData Fp) :
    Except CheckFailure (CheckedIndex (stepCompilation C b).constraints (stepPublicVars C b)
      (stepCompilation C b).nextVar d.n) :=
  cast (by rw [built.2]) (checkAt (a := Unit) (b := StepPublic D) built.1 d)

/-- The wrap circuit's checked index at given index data, from its compilation in hand. -/
def checkWrapAt (C : Circuits D) (built : WrapCompilation C) (d : IndexData Fq) :
    Except CheckFailure (CheckedIndex (wrapCompilation C).constraints (wrapPublicVars C)
      (wrapCompilation C).nextVar d.n) :=
  cast (by rw [built.2]) (checkAt (a := WrapPublic) (b := Unit) built.1 d)

/-- A compilation, key or setup rejection, located at its branch, slot or wrap circuit. -/
inductive ApplicationFailure (D : Shape) where
  /-- The branch's step circuit was rejected. -/
  | step (b : D.Branch) (failure : CheckFailure)
  /-- The wrap circuit was rejected. -/
  | wrap (failure : CheckFailure)
  /-- A branch's supplied key does not correspond to its compiled index. -/
  | stepKey (b : D.Branch) (failure : KeyFailure)
  /-- The supplied wrap key does not correspond to its compiled index. -/
  | wrapKey (failure : KeyFailure)
  /-- Wrap's verification parameters for a step branch were rejected. -/
  | stepSetup (b : D.Branch) (reason : String)
  /-- A step slot's verification parameters were rejected. -/
  | slotSetup (b : D.Branch) (i : D.Slot b) (reason : String)

/-- Checked Lean compilations, correspondence of their supplied keys, and the static setup
required by the embedded verifiers. This certificate makes no claim about an imported
constraint system. -/
structure ApplicationCertified (C : Circuits D) where
  private mk ::
  /-- Each branch's checked index. -/
  step : (b : D.Branch) → CheckedIndex (stepCompilation C b).constraints (stepPublicVars C b)
    (stepCompilation C b).nextVar (stepIndexData C b).n
  /-- The wrap circuit's checked index. -/
  wrap : CheckedIndex (wrapCompilation C).constraints (wrapPublicVars C)
    (wrapCompilation C).nextVar (wrapIndexData C).n
  /-- Each branch's supplied key commits to its checked index under the shared Step SRS. -/
  stepKey : ∀ b, KeyCorresponds C.setup.stepSrs (step b).index
    C.wiring.backend.stepKeys[b] (D.slots b)
  /-- The supplied Wrap key commits to its checked index under the shared Wrap SRS. -/
  wrapKey : KeyCorresponds C.setup.wrapSrs wrap.index
    C.wiring.backend.wrapKey MaxProofsVerified
  /-- Every slot's embedded Wrap verifier has the required SRS-dependent setup. -/
  stepWrapSetup : ∀ b i, StepWrapAssumptions C b i
  /-- Wrap's embedded Step verifier has the required setup for every branch. -/
  wrapStepSetup : ∀ b, WrapStepAssumptions C b
  /-- Slot source keys have finite commitments, representable by affine cells. -/
  sourceKeyPoints : ∀ b i,
    ∀ P ∈ (C.wiring.source b i).wrapKey.comms.indexPoints, P ≠ 0

/-- Check Wrap's constant nondegeneracy premises. The returned implication is shared with
fixture consumers that keep Lagrange correspondence as an explicit premise. Certification
discharges that premise by recomputing the table from the SRS. -/
def checkWrapStepConstants (C : Circuits D) (b : D.Branch) :
    Except String (PLift
      (C.stepLagrange C.wiring.backend.stepKeys[b].domainLog2 =
        C.wiring.backend.stepKeys[b].lagrangePoints C.setup.stepSrs
          (CircuitType.size Fp (StepPublic D)) → WrapStepAssumptions C b)) := do
  let K := C.wiring.backend.stepKeys[b]
  let ⟨hn⟩ ← requireProof (K.comms.indexPoints.all (fun P => decide (P ≠ 0)) = true)
    "step key has an infinite commitment"
  let ⟨hL⟩ ← requireProof ((C.stepLagrange K.domainLog2).toList.all fun Ps =>
    (List.finRange C.wiring.backend.stepChunks).all fun c => decide (Ps[c] ≠ 0))
    "step table has an infinite commitment"
  return ⟨fun ht => ⟨ht,
    fun P hP => of_decide_eq_true (List.all_eq_true.mp hn P hP), by
      apply (KimchiVK.avoids_lagrangeRelations_iff C.setup.stepSrs
        (C.wiring.valid.stepChunks b) _).mpr
      rw [← ht]
      exact fun Ps hPs c => of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp hL Ps hPs) c (List.mem_finRange c))⟩⟩

/-- Check a slot's constant nondegeneracy premises, leaving only Lagrange correspondence.
The universal statement premise reduces to one correction sum because its packing is fixed. -/
def checkStepWrapConstants (C : Circuits D) (b : D.Branch) (i : D.Slot b) :
    Except String (PLift
      ((C.wiring.sources b i).lagrange = (C.wiring.source b i).wrapKey.lagrangePoints
        C.setup.wrapSrs
          (CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp)) →
        StepWrapAssumptions C b i)) := do
  let source := C.wiring.source b i
  let K := source.wrapKey
  let m := CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp)
  let statement := CircuitType.fieldsToVar (F := Fp)
    (val := WrapStatement StepIPARounds Fp Bool (Type1 Fp))
    (Vector.replicate _ (.const 0))
  let ⟨hd⟩ ← requireProof (C.setup.dummySg ≠ 0) "padding commitment is infinite"
  let ⟨hs⟩ ← requireProof (m ≤ 2 ^ WrapIPARounds ∧ m ≤ K.n) "wrap statement size"
  let ⟨hL⟩ ← requireProof ((C.wiring.sources b i).lagrange.toList.all
    fun Ps => decide (Ps[0] ≠ 0)) "wrap table has an infinite commitment"
  let ⟨hc⟩ ← requireProof (∀ c : Fin 1, corrSumPt (C := IpaPallas.curve)
    statement.packed.toList (C.wiring.sources b i).lagrange.toList c ≠ 0)
    "wrap correction sum is infinite"
  return ⟨fun ht => ⟨hd, ht, fun inp msg =>
    (avoids_stepRelationsAt_iff C.setup.wrapSrs K source.wrapChunks
      (inp.statement msg) hs.1 hs.2).mpr ⟨fun c => by
        rw [corrSumPt_packed_congr _ statement, ← ht]
        exact hc c,
      by
        rw [← ht]
        intro Ps hPs c
        rw [Fin.fin_one_eq_zero c]
        exact of_decide_eq_true (List.all_eq_true.mp hL Ps hPs)⟩⟩⟩

private def domainLagrange {curve : Ipa.KimchiCurve} (σ : SRS curve.Point)
    (nc count logN : Nat) : Vector (Vector curve.Point nc) count :=
  ⟨Ipa.lagrangeBasis curve σ nc (2 ^ logN) (domainGenerator curve logN) count,
    by simp [Ipa.lagrangeBasis]⟩

private abbrev LagrangeMemo {curve : Ipa.KimchiCurve} (σ : SRS curve.Point) (nc count : Nat) :=
  List ((logN : Nat) × { table : Vector (Vector curve.Point nc) count //
    table = domainLagrange σ nc count logN })

/-- A private, proof-carrying memo: each domain is computed once at this fixed SRS and size. -/
private def lagrangeAt {curve : Ipa.KimchiCurve} {m : Type → Type} [Monad m]
    (σ : SRS curve.Point) {nc : Nat} (K : KimchiVK curve nc) (count : Nat) :
    StateT (LagrangeMemo σ nc count) m
      { table : Vector (Vector curve.Point nc) count // table = K.lagrangePoints σ count } := do
  have hs : domainLagrange σ nc count K.domainLog2 = K.lagrangePoints σ count := by
    unfold domainLagrange KimchiVK.lagrangePoints
    rw [Vector.mk.injEq]
    simp only [KimchiVK.n, K.omega_eq]
  for entry in ← get do
    if h : entry.1 = K.domainLog2 then
      return ⟨entry.2.val, entry.2.property.trans (h ▸ hs)⟩
  let table := domainLagrange σ nc count K.domainLog2
  modify (⟨K.domainLog2, table, rfl⟩ :: ·)
  return ⟨table, hs⟩

/-- Check the verifier setup, compilations in hand and their supplied keys. Lagrange tables
are recomputed once per domain at each fixed SRS, chunk count and statement size. -/
def checkApplication (C : Circuits D) (steps : (b : D.Branch) → StepCompilation C b)
    (wrap : WrapCompilation C) : Except (ApplicationFailure D) (ApplicationCertified C) := do
  let wrapSetup : (b : D.Branch) → PLift (WrapStepAssumptions C b) ←
    (finSequence (m := StateT (LagrangeMemo C.setup.stepSrs C.wiring.backend.stepChunks
        (CircuitType.size Fp (StepPublic D))) (Except (ApplicationFailure D))) fun b => do
      let constants ← liftM
        ((checkWrapStepConstants C b).mapError (ApplicationFailure.stepSetup b))
      let table ← lagrangeAt C.setup.stepSrs C.wiring.backend.stepKeys[b] _
      let ⟨ht⟩ ← requireProof
        (C.stepLagrange C.wiring.backend.stepKeys[b].domainLog2 = table.val)
        (.stepSetup b "Lagrange table differs from the SRS-derived basis")
      return PLift.up (constants.down (ht.trans table.property))).run' []
  let slotSetup : (b : D.Branch) → (i : D.Slot b) → PLift (StepWrapAssumptions C b i ∧
      ∀ P ∈ (C.wiring.source b i).wrapKey.comms.indexPoints, P ≠ 0) ←
    (finSequence (m := StateT (LagrangeMemo C.setup.wrapSrs 1
        (CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp)))
        (Except (ApplicationFailure D))) fun b => finSequence fun i => do
      let constants ← liftM
        ((checkStepWrapConstants C b i).mapError (ApplicationFailure.slotSetup b i))
      let ⟨hn⟩ ← requireProof
        ((C.wiring.source b i).wrapKey.comms.indexPoints.all (fun P => decide (P ≠ 0)))
        (.slotSetup b i "source wrap key has an infinite commitment")
      let table ← lagrangeAt C.setup.wrapSrs (C.wiring.source b i).wrapKey _
      let ⟨ht⟩ ← requireProof ((C.wiring.sources b i).lagrange = table.val)
        (.slotSetup b i "Lagrange table differs from the SRS-derived basis")
      return PLift.up (And.intro (constants.down (ht.trans table.property))
        (fun P hP => of_decide_eq_true (List.all_eq_true.mp hn P hP)))).run' []
  let step ← finSequence fun b =>
    (checkStepAt C b (steps b) (stepIndexData C b)).mapError (.step b)
  let wrap ← (checkWrapAt C wrap (wrapIndexData C)).mapError .wrap
  let stepKeys ← finSequence fun b =>
    (checkKey? C.setup.stepSrs (step b).index
      C.wiring.backend.stepKeys[b] (D.slots b)).mapError (.stepKey b)
  let wrapKey ← (checkKey? C.setup.wrapSrs wrap.index
    C.wiring.backend.wrapKey MaxProofsVerified).mapError .wrapKey
  return ⟨step, wrap, fun b => (stepKeys b).down, wrapKey.down,
    fun b i => (slotSetup b i).down.1, fun b => (wrapSetup b).down,
    fun b i => (slotSetup b i).down.2⟩

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
def ApplicationCertified.indices {C : Circuits D} (checked : ApplicationCertified C) :
    ApplicationIndices D where
  stepSize b := (stepIndexData C b).n
  step b := (checked.step b).index
  wrapSize := (wrapIndexData C).n
  wrap := checked.wrap.index
  stepPublicCount b := (checked.step b).publicCount_eq.trans (by
    have h := length_compiledPublicVars_compileWith (a := Unit) (b := StepPublic D)
      (C.stepCircuit b inertStepAdvice)
    simp only [show CircuitType.size Fp Unit = 0 from rfl, Nat.zero_add] at h
    exact h)
  wrapPublicCount := checked.wrap.publicCount_eq.trans (by
    have h := length_compiledPublicVars_compileWith (a := WrapPublic) (b := Unit)
      (C.wrapCircuit inertWrapAdvice)
    simp only [show CircuitType.size Fq Unit = 0 from rfl, Nat.add_zero] at h
    exact h)

end Pickles.Application
