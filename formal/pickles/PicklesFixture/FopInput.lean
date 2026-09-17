import PicklesFixture.Fop

/-!
# The `finalize_other_proof` input as a named bundle

The dumps' step layout is 151 flat cells, which is what a byte-comparison driver wants and
what a fixture author should never have to count. `FopInput` is the same 151 cells with
names on them: a satisfiability fixture decodes into this, and the flat layout stays the
single source of truth because the harness reaches it through the bundle's own encoding.

The bundle is unchecked: a fixture supplies the values rather than trusting a prover to,
so its `CheckedType` pays no rows and its `post` asserts nothing.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

/-- The step side's `finalize_other_proof` input, by name. The field order is the dump's
cell order: the claims at 0–25, the mask at 26–27, `domain_log2` at 28, the evaluation
block from 29, `ft(ζω)`, the two previous-challenge vectors, and the digest last. -/
structure FopInput (α : Type) where
  /-- `α, β, γ, ζ` at 0–3, the five shifted claims at 4–8, `ξ` at 9, 16 challenges at 10–25. -/
  claims : Vector α 26
  /-- The two proofs-verified mask bits. -/
  mask : Vector α 2
  /-- The domain's `log2`, as a cell. -/
  domainLog2 : α
  /-- The public pair, 15 `w` pairs, 15 coefficient pairs, the `z` pair, 6 `σ` pairs and the
  6 selector pairs. -/
  evals : Vector α 88
  /-- `ft(ζω)`. -/
  ftEval1 : α
  /-- The two 16-entry previous-challenge vectors. -/
  prevChallenges : Vector α 32
  /-- The sponge digest before evaluations. -/
  digest : α

/-- The bundle is its seven components, in cell order. -/
@[simps apply symm_apply] def FopInput.equivProd {α : Type} :
    FopInput α ≃ Vector α 26 × Vector α 2 × α × Vector α 88 × α × Vector α 32 × α where
  toFun i := (i.claims, i.mask, i.domainLog2, i.evals, i.ftEval1, i.prevChallenges, i.digest)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bundle encodes as its 151 cells, components in cell order — so its encoding IS the
dump's flat layout. -/
instance instFopInputCircuitType :
    CircuitType Fp (FopInput Fp) (FopInput (FVar Fp)) :=
  CircuitType.ofEquiv FopInput.equivProd FopInput.equivProd

/-- The bundle is unchecked: a fixture supplies its cells, so nothing is asserted of them. -/
instance instFopInputCheckedType : CheckedType Fp C (FopInput Fp) (FopInput (FVar Fp)) :=
  CheckedType.ofEquiv FopInput.equivProd FopInput.equivProd

/-- A bundle is in scope when its seven components are. -/
@[simp] theorem scoped_fopInput {st : ProverState Fp} {v : FopInput (FVar Fp)} :
    CircuitType.Scoped (val := FopInput Fp) st v ↔
      CircuitType.Scoped (val := Vector Fp 26 × Vector Fp 2 × Fp × Vector Fp 88 × Fp ×
        Vector Fp 32 × Fp) st (FopInput.equivProd v) :=
  CircuitType.scoped_ofEquiv _ _

/-- A bundle reads componentwise. -/
@[simp] theorem reads_fopInput {V : Valuation Fp} {v : FopInput (FVar Fp)} {x : FopInput Fp} :
    CircuitType.Reads V v x ↔
      CircuitType.Reads V (FopInput.equivProd v) (FopInput.equivProd x) :=
  CircuitType.reads_ofEquiv _ _

/-- The step harness on the named bundle at given known domains: its encoding is the flat
layout, so this is `fopStepHarnessAt` on the same cells. -/
def fopStepOnAt (domains : List (Pickles.KnownDomain Fp)) (input : FopInput (FVar Fp)) :
    CircuitM Fp C (Pickles.FopOutput Fp) :=
  fopStepHarnessAt domains (CircuitType.varToFields (val := FopInput Fp) input)

/-- The step harness on the named bundle at the dump's domain. -/
def fopStepOn (input : FopInput (FVar Fp)) : CircuitM Fp C (Pickles.FopOutput Fp) :=
  fopStepHarness (CircuitType.varToFields (val := FopInput Fp) input)

end PicklesFixture
