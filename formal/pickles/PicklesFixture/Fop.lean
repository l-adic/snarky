import PicklesFixture.Layout
import KimchiFixture.PS
import Pickles.FinalizeOtherProof
import Pickles.Linearization.Fp
import Pickles.Linearization.Fq

/-!
# The `finalize_other_proof` harnesses

`Pickles.finalizeOtherProofStep` and `Wrap` over the dumps' flat input layouts — 151 cells
at the step field, 148 at the wrap field — at the deployed parameters. Both return the
gadget's `FopOutput`: the success bit and the four it is the conjunction of. A driver that
only wants the constraint system discards it, which emits the same ops.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

open Pickles Kimchi.Verifier in
/-- The unfinalized proof, witness and previous challenges from the dumps' layout: the five
128-bit claims at 0–3 and 9, the shifted claims at 4–8, the `rounds` challenges from 10; then
from `base` the public pair, 15 `w` pairs, 15 coefficient pairs, the `z` pair, 6 `σ` pairs, 6
selector pairs, `ft(ζω)`, the two `rounds`-entry previous-challenge vectors, and the digest
before evaluations last. -/
def fopInputsOf {p : ℕ} {sf : Type} (mk : FVar (ZMod p) → sf) (get : ℕ → FVar (ZMod p))
    (base : ℕ) (rounds : ℕ := 16) :
    UnfinalizedProof (ZMod p) sf × AllEvals (ZMod p) × List (List (FVar (ZMod p))) :=
  let (pub, evals) := evalsAt get base
  let u : UnfinalizedProof (ZMod p) sf :=
    { deferredValues :=
        { plonk := { alpha := ⟨get 0⟩, beta := ⟨get 1⟩, gamma := ⟨get 2⟩, zeta := ⟨get 3⟩,
                     zetaToSrsLength := mk (get 4), zetaToDomainSize := mk (get 5),
                     perm := mk (get 6) }
          combinedInnerProduct := mk (get 7), b := mk (get 8), xi := ⟨get 9⟩,
          bulletproofChallenges := (List.range rounds).map fun i => ⟨get (10 + i)⟩ }
      shouldFinalize := true_
      spongeDigestBeforeEvaluations := get (base + 89 + 2 * rounds) }
  let w : AllEvals (ZMod p) := { ftEval1 := get (base + 88), pub, evals }
  (u, w, prevChallengesOf get (base + 89) rounds)

/-- The step side's parameters: the Vesta fr-sponge, `λ`, the `Fp` linearization and the
step shifts, `srs_length_log2 = 16`, `zk_rows = 3`. -/
def fopStepParams : Pickles.FopParams Fp :=
  { sponge := Bulletproof.IpaVesta.curve.frSponge.params, endoLam := endoVestaLam,
    endo := Kimchi.Fixture.PS.fpSide.endo, mds := Kimchi.Fixture.PS.fpSide.mds,
    toks := Pickles.Linearization.fpTokens, shifts := stepShifts, srsLengthLog2 := 16,
    zkRows := 3 }

/-- The step side over the 151-cell layout at given known domains: the mask at 26–27
(unchecked), `domain_log2` at 28, the evaluations from 29. -/
def fopStepHarnessAt (domains : List (Pickles.KnownDomain Fp)) (input : Vector (FVar Fp) 151) :
    CircuitM Fp C (Pickles.FopOutput Fp) := do
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  let (u, w, prev) := fopInputsOf Type1.mk get 29
  Pickles.finalizeOtherProofStep fopStepParams domains u w
    [.unchecked (get 26), .unchecked (get 27)] prev (get 28)

/-- `finalize_other_proof_step_circuit`: the dump's one known domain of `log2 = 16`. -/
def fopStepHarness (input : Vector (FVar Fp) 151) : CircuitM Fp C (Pickles.FopOutput Fp) :=
  fopStepHarnessAt [⟨16, Kimchi.Fixture.PS.fpSide.omega (2 ^ 16)⟩] input

/-- The wrap side's parameters: the Pallas fr-sponge, `λ`, the `Fq` linearization and the
wrap shifts, `srs_length_log2 = 15`, `zk_rows = 3`. -/
def fopWrapParams : Pickles.FopParams Fq :=
  { sponge := Bulletproof.IpaPallas.curve.frSponge.params, endoLam := endoPallasLam,
    endo := Kimchi.Fixture.PS.fqSide.endo, mds := Kimchi.Fixture.PS.fqSide.mds,
    toks := Pickles.Linearization.fqTokens, shifts := wrapShifts, srsLengthLog2 := 15,
    zkRows := 3 }

/-- The wrap side over the flat layout at a domain and a round count: the claims with their
`rounds` challenges first, the evaluations from `10 + rounds`, the constant domain's
generator, `ζⁿ − 1` by `pow2PowMul`. -/
def fopWrapHarnessAt (domainLog2 rounds : ℕ) {n : ℕ} (input : Vector (FVar Fq) n) :
    CircuitM Fq Cq (Pickles.FopOutput Fq) := do
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  let (u, w, prev) := fopInputsOf Type2.mk get (10 + rounds) rounds
  Pickles.finalizeOtherProofWrap fopWrapParams (Kimchi.Fixture.PS.fqSide.omega (2 ^ domainLog2))
    domainLog2 (fun z => do let t ← Pickles.pow2PowMul z domainLog2; pure (CVar.sub_ t (.const 1)))
    u w prev

/-- `finalize_other_proof_wrap_circuit`: the dump's 148 cells at the constant domain of
`log2 = 15` and 16 challenges. -/
def fopWrapHarness (input : Vector (FVar Fq) 148) : CircuitM Fq Cq (Pickles.FopOutput Fq) :=
  fopWrapHarnessAt 15 16 input

end PicklesFixture
