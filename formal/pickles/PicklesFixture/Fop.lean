import PicklesFixture.Layout
import KimchiFixture.PS
import Pickles.FinalizeOtherProof
import Pickles.WrapScalarHalf
import Pickles.Encoding
import Pickles.Linearization.Fp
import Pickles.Linearization.Fq

/-!
# The finalize-other-proof harnesses

`Pickles.finalizeOtherProofStep` and `Pickles.finalizeOtherProofWrap` at the deployed
parameters, twice over: on the gadgets' own records (`PicklesFixture.StepFop`,
`Pickles.WrapFop`), as a satisfiability fixture supplies them, and on the dumps' flat input
layouts, as the dump comparison supplies them. Both return the gadget's `Pickles.FopOutput`; a
driver that only wants the constraint system discards it.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

open Pickles Kimchi.Verifier in
/-- The unfinalized proof, evaluations and previous challenges from the dumps' layout: the
128-bit claims at 0–3 and 9, the shifted claims at 4–8, the `rounds` challenges from 10; from
`base` the evaluations (`evalsAt`), `ft(ζω)` at `base + 88`, the previous challenges from
`base + 89`, and the digest last. -/
def fopInputsOf {p : ℕ} {sf : Type} (mk : FVar (ZMod p) → sf) (get : ℕ → FVar (ZMod p))
    (base : ℕ) (rounds : ℕ := 16) :
    UnfinalizedProof rounds (FVar (ZMod p)) (BoolVar (ZMod p)) sf ×
      Pickles.ChunkedEvals 1 (FVar (ZMod p)) × List (List (FVar (ZMod p))) :=
  let (pub, evals) := evalsAt get base
  let u : UnfinalizedProof rounds (FVar (ZMod p)) (BoolVar (ZMod p)) sf :=
    { deferredValues :=
        { plonk := { alpha := ⟨get 0⟩, beta := ⟨get 1⟩, gamma := ⟨get 2⟩, zeta := ⟨get 3⟩,
                     zetaToSrsLength := mk (get 4), zetaToDomainSize := mk (get 5),
                     perm := mk (get 6) }
          combinedInnerProduct := mk (get 7), b := mk (get 8), xi := ⟨get 9⟩,
          bulletproofChallenges := Vector.ofFn fun i => ⟨get (10 + i)⟩ }
      shouldFinalize := true_
      spongeDigestBeforeEvaluations := get (base + 89 + 2 * rounds) }
  let w : Pickles.ChunkedEvals 1 (FVar (ZMod p)) :=
    ⟨get (base + 88), pub.map (#v[·]), evals.map (#v[·])⟩
  (u, w, prevChallengesOf get (base + 89) rounds)

/-- The step side's deployed parameters: the Vesta fr-sponge and the `Fp` linearization. -/
def fopStepParams : Pickles.FopParams Fp :=
  { sponge := Bulletproof.IpaVesta.curve.frSponge.params, endoLam := endoVestaLam,
    endo := Kimchi.Fixture.PS.fpSide.endo, mds := Kimchi.Fixture.PS.fpSide.mds,
    toks := Pickles.Linearization.fpTokens, shifts := stepShifts, srsLengthLog2 := 16,
    zkRows := 3 }

/-- The step side over the 151-cell layout at given known domains: the mask at 26–27
(unchecked), the domain's log2 at 28, the evaluations from 29. -/
def fopStepHarnessAt (domains : List (Pickles.KnownDomain Fp)) (input : Vector (FVar Fp) 151) :
    CircuitM Fp C (Pickles.FopOutput Fp) := do
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  let (u, w, prev) := fopInputsOf Type1.mk get 29
  Pickles.finalizeOtherProofStep fopStepParams domains u w
    [.unchecked (get 26), .unchecked (get 27)] prev (get 28)

/-- `fopStepHarnessAt` at the dump's one known domain, of log2 16. -/
def fopStepHarness (input : Vector (FVar Fp) 151) : CircuitM Fp C (Pickles.FopOutput Fp) :=
  fopStepHarnessAt [⟨16, Kimchi.Fixture.PS.fpSide.omega (2 ^ 16)⟩] input

/-- The wrap side's deployed parameters: the Pallas fr-sponge and the `Fq` linearization. -/
def fopWrapParams : Pickles.FopParams Fq :=
  { sponge := Bulletproof.IpaPallas.curve.frSponge.params, endoLam := endoPallasLam,
    endo := Kimchi.Fixture.PS.fqSide.endo, mds := Kimchi.Fixture.PS.fqSide.mds,
    toks := Pickles.Linearization.fqTokens, shifts := wrapShifts, srsLengthLog2 := 15,
    zkRows := 3 }

/-- The wrap side over the flat layout at a constant domain and `rounds` challenges: the
evaluations from `10 + rounds`, the vanishing polynomial `ζⁿ − 1` by `pow2PowMul`. -/
def fopWrapHarnessAt (domainLog2 rounds : ℕ) {n : ℕ} (input : Vector (FVar Fq) n) :
    CircuitM Fq Cq (Pickles.FopOutput Fq) := do
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  let (u, w, prev) := fopInputsOf Type2.mk get (10 + rounds) rounds
  Pickles.finalizeOtherProofWrap fopWrapParams
    (.const (Kimchi.Fixture.PS.fqSide.omega (2 ^ domainLog2)))
    (fun z => do let t ← Pickles.pow2PowMul z domainLog2; pure (CVar.sub_ t (.const 1)))
    u w prev

/-- `fopWrapHarnessAt` at the dump's constant domain, of log2 15, and 16 challenges. -/
def fopWrapHarness (input : Vector (FVar Fq) 148) : CircuitM Fq Cq (Pickles.FopOutput Fq) :=
  fopWrapHarnessAt 15 16 input

/-! ## The gadgets' records as the input

Each side's input is built from the gadget's own records, so its `CircuitType` instance is the
records' (`Pickles.Encoding`) and the harness passes the allocated bundle to the gadget as it
is. -/

/-- The step side's input at `k` rounds and `nc` chunks, as values: the unfinalized proof, the
evaluations, the mask, the previous challenges and the domain's log2. -/
abbrev StepFop (k nc : ℕ) : Type :=
  Pickles.UnfinalizedProof k Fp Bool (Type1 Fp) × Pickles.ChunkedEvals nc Fp ×
    Vector Bool Pickles.MaxProofsVerified × Vector (Vector Fp k) Pickles.MaxProofsVerified × Fp

/-- The step side's input at `k` rounds and `nc` chunks, as cells. -/
abbrev StepFopVar (k nc : ℕ) : Type :=
  Pickles.UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) ×
    Pickles.ChunkedEvals nc (FVar Fp) × Vector (BoolVar Fp) Pickles.MaxProofsVerified ×
    Vector (Vector (FVar Fp) k) Pickles.MaxProofsVerified × FVar Fp

/-- The step side on its records at a given `zkRows` and known domains. -/
def fopStepOnAt (zkRows : ℕ) (domains : List (Pickles.KnownDomain Fp)) {k nc : ℕ}
    (v : StepFopVar k nc) : CircuitM Fp C (Pickles.FopOutput Fp) :=
  let (u, w, mask, prev, domainLog2) := v
  Pickles.finalizeOtherProofStep { fopStepParams with zkRows } domains u w mask.toList
    (prev.toList.map (·.toList)) domainLog2

/-- `fopStepOnAt` at three zero-knowledge rows and the dump's one known domain, of log2 16. -/
def fopStepOn {k nc : ℕ} (v : StepFopVar k nc) : CircuitM Fp C (Pickles.FopOutput Fp) :=
  fopStepOnAt 3 [⟨16, Kimchi.Fixture.PS.fpSide.omega (2 ^ 16)⟩] v

/-- The wrap side on its records at a constant domain, `ζⁿ − 1` by `pow2PowMul`. -/
def fopWrapOnAt (domainLog2 : ℕ) {k : ℕ} (v : Pickles.WrapFopVar k 1) :
    CircuitM Fq Cq (Pickles.FopOutput Fq) :=
  Pickles.finalizeOtherProofWrap fopWrapParams
    (.const (Kimchi.Fixture.PS.fqSide.omega (2 ^ domainLog2)))
    (fun z => do let t ← Pickles.pow2PowMul z domainLog2; pure (CVar.sub_ t (.const 1)))
    v.claims v.evals (v.prev.toList.map (·.toList))

end PicklesFixture
