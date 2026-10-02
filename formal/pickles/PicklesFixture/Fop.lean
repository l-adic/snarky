import PicklesFixture.Layout
import KimchiFixture.PS
import Pickles.FinalizeOtherProof
import Pickles.WrapScalarHalf
import Pickles.Encoding
import Pickles.Linearization.Fp
import Pickles.Linearization.Fq

/-!
# The finalize-other-proof parameters and harness

The deployed parameters of `Pickles.finalizeOtherProofStep` and `Pickles.finalizeOtherProofWrap`
(`FopParams.of`), which the main circuits take, and the step side's gadget on its own records
(`PicklesFixture.StepFop`), as a benchmark supplies them. It returns the gadget's
`Pickles.FopOutput`; a driver that only wants the constraint system discards it.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

/-- The step side's deployed parameters at `nc` chunks: the Vesta curve's (`FopParams.of`), at
the step SRS of `2 ^ 16` points and the `Fp` linearization. -/
def fopStepParams (nc : ℕ) : Pickles.FopParams Fp :=
  Pickles.FopParams.of Bulletproof.IpaVesta.curve nc 16 Pickles.Linearization.fpTokens

/-- The wrap side's deployed parameters: the Pallas curve's (`FopParams.of`) at one chunk, at the
wrap SRS of `2 ^ 15` points and the `Fq` linearization. -/
def fopWrapParams : Pickles.FopParams Fq :=
  Pickles.FopParams.of Bulletproof.IpaPallas.curve 1 15 Pickles.Linearization.fqTokens

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

/-- The step side on its records at known domains, at the records' chunk count. -/
def fopStepOnAt (domains : List (Pickles.KnownDomain Fp)) {k nc : ℕ}
    (v : StepFopVar k nc) : CircuitM Fp C (Pickles.FopOutput Fp k) :=
  let (u, w, mask, prev, domainLog2) := v
  Pickles.finalizeOtherProofStep (fopStepParams nc) domains u w mask prev domainLog2

/-- `fopStepOnAt` at the dump's one known domain, of log2 16. -/
def fopStepOn {k nc : ℕ} (v : StepFopVar k nc) : CircuitM Fp C (Pickles.FopOutput Fp k) :=
  fopStepOnAt [⟨16, Kimchi.Verifier.domainGenerator Bulletproof.IpaVesta.curve 16⟩] v

end PicklesFixture
