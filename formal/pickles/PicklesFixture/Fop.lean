import PicklesFixture.Layout
import KimchiFixture.PS
import Pickles.FinalizeOtherProof
import Pickles.WrapScalarHalf
import Pickles.Encoding
import Pickles.Linearization.Fp
import Pickles.Linearization.Fq

/-!
# The finalize-other-proof parameters

The deployed parameters of `Pickles.finalizeOtherProofStep` and `Pickles.finalizeOtherProofWrap`
(`FopParams.of`), which the main circuits take.
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

end PicklesFixture
