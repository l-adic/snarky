module Pickles.CircuitDiffs.PureScript.FqSpongeTranscriptWrap
  ( compileFqSpongeTranscriptWrap
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx, wrapEndo)
import Pickles.Field (WrapField)
import Pickles.IncrementallyVerifyProof.FqSpongeTranscript (spongeTranscriptOptCircuit)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Types (ChunkedCommitment(..))
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (Bool(..), F, FVar, Snarky, const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | `fq_sponge_transcript_wrap_circuit` (OCaml `dump_circuit_impl.ml`): the two
-- | `sg_old` mask bits at 0-1 (`Boolean.Unsafe.of_cvar`, an unchecked coercion
-- | here too), the index digest at 2, two `sg_old` points at 3-6, `x_hat` at 7-8,
-- | the 15 `w_comm` points at 9-38, `z_comm` at 39-40 and the 7 `t_comm` points at
-- | 41-54, all at one chunk.
-- |
-- | Layout only: every row is the library's `spongeTranscriptOptCircuit`, the wrap
-- | verifier's fq-sponge schedule over the conditional sponge.
fqSpongeTranscriptWrapCircuit
  :: forall r
   . Vector 55 (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
fqSpongeTranscriptWrapCircuit inputs = do
  let
    at = unsafeIdx inputs
    pt i = AffinePoint { x: at i, y: at (i + 1) }

    mask :: Vector 2 (Bool (FVar WrapField))
    mask = Vector.generate \j -> coerce (at (getFinite j))

    sgOld :: Vector 2 (AffinePoint (FVar WrapField))
    sgOld = Vector.generate \j -> pt (3 + 2 * getFinite j)

    wComm :: Vector 15 (ChunkedCommitment 1 (AffinePoint (FVar WrapField)))
    wComm = Vector.generate \j -> ChunkedCommitment (pt (9 + 2 * getFinite j) :< Vector.nil)

    tComm :: Vector 7 (AffinePoint (FVar WrapField))
    tComm = Vector.generate \j -> pt (41 + 2 * getFinite j)
  void $ evalSpongeM initialSpongeCircuit $ spongeTranscriptOptCircuit { endo: const_ wrapEndo } mask
    { indexDigest: at 2
    , sgOld
    , publicComm: ChunkedCommitment (pt 7 :< Vector.nil)
    , wComm
    , zComm: ChunkedCommitment (pt 39 :< Vector.nil)
    , tComm
    }

compileFqSpongeTranscriptWrap :: Effect (CompiledCircuit WrapField)
compileFqSpongeTranscriptWrap =
  compile noAdvice (Proxy @(Vector 55 (F WrapField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    fqSpongeTranscriptWrapCircuit
