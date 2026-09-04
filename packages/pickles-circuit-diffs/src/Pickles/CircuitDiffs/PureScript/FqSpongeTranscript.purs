module Pickles.CircuitDiffs.PureScript.FqSpongeTranscript
  ( compileFqSpongeTranscriptStep
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, stepEndo, unsafeIdx)
import Pickles.Field (StepField)
import Pickles.IncrementallyVerifyProof.FqSpongeTranscript (spongeTranscriptCircuit)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Types (ChunkedCommitment(..))
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, Snarky, const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | `fq_sponge_transcript_step_circuit` (OCaml `dump_circuit_impl.ml`): the index digest
-- | at 0, two `sg_old` points at 1-4, `x_hat` at 5-6, the 15 `w_comm` points at 7-36,
-- | `z_comm` at 37-38 and the 7 `t_comm` points at 39-52, all at one chunk.
-- |
-- | Layout only: every row is the library's `spongeTranscriptCircuit`, the step
-- | verifier's fq-sponge schedule, with `x_hat` handed in as the input point.
fqSpongeTranscriptStepCircuit
  :: forall r
   . Vector 53 (FVar StepField)
  -> Snarky StepField (KimchiConstraint StepField) r Unit
fqSpongeTranscriptStepCircuit inputs = do
  let
    at = unsafeIdx inputs
    pt i = AffinePoint { x: at i, y: at (i + 1) }

    sgOld :: Vector 2 (AffinePoint (FVar StepField))
    sgOld = Vector.generate \j -> pt (1 + 2 * getFinite j)

    wComm :: Vector 15 (ChunkedCommitment 1 (AffinePoint (FVar StepField)))
    wComm = Vector.generate \j -> ChunkedCommitment (pt (7 + 2 * getFinite j) :< Vector.nil)

    tComm :: Vector 7 (AffinePoint (FVar StepField))
    tComm = Vector.generate \j -> pt (39 + 2 * getFinite j)

    xHat :: Vector 1 (AffinePoint (FVar StepField))
    xHat = pt 5 :< Vector.nil
  void $ evalSpongeM initialSpongeCircuit $ spongeTranscriptCircuit { endo: const_ stepEndo }
    { indexDigest: at 0
    , sgOld
    , wComm
    , zComm: ChunkedCommitment (pt 37 :< Vector.nil)
    , tComm
    }
    (pure xHat)

compileFqSpongeTranscriptStep :: Effect (CompiledCircuit StepField)
compileFqSpongeTranscriptStep =
  compile noAdvice (Proxy @(Vector 53 (F StepField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    fqSpongeTranscriptStepCircuit
