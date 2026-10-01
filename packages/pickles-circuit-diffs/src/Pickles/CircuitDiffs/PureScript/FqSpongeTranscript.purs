module Pickles.CircuitDiffs.PureScript.FqSpongeTranscript
  ( compileFqSpongeTranscriptStep
  ) where

import Prelude

import Data.Tuple.Nested (Tuple4, tuple4, uncurry4)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, stepEndo)
import Pickles.Field (StepField)
import Pickles.IncrementallyVerifyProof.FqSpongeTranscript (spongeTranscriptCircuit)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Types (ChunkedCommitment(..), WrapProofMessages(..))
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | `fq_sponge_transcript_step_circuit`'s input (OCaml `dump_circuit_impl.ml`), at one chunk.
newtype FqSpongeStepInput f pt = FqSpongeStepInput
  { indexDigest :: f
  , sgOld :: Vector 2 pt
  , xHat :: pt
  , messages :: WrapProofMessages 1 pt
  }

-- | The wire order.
type FqSpongeStepTuple f pt = Tuple4 f (Vector 2 pt) pt (WrapProofMessages 1 pt)

toTuple :: forall f pt. FqSpongeStepInput f pt -> FqSpongeStepTuple f pt
toTuple (FqSpongeStepInput r) = tuple4 r.indexDigest r.sgOld r.xHat r.messages

fromTuple :: forall f pt. FqSpongeStepTuple f pt -> FqSpongeStepInput f pt
fromTuple = uncurry4 \indexDigest sgOld xHat messages ->
  FqSpongeStepInput { indexDigest, sgOld, xHat, messages }

instance
  ( CircuitType f fa fv
  , CircuitType f pa pv
  ) =>
  CircuitType f (FqSpongeStepInput fa pa) (FqSpongeStepInput fv pv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(FqSpongeStepTuple fa pa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(FqSpongeStepTuple fa pa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(FqSpongeStepTuple fa pa)

-- | Layout only: every row is the library's `spongeTranscriptCircuit`, the step
-- | verifier's fq-sponge schedule, with `x_hat` handed in as the input point.
fqSpongeTranscriptStepCircuit
  :: forall r
   . UnChecked (FqSpongeStepInput (FVar StepField) (AffinePoint (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
fqSpongeTranscriptStepCircuit (UnChecked (FqSpongeStepInput input)) =
  let
    WrapProofMessages m = input.messages
  in
    void $ evalSpongeM initialSpongeCircuit $ spongeTranscriptCircuit { endo: const_ stepEndo }
      { indexDigest: input.indexDigest
      , sgOld: input.sgOld
      , wComm: m.wComm
      , zComm: m.zComm
      , tComm: Vector.concat (coerce m.tComm :: Vector 7 (Vector 1 (AffinePoint (FVar StepField))))
      }
      (pure (Vector.singleton input.xHat))

compileFqSpongeTranscriptStep :: Effect (CompiledCircuit StepField)
compileFqSpongeTranscriptStep =
  compile noAdvice (Proxy @(UnChecked (FqSpongeStepInput (F StepField) (AffinePoint StepField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    fqSpongeTranscriptStepCircuit
