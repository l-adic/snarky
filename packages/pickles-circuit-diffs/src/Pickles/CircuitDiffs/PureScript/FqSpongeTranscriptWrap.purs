module Pickles.CircuitDiffs.PureScript.FqSpongeTranscriptWrap
  ( compileFqSpongeTranscriptWrap
  ) where

import Prelude

import Data.Tuple.Nested (Tuple5, tuple5, uncurry5)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, wrapEndo)
import Pickles.Field (WrapField)
import Pickles.IncrementallyVerifyProof.FqSpongeTranscript (spongeTranscriptOptCircuit)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Types (ChunkedCommitment(..), WrapProofMessages(..))
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, Bool(..), F, FVar, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | `fq_sponge_transcript_wrap_circuit`'s input (OCaml `dump_circuit_impl.ml`), at one chunk.
-- | The mask bits are fields, coerced unchecked (`Boolean.Unsafe.of_cvar` there).
newtype FqSpongeWrapInput f pt = FqSpongeWrapInput
  { sgOldMask :: Vector 2 f
  , indexDigest :: f
  , sgOld :: Vector 2 pt
  , xHat :: pt
  , messages :: WrapProofMessages 1 pt
  }

-- | The wire order.
type FqSpongeWrapTuple f pt = Tuple5 (Vector 2 f) f (Vector 2 pt) pt (WrapProofMessages 1 pt)

toTuple :: forall f pt. FqSpongeWrapInput f pt -> FqSpongeWrapTuple f pt
toTuple (FqSpongeWrapInput r) = tuple5 r.sgOldMask r.indexDigest r.sgOld r.xHat r.messages

fromTuple :: forall f pt. FqSpongeWrapTuple f pt -> FqSpongeWrapInput f pt
fromTuple = uncurry5 \sgOldMask indexDigest sgOld xHat messages ->
  FqSpongeWrapInput { sgOldMask, indexDigest, sgOld, xHat, messages }

instance
  ( CircuitType f fa fv
  , CircuitType f pa pv
  ) =>
  CircuitType f (FqSpongeWrapInput fa pa) (FqSpongeWrapInput fv pv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(FqSpongeWrapTuple fa pa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(FqSpongeWrapTuple fa pa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(FqSpongeWrapTuple fa pa)

-- | Layout only: every row is the library's `spongeTranscriptOptCircuit`, the wrap
-- | verifier's fq-sponge schedule over the conditional sponge.
fqSpongeTranscriptWrapCircuit
  :: forall r
   . UnChecked (FqSpongeWrapInput (FVar WrapField) (AffinePoint (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
fqSpongeTranscriptWrapCircuit (UnChecked (FqSpongeWrapInput input)) =
  let
    WrapProofMessages m = input.messages
  in
    void $ evalSpongeM initialSpongeCircuit $ spongeTranscriptOptCircuit { endo: const_ wrapEndo }
      (map Bool input.sgOldMask)
      { indexDigest: input.indexDigest
      , sgOld: input.sgOld
      , publicComm: ChunkedCommitment (Vector.singleton input.xHat)
      , wComm: m.wComm
      , zComm: m.zComm
      , tComm: Vector.concat (coerce m.tComm :: Vector 7 (Vector 1 (AffinePoint (FVar WrapField))))
      }

compileFqSpongeTranscriptWrap :: Effect (CompiledCircuit WrapField)
compileFqSpongeTranscriptWrap =
  compile noAdvice (Proxy @(UnChecked (FqSpongeWrapInput (F WrapField) (AffinePoint WrapField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    fqSpongeTranscriptWrapCircuit
