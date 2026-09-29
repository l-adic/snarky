-- | The wrap circuit's final block, run after finalize-other-proof and
-- | statement packing.
module Pickles.Wrap.Verify
  ( WrapVerifyInput
  , wrapVerify
  ) where

import Prelude

import Data.Fin (reflectFinite)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (WrapField)
import Pickles.IncrementallyVerifyProof (class StepChunkLayout, IncrementallyVerifyProofInput, IncrementallyVerifyProofParams, incrementallyVerifyProof)
import Pickles.PublicInputCommit (class PublicInputCommit)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit, spongeFromConstants)
import Pickles.Types (WrapIPARounds)
import Pickles.Wrap.MessageHash (dummyPaddingSpongeStates, hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.OtherField as WrapOtherField
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (FVar, Snarky, assertEq, assertEqual_, assert_, label)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | What `wrapVerify` needs beyond the IVP params and input.
type WrapVerifyInput n d fv =
  { -- Claimed in the wrap statement
    spongeDigestBeforeEvaluations :: fv
  , messagesForNextWrapProofDigest :: fv
  , bulletproofChallenges :: Vector d (SizedF 128 fv)
  -- Hashed into the messages-for-next-wrap digest
  , newBpChallenges :: Vector n (Vector WrapIPARounds fv)
  , sg :: AffinePoint fv
  }

-- | Run the wrap IVP over `VestaG` and assert bullet-proof success,
-- | the messages-for-next-wrap digest, the sponge digest, and the
-- | bullet-proof challenges.
wrapVerify
  :: forall publicInput sgOldN stepChunks numChunksPred tCommLen tCommLenPred nonSgBases totalBases totalBasesPred d dPred n r cr
   . PrimeField WrapField
  => PublicInputCommit publicInput WrapField
  => Reflectable d Int
  => Reflectable n Int
  => Reflectable sgOldN Int
  => Reflectable stepChunks Int
  => Reflectable tCommLen Int
  => Compare n 3 LT
  => Compare 0 stepChunks LT
  => Add 1 numChunksPred stepChunks
  => Add 1 dPred d
  => StepChunkLayout stepChunks tCommLen nonSgBases
  => Add 1 tCommLenPred tCommLen
  => Add sgOldN nonSgBases totalBases
  => Add 1 totalBasesPred totalBases
  => IncrementallyVerifyProofParams stepChunks WrapField r
  -> IncrementallyVerifyProofInput publicInput sgOldN stepChunks tCommLen d (FVar WrapField) (Type1 (FVar WrapField))
  -> WrapVerifyInput n d (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) cr Unit
wrapVerify ivpParams ivpInput verifyInput = do
  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @VestaG WrapOtherField.ipaScalarOps ivpParams ivpInput Nothing

  label "ivp-assert-bp-success" $ assert_ output.success

  -- `n` real challenge vectors were supplied, so the sponge starts
  -- from the state with `PaddedLength - n` dummies already absorbed.
  let
    states = dummyPaddingSpongeStates dummyIpaChallenges.wrapExpanded
    paddingState = Vector.index states (reflectFinite @n)
    msgHashSponge = spongeFromConstants { state: paddingState.state, spongeState: paddingState.spongeState }
  computedDigest <- label "ivp-hash-msg-for-next-wrap" $ evalSpongeM msgHashSponge $
    hashMessagesForNextWrapProofCircuit'
      { sg: verifyInput.sg
      , allChallenges: verifyInput.newBpChallenges
      }
  label "ivp-assert-msg-wrap-hash" $ assertEqual_ verifyInput.messagesForNextWrapProofDigest computedDigest

  label "ivp-assert-sponge-digest" $ assertEqual_ verifyInput.spongeDigestBeforeEvaluations output.spongeDigestBeforeEvaluations

  label "ivp-assert-bp-challenges" $ for_ (Vector.zip verifyInput.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) ->
    assertEq c1 c2
