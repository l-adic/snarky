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
import Pickles.IncrementallyVerifyProof (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams, incrementallyVerifyProof)
import Pickles.PublicInputCommit (class PublicInputCommit)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit, spongeFromConstants)
import Pickles.Types (WrapIPARounds)
import Pickles.Wrap.MessageHash (dummyPaddingSpongeStates, hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.OtherField as WrapOtherField
import Prim.Int (class Add, class Compare, class Mul)
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
  :: forall publicInput sgOldN stepChunks numChunksPred tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5 totalBases totalBasesPred d dPred n r cr
   . PrimeField WrapField
  => PublicInputCommit publicInput WrapField
  => Reflectable d Int
  => Reflectable n Int
  => Reflectable sgOldN Int
  => Reflectable stepChunks Int
  => Reflectable tCommLen Int
  => Reflectable nonSgBases Int
  => Compare n 3 LT
  => Compare 0 stepChunks LT
  => Add 1 numChunksPred stepChunks
  => Add 1 dPred d
  -- Base layout, forwarded to the IVP: xHat(nc) :: ftComm ::
  -- zComm(nc) :: index(6nc) :: wComm(15nc) :: coeff(15nc) ::
  -- sigma(6nc), so the non-sg count is `1 + 44*nc`. `wCoeffN` and
  -- `indexSigmaN` are shared because `Mul`'s fundep would unify
  -- same-RHS counts otherwise.
  => Mul 7 stepChunks tCommLen
  => Add 1 tCommLenPred tCommLen
  => Mul 15 stepChunks wCoeffN
  => Mul 6 stepChunks indexSigmaN
  => Mul 44 stepChunks chunkBases
  => Add 1 chunkBases nonSgBases
  => Add sgOldN nonSgBases totalBases
  => Add stepChunks 1 sg1
  => Add sg1 stepChunks sg2
  => Add sg2 indexSigmaN sg3
  => Add sg3 wCoeffN sg4
  => Add sg4 wCoeffN sg5
  => Add sg5 indexSigmaN nonSgBases
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
