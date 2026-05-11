-- | Wrap verify: IVP + 4 assertions from wrap_main.ml.
-- |
-- | This is the extracted block 5 of wrap_main — the IPA verification and
-- | assertion block that runs after FOP and statement packing.
-- |
-- | The function:
-- |   1. Runs incrementallyVerifyProof (Wrap IVP, verifying a Step proof)
-- |   2. Asserts bulletproof_success
-- |   3. Asserts messages_for_next_wrap_proof hash matches (with pre-computed sponge padding)
-- |   4. Asserts sponge_digest matches
-- |   5. Asserts bp_challenges match
-- |
-- | Reference: mina/src/lib/crypto/pickles/wrap_main.ml:78-135
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
import Pickles.PublicInputCommit (class PublicInputCommit)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit, spongeFromConstants)
import Pickles.Types (WrapIPARounds)
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams, incrementallyVerifyProof)
import Pickles.Wrap.MessageHash (dummyPaddingSpongeStates, hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.OtherField as WrapOtherField
import Pickles.Wrap.Types (IvpBaseline)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, assertEq, assertEqual_, assert_, label)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Input to wrapVerify beyond the IVP params/input.
-- | These are the assertion targets and the data for the message hash.
type WrapVerifyInput n d fv =
  { -- Claimed values from the public input
    spongeDigestBeforeEvaluations :: fv
  , messagesForNextWrapProofDigest :: fv
  , bulletproofChallenges :: Vector d (SizedF 128 fv)
  -- Data for message hash (from FOP / witness)
  , newBpChallenges :: Vector n (Vector WrapIPARounds fv)
  -- Opening proof sg (for message hash)
  , sg :: AffinePoint fv
  }

-- | Run the Wrap IVP and assert all 4 conditions from wrap_main.ml:116-135.
-- |
-- | Specialized to the Wrap field and VestaG curve.
-- |
-- | The message hash uses a pre-computed sponge state to match OCaml's
-- | Wrap_hack.Checked approach: for n < MaxProofsVerified, (2-n) dummy
-- | challenge vectors are absorbed offline into the sponge state.
wrapVerify
  :: forall publicInput sgOldN totalBases totalBasesPred d dPred n t m r
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => PublicInputCommit publicInput WrapField
  => Reflectable d Int
  => Reflectable n Int
  => Reflectable sgOldN Int
  => Compare n 3 LT
  => Add 1 dPred d
  => Add sgOldN IvpBaseline totalBases
  => Add 1 totalBasesPred totalBases
  => IncrementallyVerifyProofParams WrapField r
  -> IncrementallyVerifyProofInput publicInput sgOldN d (FVar WrapField) (Type1 (FVar WrapField))
  -> WrapVerifyInput n d (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapVerify ivpParams ivpInput verifyInput = do
  -- Run IVP
  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @VestaG WrapOtherField.ipaScalarOps ivpParams ivpInput Nothing

  -- Assertion 1: bulletproof_success (wrap_main.ml:116)
  label "ivp-assert-bp-success" $ assert_ output.success

  -- Assertion 2: messages_for_next_wrap_proof hash (wrap_main.ml:117-125)
  -- Pre-computed sponge state: index (2-n) in dummy_messages_for_next_wrap_proof_sponge_states.
  -- n dummy vectors have already been provided as real data, so (2-n) are absorbed offline.
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

  -- Assertion 3: sponge_digest (wrap_main.ml:126-128)
  label "ivp-assert-sponge-digest" $ assertEqual_ verifyInput.spongeDigestBeforeEvaluations output.spongeDigestBeforeEvaluations

  -- Assertion 4: bp_challenges match (wrap_main.ml:129-135)
  label "ivp-assert-bp-challenges" $ for_ (Vector.zip verifyInput.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) ->
    assertEq c1 c2
