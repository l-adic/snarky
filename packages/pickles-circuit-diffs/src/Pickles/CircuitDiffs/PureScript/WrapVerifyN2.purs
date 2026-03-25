module Pickles.CircuitDiffs.PureScript.WrapVerifyN2
  ( compileWrapVerifyN2
  ) where

-- | Wrap verify circuit (N2): IVP + 4 assertions, 2 previous proofs.
-- |
-- | Input layout (212 fields):
-- |   0-176:   Same as ivp_wrap_circuit
-- |   177:     messages_for_next_wrap_proof_digest
-- |   178-192: new_bulletproof_challenges[0] (WrapIPARounds = 15 fields)
-- |   193-207: new_bulletproof_challenges[1] (WrapIPARounds = 15 fields)
-- |   208-209: prev_step_accs[0] (2 fields)
-- |   210-211: prev_step_accs[1] (2 fields)
-- |
-- | For N2 (MaxProofsVerified), no dummy padding is needed in the message hash
-- | sponge — it starts from a fresh sponge (index 2-2=0 in
-- | dummy_messages_for_next_wrap_proof_sponge_states).

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt, unsafeIdx, wrapEndo)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams, parseIvpWrapInput)
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Types (WrapField, WrapIPARounds)
import Pickles.Verify (incrementallyVerifyProof)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.OtherField as WrapOtherField
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, assertEq, assertEqual_, assert_, const_)
import Snarky.Circuit.Kimchi (groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (VestaG)
import Type.Proxy (Proxy(..))

-- | Number of previous proofs for this N2 circuit configuration.
type N = 2

-- | Total input size: 177 (IVP) + 1 (digest) + N*WrapIPARounds (bp challenges) + N*2 (sg points)
type InputSize = 212

wrapVerifyN2Circuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => IvpWrapParams
  -> Vector InputSize (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapVerifyN2Circuit { lagrangeComms, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }

    -- Reuse IvpWrap's parsing for positions 0-176
    ivpInput = parseIvpWrapInput (Vector.take inputs :: Vector 177 _)

    constDummyPt = let { x: F x', y: F y' } = dummyVestaPt in { x: const_ x', y: const_ y' }

    -- Extra inputs (positions 177-211)
    messagesForNextWrapProofDigest = at 177

    newBpChallenges :: Vector N (Vector WrapIPARounds (FVar WrapField))
    newBpChallenges =
      (Vector.generate \j -> at (178 + getFinite j))
        :< (Vector.generate \j -> at (193 + getFinite j))
        :< Vector.nil

    prevStepAcc0 = readPt 208
    prevStepAcc1 = readPt 210

    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeComms
      , blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }

    fullIvpInput =
      { publicInput: ivpInput.publicInput
      , sgOld: prevStepAcc0 :< prevStepAcc1 :< Vector.nil
      , sigmaCommLast: constDummyPt
      , columnComms:
          { index: (Vector.replicate constDummyPt) :: Vector 6 _
          , coeff: (Vector.replicate constDummyPt) :: Vector 15 _
          , sigma: (Vector.replicate constDummyPt) :: Vector 6 _
          }
      , deferredValues: ivpInput.deferredValues
      , wComm: ivpInput.wComm
      , zComm: ivpInput.zComm
      , tComm: ivpInput.tComm
      , opening: ivpInput.opening
      }

  -- Run IVP
  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @VestaG WrapOtherField.ipaScalarOps ivpParams fullIvpInput Nothing

  -- Assertion 1: bulletproof_success (wrap_main.ml:116)
  assert_ output.success

  -- Assertion 2: messages_for_next_wrap_proof hash (wrap_main.ml:117-125)
  -- N2: no dummy padding needed, fresh sponge (index 2-2=0).
  computedMsgDigest <- evalSpongeM initialSpongeCircuit $
    hashMessagesForNextWrapProofCircuit'
      { sg: ivpInput.opening.sg
      , allChallenges: newBpChallenges
      }
  assertEqual_ messagesForNextWrapProofDigest computedMsgDigest

  -- Assertion 3: sponge_digest (wrap_main.ml:126-128)
  assertEqual_ output.spongeDigestBeforeEvaluations ivpInput.claimedDigest

  -- Assertion 4: bp_challenges match (wrap_main.ml:129-135)
  for_ (Vector.zip ivpInput.deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) ->
    assertEq c1 c2

compileWrapVerifyN2 :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapVerifyN2 srsData =
  compilePure (Proxy @(Vector InputSize (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> wrapVerifyN2Circuit srsData inputs)
    Kimchi.initialState
