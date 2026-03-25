module Pickles.CircuitDiffs.PureScript.WrapVerify
  ( compileWrapVerify
  ) where

-- | Wrap verify circuit: IVP + 4 assertions.
-- | Extends ivp_wrap_circuit with the assertion block from wrap_main.
-- |
-- | Input layout (196 fields):
-- |   0-176:   Same as ivp_wrap_circuit (public_input, plonk, messages, opening, etc.)
-- |   177:     messages_for_next_wrap_proof_digest
-- |   178-192: new_bulletproof_challenges (N × WrapIPARounds fields)
-- |   193:     (unused padding)
-- |   194-195: prev_step_accs (N × 2 fields)
-- |
-- | The message hash (assertion 2) matches OCaml's Wrap_hack.Checked approach:
-- | the sponge is pre-initialized with the state after absorbing
-- | (MaxProofsVerified - N) dummy challenge vectors, then only the real
-- | data is absorbed in-circuit. This avoids generating Poseidon gates for
-- | the dummy absorption.
-- | Reference: mina/src/lib/crypto/pickles/wrap_hack.ml:96-142

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt, unsafeIdx, wrapEndo)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams, parseIvpWrapInput)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Sponge (absorbMany, evalSpongeM, getSpongeState, initialSponge, initialSpongeCircuit, runPureSpongeM, spongeFromConstants)
import RandomOracle.Sponge (Sponge) as Sponge
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

-- | Number of previous proofs for this N1 circuit configuration.
type N = 1

-- | Total input size: 177 (IVP) + 1 (digest) + N*WrapIPARounds (bp challenges) + 1 (padding) + N*2 (sg points)
type InputSize = 196

-- | Pre-computed sponge state after absorbing (MaxProofsVerified - N) dummy
-- | challenge vectors. This matches OCaml's
-- | dummy_messages_for_next_wrap_proof_sponge_states[2 - N].
-- |
-- | For N=1: absorb 1 set of 15 dummy expanded challenges into a fresh sponge.
-- | For N=2: no dummies needed (fresh sponge).
msgHashInitialSponge :: Sponge.Sponge (FVar WrapField)
msgHashInitialSponge =
  let
    -- Number of dummy vectors to absorb = MaxProofsVerified - N = 2 - 1 = 1
    dummyChallenges = dummyIpaChallenges.wrapExpanded
    -- Run a pure sponge, absorbing the dummy challenges
    Tuple _ finalState = runPureSpongeM (initialSponge :: Sponge.Sponge WrapField) do
      absorbMany dummyChallenges
      getSpongeState
  in
    spongeFromConstants { state: finalState.state, spongeState: finalState.spongeState }

wrapVerifyCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => IvpWrapParams
  -> Vector InputSize (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapVerifyCircuit { lagrangeComms, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }

    -- Reuse IvpWrap's parsing for positions 0-176
    ivpInput = parseIvpWrapInput (Vector.take inputs :: Vector 177 _)

    constDummyPt = let { x: F x', y: F y' } = dummyVestaPt in { x: const_ x', y: const_ y' }

    -- Extra inputs (positions 177-195)
    messagesForNextWrapProofDigest = at 177

    newBpChallenges :: Vector N (Vector WrapIPARounds (FVar WrapField))
    newBpChallenges = (Vector.generate \j -> at (178 + getFinite j)) :< Vector.nil

    prevStepAcc = readPt 194

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
      , sgOld: prevStepAcc :< Vector.nil
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
  -- Use pre-computed sponge state (after absorbing dummy challenges) to match OCaml.
  computedMsgDigest <- evalSpongeM msgHashInitialSponge $
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

compileWrapVerify :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapVerify srsData =
  compilePure (Proxy @(Vector InputSize (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> wrapVerifyCircuit srsData inputs)
    Kimchi.initialState
