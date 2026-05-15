module Pickles.CircuitDiffs.PureScript.WrapVerify
  ( compileWrapVerify
  ) where

-- | Wrap verify circuit (N1): thin wrapper that parses 196 flat inputs
-- | and calls the library wrapVerify function.

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt, unsafeIdx, wrapEndo)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams, parseIvpWrapInput)
import Pickles.Field (WrapField)
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Types (ChunkedCommitment(..), WrapIPARounds)
import Pickles.Wrap.Verify (wrapVerify)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (VestaG)
import Type.Proxy (Proxy(..))

type N = 1
type InputSize = 196

wrapVerifyCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => IvpWrapParams
  -> Vector InputSize (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapVerifyCircuit { lagrangeAt, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    ivpInput = parseIvpWrapInput (Vector.take inputs)
    constDummyPt = let { x: F x', y: F y' } = dummyVestaPt in { x: const_ x', y: const_ y' }

    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeAt
      , blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }

    -- Layout (N1, 196 inputs):
    --   0-176:   IVP input (parseIvpWrapInput)
    --   177:     messagesForNextWrapProofDigest
    --   178-192: newBpChallenges[0]  (WrapIPARounds = 15)
    --   193:     unused (OCaml dump assumes Tock.Rounds=16 for offset calc, but it's 15;
    --            in N2 this slot is used by newBpChallenges[1])
    --   194-195: sgOld[0] (x, y)
    fullIvpInput =
      { publicInput: ivpInput.publicInput
      , sgOld: readPt 194 :< Vector.nil
      , sgOldMask: (const_ one) :< Vector.nil
      , sigmaCommLast: ChunkedCommitment (Vector.singleton constDummyPt)
      , columnComms:
          { index: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          , coeff: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 15 _
          , sigma: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          }
      , deferredValues: ivpInput.deferredValues
      , wComm: map (ChunkedCommitment <<< Vector.singleton) ivpInput.wComm
      , zComm: ChunkedCommitment (Vector.singleton ivpInput.zComm)
      , tComm: ivpInput.tComm
      , opening: ivpInput.opening
      }

    verifyInput =
      { spongeDigestBeforeEvaluations: ivpInput.claimedDigest
      , messagesForNextWrapProofDigest: at 177
      , bulletproofChallenges: ivpInput.deferredValues.bulletproofChallenges
      , newBpChallenges: ((Vector.generate \j -> at (178 + getFinite j)) :: Vector WrapIPARounds _) :< Vector.nil
      , sg: ivpInput.opening.sg
      }

  wrapVerify ivpParams fullIvpInput verifyInput

compileWrapVerify :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapVerify srsData =
  compilePure (Proxy @(Vector InputSize (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> wrapVerifyCircuit srsData inputs)
    Kimchi.initialState
