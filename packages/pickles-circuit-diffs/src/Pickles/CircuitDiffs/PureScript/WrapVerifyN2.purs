module Pickles.CircuitDiffs.PureScript.WrapVerifyN2
  ( compileWrapVerifyN2
  ) where

-- | Wrap verify circuit (N2): thin wrapper that parses 212 flat inputs
-- | and calls the library wrapVerify function.

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt, unsafeIdx, wrapEndo)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams, parseIvpWrapInput)
import Pickles.Field (WrapField)
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Types (WrapIPARounds)
import Pickles.Wrap.Verify (wrapVerify)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (VestaG)
import Type.Proxy (Proxy(..))

type N = 2
type InputSize = 212

wrapVerifyN2Circuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => IvpWrapParams
  -> Vector InputSize (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapVerifyN2Circuit { lagrangeAt, blindingH } inputs = do
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

    fullIvpInput =
      { publicInput: ivpInput.publicInput
      , sgOld: readPt 208 :< readPt 210 :< Vector.nil
      , sgOldMask: Vector.replicate ((const_ one))
      , sigmaCommLast: constDummyPt
      , columnComms:
          { index: (Vector.replicate constDummyPt) :: Vector 6 _
          , coeff: (Vector.replicate constDummyPt) :: Vector 15 _
          , sigma: (Vector.replicate constDummyPt) :: Vector 6 _
          }
      , deferredValues: ivpInput.deferredValues
      , wComm: map Vector.singleton ivpInput.wComm
      , zComm: Vector.singleton ivpInput.zComm
      , tComm: ivpInput.tComm
      , opening: ivpInput.opening
      }

    verifyInput =
      { spongeDigestBeforeEvaluations: ivpInput.claimedDigest
      , messagesForNextWrapProofDigest: at 177
      , bulletproofChallenges: ivpInput.deferredValues.bulletproofChallenges
      , newBpChallenges:
          ((Vector.generate \j -> at (178 + getFinite j)) :: Vector WrapIPARounds _)
            :< ((Vector.generate \j -> at (193 + getFinite j)) :: Vector WrapIPARounds _)
            :< Vector.nil
      , sg: ivpInput.opening.sg
      }

  wrapVerify ivpParams fullIvpInput verifyInput

compileWrapVerifyN2 :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapVerifyN2 srsData =
  compilePure (Proxy @(Vector InputSize (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> wrapVerifyN2Circuit srsData inputs)
    Kimchi.initialState
