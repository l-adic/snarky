module Pickles.CircuitDiffs.PureScript.WrapVerifyN2
  ( compileWrapVerifyN2
  ) where

-- | Wrap verify circuit (N2): thin wrapper that parses 212 flat inputs
-- | and calls the library wrapVerify function.

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt, unsafeIdx, wrapEndo)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams, parseIvpWrapInput)
import Pickles.Field (WrapField)
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Types (ChunkedCommitment(..), WrapIPARounds)
import Pickles.Wrap.Verify (wrapVerify)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, curveParams)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

type N = 2
type InputSize = 212

wrapVerifyN2Circuit
  :: forall r
   . PrimeField WrapField
  => IvpWrapParams
  -> Vector InputSize (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
wrapVerifyN2Circuit { lagrangeAt, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = AffinePoint { x: at i, y: at (i + 1) }
    ivpInput = parseIvpWrapInput (Vector.take inputs)
    constDummyPt = let AffinePoint { x: F x', y: F y' } = dummyVestaPt in AffinePoint { x: const_ x', y: const_ y' }

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
      , newBpChallenges:
          ((Vector.generate \j -> at (178 + getFinite j)) :: Vector WrapIPARounds _)
            :< ((Vector.generate \j -> at (193 + getFinite j)) :: Vector WrapIPARounds _)
            :< Vector.nil
      , sg: ivpInput.opening.sg
      }

  wrapVerify ivpParams fullIvpInput verifyInput

compileWrapVerifyN2 :: IvpWrapParams -> Effect (CompiledCircuit WrapField)
compileWrapVerifyN2 srsData =
  compile noAdvice (Proxy @(Vector InputSize (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> wrapVerifyN2Circuit srsData inputs)
