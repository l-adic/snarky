module Pickles.CircuitDiffs.PureScript.WrapVerifyN2
  ( compileWrapVerifyN2
  ) where

-- | Wrap verify circuit (N2): the library `wrapVerify` over the dump's typed input.

import Prelude

import Data.Maybe (Maybe(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt, wrapEndo)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpHarnessInput(..), IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.WrapVerify (WrapVerifyInput(..))
import Pickles.Field (WrapField)
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Types (ChunkedCommitment(..), WrapProofMessages(..))
import Pickles.Wrap.Verify (wrapVerify)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, Snarky, UnChecked(..), const_)
import Snarky.Circuit.Kimchi (groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

wrapVerifyN2Circuit
  :: forall r
   . IvpWrapParams
  -> UnChecked (WrapVerifyInput 2 Unit (FVar WrapField) (BoolVar WrapField) (AffinePoint (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
wrapVerifyN2Circuit { lagrangeAt, blindingH } (UnChecked (WrapVerifyInput input)) = do
  let
    IvpHarnessInput ivp = input.ivp
    WrapProofMessages m = ivp.messages
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
      { publicInput: ivp.publicInput
      , sgOld: input.sgOld
      , sgOldMask: Just (Vector.replicate (const_ one))
      , sigmaCommLast: ChunkedCommitment (Vector.singleton constDummyPt)
      , columnComms:
          { index: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          , coeff: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 15 _
          , sigma: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          }
      , deferredValues: ivp.deferredValues
      , wComm: m.wComm
      , zComm: m.zComm
      , tComm: Vector.concat (coerce m.tComm :: Vector 7 (Vector 1 (AffinePoint (FVar WrapField))))
      , opening: ivp.opening
      }

    verifyInput =
      { spongeDigestBeforeEvaluations: ivp.claimedDigest
      , messagesForNextWrapProofDigest: input.messagesForNextWrapProofDigest
      , bulletproofChallenges: ivp.deferredValues.bulletproofChallenges
      , newBpChallenges: input.newBpChallenges
      , sg: ivp.opening.sg
      }

  wrapVerify ivpParams fullIvpInput verifyInput

compileWrapVerifyN2 :: IvpWrapParams -> Effect (CompiledCircuit WrapField)
compileWrapVerifyN2 srsData =
  compile noAdvice
    (Proxy @(UnChecked (WrapVerifyInput 2 Unit (F WrapField) Boolean (AffinePoint WrapField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    (wrapVerifyN2Circuit srsData)
