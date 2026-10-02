module Pickles.CircuitDiffs.PureScript.IvpStep
  ( compileIvpStep
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyPallasPt, dummyWrapSg, stepEndo)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpHarnessInput(..))
import Pickles.CircuitDiffs.PureScript.XhatStep (XhatStepInput)
import Pickles.Field (StepField)
import Pickles.IncrementallyVerifyProof (incrementallyVerifyProof)
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (ChunkedCommitment(..), WrapProofMessages(..))
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, Snarky, UnChecked(..), assertEq, assertEqual_, const_)
import Snarky.Circuit.Kimchi (SplitField, Type2, groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

type IvpStepParams =
  { lagrangeAt :: LagrangeBaseLookup 1 StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | `ivp_step_circuit`'s input: the packed wrap statement (`xhat_step_circuit`'s input), the
-- | wrap proof at 15 rounds, split Type2-shifted.
type IvpStepInput f b pt = IvpHarnessInput (XhatStepInput f) 15 f pt (Type2 (SplitField f b))

-- | The library's `incrementallyVerifyProof` on the step side, the two `sg_old` the dummy wrap
-- | `sg` and the key the dummy, then the digest and challenges against the claims.
ivpStepCircuit
  :: forall r
   . IvpStepParams
  -> UnChecked (IvpStepInput (FVar StepField) (BoolVar StepField) (AffinePoint (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
ivpStepCircuit { lagrangeAt, blindingH } (UnChecked (IvpHarnessInput input)) = do
  let
    WrapProofMessages m = input.messages

    constDummySg :: AffinePoint (FVar StepField)
    constDummySg = AffinePoint { x: const_ (unwrap dummyWrapSg).x, y: const_ (unwrap dummyWrapSg).y }

    constDummyPt = let AffinePoint { x: F x', y: F y' } = dummyPallasPt in AffinePoint { x: const_ x', y: const_ y' }

    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeAt
      , blindingH
      , correctionMode: PureCorrections
      , endo: stepEndo
      , groupMapParams: groupMapParams (Proxy @PallasG)
      , useOptSponge: false
      }
    ivpInput =
      { publicInput: input.publicInput
      , sgOld: constDummySg :< constDummySg :< Vector.nil
      , sgOldMask: Nothing
      -- VK data as circuit variables (dummy constants for circuit-diff test)
      , sigmaCommLast: ChunkedCommitment (Vector.singleton constDummyPt)
      , columnComms:
          { index: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          , coeff: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 15 _
          , sigma: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          }
      , deferredValues: input.deferredValues
      , wComm: m.wComm
      , zComm: m.zComm
      , tComm: Vector.concat (coerce m.tComm :: Vector 7 (Vector 1 (AffinePoint (FVar StepField))))
      , opening: input.opening
      }
  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @PallasG StepOtherField.ipaScalarOps ivpParams ivpInput Nothing
  assertEqual_ output.spongeDigestBeforeEvaluations input.claimedDigest
  for_ (Vector.zip input.deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) ->
    assertEq c1 c2

compileIvpStep :: IvpStepParams -> Effect (CompiledCircuit StepField)
compileIvpStep srsData =
  compile noAdvice
    (Proxy @(UnChecked (IvpStepInput (F StepField) Boolean (AffinePoint StepField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    (ivpStepCircuit srsData)
