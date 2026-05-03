module Pickles.CircuitDiffs.PureScript.FullStepVerifyOne
  ( compileFullStepVerifyOne
  , FullStepVerifyOneParams
  ) where

-- | Thin wrapper around Pickles.Step.VerifyOne.verifyOne for circuit diff testing.
-- | Parses 286 flat inputs and calls the library function.

import Prelude

import Data.Fin (getFinite)
import Data.Fin as Fin
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, dummyPallasPt, dummyWrapSg, stepEndo, unsafeIdx)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Step.FinalizeOtherProof (DomainMode(..))
import Pickles.Step.VerifyOne (verifyOne)
import Pickles.Types (StepField)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type FullStepVerifyOneParams =
  { lagrangeAt :: LagrangeBaseLookup StepField
  , blindingH :: AffinePoint (F StepField)
  }

fullStepVerifyOneCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => FullStepVerifyOneParams
  -> Vector 286 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
fullStepVerifyOneCircuit { lagrangeAt, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    readOtherField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    constDummyPt = let { x: F x', y: F y' } = dummyPallasPt in { x: const_ x', y: const_ y' }

    constDummySg :: AffinePoint (FVar StepField)
    constDummySg = { x: const_ dummyWrapSg.x, y: const_ dummyWrapSg.y }

    o = 1 -- offset for app_state

    -- Parse flat inputs into VerifyOneInput
    evalPair :: forall n. Int -> Fin.Finite n -> { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
    evalPair base j =
      { zeta: at (base + 2 * Fin.getFinite j)
      , omegaTimesZeta: at (base + 2 * Fin.getFinite j + 1)
      }

    proofStateBase = o + 114
    evalsBase = o + 144
    unfBase = 252
    mask0 = at (proofStateBase + 26)
    mask1 = at (proofStateBase + 27)

    input =
      { appStateFields: [ at 0 ]
      , wComm: (Vector.generate \j -> readPt (o + 2 * getFinite j)) :: Vector 15 _
      , zComm: readPt (o + 30)
      , tComm: (Vector.generate \j -> readPt (o + 32 + 2 * getFinite j)) :: Vector 7 _
      , lr:
          ( Vector.generate \j ->
              { l: readPt (o + 46 + 4 * getFinite j)
              , r: readPt (o + 46 + 4 * getFinite j + 2)
              }
          ) :: Vector 15 _
      , z1: readOtherField (o + 106)
      , z2: readOtherField (o + 108)
      , delta: readPt (o + 110)
      , sg: readPt (o + 112)
      , proofState:
          { plonk:
              { alpha: asSizedF128 (at proofStateBase)
              , beta: asSizedF128 (at (proofStateBase + 1))
              , gamma: asSizedF128 (at (proofStateBase + 2))
              , zeta: asSizedF128 (at (proofStateBase + 3))
              , perm: Type1 (at (proofStateBase + 6))
              , zetaToSrsLength: Type1 (at (proofStateBase + 4))
              , zetaToDomainSize: Type1 (at (proofStateBase + 5))
              }
          , combinedInnerProduct: Type1 (at (proofStateBase + 7))
          , b: Type1 (at (proofStateBase + 8))
          , xi: asSizedF128 (at (proofStateBase + 9))
          , bulletproofChallenges:
              (Vector.generate \j -> asSizedF128 (at (proofStateBase + 10 + getFinite j))) :: Vector 16 _
          , spongeDigest: at (proofStateBase + 29)
          }
      , allEvals:
          { ftEval1: at (evalsBase + 88)
          , publicEvals: { zeta: at evalsBase, omegaTimesZeta: at (evalsBase + 1) }
          , witnessEvals: (Vector.generate (evalPair (evalsBase + 2))) :: Vector 15 _
          , coeffEvals: (Vector.generate (evalPair (evalsBase + 32))) :: Vector 15 _
          , zEvals: { zeta: at (evalsBase + 62), omegaTimesZeta: at (evalsBase + 63) }
          , sigmaEvals: (Vector.generate (evalPair (evalsBase + 64))) :: Vector 6 _
          , indexEvals: (Vector.generate (evalPair (evalsBase + 76))) :: Vector 6 _
          }
      , prevChallenges: (\x -> x :< Vector.nil) (Vector.generate \j -> at (234 + getFinite j))
      , prevSgs: readPt 250 :< Vector.nil
      , unfinalized:
          { deferredValues:
              { plonk:
                  { alpha: asSizedF128 (at (unfBase + 13))
                  , beta: asSizedF128 (at (unfBase + 11))
                  , gamma: asSizedF128 (at (unfBase + 12))
                  , zeta: asSizedF128 (at (unfBase + 14))
                  , perm: readOtherField (unfBase + 8)
                  , zetaToSrsLength: readOtherField (unfBase + 4)
                  , zetaToDomainSize: readOtherField (unfBase + 6)
                  }
              , combinedInnerProduct: readOtherField (unfBase + 0)
              , b: readOtherField (unfBase + 2)
              , xi: asSizedF128 (at (unfBase + 15))
              , bulletproofChallenges:
                  (Vector.generate \j -> asSizedF128 (at (unfBase + 16 + getFinite j))) :: Vector 15 _
              }
          , shouldFinalize: coerce (at (unfBase + 31)) :: BoolVar StepField
          , claimedDigest: at (unfBase + 10)
          }
      , messagesForNextWrapProof: at 284
      , mustVerify: coerce (at 285) :: BoolVar StepField
      , branchData: { mask0, mask1, domainLog2Var: at (proofStateBase + 28) }
      , proofMask: (coerce mask1 :: BoolVar StepField) :< Vector.nil
      , vkComms:
          { sigma: (Vector.replicate constDummyPt) :: Vector 6 _
          , sigmaLast: constDummyPt
          , coeff: (Vector.replicate constDummyPt) :: Vector 15 _
          , index: (Vector.replicate constDummyPt) :: Vector 6 _
          }
      , sgOld: constDummySg :< readPt 250 :< Vector.nil
      }

    domainLog2 = 16
    fopParams =
      { domains:
          { generator: const_ (LinFFI.domainGenerator @StepField domainLog2)
          , log2: domainLog2
          } :< Vector.nil
      , shifts: map const_ (LinFFI.domainShifts @StepField domainLog2)
      , srsLengthLog2: 16
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      , domainMode: KnownDomainsMode
      }

    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeAt
      , blindingH
      , correctionMode: PureCorrections
      , endo: stepEndo
      , groupMapParams: groupMapParams (Proxy @PallasG)
      , useOptSponge: false
      }

  _result <- verifyOne fopParams input ivpParams
  pure unit

compileFullStepVerifyOne :: FullStepVerifyOneParams -> CompiledCircuit StepField
compileFullStepVerifyOne params =
  compilePure (Proxy @(Vector 286 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> fullStepVerifyOneCircuit params inputs)
    Kimchi.initialState
