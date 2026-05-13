module Pickles.CircuitDiffs.PureScript.StepVerifyN2
  ( compileStepVerifyN2
  ) where

-- | Step_verifier.verify circuit with N2 (2 previous proofs).
-- | Same structure as StepVerify but with Per_proof_witness N2 layout:
-- | prev_challenges has 2 vectors, prev_sg has 2 points.
-- |
-- | Input layout (304 fields):
-- |   0-113:   wrap_proof (114 fields)
-- |   114-143: proof_state (30 fields)
-- |   144-232: prev_proof_evals (89 fields, dead inputs)
-- |   233-264: prev_challenges (2 × 16 = 32 fields)
-- |   265-268: prev_challenge_polynomial_commitments (2 × 2 = 4 fields)
-- |   269-300: unfinalized (32 fields)
-- |   301:     is_base_case
-- |   302:     messages_for_next_wrap_proof
-- |   303:     messages_for_next_step_proof

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, dummyPallasPt, stepEndo, unsafeIdx)
import Pickles.Field (StepField)
import Pickles.IncrementallyVerifyProof (incrementallyVerifyProof, packStatement)
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.OtherField as StepOtherField
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, assertEq, const_, if_)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type StepVerifyN2Params =
  { lagrangeAt :: LagrangeBaseLookup StepField
  , blindingH :: AffinePoint (F StepField)
  }

stepVerifyN2Circuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepVerifyN2Params
  -> Vector 304 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
stepVerifyN2Circuit { lagrangeAt, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    readOtherField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    constDummyPt = let { x: F x', y: F y' } = dummyPallasPt in { x: const_ x', y: const_ y' }

    -- Parse wrap_proof (0-113) — same as N0
    wComm :: Vector 15 (AffinePoint (FVar StepField))
    wComm = Vector.generate \j -> readPt (2 * getFinite j)
    zComm = readPt 30

    tComm :: Vector 7 (AffinePoint (FVar StepField))
    tComm = Vector.generate \j -> readPt (32 + 2 * getFinite j)

    lr :: Vector 15 { l :: AffinePoint (FVar StepField), r :: AffinePoint (FVar StepField) }
    lr = Vector.generate \j ->
      { l: readPt (46 + 4 * getFinite j)
      , r: readPt (46 + 4 * getFinite j + 2)
      }

    -- Parse proof_state (114-143) into WrapStatement — same as N0
    statement =
      { proofState:
          { deferredValues:
              { plonk:
                  { alpha: asSizedF128 (at 114)
                  , beta: asSizedF128 (at 115)
                  , gamma: asSizedF128 (at 116)
                  , zeta: asSizedF128 (at 117)
                  , perm: Type1 (at 120)
                  , zetaToSrsLength: Type1 (at 118)
                  , zetaToDomainSize: Type1 (at 119)
                  }
              , combinedInnerProduct: Type1 (at 121)
              , b: Type1 (at 122)
              , xi: asSizedF128 (at 123)
              , bulletproofChallenges:
                  (Vector.generate \j -> asSizedF128 (at (124 + getFinite j))) :: Vector 16 _
              , branchData:
                  { domainLog2: at 142
                  , proofsVerifiedMask: (coerce (at 140) :: BoolVar StepField) :< (coerce (at 141) :: BoolVar StepField) :< Vector.nil
                  }
              }
          , spongeDigestBeforeEvaluations: at 143
          , messagesForNextWrapProof: at 302
          }
      , messagesForNextStepProof: at 303
      }

    publicInput = packStatement statement

    -- Parse prev_challenge_polynomial_commitments (265-268) — N2: 2 real sg points
    sgOld :: Vector 2 (AffinePoint (FVar StepField))
    sgOld = Vector.generate \j -> readPt (265 + 2 * getFinite j)

    -- Parse unfinalized (269-300) — same layout as N0 but shifted
    unfBase = 269
    deferredValues =
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

    isBaseCase = coerce (at 301) :: BoolVar StepField
    claimedDigest = at (unfBase + 10)

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
      { publicInput
      , sgOld
      , sgOldMask: Vector.replicate ((const_ one))
      , sigmaCommLast: constDummyPt
      , columnComms:
          { index: (Vector.replicate constDummyPt) :: Vector 6 _
          , coeff: (Vector.replicate constDummyPt) :: Vector 15 _
          , sigma: (Vector.replicate constDummyPt) :: Vector 6 _
          }
      , deferredValues
      , wComm: map Vector.singleton wComm
      , zComm: Vector.singleton zComm
      , tComm
      , opening:
          { delta: readPt 110
          , sg: readPt 112
          , lr
          , z1: readOtherField 106
          , z2: readOtherField 108
          }
      }

  -- Run IVP
  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @PallasG StepOtherField.ipaScalarOps ivpParams ivpInput Nothing

  -- Assert digest — UNCONDITIONAL
  assertEq claimedDigest output.spongeDigestBeforeEvaluations

  -- Assert bp challenges — gated by is_base_case
  for_ (Vector.zip deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) -> do
    c2' <- if_ isBaseCase c1 c2
    assertEq c1 c2'

compileStepVerifyN2 :: StepVerifyN2Params -> CompiledCircuit StepField
compileStepVerifyN2 srsData =
  compilePure (Proxy @(Vector 304 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> stepVerifyN2Circuit srsData inputs)
    Kimchi.initialState
