module Pickles.CircuitDiffs.PureScript.StepVerify
  ( compileStepVerify
  , StepVerifyParams
  ) where

-- | Step_verifier.verify circuit test.
-- | Parses flat inputs, builds WrapStatement, calls packStatement + verify.

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, dummyPallasPt, dummyWrapSg, stepEndo, unsafeIdx)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Verify (incrementallyVerifyProof, packStatement)
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

-- | Step_verifier.verify circuit — tests the full verify pipeline:
-- |   1. packStatement (Spec.pack equivalent)
-- |   2. incrementallyVerifyProof
-- |   3. Assertions (digest + bp challenges)
-- |
-- | Input layout (268 fields):
-- |   0-113:   wrap_proof (114 fields)
-- |   114-143: proof_state (30 fields)
-- |   144-232: all_evals (89 fields, dead inputs)
-- |   233-264: unfinalized (32 fields)
-- |   265:     is_base_case
-- |   266:     messages_for_next_wrap_proof
-- |   267:     messages_for_next_step_proof

type StepVerifyParams =
  { lagrangeAt :: LagrangeBaseLookup StepField
  , blindingH :: AffinePoint (F StepField)
  }

stepVerifyCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepVerifyParams
  -> Vector 268 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
stepVerifyCircuit { lagrangeAt, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    readOtherField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    constDummySg :: AffinePoint (FVar StepField)
    constDummySg = { x: const_ dummyWrapSg.x, y: const_ dummyWrapSg.y }
    constDummyPt = let { x: F x', y: F y' } = dummyPallasPt in { x: const_ x', y: const_ y' }

    -- Parse wrap_proof (0-113)
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

    -- Parse proof_state (114-143) into WrapStatement
    -- Hlist order: plonk(alpha,beta,gamma,zeta,zetaToSrs,zetaToDom,perm),
    --             cip, b, xi, bp_challenges(16), mask(2), domain_log2, digest
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
          , messagesForNextWrapProof: at 266
          }
      , messagesForNextStepProof: at 267
      }

    -- packStatement: Spec.pack(to_data(statement))
    publicInput = packStatement statement

    -- Parse unfinalized (233-264)
    deferredValues =
      { plonk:
          { alpha: asSizedF128 (at 246)
          , beta: asSizedF128 (at 244)
          , gamma: asSizedF128 (at 245)
          , zeta: asSizedF128 (at 247)
          , perm: readOtherField 241
          , zetaToSrsLength: readOtherField 237
          , zetaToDomainSize: readOtherField 239
          }
      , combinedInnerProduct: readOtherField 233
      , b: readOtherField 235
      , xi: asSizedF128 (at 248)
      , bulletproofChallenges:
          (Vector.generate \j -> asSizedF128 (at (249 + getFinite j))) :: Vector 15 _
      }

    isBaseCase = coerce (at 265) :: BoolVar StepField
    claimedDigest = at 243

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
      , sgOld: constDummySg :< constDummySg :< Vector.nil
      , sgOldMask: Vector.replicate ((const_ one))
      , sigmaCommLast: constDummyPt
      , columnComms:
          { index: (Vector.replicate constDummyPt) :: Vector 6 _
          , coeff: (Vector.replicate constDummyPt) :: Vector 15 _
          , sigma: (Vector.replicate constDummyPt) :: Vector 6 _
          }
      , deferredValues
      , wComm
      , zComm
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

  -- Assert digest — UNCONDITIONAL (step_verifier.ml:1294)
  assertEq claimedDigest output.spongeDigestBeforeEvaluations

  -- Assert bp challenges — gated by is_base_case (step_verifier.ml:1300-1314)
  for_ (Vector.zip deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) -> do
    c2' <- if_ isBaseCase c1 c2
    assertEq c1 c2'

compileStepVerify :: StepVerifyParams -> CompiledCircuit StepField
compileStepVerify srsData =
  compilePure (Proxy @(Vector 268 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> stepVerifyCircuit srsData inputs)
    Kimchi.initialState
