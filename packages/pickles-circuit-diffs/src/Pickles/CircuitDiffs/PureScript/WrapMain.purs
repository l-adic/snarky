module Pickles.CircuitDiffs.PureScript.WrapMain
  ( compileWrapMainN1
  ) where

-- | N1 test wrapper for wrap_main library circuit.
-- |
-- | Parses 401 flat inputs and constructs the typed records for
-- | Pickles.Wrap.Main.wrapMainCircuit @1 @1 @0.
-- |
-- | Configuration: branches=1, step_widths=[1],
-- | Max_widths_by_slot=[N1,N0], Features.none.

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, dummyVestaPt, unsafeIdx)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Types (StepIPARounds, WrapField, WrapIPARounds)
import Pickles.Wrap.Main (ProofWitnessData, UnfinalizedProofData, WrapMainAdvice, WrapMainConfig, WrapStatementData, wrapMainCircuit)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type InputSize = 401

parseUnfinalizedProof :: (Int -> FVar WrapField) -> Int -> UnfinalizedProofData
parseUnfinalizedProof at o =
  { deferredValues:
      { plonk:
          { alpha: asSizedF128 (at (o + 8))
          , beta: asSizedF128 (at (o + 6))
          , gamma: asSizedF128 (at (o + 7))
          , zeta: asSizedF128 (at (o + 9))
          , zetaToSrsLength: Type2 (at (o + 2))
          , zetaToDomainSize: Type2 (at (o + 3))
          , perm: Type2 (at (o + 4))
          }
      , combinedInnerProduct: Type2 (at (o + 0))
      , b: Type2 (at (o + 1))
      , xi: asSizedF128 (at (o + 10))
      , bulletproofChallenges: Vector.generate \j -> asSizedF128 (at (o + 11 + getFinite j))
      }
  , shouldFinalize: coerce (at (o + 26)) :: BoolVar WrapField
  , spongeDigestBeforeEvaluations: at (o + 5)
  , rawFq: at (o + 0) :< at (o + 1) :< at (o + 2) :< at (o + 3) :< at (o + 4) :< Vector.nil
  }

parseEvals :: (Int -> FVar WrapField) -> Int -> ProofWitnessData
parseEvals at base =
  let
    ep b i = { zeta: at (b + 2 * i), omegaTimesZeta: at (b + 2 * i + 1) }
  in
    { allEvals:
        { ftEval1: at (base + 88)
        , publicEvals: { zeta: at base, omegaTimesZeta: at (base + 1) }
        , witnessEvals: Vector.generate \j -> ep (base + 2) (getFinite j)
        , coeffEvals: Vector.generate \j -> ep (base + 32) (getFinite j)
        , zEvals: { zeta: at (base + 62), omegaTimesZeta: at (base + 63) }
        , sigmaEvals: Vector.generate \j -> ep (base + 64) (getFinite j)
        , indexEvals: Vector.generate \j -> ep (base + 76) (getFinite j)
        }
    }

wrapMainN1Test
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => IvpWrapParams
  -> Vector InputSize (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapMainN1Test { lagrangeComms, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    { x: F dummyX, y: F dummyY } = dummyVestaPt
    dummyPt = { x: const_ dummyX, y: const_ dummyY } :: AffinePoint (FVar WrapField)
    dummyWrapChals = map const_ dummyIpaChallenges.wrapExpanded

    stmt :: WrapStatementData
    stmt =
      { plonk:
          { alpha: asSizedF128 (at 0)
          , beta: asSizedF128 (at 1)
          , gamma: asSizedF128 (at 2)
          , zeta: asSizedF128 (at 3)
          , perm: Type1 (at 4)
          , zetaToSrsLength: Type1 (at 5)
          , zetaToDomainSize: Type1 (at 6)
          }
      , xi: asSizedF128 (at 7)
      , combinedInnerProduct: Type1 (at 8)
      , b: Type1 (at 9)
      , branchData: at 10
      , bulletproofChallenges: Vector.generate \j -> asSizedF128 (at (11 + getFinite j))
      , spongeDigestBeforeEvaluations: at 27
      , messagesForNextWrapProofDigest: at 28
      , messagesForNextStepProof: at 29
      }

    oldBpChals0 :: Vector WrapIPARounds (FVar WrapField)
    oldBpChals0 = Vector.generate \j -> at (90 + getFinite j)

    advice :: WrapMainAdvice 1 0
    advice =
      { whichBranch: at 30
      , prevProofState:
          { unfProof0: parseUnfinalizedProof at 31
          , unfProof1: parseUnfinalizedProof at 58
          , prevMsgForNextStep: at 85
          }
      , prevStepAccs: { acc0: readPt 86, acc1: readPt 88 }
      -- N1: slot0 has 1 real vector, pad with 1 dummy in front
      , paddedChals0: dummyWrapChals :< oldBpChals0 :< Vector.nil
      -- N1: slot1 has 0 real vectors, pad with 2 dummies
      , paddedChals1: dummyWrapChals :< dummyWrapChals :< Vector.nil
      , slot0Chals: oldBpChals0 :< Vector.nil
      , slot1Chals: Vector.nil
      , evals: { evals0: parseEvals at 105, evals1: parseEvals at 194 }
      , wrapDomainIndices: { idx0: at 283, idx1: at 284 }
      , openingProof:
          { lr: (Vector.generate \j -> { l: readPt (285 + 4 * getFinite j), r: readPt (285 + 4 * getFinite j + 2) }) :: Vector StepIPARounds _
          , z1: Type1 (at 349)
          , z2: Type1 (at 350)
          , delta: readPt 351
          , sg: readPt 353
          }
      , messages:
          { wComm: Vector.generate \j -> readPt (355 + 2 * getFinite j)
          , zComm: readPt 385
          , tComm: Vector.generate \j -> readPt (387 + 2 * getFinite j)
          }
      }

    config :: WrapMainConfig 1
    config =
      { stepWidths: 1 :< Vector.nil
      , domainLog2s: 16 :< Vector.nil
      , stepKeys:
          let
            dummyVK =
              { sigmaComm: Vector.replicate dummyPt :: Vector 7 _
              , coefficientsComm: Vector.replicate dummyPt :: Vector 15 _
              , genericComm: dummyPt
              , psmComm: dummyPt
              , completeAddComm: dummyPt
              , mulComm: dummyPt
              , emulComm: dummyPt
              , endomulScalarComm: dummyPt
              }
          in
            dummyVK :< Vector.nil
      , lagrangeComms: lagrangeComms
      , blindingH
      , allPossibleDomainLog2s: unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }

  wrapMainCircuit @1 @1 @0 config stmt advice

compileWrapMainN1 :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapMainN1 srsData =
  compilePure (Proxy @(Vector InputSize (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> wrapMainN1Test srsData inputs)
    Kimchi.initialState
