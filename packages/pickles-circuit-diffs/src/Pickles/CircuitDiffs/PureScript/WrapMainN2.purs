module Pickles.CircuitDiffs.PureScript.WrapMainN2
  ( compileWrapMainN2
  ) where

-- | N2 test wrapper for wrap_main library circuit.
-- |
-- | Parses 431 flat inputs and constructs the typed records for
-- | Pickles.Wrap.Main.wrapMainCircuit @2 @2 @1.
-- |
-- | Configuration: branches=2, step_widths=[0,2],
-- | Max_widths_by_slot=[N2,N1], Features.none.

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

type InputSize = 431

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

wrapMainN2Test
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => IvpWrapParams
  -> Vector InputSize (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapMainN2Test { lagrangeComms, blindingH } inputs = do
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

    -- N2: old_bp_chals — 3 vectors of 15 (slot0: 2, slot1: 1)
    oldBpChals0a :: Vector WrapIPARounds (FVar WrapField)
    oldBpChals0a = Vector.generate \j -> at (90 + getFinite j)

    oldBpChals0b :: Vector WrapIPARounds (FVar WrapField)
    oldBpChals0b = Vector.generate \j -> at (105 + getFinite j)

    oldBpChals1 :: Vector WrapIPARounds (FVar WrapField)
    oldBpChals1 = Vector.generate \j -> at (120 + getFinite j)

    advice :: WrapMainAdvice 2 1
    advice =
      { whichBranch: at 30
      , prevProofState:
          { unfProof0: parseUnfinalizedProof at 31
          , unfProof1: parseUnfinalizedProof at 58
          , prevMsgForNextStep: at 85
          }
      , prevStepAccs: { acc0: readPt 86, acc1: readPt 88 }
      -- N2: slot0 has 2 real vectors, no dummy padding
      , paddedChals0: oldBpChals0a :< oldBpChals0b :< Vector.nil
      -- N2: slot1 has 1 real vector, pad with 1 dummy in front
      , paddedChals1: dummyWrapChals :< oldBpChals1 :< Vector.nil
      , slot0Chals: oldBpChals0a :< oldBpChals0b :< Vector.nil
      , slot1Chals: oldBpChals1 :< Vector.nil
      , evals: { evals0: parseEvals at 135, evals1: parseEvals at 224 }
      , wrapDomainIndices: { idx0: at 313, idx1: at 314 }
      , openingProof:
          { lr: (Vector.generate \j -> { l: readPt (315 + 4 * getFinite j), r: readPt (315 + 4 * getFinite j + 2) }) :: Vector StepIPARounds _
          , z1: Type1 (at 379)
          , z2: Type1 (at 380)
          , delta: readPt 381
          , sg: readPt 383
          }
      , messages:
          { wComm: Vector.generate \j -> readPt (385 + 2 * getFinite j)
          , zComm: readPt 415
          , tComm: Vector.generate \j -> readPt (417 + 2 * getFinite j)
          }
      }

    config :: WrapMainConfig 2
    config =
      { stepWidths: 0 :< 2 :< Vector.nil
      , domainLog2s: 16 :< 16 :< Vector.nil
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
            dummyVK :< dummyVK :< Vector.nil
      , lagrangeComms: lagrangeComms
      , blindingH
      , allPossibleDomainLog2s: unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }

  wrapMainCircuit @2 @2 @1 config stmt advice

compileWrapMainN2 :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapMainN2 srsData =
  compilePure (Proxy @(Vector InputSize (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> wrapMainN2Test srsData inputs)
    Kimchi.initialState
