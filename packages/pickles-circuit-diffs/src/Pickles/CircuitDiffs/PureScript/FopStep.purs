module Pickles.CircuitDiffs.PureScript.FopStep
  ( FopStepInput
  , parseFopStepInput
  , fopStepCircuit
  , compileFopStep
  ) where

import Prelude

import Data.Fin (Finite, getFinite)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, domainLog2, srsLengthLog2, stepEndo, unsafeIdx)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofOutput, finalizeOtherProofCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (StepField)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F, FVar, SizedF, Snarky, const_)
import Snarky.Circuit.Kimchi (Type1(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

type FopStepInput =
  { plonk ::
      { alpha :: SizedF 128 (FVar StepField)
      , beta :: SizedF 128 (FVar StepField)
      , gamma :: SizedF 128 (FVar StepField)
      , zeta :: SizedF 128 (FVar StepField)
      , zetaToSrsLength :: Type1 (FVar StepField)
      , zetaToDomainSize :: Type1 (FVar StepField)
      , perm :: Type1 (FVar StepField)
      }
  , combinedInnerProduct :: Type1 (FVar StepField)
  , b :: Type1 (FVar StepField)
  , xi :: SizedF 128 (FVar StepField)
  , bulletproofChallenges :: Vector 16 (SizedF 128 (FVar StepField))
  , mask :: Vector 2 (BoolVar StepField)
  , spongeDigestBeforeEvaluations :: FVar StepField
  , domainLog2Var :: FVar StepField
  , allEvals ::
      { ftEval1 :: FVar StepField
      , publicEvals :: { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      , witnessEvals :: Vector 15 { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      , coeffEvals :: Vector 15 { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      , zEvals :: { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      , sigmaEvals :: Vector 6 { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      , indexEvals :: Vector 6 { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      }
  , prevChallenges :: Vector 2 (Vector 16 (FVar StepField))
  }

parseFopStepInput :: Vector 151 (FVar StepField) -> FopStepInput
parseFopStepInput inputs =
  let
    at = unsafeIdx inputs

    evalPair :: forall n. Int -> Finite n -> { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
    evalPair base j =
      { zeta: at (base + 2 * getFinite j)
      , omegaTimesZeta: at (base + 2 * getFinite j + 1)
      }
  in
    { plonk:
        { alpha: asSizedF128 (at 0)
        , beta: asSizedF128 (at 1)
        , gamma: asSizedF128 (at 2)
        , zeta: asSizedF128 (at 3)
        , zetaToSrsLength: Type1 (at 4)
        , zetaToDomainSize: Type1 (at 5)
        , perm: Type1 (at 6)
        }
    , combinedInnerProduct: Type1 (at 7)
    , b: Type1 (at 8)
    , xi: asSizedF128 (at 9)
    , bulletproofChallenges: Vector.generate \j -> asSizedF128 (at (10 + getFinite j))
    , mask: Vector.generate \j -> coerce (at (26 + getFinite j))
    , spongeDigestBeforeEvaluations: at 150
    , domainLog2Var: at 28
    , allEvals:
        { ftEval1: at 117
        , publicEvals: { zeta: at 29, omegaTimesZeta: at 30 }
        , witnessEvals: Vector.generate (evalPair 31)
        , coeffEvals: Vector.generate (evalPair 61)
        , zEvals: { zeta: at 91, omegaTimesZeta: at 92 }
        , sigmaEvals: Vector.generate (evalPair 93)
        , indexEvals: Vector.generate (evalPair 105)
        }
    , prevChallenges: Vector.generate \j ->
        Vector.generate \k -> at (118 + 16 * getFinite j + getFinite k)
    }

fopStepCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => FopStepInput
  -> Snarky (KimchiConstraint StepField) t m (FinalizeOtherProofOutput 16 StepField)
fopStepCircuit input =
  let
    unfinalized =
      { deferredValues:
          { plonk: input.plonk
          , combinedInnerProduct: input.combinedInnerProduct
          , b: input.b
          , xi: input.xi
          , bulletproofChallenges: input.bulletproofChallenges
          }
      , shouldFinalize: coerce (const_ one :: FVar StepField)
      , spongeDigestBeforeEvaluations: input.spongeDigestBeforeEvaluations
      }
    params =
      { domain:
          { generator: LinFFI.domainGenerator @StepField domainLog2
          , shifts: LinFFI.domainShifts @StepField domainLog2
          }
      , domainLog2
      , srsLengthLog2
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      }
  in
    finalizeOtherProofCircuit StepOtherField.fopShiftOps params
      { unfinalized
      , witness: { allEvals: input.allEvals }
      , mask: input.mask
      , prevChallenges: input.prevChallenges
      , domainLog2Var: input.domainLog2Var
      }

compileFopStep :: CompiledCircuit StepField
compileFopStep =
  compilePure (Proxy @(Vector 151 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ fopStepCircuit (parseFopStepInput inputs))
    Kimchi.initialState
