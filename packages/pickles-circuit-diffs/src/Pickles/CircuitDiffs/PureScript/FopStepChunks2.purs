-- | The step finalize over a two-chunk step proof, as a comparison
-- | target: `finalizeOtherProofCircuit` with every evaluation carried
-- | at two chunks, so the circuit absorbs every chunk and recombines
-- | them in circuit. Every other parameter is `FopStep`'s, except
-- | `zkRows`, which follows the chunk count.
-- |
-- | The input layout is `FopStep`'s with each evaluation widened: 29
-- | deferred-value cells, then 44 columns of four cells each (the two
-- | `zeta` chunks, then the two `omega*zeta` chunks) in the order
-- | public, witness (15), coefficients (15), `z`, sigma (6), index
-- | (6), then `ftEval1`, the two previous challenge vectors and the
-- | sponge digest.
module Pickles.CircuitDiffs.PureScript.FopStepChunks2
  ( compileFopStepChunks2
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Fin (getFinite)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, domainLog2, srsLengthLog2, stepEndo, unsafeIdx)
import Pickles.Constants (zkRowsForNumChunks)
import Pickles.Field (StepField)
import Pickles.FinalizeOtherProof (DomainMode(..))
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI (PointEval)
import Pickles.Linearization.FFI as LinFFI
import Pickles.Step.FinalizeOtherProof (finalizeOtherProofCircuit)
import Pickles.Step.OtherField as StepOtherField
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (Bool(..), F, FVar, const_)
import Snarky.Circuit.Kimchi (Type1(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

numChunks :: Int
numChunks = 2

compileFopStepChunks2 :: Effect (CompiledCircuit StepField)
compileFopStepChunks2 =
  compile noAdvice (Proxy @(Vector 239 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    \inputs ->
      let
        at = unsafeIdx inputs
        tail = 29 + 88 * numChunks

        column :: Int -> NonEmptyArray (PointEval (FVar StepField))
        column k =
          let
            base = 29 + 2 * numChunks * k
            chunk c = { zeta: at (base + c), omegaTimesZeta: at (base + numChunks + c) }
          in
            NEA.cons' (chunk 0) (map chunk (Array.drop 1 (Array.range 0 (numChunks - 1))))

        columns :: forall n. Reflectable n Int => Int -> Vector n (NonEmptyArray (PointEval (FVar StepField)))
        columns from = Vector.generate \j -> column (from + getFinite j)
      in
        void $ finalizeOtherProofCircuit StepOtherField.fopShiftOps
          { domains:
              { generator: const_ (LinFFI.domainGenerator @StepField domainLog2)
              , log2: domainLog2
              } :< Vector.nil
          , shifts: map const_ (LinFFI.domainShifts @StepField domainLog2)
          , srsLengthLog2
          , zkRows: zkRowsForNumChunks numChunks
          , endo: stepEndo
          , linearizationPoly: Linearization.pallas
          , domainMode: KnownDomainsMode
          }
          { unfinalized:
              { deferredValues:
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
                  , bulletproofChallenges:
                      (Vector.generate (\j -> asSizedF128 (at (10 + getFinite j))) :: Vector 16 _)
                  }
              , shouldFinalize: coerce (const_ one :: FVar StepField)
              , spongeDigestBeforeEvaluations: at (tail + 33)
              }
          , chunkedEvals:
              { ftEval1: at tail
              , publicEvals: column 0
              , witnessEvals: columns 1
              , coeffEvals: columns 16
              , zEvals: column 31
              , sigmaEvals: columns 32
              , indexEvals: columns 38
              }
          , mask: (Vector.generate (\j -> coerce (at (26 + getFinite j))) :: Vector 2 _)
          , prevChallenges:
              ( Vector.generate \j ->
                  Vector.generate \k -> at (tail + 1 + 16 * getFinite j + getFinite k)
              ) :: Vector 2 (Vector 16 _)
          , domainLog2Var: at 28
          }
