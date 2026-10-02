-- | The step finalize over a two-chunk step proof, as a comparison
-- | target: `finalizeOtherProofCircuit` with every evaluation carried
-- | at two chunks, so the circuit absorbs every chunk and recombines
-- | them in circuit. Every other parameter is `FopStep`'s, except
-- | `zkRows`, which follows the chunk count.
module Pickles.CircuitDiffs.PureScript.FopStepChunks2
  ( compileFopStepChunks2
  ) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple2, Tuple7, tuple2, tuple7, uncurry2, uncurry7)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, domainLog2, srsLengthLog2, stepEndo)
import Pickles.CircuitDiffs.PureScript.FopStep (FopStepInput(..))
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
import Snarky.Circuit.DSL (class CircuitType, Bool(..), BoolVar, F, FVar, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | The evaluations at `nc` chunks, as the dump lays them out: each column its `zeta` chunks
-- | then its `omega*zeta` chunks, in the order public, witness (15), coefficients (15), `z`,
-- | sigma (6), index (6), then `ftEval1`.
newtype ChunkedAllocEvals nc f = ChunkedAllocEvals
  { publicEvals :: PointEval (Vector nc f)
  , witnessEvals :: Vector 15 (PointEval (Vector nc f))
  , coeffEvals :: Vector 15 (PointEval (Vector nc f))
  , zEvals :: PointEval (Vector nc f)
  , sigmaEvals :: Vector 6 (PointEval (Vector nc f))
  , indexEvals :: Vector 6 (PointEval (Vector nc f))
  , ftEval1 :: f
  }

-- | One column as its `(zeta, zetaw)` chunk pair.
type Column nc f = Tuple2 (Vector nc f) (Vector nc f)

-- | The wire order.
type ChunkedEvalsTuple nc f =
  Tuple7 (Column nc f) (Vector 15 (Column nc f)) (Vector 15 (Column nc f)) (Column nc f)
    (Vector 6 (Column nc f))
    (Vector 6 (Column nc f))
    f

toTuple :: forall nc f. ChunkedAllocEvals nc f -> ChunkedEvalsTuple nc f
toTuple (ChunkedAllocEvals e) =
  tuple7 (col e.publicEvals) (map col e.witnessEvals) (map col e.coeffEvals) (col e.zEvals)
    (map col e.sigmaEvals)
    (map col e.indexEvals)
    e.ftEval1
  where
  col p = tuple2 p.zeta p.omegaTimesZeta

fromTuple :: forall nc f. ChunkedEvalsTuple nc f -> ChunkedAllocEvals nc f
fromTuple = uncurry7 \publicEvals witnessEvals coeffEvals zEvals sigmaEvals indexEvals ftEval1 ->
  ChunkedAllocEvals
    { publicEvals: point publicEvals
    , witnessEvals: map point witnessEvals
    , coeffEvals: map point coeffEvals
    , zEvals: point zEvals
    , sigmaEvals: map point sigmaEvals
    , indexEvals: map point indexEvals
    , ftEval1
    }
  where
  point = uncurry2 \zeta omegaTimesZeta -> { zeta, omegaTimesZeta }

instance (Reflectable nc Int, CircuitType f fa fv) => CircuitType f (ChunkedAllocEvals nc fa) (ChunkedAllocEvals nc fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(ChunkedEvalsTuple nc fa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(ChunkedEvalsTuple nc fa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(ChunkedEvalsTuple nc fa)

-- | A column's evaluations, chunk by chunk.
chunks :: forall f. PointEval (Vector 2 f) -> NonEmptyArray (PointEval f)
chunks p = Vector.toUnfoldable1 (Vector.zipWith (\zeta omegaTimesZeta -> { zeta, omegaTimesZeta }) p.zeta p.omegaTimesZeta)

fopStepChunks2Circuit
  :: forall r
   . UnChecked (FopStepInput (ChunkedAllocEvals 2 (FVar StepField)) (FVar StepField) (BoolVar StepField))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
fopStepChunks2Circuit (UnChecked (FopStepInput i)) =
  let
    dv = i.deferredValues
    ChunkedAllocEvals e = i.evals
  in
    void $ finalizeOtherProofCircuit StepOtherField.fopShiftOps
      { domains:
          NEA.singleton
            { generator: const_ (LinFFI.domainGenerator @StepField domainLog2)
            , log2: domainLog2
            }
      , shifts: map const_ (LinFFI.domainShifts @StepField domainLog2)
      , srsLengthLog2
      , zkRows: zkRowsForNumChunks 2
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      , domainMode: KnownDomainsMode
      }
      { unfinalized:
          { deferredValues:
              { plonk: dv.plonk
              , combinedInnerProduct: dv.combinedInnerProduct
              , b: dv.b
              , xi: dv.xi
              , bulletproofChallenges: dv.bulletproofChallenges
              }
          , shouldFinalize: coerce (const_ one :: FVar StepField)
          , spongeDigestBeforeEvaluations: i.spongeDigest
          }
      , chunkedEvals:
          { ftEval1: e.ftEval1
          , publicEvals: chunks e.publicEvals
          , witnessEvals: map chunks e.witnessEvals
          , coeffEvals: map chunks e.coeffEvals
          , zEvals: chunks e.zEvals
          , sigmaEvals: map chunks e.sigmaEvals
          , indexEvals: map chunks e.indexEvals
          }
      , mask: dv.branchData.proofsVerifiedMask
      , prevChallenges: i.prevChallenges
      , domainLog2Var: dv.branchData.domainLog2
      }

compileFopStepChunks2 :: Effect (CompiledCircuit StepField)
compileFopStepChunks2 =
  compile noAdvice
    (Proxy @(UnChecked (FopStepInput (ChunkedAllocEvals 2 (F StepField)) (F StepField) Boolean)))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    fopStepChunks2Circuit
