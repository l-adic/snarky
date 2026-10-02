module Pickles.CircuitDiffs.PureScript.FopStep
  ( FopStepInput(..)
  , compileFopStep
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Tuple.Nested (Tuple4, tuple4, uncurry4)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, domainLog2, srsLengthLog2, stepEndo)
import Pickles.CircuitDiffs.PureScript.PerProofWitness (WrapDeferredHlist, wrapDeferredFromHlist, wrapDeferredToHlist)
import Pickles.Constants (zkRowsByDefault)
import Pickles.DeferredValues (WrapDeferredValues)
import Pickles.Field (StepField)
import Pickles.FinalizeOtherProof (DomainMode(..))
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PlonkChecks (singleChunkEvals)
import Pickles.Step.FinalizeOtherProof (finalizeOtherProofCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (AllocEvals(..))
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, Bool(..), BoolVar, F, FVar, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | `finalize_other_proof{,_chunks2}_step_circuit`'s input (OCaml `dump_circuit_impl.ml`): the
-- | wrap statement's deferred values in OCaml's hlist order, the evaluations `ev`, the two
-- | previous challenge vectors and the sponge digest.
newtype FopStepInput ev f b = FopStepInput
  { deferredValues :: WrapDeferredValues 16 f (Type1 f) b
  , evals :: ev
  , prevChallenges :: Vector 2 (Vector 16 f)
  , spongeDigest :: f
  }

-- | The wire order.
type FopStepTuple ev f b = Tuple4 (WrapDeferredHlist f b) ev (Vector 2 (Vector 16 f)) f

toTuple :: forall ev f b. FopStepInput ev f b -> FopStepTuple ev f b
toTuple (FopStepInput i) =
  tuple4 (wrapDeferredToHlist i.deferredValues) i.evals i.prevChallenges i.spongeDigest

fromTuple :: forall ev f b. FopStepTuple ev f b -> FopStepInput ev f b
fromTuple = uncurry4 \dv evals prevChallenges spongeDigest ->
  FopStepInput { deferredValues: wrapDeferredFromHlist dv, evals, prevChallenges, spongeDigest }

instance
  ( CircuitType f ea ev
  , CircuitType f fa fv
  , CircuitType f ba bv
  , CircuitType f (Type1 fa) (Type1 fv)
  ) =>
  CircuitType f (FopStepInput ea fa ba) (FopStepInput ev fv bv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(FopStepTuple ea fa ba))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(FopStepTuple ea fa ba) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(FopStepTuple ea fa ba)

fopStepCircuit
  :: forall r
   . UnChecked (FopStepInput (AllocEvals (FVar StepField)) (FVar StepField) (BoolVar StepField))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
fopStepCircuit (UnChecked (FopStepInput i)) =
  let
    dv = i.deferredValues
    AllocEvals evals = i.evals
    unfinalized =
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
    params =
      { domains:
          NEA.singleton
            { generator: const_ (LinFFI.domainGenerator @StepField domainLog2)
            , log2: domainLog2
            }
      , shifts: map const_ (LinFFI.domainShifts @StepField domainLog2)
      , srsLengthLog2
      , zkRows: zkRowsByDefault
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      , domainMode: KnownDomainsMode
      }
  in
    void $ finalizeOtherProofCircuit StepOtherField.fopShiftOps params
      { unfinalized
      , chunkedEvals: singleChunkEvals evals
      , mask: dv.branchData.proofsVerifiedMask
      , prevChallenges: i.prevChallenges
      , domainLog2Var: dv.branchData.domainLog2
      }

compileFopStep :: Effect (CompiledCircuit StepField)
compileFopStep =
  compile noAdvice
    (Proxy @(UnChecked (FopStepInput (AllocEvals (F StepField)) (F StepField) Boolean)))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    fopStepCircuit
