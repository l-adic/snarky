module Pickles.CircuitDiffs.PureScript.FopWrap
  ( FopWrapInput(..)
  , compileFopWrap
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple4, tuple4, uncurry4)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, wrapDomainLog2, wrapEndo, wrapSrsLengthLog2)
import Pickles.CircuitDiffs.PureScript.PerProofWitness (DeferredHlist, deferredFromHlist, deferredToHlist)
import Pickles.Constants (zkRowsByDefault)
import Pickles.DeferredValues (DeferredValues)
import Pickles.Field (WrapField)
import Pickles.FinalizeOtherProof (DomainMode(..))
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.Types (AllocEvals(..))
import Pickles.Wrap.FinalizeOtherProof (pow2PowMul, wrapFinalizeOtherProofCircuit)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, Bool(..), F, FVar, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, sub_)
import Snarky.Circuit.Kimchi (Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | A wrap-side finalize input at `d` rounds (OCaml `dump_circuit_impl.ml`): the step proof's
-- | deferred values in OCaml's hlist order, shifted values `s`, the evaluations, the two
-- | previous challenge vectors and the sponge digest.
newtype FopWrapInput d f s = FopWrapInput
  { deferredValues :: DeferredValues d f s
  , evals :: AllocEvals f
  , prevChallenges :: Vector 2 (Vector d f)
  , spongeDigest :: f
  }

-- | The wire order.
type FopWrapTuple d f s = Tuple4 (DeferredHlist d f s) (AllocEvals f) (Vector 2 (Vector d f)) f

toTuple :: forall d f s. FopWrapInput d f s -> FopWrapTuple d f s
toTuple (FopWrapInput i) =
  tuple4 (deferredToHlist i.deferredValues) i.evals i.prevChallenges i.spongeDigest

fromTuple :: forall d f s. FopWrapTuple d f s -> FopWrapInput d f s
fromTuple = uncurry4 \dv evals prevChallenges spongeDigest ->
  FopWrapInput { deferredValues: deferredFromHlist dv, evals, prevChallenges, spongeDigest }

instance
  ( Reflectable d Int
  , CircuitType f fa fv
  , CircuitType f sa sv
  ) =>
  CircuitType f (FopWrapInput d fa sa) (FopWrapInput d fv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(FopWrapTuple d fa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(FopWrapTuple d fa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(FopWrapTuple d fa sa)

-- | `finalize_other_proof_wrap_circuit`: the wrap-side finalize at 16 rounds, Type2-shifted.
fopWrapCircuit
  :: forall r
   . UnChecked (FopWrapInput 16 (FVar WrapField) (Type2 (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
fopWrapCircuit (UnChecked (FopWrapInput i)) =
  let
    AllocEvals allEvals = i.evals
    unfinalized =
      { deferredValues: i.deferredValues
      , shouldFinalize: coerce (const_ one :: FVar WrapField)
      , spongeDigestBeforeEvaluations: i.spongeDigest
      }
    params =
      { domains:
          NEA.singleton
            { generator: const_ (LinFFI.domainGenerator @WrapField wrapDomainLog2)
            , log2: wrapDomainLog2
            }
      , shifts: map const_ (LinFFI.domainShifts @WrapField wrapDomainLog2)
      , srsLengthLog2: wrapSrsLengthLog2
      , zkRows: zkRowsByDefault
      , endo: wrapEndo
      , linearizationPoly: Linearization.vesta
      , domainMode: KnownDomainsMode
      }
    vanishingPoly z = do
      zetaToN <- pow2PowMul z wrapDomainLog2
      pure (zetaToN `sub_` const_ one)
  in
    void $ wrapFinalizeOtherProofCircuit params vanishingPoly
      { unfinalized
      , allEvals
      , prevChallenges: i.prevChallenges
      }

compileFopWrap :: Effect (CompiledCircuit WrapField)
compileFopWrap =
  compile noAdvice
    (Proxy @(UnChecked (FopWrapInput 16 (F WrapField) (Type2 (F WrapField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    fopWrapCircuit
