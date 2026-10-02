-- | `wrapFinalizePrevProofs`, the wrap circuit's finalize block, at two
-- | branches and two slots, matching `wrap_finalize_n2_circuit`. Branch
-- | 0's slots are pinned to wrap domains `[N1, N1]`, branch 1's to
-- | `[N0, N2]`.
module Pickles.CircuitDiffs.PureScript.WrapFinalize
  ( compileWrapFinalizeN2
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (Tuple2, Tuple3, tuple2, tuple3, uncurry2, uncurry3)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.CircuitDiffs.PureScript.FopWrap (FopWrapInput(..))
import Pickles.Field (WrapField)
import Pickles.ProofsVerified (ProofsVerified(..))
import Pickles.Pseudo as Pseudo
import Pickles.Types (AllocEvals(..), WrapIPARounds)
import Pickles.Wrap.Main (wrapFinalizePrevProofs)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F, FVar, Snarky, UnChecked(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | One slot of `wrap_finalize_n2_circuit`'s input (OCaml `dump_circuit_impl.ml`):
-- | `finalize_other_proof_wrap_circuit`'s input at the wrap circuit's 15 rounds, then
-- | `shouldFinalize` and the slot's wrap domain index.
newtype WrapFinalizeSlot f b = WrapFinalizeSlot
  { fop :: FopWrapInput WrapIPARounds f (Type2 f)
  , shouldFinalize :: b
  , domainIndex :: f
  }

-- | The wire order.
type WrapFinalizeSlotTuple f b = Tuple3 (FopWrapInput WrapIPARounds f (Type2 f)) b f

slotToTuple :: forall f b. WrapFinalizeSlot f b -> WrapFinalizeSlotTuple f b
slotToTuple (WrapFinalizeSlot s) = tuple3 s.fop s.shouldFinalize s.domainIndex

slotFromTuple :: forall f b. WrapFinalizeSlotTuple f b -> WrapFinalizeSlot f b
slotFromTuple = uncurry3 \fop shouldFinalize domainIndex ->
  WrapFinalizeSlot { fop, shouldFinalize, domainIndex }

instance
  ( CircuitType f fa fv
  , CircuitType f ba bv
  , CircuitType f (FopWrapInput WrapIPARounds fa (Type2 fa)) (FopWrapInput WrapIPARounds fv (Type2 fv))
  ) =>
  CircuitType f (WrapFinalizeSlot fa ba) (WrapFinalizeSlot fv bv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(WrapFinalizeSlotTuple fa ba))
  valueToFields = genericValueToFields <<< slotToTuple
  fieldsToValue = slotFromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(WrapFinalizeSlotTuple fa ba) <<< slotToTuple
  fieldsToVar = slotFromTuple <<< genericFieldsToVar @(WrapFinalizeSlotTuple fa ba)

-- | `wrap_finalize_n2_circuit`'s input: the branch index, then the two slots.
newtype WrapFinalizeInput f b = WrapFinalizeInput
  { branchIndex :: f
  , slots :: Vector 2 (WrapFinalizeSlot f b)
  }

-- | The wire order.
type WrapFinalizeTuple f b = Tuple2 f (Vector 2 (WrapFinalizeSlot f b))

toTuple :: forall f b. WrapFinalizeInput f b -> WrapFinalizeTuple f b
toTuple (WrapFinalizeInput i) = tuple2 i.branchIndex i.slots

fromTuple :: forall f b. WrapFinalizeTuple f b -> WrapFinalizeInput f b
fromTuple = uncurry2 \branchIndex slots -> WrapFinalizeInput { branchIndex, slots }

instance
  ( CircuitType f fa fv
  , CircuitType f (WrapFinalizeSlot fa ba) (WrapFinalizeSlot fv bv)
  ) =>
  CircuitType f (WrapFinalizeInput fa ba) (WrapFinalizeInput fv bv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(WrapFinalizeTuple fa ba))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(WrapFinalizeTuple fa ba) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(WrapFinalizeTuple fa ba)

wrapFinalizeN2Circuit
  :: forall r
   . UnChecked (WrapFinalizeInput (FVar WrapField) (BoolVar WrapField))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
wrapFinalizeN2Circuit (UnChecked (WrapFinalizeInput input)) = do
  let
    slot (WrapFinalizeSlot s) =
      let
        FopWrapInput fop = s.fop
        AllocEvals evals = fop.evals
      in
        { unfinalized:
            { deferredValues: fop.deferredValues
            , shouldFinalize: s.shouldFinalize
            , spongeDigestBeforeEvaluations: fop.spongeDigest
            }
        , evals
        , prevChallenges: fop.prevChallenges
        , domainIndex: s.domainIndex
        }
    slots = map slot input.slots
    pins =
      (Just N1 :< Just N1 :< Vector.nil)
        :< (Just N0 :< Just N2 :< Vector.nil)
        :< Vector.nil
  whichBranch <- Pseudo.oneHotVector @2 input.branchIndex
  _ <- wrapFinalizePrevProofs whichBranch pins
    (map _.domainIndex slots)
    (map _.unfinalized slots)
    (map _.evals slots)
    (map _.prevChallenges slots)
  pure unit

compileWrapFinalizeN2 :: Effect (CompiledCircuit WrapField)
compileWrapFinalizeN2 =
  compile noAdvice (Proxy @(UnChecked (WrapFinalizeInput (F WrapField) Boolean))) (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    wrapFinalizeN2Circuit
