-- | Per-slot containers for `stepMain`, one entry per previous proof a
-- | rule declares.
-- |
-- | A rule's prevs are a type-level chain of `Pickles.Slots.Slot`
-- | descriptors ending in `Unit`, and the slots need not agree on a
-- | statement type:
-- |
-- |   Slot 1 (StatementIO Stmt Unit) /\ Slot 2 Stmt' /\ Unit
-- |
-- | Two carriers come from that one spec: `pwCarrier`, the per-slot
-- | `PerProofWitness` values, and `vkCarrier`, the per-slot wrap-VK
-- | sources. `traverseStepSlotsAWithVk` walks them in lockstep under
-- | one shared chunk count per slot.
module Pickles.Step.Slots
  ( class StepSlotsCarrier
  , class SlotStatementsCarrier
  , class SlotVkCarrier
  , class StepSlotsTyp
  , SlotWitnessVal
  , SlotWitnessVar
  , stepSlotsTyp
  , traverseStepSlotsA
  , traverseStepSlotsAWithVk
  , replicateStepSlotsCarrier
  ) where

import Prelude

import Data.Fin (Finite, finZero, shiftSucc)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Field (StepField)
import Pickles.Slots (Slot)
import Pickles.Step.Types (PerProofWitness, WrapProof, perProofWitnessTyp)
import Pickles.Step.VkSource (SlotVkSource)
import Pickles.Typ (Typ, pairTyp, unitTyp)
import Pickles.Types (PaddedLength, StepIPARounds, WrapIPARounds, WrapVkChunks)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, BoolVar, F, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)
import Snarky.Types.Shifted (SplitField, Type2)
import Type.Proxy (Proxy(..))

-- | `spec` → `vkCarrier`, split out of `StepSlotsCarrier` so the two
-- | `StepSlotsCarrier` constraints a caller needs — one at value
-- | elements, one at variables — agree on the carrier. `SlotVkSource`
-- | carries no field-element parameter, so the shape is the same for
-- | both; without the tighter fundep PS infers two distinct carrier
-- | variables.
class SlotVkCarrier :: Type -> Type -> Constraint
class SlotVkCarrier spec vkCarrier | spec -> vkCarrier

instance SlotVkCarrier Unit Unit

instance
  SlotVkCarrier rest restVk =>
  SlotVkCarrier (Slot n statement /\ rest) (SlotVkSource WrapVkChunks /\ restVk)

-- | `spec` → (`len`, `pwCarrier`, `vkCarrier`), with two traversals:
-- | one over `pwCarrier` alone, one zipping it with `vkCarrier`.
-- | Compiled and side-loaded slots present the same carrier shapes, so
-- | the spec does not distinguish them.
-- |
-- | `nc`, the wrap-VK chunk count, is a class parameter rather than a
-- | per-slot rank-2 binder: that is what lets the callback body use the
-- | caller's own layout constraints at `nc`, so `verifyOne` can be
-- | called directly, with no restated constraints and no `unsafeCoerce`.
-- | Being a wrap-side count, it is `Pickles.Types.WrapVkChunks` for
-- | every slot of every compile.
class StepSlotsCarrier
  :: Type -> Int -> Int -> Int -> Type -> Type -> Type -> Int -> Type -> Type -> Constraint
class
  SlotVkCarrier spec vkCarrier <=
  StepSlotsCarrier spec nc ds dw f sf b len pwCarrier vkCarrier
  | spec ds dw f sf b -> len pwCarrier
  , spec -> vkCarrier
  where
  -- | Walk `pwCarrier` in slot order, ignoring the VK carrier.
  traverseStepSlotsA
    :: forall m result
     . Applicative m
    => ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => Proxy n
         -> Finite len
         -> PerProofWitness nc ds dw f sf b
         -> m result
       )
    -> pwCarrier
    -> m (Vector len result)

  -- | Walk `pwCarrier` and `vkCarrier` in lockstep. The callback gets a
  -- | slot's `PerProofWitness` and its `SlotVkSource` at the same `nc`,
  -- | so no equality bridge is needed.
  traverseStepSlotsAWithVk
    :: forall m result
     . Applicative m
    => ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => Proxy n
         -> Finite len
         -> PerProofWitness nc ds dw f sf b
         -> SlotVkSource nc
         -> m result
       )
    -> pwCarrier
    -> vkCarrier
    -> m (Vector len result)

  -- | Build a `pwCarrier` by specializing one rank-2 dummy slot at each
  -- | slot's own `n`.
  replicateStepSlotsCarrier
    :: ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => Proxy n
         -> PerProofWitness nc ds dw f sf b
       )
    -> pwCarrier

instance StepSlotsCarrier Unit nc ds dw f sf b 0 Unit Unit where
  traverseStepSlotsA _ _ = pure Vector.nil
  traverseStepSlotsAWithVk _ _ _ = pure Vector.nil
  replicateStepSlotsCarrier _ = unit

instance
  ( StepSlotsCarrier rest WrapVkChunks ds dw f sf b restLen restPw restVk
  , Add restLen 1 len
  , Reflectable n Int
  , Add pad n PaddedLength
  , Reflectable pad Int
  ) =>
  StepSlotsCarrier
    (Slot n statement /\ rest)
    WrapVkChunks
    ds
    dw
    f
    sf
    b
    len
    (PerProofWitness WrapVkChunks ds dw f sf b /\ restPw)
    (SlotVkSource WrapVkChunks /\ restVk)
  where
  traverseStepSlotsA f (here /\ rest) =
    Vector.cons
      <$> f (Proxy :: Proxy n) (finZero :: Finite len) here
      <*> traverseStepSlotsA @rest (\pn i' pw -> f pn (shiftSucc i') pw) rest

  traverseStepSlotsAWithVk f (pwHere /\ pwRest) (vkHere /\ vkRest) =
    Vector.cons
      <$> f (Proxy :: Proxy n) (finZero :: Finite len) pwHere vkHere
      <*> traverseStepSlotsAWithVk @rest
        (\pn i' pw vk -> f pn (shiftSucc i') pw vk)
        pwRest
        vkRest

  replicateStepSlotsCarrier dummyPPW =
    dummyPPW (Proxy :: Proxy n) /\ replicateStepSlotsCarrier @rest dummyPPW

-- | A slot's per-proof witness at the one pair of instantiations every
-- | caller of `StepSlotsCarrier` uses: values over `F StepField`,
-- | variables over `FVar StepField`.
type SlotWitnessVal slotVkChunks =
  PerProofWitness slotVkChunks StepIPARounds WrapIPARounds
    (F StepField)
    (Type2 (SplitField (F StepField) Boolean))
    Boolean

type SlotWitnessVar slotVkChunks =
  PerProofWitness slotVkChunks StepIPARounds WrapIPARounds
    (FVar StepField)
    (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
    (BoolVar StepField)

-- | The per-proof carrier's layout, as a `Typ`.
-- |
-- | `StepSlotsCarrier` is indexed by one field-element type at a time,
-- | so it names the value carrier and the variable carrier through two
-- | separate dictionaries. A `Typ` relates the two and needs both at
-- | once — hence a second class over the same spec, pinned to the pair
-- | of instantiations every caller uses.
-- |
-- | It is also where the slot width crosses from the type level to the
-- | value level: the spec declares it, and it is reflected here and
-- | handed to `perProofWitnessTyp` as an ordinary integer.
class StepSlotsTyp :: Type -> Type -> Type -> Constraint
class StepSlotsTyp spec valCarrier varCarrier | spec -> valCarrier varCarrier where
  stepSlotsTyp :: Typ StepField (KimchiConstraint StepField) valCarrier varCarrier

instance StepSlotsTyp Unit Unit Unit where
  stepSlotsTyp = unitTyp

instance
  ( StepSlotsTyp rest restVal restVar
  , Reflectable n Int
  , CircuitType StepField
      (WrapProof WrapIPARounds WrapVkChunks (WeierstrassAffinePoint PallasG (F StepField)) (Type2 (SplitField (F StepField) Boolean)))
      (WrapProof WrapIPARounds WrapVkChunks (WeierstrassAffinePoint PallasG (FVar StepField)) (Type2 (SplitField (FVar StepField) (BoolVar StepField))))
  , CheckedType StepField (KimchiConstraint StepField)
      (WrapProof WrapIPARounds WrapVkChunks (WeierstrassAffinePoint PallasG (FVar StepField)) (Type2 (SplitField (FVar StepField) (BoolVar StepField))))
  ) =>
  StepSlotsTyp
    (Slot n statement /\ rest)
    (SlotWitnessVal WrapVkChunks /\ restVal)
    (SlotWitnessVar WrapVkChunks /\ restVar)
  where
  stepSlotsTyp =
    pairTyp (perProofWitnessTyp (reflectType (Proxy :: Proxy n))) (stepSlotsTyp @rest)

-- | `spec` → the per-slot statements carrier: one entry per prev,
-- | holding that prev's own `statement` type.
class SlotStatementsCarrier :: Type -> Type -> Constraint
class SlotStatementsCarrier spec valCarrier | spec -> valCarrier

instance SlotStatementsCarrier Unit Unit

instance
  SlotStatementsCarrier rest restValCarrier =>
  SlotStatementsCarrier
    (Slot n statement /\ rest)
    (statement /\ restValCarrier)
