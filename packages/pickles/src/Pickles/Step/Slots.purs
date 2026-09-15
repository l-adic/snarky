-- | Heterogeneous per-slot containers for `step_main`.
-- |
-- | A rule's prev list is encoded at the type level as a tuple chain
-- | of `Slot` descriptors (from `Pickles.Slots`) ending in `Unit`:
-- |
-- |   Slot Compiled 1 1 (StatementIO Stmt) /\ Slot SideLoaded 2 1 Stmt' /\ Unit
-- |
-- | Two parallel carriers, both derived from the same spec:
-- |
-- | * `pwCarrier` — `PerProofWitness n nc … /\ rest`, the per-slot
-- |   wrap-proof witnesses (advice).
-- | * `vkCarrier` — `SlotVkSource nc /\ rest`, the per-slot wrap-VK
-- |   sources (compile-time blueprint + side-loaded `exists`).
-- |
-- | Both share the slot's `nc` at every position because they're
-- | parallel pattern matches on the same `Slot k n nc statement`.
-- | `traverseStepSlotsAWithVk` walks both in lockstep and exposes
-- | `pw` and `vkSrc` to the rank-2 callback under one shared `nc`
-- | binder per slot — the type system enforces (per slot) that the
-- | wrap proof's chunks count equals its VK's chunks count, which
-- | is the protocol invariant.
-- |
-- | Reference: OCaml
-- | `per_proof_witness.ml`, `step_main.ml`'s `exists_prevs`,
-- | `wrap_main.ml:80`'s `~num_chunks`.
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
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Field (StepField)
import Pickles.Slots (Slot)
import Pickles.Step.Types (PerProofWitness)
import Pickles.Step.VkSource (SlotVkSource)
import Pickles.Typ (Typ, pairTyp, typOf, unitTyp)
import Pickles.Types (PaddedLength, StepIPARounds, WrapIPARounds)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, BoolVar, F, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Types.Shifted (SplitField, Type2)

-- | `vkCarrier` derivation from `spec` (independent of `f`/`sf`/`b`).
-- | `SlotVkSource nc` doesn't carry the value/var field-element
-- | parameter, so the vk-carrier shape is shared across the
-- | compile-time (`F StepField`/`Boolean`) and in-circuit
-- | (`FVar StepField`/`BoolVar StepField`) instances of
-- | `StepSlotsCarrier`. Splitting it out into its own class with a
-- | tighter fundep prevents PS from inferring two distinct vkCarrier
-- | type variables across the two `StepSlotsCarrier` constraints in
-- | callers that need both.
class SlotVkCarrier :: Type -> Type -> Constraint
class SlotVkCarrier spec vkCarrier | spec -> vkCarrier

instance SlotVkCarrier Unit Unit

instance
  SlotVkCarrier rest restVk =>
  SlotVkCarrier (Slot k n slotVkChunks statement /\ rest) (SlotVkSource slotVkChunks /\ restVk)

-- | Spec → (`len`, `pwCarrier`, `vkCarrier`) mapping plus two
-- | traversals: one over `pwCarrier` alone (legacy), one zipping
-- | `pwCarrier` with `vkCarrier` (each slot's `pw` and `vkSrc`
-- | share the same `nc`).
-- |
-- | Carrier derivation:
-- |
-- | * `Unit` (empty spec) → `Unit` / `Unit`
-- | * `Slot k n nc stmt /\ rest` →
-- |     `PerProofWitness n nc … /\ restPw` and `SlotVkSource nc /\ restVk`
-- |
-- | The kind `k` doesn't affect either carrier — both compiled and
-- | side-loaded slots present the same `PerProofWitness` and
-- | `SlotVkSource` shapes. `vkCarrier` is determined by `spec` alone
-- | (see `SlotVkCarrier` superclass) so it stays consistent across
-- | the value-side and var-side `StepSlotsCarrier` dictionaries.
class StepSlotsCarrier
  :: Type -> Int -> Int -> Type -> Type -> Type -> Int -> Type -> Type -> Constraint
class
  SlotVkCarrier spec vkCarrier <=
  StepSlotsCarrier spec ds dw f sf b len pwCarrier vkCarrier
  | spec ds dw f sf b -> len pwCarrier
  , spec -> vkCarrier
  where
  -- | Walk the per-proof-witness carrier in slot order. Legacy
  -- | traversal that ignores the VK carrier — kept for paths that
  -- | don't need per-slot VK access.
  traverseStepSlotsA
    :: forall m result
     . Applicative m
    => ( forall n slotVkChunks ncPred tCommLen tCommLenPred pad nonSgBases chunkBases wCoeffN indexSigmaN sg1 sg2 sg3 sg4 totalBases totalBasesPred
          . Reflectable n Int
         => Reflectable slotVkChunks Int
         => Reflectable tCommLen Int
         => Reflectable nonSgBases Int
         => Reflectable pad Int
         => Compare 0 slotVkChunks LT
         => Add 1 ncPred slotVkChunks
         => Mul 7 slotVkChunks tCommLen
         => Add 1 tCommLenPred tCommLen
         -- Shared bindings (Mul fundep collapses same-RHS counts).
         => Mul 15 slotVkChunks wCoeffN
         => Mul 6 slotVkChunks indexSigmaN
         => Mul 43 slotVkChunks chunkBases
         => Add 2 chunkBases nonSgBases
         => Add 2 nonSgBases totalBases
         => Add 2 slotVkChunks sg1
         => Add sg1 indexSigmaN sg2
         => Add sg2 wCoeffN sg3
         => Add sg3 wCoeffN sg4
         => Add sg4 indexSigmaN nonSgBases
         => Add 1 totalBasesPred totalBases
         => Add pad n PaddedLength
         => Finite len
         -> PerProofWitness n slotVkChunks ds dw f sf b
         -> m result
       )
    -> pwCarrier
    -> m (Vector len result)

  -- | Walk `pwCarrier` and `vkCarrier` in lockstep. The rank-2
  -- | callback gets `pw :: PerProofWitness n nc …` and
  -- | `vkSrc :: SlotVkSource nc` both at the slot's `nc` (same
  -- | type variable — the parallel Cons instance binds them to the
  -- | shared spec's `nc`). No equality bridge required.
  traverseStepSlotsAWithVk
    :: forall m result
     . Applicative m
    => ( forall n slotVkChunks ncPred tCommLen tCommLenPred pad nonSgBases chunkBases wCoeffN indexSigmaN sg1 sg2 sg3 sg4 totalBases totalBasesPred
          . Reflectable n Int
         => Reflectable slotVkChunks Int
         => Reflectable tCommLen Int
         => Reflectable nonSgBases Int
         => Reflectable pad Int
         => Compare 0 slotVkChunks LT
         => Add 1 ncPred slotVkChunks
         => Mul 7 slotVkChunks tCommLen
         => Add 1 tCommLenPred tCommLen
         -- Shared bindings (Mul fundep collapses same-RHS counts).
         => Mul 15 slotVkChunks wCoeffN
         => Mul 6 slotVkChunks indexSigmaN
         => Mul 43 slotVkChunks chunkBases
         => Add 2 chunkBases nonSgBases
         => Add 2 nonSgBases totalBases
         => Add 2 slotVkChunks sg1
         => Add sg1 indexSigmaN sg2
         => Add sg2 wCoeffN sg3
         => Add sg3 wCoeffN sg4
         => Add sg4 indexSigmaN nonSgBases
         => Add 1 totalBasesPred totalBases
         => Add pad n PaddedLength
         => Finite len
         -> PerProofWitness n slotVkChunks ds dw f sf b
         -> SlotVkSource slotVkChunks
         -> m result
       )
    -> pwCarrier
    -> vkCarrier
    -> m (Vector len result)

  -- | Build a `pwCarrier` from a rank-2 polymorphic dummy slot. Each
  -- | slot auto-specialises the dummy to its own `n_i` and `nc_i`.
  replicateStepSlotsCarrier
    :: ( forall n slotVkChunks ncPred tCommLen tCommLenPred pad nonSgBases chunkBases wCoeffN indexSigmaN sg1 sg2 sg3 sg4 totalBases totalBasesPred
          . Reflectable n Int
         => Reflectable slotVkChunks Int
         => Reflectable tCommLen Int
         => Reflectable nonSgBases Int
         => Reflectable pad Int
         => Compare 0 slotVkChunks LT
         => Add 1 ncPred slotVkChunks
         => Mul 7 slotVkChunks tCommLen
         => Add 1 tCommLenPred tCommLen
         -- Shared bindings (Mul fundep collapses same-RHS counts).
         => Mul 15 slotVkChunks wCoeffN
         => Mul 6 slotVkChunks indexSigmaN
         => Mul 43 slotVkChunks chunkBases
         => Add 2 chunkBases nonSgBases
         => Add 2 nonSgBases totalBases
         => Add 2 slotVkChunks sg1
         => Add sg1 indexSigmaN sg2
         => Add sg2 wCoeffN sg3
         => Add sg3 wCoeffN sg4
         => Add sg4 indexSigmaN nonSgBases
         => Add 1 totalBasesPred totalBases
         => Add pad n PaddedLength
         => PerProofWitness n slotVkChunks ds dw f sf b
       )
    -> pwCarrier

instance StepSlotsCarrier Unit ds dw f sf b 0 Unit Unit where
  traverseStepSlotsA _ _ = pure Vector.nil
  traverseStepSlotsAWithVk _ _ _ = pure Vector.nil
  replicateStepSlotsCarrier _ = unit

instance
  ( StepSlotsCarrier rest ds dw f sf b restLen restPw restVk
  , Add restLen 1 len
  , Reflectable n Int
  , Reflectable slotVkChunks Int
  , Reflectable tCommLen Int
  , Reflectable nonSgBases Int
  , Compare 0 slotVkChunks LT
  , Add 1 ncPred slotVkChunks
  , Mul 7 slotVkChunks tCommLen
  , Add 1 tCommLenPred tCommLen
  , Mul 15 slotVkChunks wCoeffN
  , Mul 6 slotVkChunks indexSigmaN
  , Mul 43 slotVkChunks chunkBases
  , Add 2 chunkBases nonSgBases
  , Add 2 nonSgBases totalBases
  , Add 2 slotVkChunks sg1
  , Add sg1 indexSigmaN sg2
  , Add sg2 wCoeffN sg3
  , Add sg3 wCoeffN sg4
  , Add sg4 indexSigmaN nonSgBases
  , Add 1 totalBasesPred totalBases
  , Add pad n PaddedLength
  , Reflectable pad Int
  ) =>
  StepSlotsCarrier
    (Slot k n slotVkChunks statement /\ rest)
    ds
    dw
    f
    sf
    b
    len
    (PerProofWitness n slotVkChunks ds dw f sf b /\ restPw)
    (SlotVkSource slotVkChunks /\ restVk)
  where
  traverseStepSlotsA f (here /\ rest) =
    Vector.cons
      <$> f (finZero :: Finite len) here
      <*> traverseStepSlotsA @rest (\i' pw -> f (shiftSucc i') pw) rest

  traverseStepSlotsAWithVk f (pwHere /\ pwRest) (vkHere /\ vkRest) =
    Vector.cons
      <$> f (finZero :: Finite len) pwHere vkHere
      <*> traverseStepSlotsAWithVk @rest
        (\i' pw vk -> f (shiftSucc i') pw vk)
        pwRest
        vkRest

  replicateStepSlotsCarrier dummyPPW =
    dummyPPW /\ replicateStepSlotsCarrier @rest dummyPPW

-- | A slot's per-proof witness, at the one pair of instantiations every
-- | caller of `StepSlotsCarrier` uses: values over `F StepField`,
-- | variables over `FVar StepField`.
type SlotWitnessVal n slotVkChunks =
  PerProofWitness n slotVkChunks StepIPARounds WrapIPARounds
    (F StepField)
    (Type2 (SplitField (F StepField) Boolean))
    Boolean

type SlotWitnessVar n slotVkChunks =
  PerProofWitness n slotVkChunks StepIPARounds WrapIPARounds
    (FVar StepField)
    (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
    (BoolVar StepField)

-- | The per-proof carrier's layout, as a value.
-- |
-- | `StepSlotsCarrier` is indexed by one field-element type at a time,
-- | so it names the value carrier and the variable carrier through two
-- | separate dictionaries. A `Typ` relates the two, so it needs both at
-- | once; hence a second class over the same spec, pinned to the pair
-- | of instantiations every caller actually uses.
-- |
-- | Each slot's witness still comes from the class via `typOf`. What is
-- | reified here is only the chain that joins the slots, and `pairTyp`
-- | reproduces the layout the tuple instance gives it. Nothing moves to
-- | runtime yet.
class StepSlotsTyp :: Type -> Type -> Type -> Constraint
class StepSlotsTyp spec valCarrier varCarrier | spec -> valCarrier varCarrier where
  stepSlotsTyp :: Typ StepField (KimchiConstraint StepField) valCarrier varCarrier

instance StepSlotsTyp Unit Unit Unit where
  stepSlotsTyp = unitTyp

instance
  ( StepSlotsTyp rest restVal restVar
  , CircuitType StepField (SlotWitnessVal n slotVkChunks) (SlotWitnessVar n slotVkChunks)
  , CheckedType StepField (KimchiConstraint StepField) (SlotWitnessVar n slotVkChunks)
  ) =>
  StepSlotsTyp
    (Slot k n slotVkChunks statement /\ rest)
    (SlotWitnessVal n slotVkChunks /\ restVal)
    (SlotWitnessVar n slotVkChunks /\ restVar)
  where
  stepSlotsTyp = pairTyp typOf (stepSlotsTyp @rest)

-- | Type-level mapping `spec → valCarrier` for the heterogeneous
-- | per-slot statements carrier (one slot per prev, holding that
-- | prev's `statement` type). Funcdep `spec -> valCarrier`.
class SlotStatementsCarrier :: Type -> Type -> Constraint
class SlotStatementsCarrier spec valCarrier | spec -> valCarrier

instance SlotStatementsCarrier Unit Unit

instance
  SlotStatementsCarrier rest restValCarrier =>
  SlotStatementsCarrier
    (Slot k n slotVkChunks statement /\ rest)
    (statement /\ restValCarrier)
