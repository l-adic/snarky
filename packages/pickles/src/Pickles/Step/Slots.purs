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
-- | Step-side analog of `Pickles.Wrap.Slots`. Reference: OCaml
-- | `per_proof_witness.ml`, `step_main.ml`'s `exists_prevs`,
-- | `wrap_main.ml:80`'s `~num_chunks`.
module Pickles.Step.Slots
  ( class StepSlotsCarrier
  , class SlotStatementsCarrier
  , class SlotVkCarrier
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
import Pickles.Slots (Slot)
import Pickles.Step.Types (PerProofWitness)
import Pickles.Step.VkSource (SlotVkSource)
import Pickles.Types (PaddedLength)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)

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
  SlotVkCarrier (Slot k n nc statement /\ rest) (SlotVkSource nc /\ restVk)

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
    => ( forall n nc ncPred tCommLen tCommLenPred pad nonSgBases chunkBases wCoeffN indexSigmaN sg1 sg2 sg3 sg4 totalBases totalBasesPred
          . Reflectable n Int
         => Reflectable nc Int
         => Reflectable tCommLen Int
         => Reflectable nonSgBases Int
         => Reflectable pad Int
         => Compare 0 nc LT
         => Add 1 ncPred nc
         => Mul 7 nc tCommLen
         => Add 1 tCommLenPred tCommLen
         -- Shared bindings (Mul fundep collapses same-RHS counts).
         => Mul 15 nc wCoeffN
         => Mul 6 nc indexSigmaN
         => Mul 43 nc chunkBases
         => Add 2 chunkBases nonSgBases
         => Add 2 nonSgBases totalBases
         => Add 2 nc sg1
         => Add sg1 indexSigmaN sg2
         => Add sg2 wCoeffN sg3
         => Add sg3 wCoeffN sg4
         => Add sg4 indexSigmaN nonSgBases
         => Add 1 totalBasesPred totalBases
         => Add pad n PaddedLength
         => Finite len
         -> PerProofWitness n nc ds dw f sf b
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
    => ( forall n nc ncPred tCommLen tCommLenPred pad nonSgBases chunkBases wCoeffN indexSigmaN sg1 sg2 sg3 sg4 totalBases totalBasesPred
          . Reflectable n Int
         => Reflectable nc Int
         => Reflectable tCommLen Int
         => Reflectable nonSgBases Int
         => Reflectable pad Int
         => Compare 0 nc LT
         => Add 1 ncPred nc
         => Mul 7 nc tCommLen
         => Add 1 tCommLenPred tCommLen
         -- Shared bindings (Mul fundep collapses same-RHS counts).
         => Mul 15 nc wCoeffN
         => Mul 6 nc indexSigmaN
         => Mul 43 nc chunkBases
         => Add 2 chunkBases nonSgBases
         => Add 2 nonSgBases totalBases
         => Add 2 nc sg1
         => Add sg1 indexSigmaN sg2
         => Add sg2 wCoeffN sg3
         => Add sg3 wCoeffN sg4
         => Add sg4 indexSigmaN nonSgBases
         => Add 1 totalBasesPred totalBases
         => Add pad n PaddedLength
         => Finite len
         -> PerProofWitness n nc ds dw f sf b
         -> SlotVkSource nc
         -> m result
       )
    -> pwCarrier
    -> vkCarrier
    -> m (Vector len result)

  -- | Build a `pwCarrier` from a rank-2 polymorphic dummy slot. Each
  -- | slot auto-specialises the dummy to its own `n_i` and `nc_i`.
  replicateStepSlotsCarrier
    :: ( forall n nc ncPred tCommLen tCommLenPred pad nonSgBases chunkBases wCoeffN indexSigmaN sg1 sg2 sg3 sg4 totalBases totalBasesPred
          . Reflectable n Int
         => Reflectable nc Int
         => Reflectable tCommLen Int
         => Reflectable nonSgBases Int
         => Reflectable pad Int
         => Compare 0 nc LT
         => Add 1 ncPred nc
         => Mul 7 nc tCommLen
         => Add 1 tCommLenPred tCommLen
         -- Shared bindings (Mul fundep collapses same-RHS counts).
         => Mul 15 nc wCoeffN
         => Mul 6 nc indexSigmaN
         => Mul 43 nc chunkBases
         => Add 2 chunkBases nonSgBases
         => Add 2 nonSgBases totalBases
         => Add 2 nc sg1
         => Add sg1 indexSigmaN sg2
         => Add sg2 wCoeffN sg3
         => Add sg3 wCoeffN sg4
         => Add sg4 indexSigmaN nonSgBases
         => Add 1 totalBasesPred totalBases
         => Add pad n PaddedLength
         => PerProofWitness n nc ds dw f sf b
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
  , Reflectable nc Int
  , Reflectable tCommLen Int
  , Reflectable nonSgBases Int
  , Compare 0 nc LT
  , Add 1 ncPred nc
  , Mul 7 nc tCommLen
  , Add 1 tCommLenPred tCommLen
  , Mul 15 nc wCoeffN
  , Mul 6 nc indexSigmaN
  , Mul 43 nc chunkBases
  , Add 2 chunkBases nonSgBases
  , Add 2 nonSgBases totalBases
  , Add 2 nc sg1
  , Add sg1 indexSigmaN sg2
  , Add sg2 wCoeffN sg3
  , Add sg3 wCoeffN sg4
  , Add sg4 indexSigmaN nonSgBases
  , Add 1 totalBasesPred totalBases
  , Add pad n PaddedLength
  , Reflectable pad Int
  ) =>
  StepSlotsCarrier
    (Slot k n nc statement /\ rest)
    ds
    dw
    f
    sf
    b
    len
    (PerProofWitness n nc ds dw f sf b /\ restPw)
    (SlotVkSource nc /\ restVk)
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

-- | Type-level mapping `spec → valCarrier` for the heterogeneous
-- | per-slot statements carrier (one slot per prev, holding that
-- | prev's `statement` type). Funcdep `spec -> valCarrier`.
class SlotStatementsCarrier :: Type -> Type -> Constraint
class SlotStatementsCarrier spec valCarrier | spec -> valCarrier

instance SlotStatementsCarrier Unit Unit

instance
  SlotStatementsCarrier rest restValCarrier =>
  SlotStatementsCarrier
    (Slot k n nc statement /\ rest)
    (statement /\ restValCarrier)
