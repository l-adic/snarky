-- | Heterogeneous per-slot container for `step_main`.
-- |
-- | A rule's prev list is encoded at the type level as a tuple chain
-- | of `Slot` descriptors (from `Pickles.Slots`) ending in `Unit`:
-- |
-- |   Slot Compiled 1 (StatementIO Stmt) /\ Slot SideLoaded 2 Stmt' /\ Unit
-- |
-- | Heterogeneity matters for rules like `Tree_proof_return` (Ns =
-- | `[0, 2]`): each slot's `Per_proof_witness.t` is sized by THAT
-- | prev's own `n`, not the rule-level max.
-- |
-- | The `StepSlotsCarrier` class derives the concrete nested-tuple
-- | value carrier from the spec (fundep) and provides a rank-2
-- | traversal that invokes a callback per slot with that slot's `n_i`
-- | in scope.
-- |
-- | Step-side analog of `Pickles.Wrap.Slots`. Reference: OCaml
-- | `per_proof_witness.ml`, `step_main.ml`'s `exists_prevs`.
module Pickles.Step.Slots
  ( class StepSlotsCarrier
  , class SlotStatementsCarrier
  , traverseStepSlotsA
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
import Pickles.Types (PaddedLength)
import Prim.Int (class Add)

-- | Spec → (`len`, `carrier`) mapping plus a rank-2 traversal.
-- |
-- | Carrier derivation:
-- |
-- | * `Unit` (empty spec) → `Unit`
-- | * `Slot k n stmt /\ rest` → `PerProofWitness n … /\ restCarrier`
-- |
-- | The kind `k` doesn't affect the carrier — both compiled and
-- | side-loaded slots present the same `PerProofWitness` shape.
class StepSlotsCarrier
  :: Type -> Int -> Int -> Int -> Type -> Type -> Type -> Int -> Type -> Constraint
class
  StepSlotsCarrier spec numChunks ds dw f sf b len carrier
  | spec numChunks ds dw f sf b -> len carrier
  where
  -- | Walk the carrier in slot order. The callback's `forall n. ...`
  -- | prefix gives each invocation access to its slot's `n_i`. The
  -- | `Finite len` index is the absolute slot position (lifted via
  -- | `shiftSucc` at each recursive layer).
  traverseStepSlotsA
    :: forall m result
     . Applicative m
    => ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => Finite len
         -> PerProofWitness n numChunks ds dw f sf b
         -> m result
       )
    -> carrier
    -> m (Vector len result)

  -- | Build a carrier from a rank-2 polymorphic dummy slot. Each slot
  -- | auto-specialises the dummy to its own `n_i`.
  replicateStepSlotsCarrier
    :: ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => PerProofWitness n numChunks ds dw f sf b
       )
    -> carrier

instance StepSlotsCarrier Unit numChunks ds dw f sf b 0 Unit where
  traverseStepSlotsA _ _ = pure Vector.nil
  replicateStepSlotsCarrier _ = unit

instance
  ( StepSlotsCarrier rest numChunks ds dw f sf b restLen rcarrier
  , Add restLen 1 len
  , Reflectable n Int
  , Add pad n PaddedLength
  , Reflectable pad Int
  ) =>
  StepSlotsCarrier
    (Slot k n statement /\ rest)
    numChunks
    ds
    dw
    f
    sf
    b
    len
    (PerProofWitness n numChunks ds dw f sf b /\ rcarrier)
  where
  traverseStepSlotsA f (here /\ rest) =
    Vector.cons
      <$> f (finZero :: Finite len) here
      <*> traverseStepSlotsA @rest (\i' pw -> f (shiftSucc i') pw) rest

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
    (Slot k n statement /\ rest)
    (statement /\ restValCarrier)
