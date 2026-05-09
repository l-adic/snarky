-- | Heterogeneous per-prev container for `step_main`.
-- |
-- | Encodes the per-prev spec as a type-level list of `(n, statement)`
-- | pairs (`PrevsSpecCons` / `PrevsSpecSideLoadedCons` / `PrevsSpecNil`)
-- | so each slot's `Per_proof_witness.t` is sized by THAT prev's own
-- | `max_proofs_verified`. Required for byte-identity on
-- | heterogeneous-prev rules like `Tree_proof_return` (Ns = `[0; 2]`),
-- | where a uniform-`n` encoding over-allocates per-slot fields.
-- |
-- | The `PrevsCarrier` class derives the concrete nested-tuple carrier
-- | from the spec (fundep) and provides a rank-2 traversal that
-- | invokes a callback per slot with that slot's `n_i` in scope.
-- |
-- | Step-side analog of `Pickles.Wrap.Slots`. Reference: OCaml
-- | `per_proof_witness.ml`, `step_main.ml`'s `exists_prevs`.
module Pickles.Step.Prevs
  ( PrevsSpecNil
  , PrevsSpecCons
  , PrevsSpecSideLoadedCons
  , StepSlot(..)
  , class PrevsCarrier
  , class PrevValuesCarrier
  , traversePrevsA
  , replicatePrevsCarrier
  ) where

import Prelude

import Data.Fin (Finite, finZero, shiftSucc)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Types (PaddedLength, StepPerProofWitness)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (BoolVar, F, FVar)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Type.Proxy (Proxy(..))

-- | Empty prev list (rule verifies zero previous proofs). Phantom; no
-- | inhabitants.
data PrevsSpecNil

-- | Cons a compiled prev with `max_proofs_verified = n` and statement
-- | type `statement` onto the spec. `statement` is the prev's
-- | `StatementIO input output` (kimchi-public payload of that prev's
-- | proof). Input-mode prevs use `StatementIO i Unit`; Output-mode
-- | use `StatementIO Unit o`.
data PrevsSpecCons :: Int -> Type -> Type -> Type
data PrevsSpecCons n statement rest

-- | Cons a side-loaded prev with compile-time upper bound `mpvMax` on
-- | the side-loaded tag's `max_proofs_verified`. The runtime mpv (read
-- | from the side-loaded VK's one-hot bits) may be `0`, `1`, or
-- | `mpvMax`; the verifier circuit is sized for `mpvMax` and masks
-- | unused slots.
-- |
-- | Same per-proof witness shape as `PrevsSpecCons mpvMax …` — only
-- | the routing differs: `wrap_key` and `actual_wrap_domain` come
-- | from a runtime `Pickles.Sideload.VerificationKey` rather than
-- | compile-time-baked data.
data PrevsSpecSideLoadedCons :: Int -> Type -> Type -> Type
data PrevsSpecSideLoadedCons mpvMax statement rest

-- | Per-slot runtime data for one step prev. Currently just the
-- | per-proof witness; bundled so a single spec-indexed carrier
-- | threads through the prover stack.
newtype StepSlot n ds dw f sf b = StepSlot
  { sppw :: StepPerProofWitness n ds dw f sf b
  }

-- | Spec → (`len`, `carrier`) mapping plus a rank-2 traversal.
-- |
-- | Carrier derivation:
-- |
-- | * `PrevsSpecNil` → `Unit`
-- | * `PrevsSpecCons n stmt rest` → `StepSlot n … /\ restCarrier`
-- | * `PrevsSpecSideLoadedCons mpvMax stmt rest` → `StepSlot mpvMax … /\ restCarrier`
class PrevsCarrier
  :: Type -> Int -> Int -> Type -> Type -> Type -> Int -> Type -> Constraint
class
  PrevsCarrier spec ds dw f sf b len carrier
  | spec ds dw f sf b -> len carrier
  where
  -- | Walk the carrier in slot order. The callback's `forall n. ...`
  -- | prefix gives each invocation access to its slot's `n_i`. The
  -- | `Finite len` index is the absolute slot position (lifted via
  -- | `shiftSucc` at each recursive layer).
  traversePrevsA
    :: forall m result
     . Applicative m
    => ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => Finite len
         -> StepSlot n ds dw f sf b
         -> m result
       )
    -> carrier
    -> m (Vector len result)

  -- | Build a carrier from a rank-2 polymorphic dummy slot. Each slot
  -- | auto-specialises the dummy to its own `n_i`.
  replicatePrevsCarrier
    :: ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => StepSlot n ds dw f sf b
       )
    -> carrier

instance PrevsCarrier PrevsSpecNil ds dw f sf b 0 Unit where
  traversePrevsA _ _ = pure Vector.nil
  replicatePrevsCarrier _ = unit

instance
  ( PrevsCarrier rest ds dw f sf b restLen rcarrier
  , Add restLen 1 len
  , Reflectable n Int
  , Add pad n PaddedLength
  , Reflectable pad Int
  ) =>
  PrevsCarrier
    (PrevsSpecCons n statement rest)
    ds
    dw
    f
    sf
    b
    len
    (StepSlot n ds dw f sf b /\ rcarrier)
  where
  traversePrevsA f (here /\ rest) =
    Vector.cons
      <$> f (finZero :: Finite len) here
      <*> traversePrevsA @rest (\i' pw -> f (shiftSucc i') pw) rest

  replicatePrevsCarrier dummyPPW =
    dummyPPW /\ replicatePrevsCarrier @rest dummyPPW

instance
  ( PrevsCarrier rest ds dw f sf b restLen rcarrier
  , Add restLen 1 len
  , Reflectable mpvMax Int
  , Add pad mpvMax PaddedLength
  , Reflectable pad Int
  ) =>
  PrevsCarrier
    (PrevsSpecSideLoadedCons mpvMax statement rest)
    ds
    dw
    f
    sf
    b
    len
    (StepSlot mpvMax ds dw f sf b /\ rcarrier)
  where
  traversePrevsA f (here /\ rest) =
    Vector.cons
      <$> f (finZero :: Finite len) here
      <*> traversePrevsA @rest (\i' pw -> f (shiftSucc i') pw) rest

  replicatePrevsCarrier dummyPPW =
    dummyPPW /\ replicatePrevsCarrier @rest dummyPPW

-- `StepSlot` is a newtype around `sppw`, so its `CircuitType` /
-- `CheckedType` forward to `StepPerProofWitness`'s. The wrapper
-- contributes zero fields.

instance
  ( CircuitType f
      (StepPerProofWitness n ds dw (F f) sf Boolean)
      (StepPerProofWitness n ds dw (FVar f) sfvar (BoolVar f))
  ) =>
  CircuitType f
    (StepSlot n ds dw (F f) sf Boolean)
    (StepSlot n ds dw (FVar f) sfvar (BoolVar f)) where
  sizeInFields pf _ = sizeInFields pf
    (Proxy @(StepPerProofWitness n ds dw (F f) sf Boolean))
  valueToFields (StepSlot r) =
    valueToFields @f @(StepPerProofWitness n ds dw (F f) sf Boolean) r.sppw
  fieldsToValue fs = StepSlot
    { sppw: fieldsToValue @f @(StepPerProofWitness n ds dw (F f) sf Boolean) fs
    }
  varToFields (StepSlot r) =
    varToFields
      @f
      @(StepPerProofWitness n ds dw (F f) sf Boolean)
      @(StepPerProofWitness n ds dw (FVar f) sfvar (BoolVar f))
      r.sppw
  fieldsToVar fs = StepSlot
    { sppw:
        fieldsToVar
          @f
          @(StepPerProofWitness n ds dw (F f) sf Boolean)
          @(StepPerProofWitness n ds dw (FVar f) sfvar (BoolVar f))
          fs
    }

instance
  ( CheckedType f c
      (StepPerProofWitness n ds dw (FVar f) sfvar (BoolVar f))
  ) =>
  CheckedType f c (StepSlot n ds dw (FVar f) sfvar (BoolVar f)) where
  check (StepSlot r) = check r.sppw

-- | Type-level mapping `spec → valCarrier` for the heterogeneous
-- | prev-statements carrier (one slot per prev, holding that prev's
-- | `statement` type). Funcdep `spec -> valCarrier`.
class PrevValuesCarrier :: Type -> Type -> Constraint
class PrevValuesCarrier spec valCarrier | spec -> valCarrier

instance PrevValuesCarrier PrevsSpecNil Unit

instance
  PrevValuesCarrier rest restValCarrier =>
  PrevValuesCarrier
    (PrevsSpecCons n statement rest)
    (statement /\ restValCarrier)

instance
  PrevValuesCarrier rest restValCarrier =>
  PrevValuesCarrier
    (PrevsSpecSideLoadedCons mpvMax statement rest)
    (statement /\ restValCarrier)
