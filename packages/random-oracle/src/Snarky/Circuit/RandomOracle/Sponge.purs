-- | Circuit (checked) version of the Poseidon sponge.
-- |
-- | This module provides sponge operations (absorb/squeeze) that work within
-- | the circuit/constraint system. The sponge state is tracked at the PureScript
-- | level, while the actual field element state lives in the circuit.
-- |
-- | Key differences from the pure sponge:
-- | - Uses the Kimchi Poseidon gate for permutation (single constraint)
-- | - Operations are monadic (return Snarky computations)
-- | - Uses FVar f for field elements
module Snarky.Circuit.RandomOracle.Sponge
  ( absorb
  , squeeze
  , initialState
  , module ReExports
  ) where

import Prelude

import Data.Enum (succ)
import Data.Fin (Finite, unsafeFinite)
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import RandomOracle.Sponge (Sponge, SpongeState(..), create, rate, state) as ReExports
import RandomOracle.Sponge (Sponge, SpongeState(..), rate)
import RandomOracle.Sponge as Sponge
import Snarky.Circuit.CVar (add_, const_)
import Snarky.Circuit.DSL (class CircuitM, Snarky)
import Snarky.Circuit.Kimchi.Poseidon (poseidon)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)

-- | Initial state: all zeros (lifted from pure initialState)
initialState :: forall f. PrimeField f => Vector 3 (FVar f)
initialState = map const_ Sponge.initialState

-- | Absorb a single field element into the sponge.
-- |
-- | This follows the same logic as the pure sponge:
-- | - If we've absorbed `rate` elements, permute first
-- | - Add the element to the current position
-- | - Track the new sponge state
absorb
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => FVar f
  -> Sponge (FVar f)
  -> Snarky (KimchiConstraint f) t m (Sponge (FVar f))
absorb x sponge = case sponge.spongeState of
  Absorbed n ->
    if n == rate then do
      -- Rate limit reached, permute first then absorb
      newState <- poseidon sponge.state
      let newState' = Vector.modifyAt p0 (add_ x) newState
      pure { state: newState', spongeState: Absorbed p1 }
    else
      -- Add to current position (no permutation needed)
      let
        newState = Vector.modifyAt n (add_ x) sponge.state
        pNext = unsafePartial fromJust $ succ n
      in
        pure { state: newState, spongeState: Absorbed pNext }
  Squeezed _ ->
    -- Coming from squeezed state, add at position 0
    let
      newState = Vector.modifyAt p0 (add_ x) sponge.state
    in
      pure { state: newState, spongeState: Absorbed p1 }
  where
  p0 :: Finite 3
  p0 = unsafeFinite 0

  p1 :: Finite 3
  p1 = unsafeFinite 1

-- | Squeeze a field element from the sponge.
-- |
-- | This follows the same logic as the pure sponge:
-- | - If coming from absorbed state, permute first
-- | - If we've squeezed `rate` elements, permute first
-- | - Return the element at the current position
squeeze
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Sponge (FVar f)
  -> Snarky (KimchiConstraint f) t m { result :: FVar f, sponge :: Sponge (FVar f) }
squeeze sponge = case sponge.spongeState of
  Squeezed n ->
    if n == rate then do
      -- Rate limit reached, permute first then squeeze
      newState <- poseidon sponge.state
      let result = Vector.index newState p0
      pure { result, sponge: { state: newState, spongeState: Squeezed p1 } }
    else
      -- Return from current position (no permutation needed)
      let
        result = Vector.index sponge.state n
        pNext = unsafePartial fromJust $ succ n
      in
        pure { result, sponge: { state: sponge.state, spongeState: Squeezed pNext } }
  Absorbed _ -> do
    -- Coming from absorbed state, permute first
    newState <- poseidon sponge.state
    let result = Vector.index newState p0
    pure { result, sponge: { state: newState, spongeState: Squeezed p1 } }
  where
  p0 :: Finite 3
  p0 = unsafeFinite 0

  p1 :: Finite 3
  p1 = unsafeFinite 1
