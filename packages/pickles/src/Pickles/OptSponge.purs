-- | Conditional sponge for optional absorption.
-- |
-- | Unlike the regular sponge which tracks position at compile time,
-- | OptSponge tracks position as a circuit boolean because conditional
-- | absorption makes the position data-dependent at runtime.
-- |
-- | Reference: mina/src/lib/crypto/pickles/opt_sponge.ml
module Pickles.OptSponge
  ( OptSponge
  , create
  , squeeze
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (unsafeFinite)
import Data.Foldable (foldM)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (sub_)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, addConstraint, all_, and_, any_, const_, exists, false_, if_, mul_, not_, or_, readCVar, xor_)
import Snarky.Circuit.Kimchi.Poseidon (poseidon)
import Snarky.Constraint.Basic (r1cs)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)

type OptSponge f =
  { state :: Vector 3 (FVar f)
  , pos :: BoolVar f
  , needsFinalPermuteIfEmpty :: Boolean
  }

-- | Create a fresh OptSponge with zero initial state.
create :: forall f. PrimeField f => OptSponge f
create =
  { state: Vector.replicate (const_ zero)
  , pos: false_
  , needsFinalPermuteIfEmpty: true
  }

-- | Squeeze the sponge after consuming all pending absorptions.
-- | Returns state[0] after the final permutation.
squeeze
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => OptSponge f
  -> Array (Tuple (BoolVar f) (FVar f))
  -> Snarky (KimchiConstraint f) t m (FVar f)
squeeze sponge pending = do
  finalState <- consume sponge pending
  pure $ Vector.index finalState (unsafeFinite 0)

-------------------------------------------------------------------------------
-- Internal
-------------------------------------------------------------------------------

-- | Conditionally add x to rate position based on pos.
-- | When pos = false (0), adds to state[0]; when pos = true (1), adds to state[1].
-- |
-- | For each rate position j, witnesses s_j' and constrains:
-- |   x * flag_j = s_j' - s_j
-- | where flag_0 = NOT pos, flag_1 = pos.
addIn
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> BoolVar f
  -> FVar f
  -> Snarky (KimchiConstraint f) t m (Vector 3 (FVar f))
addIn state pos x = do
  let
    iEquals0 = not_ pos
    iEquals1 = pos
    s0 = Vector.index state (unsafeFinite 0)
    s1 = Vector.index state (unsafeFinite 1)

  -- Update position 0: s0' = s0 + (NOT pos) * x
  s0' <- exists do
    s0Val <- readCVar s0
    flagVal <- readCVar (coerce iEquals0 :: FVar f)
    xVal <- readCVar x
    pure $ if flagVal /= zero then s0Val + xVal else s0Val
  addConstraint $ r1cs
    { left: x
    , right: coerce iEquals0
    , output: s0' `sub_` s0
    }

  -- Update position 1: s1' = s1 + pos * x
  s1' <- exists do
    s1Val <- readCVar s1
    flagVal <- readCVar (coerce iEquals1 :: FVar f)
    xVal <- readCVar x
    pure $ if flagVal /= zero then s1Val + xVal else s1Val
  addConstraint $ r1cs
    { left: x
    , right: coerce iEquals1
    , output: s1' `sub_` s1
    }

  pure $ Vector.modifyAt (unsafeFinite 0) (const s0')
    $ Vector.modifyAt (unsafeFinite 1) (const s1') state

-- | Conditional poseidon permutation.
-- | Runs the permutation, then selects between permuted and original state.
condPermute
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => BoolVar f
  -> Vector 3 (FVar f)
  -> Snarky (KimchiConstraint f) t m (Vector 3 (FVar f))
condPermute permute state = do
  permuted <- poseidon state
  if_ permute permuted state

-- | Process one pair of conditional absorptions.
-- | Matches OCaml's consume_pairs fold body exactly.
consumePair
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => { state :: Vector 3 (FVar f), pos :: BoolVar f }
  -> Tuple { b :: BoolVar f, x :: FVar f } { b :: BoolVar f, x :: FVar f }
  -> Snarky (KimchiConstraint f) t m { state :: Vector 3 (FVar f), pos :: BoolVar f }
consumePair { state, pos: p } (Tuple first second) = do
  let { b, x } = first
  let { b: b', x: y } = second

  -- Position tracking
  p' <- xor_ p b
  posAfter <- xor_ p' b'

  -- Mask y by b'
  yMasked <- mul_ y (coerce b')

  -- Only add y after permutation when (b=1, b'=1, p=1)
  addInYAfter <- all_ [ b, b', p ]
  let addInYBefore = not_ addInYAfter

  -- Add x*b to state at position p
  xb <- mul_ x (coerce b)
  state1 <- addIn state p xb

  -- Add yMasked*before_flag to state at position p'
  yBefore <- mul_ yMasked (coerce addInYBefore)
  state2 <- addIn state1 p' yBefore

  -- Compute permute flag: (b && b') || (p && (b || b'))
  -- OCaml evaluates right-to-left for list construction, so:
  -- 1. all [p, b ||| b'] is computed first (rightmost list element)
  -- 2. all [b, b'] is computed second (leftmost)
  -- 3. any [left, right]
  bOrB' <- or_ b b'
  pAndBOrB' <- and_ p bOrB'
  bAndB' <- and_ b b'
  permute <- or_ bAndB' pAndBOrB'

  -- Conditional permutation
  state3 <- condPermute permute state2

  -- Add yMasked*after_flag to state at position p'
  yAfter <- mul_ yMasked (coerce addInYAfter)
  state4 <- addIn state3 p' yAfter

  pure { state: state4, pos: posAfter }

-- | Consume all pending absorptions and perform final permutation.
consume
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => OptSponge f
  -> Array (Tuple (BoolVar f) (FVar f))
  -> Snarky (KimchiConstraint f) t m (Vector 3 (FVar f))
consume { state: initState, pos: startPos, needsFinalPermuteIfEmpty } input = do
  let
    n = Array.length input
    numPairs = n / 2
    remaining = n - 2 * numPairs

    -- Build pairs array matching OCaml's Array.init
    pairs = Array.mapWithIndex
      ( \i _ ->
          let
            first = unsafePartial $ Array.unsafeIndex input (2 * i)
            second = unsafePartial $ Array.unsafeIndex input (2 * i + 1)
          in
            Tuple
              { b: fst first, x: snd first }
              { b: fst second, x: snd second }
      )
      (Array.replicate numPairs unit)

  -- Process all pairs
  { state, pos } <- foldM consumePair { state: initState, pos: startPos } pairs

  -- Compute empty_input = not (any (map fst input))
  emptyInput <- not $ any_ (map fst input)

  -- Handle remainder and compute should_permute
  case remaining of
    0 -> do
      shouldPermute <-
        if needsFinalPermuteIfEmpty then or_ emptyInput pos
        else pure pos
      condPermute shouldPermute state
    1 -> do
      let
        lastElem = unsafePartial $ Array.unsafeIndex input (n - 1)
        b = fst lastElem
        x = snd lastElem
        p = pos
      _posAfter <- xor_ p b
      xb <- mul_ x (coerce b)
      state' <- addIn state p xb
      shouldPermute <-
        if needsFinalPermuteIfEmpty then any_ [ p, b, emptyInput ]
        else any_ [ p, b ]
      condPermute shouldPermute state'
    _ -> pure state -- unreachable
