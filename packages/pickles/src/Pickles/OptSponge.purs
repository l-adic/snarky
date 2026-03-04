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
import Data.List (List)
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector)
import Data.Vector as Vector
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (sub_)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, addConstraint, all_, and_, any_, const_, exists, false_, if_, mul_, not_, or_, read, readCVar, xor_)
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
  pure $ Vector.index finalState (unsafeFinite @3 0)

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
    s0 = Vector.index state (unsafeFinite @3 0)
    s1 = Vector.index state (unsafeFinite @3 1)

  -- Update position 0: s0' = s0 + (NOT pos) * x
  s0' <- exists do
    s0Val <- readCVar s0
    flagVal <- read iEquals0
    xVal <- readCVar x
    pure $ if flagVal then s0Val + xVal else s0Val
  addConstraint $ r1cs
    { left: x
    , right: coerce iEquals0
    , output: s0' `sub_` s0
    }

  -- Update position 1: s1' = s1 + pos * x
  s1' <- exists do
    s1Val <- readCVar s1
    flagVal <- read iEquals1
    xVal <- readCVar x
    pure $ if flagVal then s1Val + xVal else s1Val
  addConstraint $ r1cs
    { left: x
    , right: coerce iEquals1
    , output: s1' `sub_` s1
    }

  pure $ Vector.modifyAt (unsafeFinite @3 0) (const s0')
    $ Vector.modifyAt (unsafeFinite @3 1) (const s1') state

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
    -- Build pairs array matching OCaml's Array.init
    { pairs, leftover } =
      let
        ps = mkPairs input
      in
        ps
          { pairs =
              map
                ( \(Tuple (Tuple z1b z1x) (Tuple z2b z2x)) ->
                    Tuple { b: z1b, x: z1x } { b: z2b, x: z2x }
                )
                ps.pairs
          }

  -- Process all pairs
  { state, pos } <- foldM consumePair { state: initState, pos: startPos } pairs

  -- Compute empty_input = not (any (map fst input))
  emptyInput <- not $ any_ (map fst input)

  -- Handle remainder and compute should_permute
  -- unsafePartial is safe because remainder is mod 2
  case leftover of
    Nothing -> do
      shouldPermute <-
        if needsFinalPermuteIfEmpty then or_ emptyInput pos
        else pure pos
      condPermute shouldPermute state
    Just (Tuple b x) -> do
      _posAfter <- xor_ pos b
      xb <- mul_ x (coerce b)
      state' <- addIn state pos xb
      shouldPermute <-
        if needsFinalPermuteIfEmpty then any_ [ pos, b, emptyInput ]
        else any_ [ pos, b ]
      condPermute shouldPermute state'
  where
  mkPairs
    :: forall a
     . Array a
    -> { pairs :: Array (Tuple a a)
       , leftover :: Maybe a
       }
  mkPairs as =
    let
      as' :: List a
      as' = Array.toUnfoldable as
    in
      go { pairs: [], leftover: Nothing } as'
    where
    go acc List.Nil = acc
    go acc (List.Cons a List.Nil) = acc { leftover = Just a }
    go acc (List.Cons a (List.Cons b rest)) =
      go (acc { pairs = acc.pairs `Array.snoc` Tuple a b }) rest
