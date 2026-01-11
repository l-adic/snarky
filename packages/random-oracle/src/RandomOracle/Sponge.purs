-- | Poseidon sponge construction for use with random oracles.
-- |
-- | This module implements a duplex sponge with:
-- | - State size: 3
-- | - Rate: 2
-- | - Capacity: 1
module RandomOracle.Sponge
  ( Sponge
  , SpongeState(..)
  , create
  , absorb
  , squeeze
  , state
  , rate
  , stateSize
  , initialState
  , permute
  ) where

import Prelude

import Data.Array (foldl)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Data.Fin (unsafeFinite, getFinite)
import Data.FunctorWithIndex (mapWithIndex)
import Poseidon.Class (class PoseidonField, fullRound)

-- | The state size of the Poseidon sponge (always 3)
stateSize :: Int
stateSize = 3

-- | The rate of the sponge (how many elements can be absorbed per permutation)
rate :: Int
rate = 2

-- | The sponge state tracks whether we are absorbing or squeezing
data SpongeState
  = Absorbed Int -- ^ Number of elements absorbed since last permutation
  | Squeezed Int -- ^ Number of elements squeezed since last permutation

derive instance eqSpongeState :: Eq SpongeState
derive instance ordSpongeState :: Ord SpongeState

instance showSpongeState :: Show SpongeState where
  show (Absorbed n) = "Absorbed(" <> show n <> ")"
  show (Squeezed n) = "Squeezed(" <> show n <> ")"

-- | The sponge structure with state and mode
type Sponge f =
  { state :: Vector 3 f
  , spongeState :: SpongeState
  }

-- | Initial state: all zeros
initialState :: forall f. Semiring f => Vector 3 f
initialState = Vector.generate (const zero)

-- | Create a new sponge with optional initial state
create :: forall f. Semiring f => Vector 3 f -> Sponge f
create init =
  { state: init
  , spongeState: Absorbed 0
  }

-- | Run the Poseidon permutation (55 full rounds)
permute :: forall f. PoseidonField f => Vector 3 f -> Vector 3 f
permute st = foldl (\s i -> fullRound s i) st rounds
  where
  rounds :: Array Int
  rounds = [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54 ]

-- | Add a value to the state at a given position
addAt :: forall f. Semiring f => Int -> f -> Vector 3 f -> Vector 3 f
addAt pos x st =
  mapWithIndex (\idx v -> if getFinite idx == pos then v + x else v) st

-- | Absorb a single field element into the sponge
absorb :: forall f. PoseidonField f => f -> Sponge f -> Sponge f
absorb x sponge = case sponge.spongeState of
  Absorbed n ->
    if n == rate then
      -- Rate limit reached, permute first then absorb
      let
        newState = permute sponge.state
        newState' = addAt 0 x newState
      in
        { state: newState', spongeState: Absorbed 1 }
    else
      -- Add to current position
      let
        newState = addAt n x sponge.state
      in
        { state: newState, spongeState: Absorbed (n + 1) }
  Squeezed _ ->
    -- Coming from squeezed state, add at position 0
    let
      newState = addAt 0 x sponge.state
    in
      { state: newState, spongeState: Absorbed 1 }

-- | Squeeze a field element from the sponge
squeeze :: forall f. PoseidonField f => Sponge f -> Tuple f (Sponge f)
squeeze sponge = case sponge.spongeState of
  Squeezed n ->
    if n == rate then
      -- Rate limit reached, permute first then squeeze
      let
        newState = permute sponge.state
        result = Vector.index newState (unsafeFinite 0)
      in
        Tuple result { state: newState, spongeState: Squeezed 1 }
    else
      -- Return from current position
      let
        result = Vector.index sponge.state (unsafeFinite n)
      in
        Tuple result { state: sponge.state, spongeState: Squeezed (n + 1) }
  Absorbed _ ->
    -- Coming from absorbed state, permute first
    let
      newState = permute sponge.state
      result = Vector.index newState (unsafeFinite 0)
    in
      Tuple result { state: newState, spongeState: Squeezed 1 }

-- | Get the current state of the sponge
state :: forall f. Sponge f -> Vector 3 f
state sponge = sponge.state
