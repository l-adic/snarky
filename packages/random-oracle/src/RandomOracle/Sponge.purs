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
import Data.Array as Array
import Data.Enum (succ)
import Data.Fin (Finite, unsafeFinite)
import Data.Generic.Rep (class Generic)
import Data.Maybe (fromJust)
import Data.Show.Generic (genericShow)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField, fullRound, getNumRounds)
import Type.Proxy (Proxy(..))

-- | The state size of the Poseidon sponge (always 3)
stateSize :: Int
stateSize = 3

-- | The rate of the sponge (how many elements can be absorbed per permutation)
rate :: Finite 3
rate = unsafeFinite 2

-- | The sponge state tracks whether we are absorbing or squeezing
data SpongeState
  = Absorbed (Finite 3) -- ^ Number of elements absorbed since last permutation
  | Squeezed (Finite 3) -- ^ Number of elements squeezed since last permutation

derive instance eqSpongeState :: Eq SpongeState
derive instance ordSpongeState :: Ord SpongeState

derive instance Generic SpongeState _

instance showSpongeState :: Show SpongeState where
  show x = genericShow x

-- | The sponge structure with state and mode
type Sponge f =
  { state :: Vector 3 f
  , spongeState :: SpongeState
  }

-- | Initial state: all zeros
initialState :: forall f. Semiring f => Vector 3 f
initialState = Vector.generate (const zero)

-- | Create a new sponge with the given initial state
create :: forall f. Vector 3 f -> Sponge f
create init =
  { state: init
  , spongeState: Absorbed (unsafeFinite 0)
  }

-- | Run the Poseidon permutation (55 full rounds)
permute :: forall f. PoseidonField f => Vector 3 f -> Vector 3 f
permute st =
  let
    n = getNumRounds (Proxy @f)
  in
    foldl (\s i -> fullRound s i) st (Array.range 0 (n - 1))

-- | Absorb a single field element into the sponge
absorb :: forall f. PoseidonField f => f -> Sponge f -> Sponge f
absorb x sponge = case sponge.spongeState of
  Absorbed n ->
    if n == rate then
      -- Rate limit reached, permute first then absorb
      let
        newState = permute sponge.state
        newState' = Vector.modifyAt p0 (add x) newState
      in
        { state: newState', spongeState: Absorbed p1 }
    else
      -- Add to current position
      let
        newState = Vector.modifyAt n (add x) sponge.state
        -- must be < rate == 2
        pNext = unsafePartial fromJust $ succ n
      in
        { state: newState, spongeState: Absorbed pNext }
  Squeezed _ ->
    -- Coming from squeezed state, add at position 0
    let
      newState = Vector.modifyAt p0 (add x) sponge.state
    in
      { state: newState, spongeState: Absorbed p1 }
  where
  p0 :: Finite 3
  p0 = unsafeFinite 0

  p1 :: Finite 3
  p1 = unsafeFinite 1

-- | Squeeze a field element from the sponge
squeeze :: forall f. PoseidonField f => Sponge f -> { result :: f, sponge :: Sponge f }
squeeze sponge = case sponge.spongeState of
  Squeezed n ->
    if n == rate then
      -- Rate limit reached, permute first then squeeze
      let
        newState = permute sponge.state
        result = Vector.index newState p0
      in
        { result, sponge: { state: newState, spongeState: Squeezed p1 } }
    else
      -- Return from current position
      let
        result = Vector.index sponge.state n
        -- must be < rate == 2
        pNext = unsafePartial fromJust $ succ n
      in
        { result, sponge: { state: sponge.state, spongeState: Squeezed pNext } }
  Absorbed _ ->
    -- Coming from absorbed state, permute first
    let
      newState = permute sponge.state
      result = Vector.index newState p0
    in
      { result, sponge: { state: newState, spongeState: Squeezed p1 } }
  where
  p0 :: Finite 3
  p0 = unsafeFinite 0

  p1 :: Finite 3
  p1 = unsafeFinite 1

-- | Get the current state of the sponge
state :: forall f. Sponge f -> Vector 3 f
state sponge = sponge.state
