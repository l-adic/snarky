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
  -- Stateful monad (matching OCaml's mutable Opt_sponge.t)
  , OptSpongePhase(..)
  , OptSpongeState
  , OptSpongeM(..)
  , runOptSpongeM
  , liftSnarky
  , optAbsorb
  , optAbsorbPoint
  , optSqueeze
  , optChallenge
  , optScalarChallenge
  , peekPreSqueezeState
  , toRegularSponge
  , ofSponge
  , runOptSpongeFromSponge
  ) where

import Prelude

import Control.Monad.State.Trans (StateT(..), runStateT)
import Data.Array as Array
import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (foldM)
import Data.List (List)
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector)
import Data.Vector as Vector
import Poseidon (class PoseidonField)
import RandomOracle.Sponge as RegSponge
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (sub_)
import Snarky.Circuit.DSL (Bool(..), BoolVar, FVar, SizedF, Snarky, addConstraint, all_, and_, any_, const_, exists, false_, if_, mul_, not_, or_, read, readCVar, true_, xor_)
import Snarky.Circuit.Kimchi.Poseidon (poseidon)
import Snarky.Circuit.Kimchi.RangeCheck (lowest128Bits')
import Snarky.Constraint.Basic (r1cs)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint(..))

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
  :: forall f r
   . PoseidonField f
  => PrimeField f
  => OptSponge f
  -> Array (Tuple (BoolVar f) (FVar f))
  -> Snarky f (KimchiConstraint f) r (FVar f)
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
  :: forall f r
   . PrimeField f
  => Vector 3 (FVar f)
  -> BoolVar f
  -> FVar f
  -> Snarky f (KimchiConstraint f) r (Vector 3 (FVar f))
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
  :: forall f r
   . PoseidonField f
  => PrimeField f
  => BoolVar f
  -> Vector 3 (FVar f)
  -> Snarky f (KimchiConstraint f) r (Vector 3 (FVar f))
condPermute permute state = do
  permuted <- poseidon state
  if_ permute permuted state

-- | Process one pair of conditional absorptions.
-- | Matches OCaml's consume_pairs fold body exactly.
consumePair
  :: forall f r
   . PoseidonField f
  => PrimeField f
  => { state :: Vector 3 (FVar f), pos :: BoolVar f }
  -> Tuple { b :: BoolVar f, x :: FVar f } { b :: BoolVar f, x :: FVar f }
  -> Snarky f (KimchiConstraint f) r { state :: Vector 3 (FVar f), pos :: BoolVar f }
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
  :: forall f r
   . PoseidonField f
  => PrimeField f
  => OptSponge f
  -> Array (Tuple (BoolVar f) (FVar f))
  -> Snarky f (KimchiConstraint f) r (Vector 3 (FVar f))
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
  case leftover of
    Nothing -> do
      shouldPermute <-
        if needsFinalPermuteIfEmpty then or_ emptyInput pos
        else pure pos
      condPermute shouldPermute state
    Just (Tuple b x) -> do
      void $ xor_ pos b
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
      as' = Array.toUnfoldable as
    in
      go { pairs: [], leftover: Nothing } as'
    where
    go acc List.Nil = acc
    go acc (List.Cons a List.Nil) = acc { leftover = Just a }
    go acc (List.Cons a (List.Cons b rest)) =
      go (acc { pairs = acc.pairs `Array.snoc` Tuple a b }) rest

-------------------------------------------------------------------------------
-- | Stateful OptSponge monad (matches OCaml's mutable Opt_sponge.t)
-------------------------------------------------------------------------------

-- | Sponge phase: either accumulating absorptions or in squeezed state.
data OptSpongePhase f
  = Absorbing { nextIndex :: BoolVar f, xs :: List (Tuple (BoolVar f) (FVar f)) }
  | OptSqueezed Int

-- | Full mutable-like state for the Opt sponge.
type OptSpongeState f =
  { state :: Vector 3 (FVar f)
  , phase :: OptSpongePhase f
  , needsFinalPermuteIfEmpty :: Boolean
  }

-- | Stateful Opt sponge monad wrapping Snarky.
newtype OptSpongeM f c r a = OptSpongeM (StateT (OptSpongeState f) (Snarky f c r) a)

derive instance Newtype (OptSpongeM f c r a) _
derive newtype instance Functor (Snarky f c r) => Functor (OptSpongeM f c r)
derive newtype instance (Monad (Snarky f c r)) => Apply (OptSpongeM f c r)
derive newtype instance (Monad (Snarky f c r)) => Applicative (OptSpongeM f c r)
derive newtype instance (Monad (Snarky f c r)) => Bind (OptSpongeM f c r)
derive newtype instance (Monad (Snarky f c r)) => Monad (OptSpongeM f c r)

-- | Run an OptSpongeM computation, returning both result and final state.
runOptSpongeM
  :: forall f r a
   . PrimeField f
  => PrimeField f
  => OptSpongeM f (KimchiConstraint f) r a
  -> Snarky f (KimchiConstraint f) r (Tuple a (OptSpongeState f))
runOptSpongeM computation =
  runStateT (unwrap computation) initialOptState
  where
  initialOptState =
    { state: Vector.replicate (const_ zero)
    , phase: Absorbing { nextIndex: false_, xs: List.Nil }
    , needsFinalPermuteIfEmpty: true
    }

-- | Run an OptSpongeM computation starting from a regular sponge.
-- | Converts the regular sponge to OptSpongeState via ofSponge, then runs.
runOptSpongeFromSponge
  :: forall f r a
   . PoseidonField f
  => PrimeField f
  => RegSponge.Sponge (FVar f)
  -> OptSpongeM f (KimchiConstraint f) r a
  -> Snarky f (KimchiConstraint f) r (Tuple a (OptSpongeState f))
runOptSpongeFromSponge sponge computation = do
  initState <- ofSponge sponge
  runStateT (unwrap computation) initState

-- | Lift a Snarky computation into OptSpongeM.
liftSnarky
  :: forall f r a
   . PrimeField f
  => Snarky f (KimchiConstraint f) r a
  -> OptSpongeM f (KimchiConstraint f) r a
liftSnarky ma = wrap $ StateT \s -> ma <#> \a -> Tuple a s

-- | Absorb a (flag, value) pair. Just accumulates; processing happens at squeeze.
optAbsorb
  :: forall f r
   . PrimeField f
  => Tuple (BoolVar f) (FVar f)
  -> OptSpongeM f (KimchiConstraint f) r Unit
optAbsorb pair = wrap $ StateT \s -> pure $ Tuple unit case s.phase of
  Absorbing { nextIndex, xs } ->
    s { phase = Absorbing { nextIndex, xs: pair List.: xs } }
  OptSqueezed _ ->
    s { phase = Absorbing { nextIndex: false_, xs: List.singleton pair } }

-- | Absorb a curve point with Boolean.true_ flag (unconditional).
optAbsorbPoint
  :: forall f r
   . PrimeField f
  => AffinePoint (FVar f)
  -> OptSpongeM f (KimchiConstraint f) r Unit
optAbsorbPoint (AffinePoint { x, y }) = do
  optAbsorb (Tuple true_ x)
  optAbsorb (Tuple true_ y)

-- | Squeeze a field element from the Opt sponge.
-- | Matches OCaml's Opt_sponge.squeeze exactly:
-- | - If Absorbing: consume all pending, return state[0], switch to Squeezed 1
-- | - If Squeezed n < rate: return state[n], switch to Squeezed (n+1)
-- | - If Squeezed n = rate: permute, return state[0], switch to Squeezed 1
optSqueeze
  :: forall f r
   . PoseidonField f
  => PrimeField f
  => OptSpongeM f (KimchiConstraint f) r (FVar f)
optSqueeze = wrap $ StateT \s -> case s.phase of
  OptSqueezed n ->
    if n >= 2 {- rate -} then do
      newState <- poseidon s.state
      pure $ Tuple (Vector.index newState (unsafeFinite @3 0))
        (s { state = newState, phase = OptSqueezed 1 })
    else
      pure $ Tuple (Vector.index s.state (unsafeFinite @3 n))
        (s { phase = OptSqueezed (n + 1) })
  Absorbing { nextIndex, xs } -> do
    let input = Array.fromFoldable (List.reverse xs)
    newState <- consume
      { state: s.state
      , pos: nextIndex
      , needsFinalPermuteIfEmpty: s.needsFinalPermuteIfEmpty
      }
      input
    pure $ Tuple (Vector.index newState (unsafeFinite @3 0))
      (s { state = newState, phase = OptSqueezed 1, needsFinalPermuteIfEmpty = true })

-- | Diagnostic: flush pending absorbs and return the resulting 3-field
-- | sponge state — equivalent to the state an external reference
-- | sponge (e.g. kimchi's) would be in right before the next squeeze.
-- |
-- | After this call, the sponge is left in `OptSqueezed 0` phase with
-- | state = post-consume state. The next `optSqueeze` then returns
-- | state[0] and advances to `OptSqueezed 1` — exactly what would
-- | happen if this peek hadn't been called AND the pending absorbs
-- | had been consumed by that optSqueeze's own Absorbing branch.
-- |
-- | Safe to insert just before a `optChallenge` / `optScalarChallenge`
-- | call for debugging without changing circuit semantics.
peekPreSqueezeState
  :: forall f r
   . PoseidonField f
  => PrimeField f
  => OptSpongeM f (KimchiConstraint f) r (Vector 3 (FVar f))
peekPreSqueezeState = wrap $ StateT \s -> case s.phase of
  OptSqueezed _ -> pure $ Tuple s.state s
  Absorbing { nextIndex, xs } -> do
    let input = Array.fromFoldable (List.reverse xs)
    newState <- consume
      { state: s.state
      , pos: nextIndex
      , needsFinalPermuteIfEmpty: s.needsFinalPermuteIfEmpty
      }
      input
    pure $ Tuple newState
      ( s
          { state = newState
          , phase = OptSqueezed 0
          , needsFinalPermuteIfEmpty = true
          }
      )

-- | Squeeze a challenge (lowest 128 bits, constrain_low_bits:true).
-- | Matches OCaml's Opt.challenge.
optChallenge
  :: forall f r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => PrimeField f
  => FVar f -- ^ endo constant
  -> OptSpongeM f (KimchiConstraint f) r (SizedF 128 (FVar f))
optChallenge endo = do
  x <- optSqueeze
  liftSnarky $ lowest128Bits' true endo x

-- | Squeeze a scalar challenge (lowest 128 bits, constrain_low_bits:false).
-- | Matches OCaml's Opt.scalar_challenge.
optScalarChallenge
  :: forall f r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => PrimeField f
  => FVar f -- ^ endo constant
  -> OptSpongeM f (KimchiConstraint f) r (SizedF 128 (FVar f))
optScalarChallenge endo = do
  x <- optSqueeze
  liftSnarky $ lowest128Bits' false endo x

-- | Convert OptSponge state to a regular Sponge for continuation (e.g., bulletproof check).
-- | Only valid when the OptSponge is in Squeezed state.
toRegularSponge
  :: forall f r
   . PrimeField f
  => OptSpongeM f (KimchiConstraint f) r (RegSponge.Sponge (FVar f))
toRegularSponge = wrap $ StateT \s -> case s.phase of
  OptSqueezed n ->
    pure $ Tuple
      { state: s.state, spongeState: RegSponge.Squeezed (unsafeFinite @3 n) }
      s
  Absorbing _ ->
    pure $ Tuple
      { state: s.state, spongeState: RegSponge.Absorbed (unsafeFinite @3 0) }
      s

-- | Convert a regular sponge to OptSpongeState, matching OCaml's Opt_sponge.of_sponge.
-- |
-- | Reference: mina/src/lib/crypto/pickles/opt_sponge.ml:46-74
ofSponge
  :: forall f r
   . PoseidonField f
  => PrimeField f
  => RegSponge.Sponge (FVar f)
  -> Snarky f (KimchiConstraint f) r (OptSpongeState f)
ofSponge sponge = case sponge.spongeState of
  RegSponge.Squeezed n ->
    pure
      { state: sponge.state
      , phase: OptSqueezed (getFinite n)
      , needsFinalPermuteIfEmpty: true
      }
  RegSponge.Absorbed n -> case getFinite n of
    0 ->
      pure
        { state: sponge.state
        , phase: Absorbing { nextIndex: false_, xs: List.Nil }
        , needsFinalPermuteIfEmpty: true
        }
    1 ->
      pure
        { state: sponge.state
        , phase: Absorbing { nextIndex: true_, xs: List.Nil }
        , needsFinalPermuteIfEmpty: true
        }
    _ -> do
      -- Absorbed 2: apply permutation, reset to position 0
      permuted <- poseidon sponge.state
      pure
        { state: permuted
        , phase: Absorbing { nextIndex: false_, xs: List.Nil }
        , needsFinalPermuteIfEmpty: false
        }

