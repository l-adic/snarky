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
  , toRegularSponge
  ) where

import Prelude

import Control.Monad.State.Trans (StateT(..), runStateT)
import Data.Array as Array
import Data.Fin (unsafeFinite)
import Data.Foldable (foldM)
import Data.List (List)
import Data.List as List
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector)
import Data.Vector as Vector
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (sub_)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, UnChecked(..), add_, addConstraint, all_, and_, any_, assertEqual_, const_, exists, false_, fromField, if_, mul_, not_, or_, read, readCVar, scale_, true_, xor_)
import Snarky.Circuit.DSL as SizedF
import Snarky.Circuit.Kimchi.EndoScalar as EndoScalar
import Snarky.Circuit.Kimchi.Poseidon (poseidon)
import Snarky.Constraint.Basic (r1cs)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint)
import RandomOracle.Sponge as RegSponge

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
newtype OptSpongeM f c t m a = OptSpongeM (StateT (OptSpongeState f) (Snarky c t m) a)

derive instance Newtype (OptSpongeM f c t m a) _
derive newtype instance Functor (Snarky c t m) => Functor (OptSpongeM f c t m)
derive newtype instance (Monad (Snarky c t m)) => Apply (OptSpongeM f c t m)
derive newtype instance (Monad (Snarky c t m)) => Applicative (OptSpongeM f c t m)
derive newtype instance (Monad (Snarky c t m)) => Bind (OptSpongeM f c t m)
derive newtype instance (Monad (Snarky c t m)) => Monad (OptSpongeM f c t m)

-- | Run an OptSpongeM computation, returning both result and final state.
runOptSpongeM
  :: forall f t m a
   . PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => OptSpongeM f (KimchiConstraint f) t m a
  -> Snarky (KimchiConstraint f) t m (Tuple a (OptSpongeState f))
runOptSpongeM computation =
  runStateT (unwrap computation) initialOptState
  where
  initialOptState :: OptSpongeState f
  initialOptState =
    { state: Vector.replicate (const_ zero)
    , phase: Absorbing { nextIndex: false_, xs: List.Nil }
    , needsFinalPermuteIfEmpty: true
    }

-- | Lift a Snarky computation into OptSpongeM.
liftSnarky
  :: forall f t m a
   . CircuitM f (KimchiConstraint f) t m
  => Snarky (KimchiConstraint f) t m a
  -> OptSpongeM f (KimchiConstraint f) t m a
liftSnarky ma = wrap $ StateT \s -> ma <#> \a -> Tuple a s

-- | Absorb a (flag, value) pair. Just accumulates; processing happens at squeeze.
optAbsorb
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => Tuple (BoolVar f) (FVar f)
  -> OptSpongeM f (KimchiConstraint f) t m Unit
optAbsorb pair = wrap $ StateT \s -> pure $ Tuple unit case s.phase of
  Absorbing { nextIndex, xs } ->
    s { phase = Absorbing { nextIndex, xs: pair List.: xs } }
  OptSqueezed _ ->
    s { phase = Absorbing { nextIndex: false_, xs: List.singleton pair } }

-- | Absorb a curve point with Boolean.true_ flag (unconditional).
optAbsorbPoint
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> OptSpongeM f (KimchiConstraint f) t m Unit
optAbsorbPoint { x, y } = do
  optAbsorb (Tuple true_ x)
  optAbsorb (Tuple true_ y)

-- | Squeeze a field element from the Opt sponge.
-- | Matches OCaml's Opt_sponge.squeeze exactly:
-- | - If Absorbing: consume all pending, return state[0], switch to Squeezed 1
-- | - If Squeezed n < rate: return state[n], switch to Squeezed (n+1)
-- | - If Squeezed n = rate: permute, return state[0], switch to Squeezed 1
optSqueeze
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => OptSpongeM f (KimchiConstraint f) t m (FVar f)
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

-- | Squeeze a challenge (lowest 128 bits, constrain_low_bits:true).
-- | Matches OCaml's Opt.challenge.
optChallenge
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => FVar f -- ^ endo constant
  -> OptSpongeM f (KimchiConstraint f) t m (SizedF 128 (FVar f))
optChallenge endo = do
  x <- optSqueeze
  liftSnarky $ lowest128BitsInternal true endo x

-- | Squeeze a scalar challenge (lowest 128 bits, constrain_low_bits:false).
-- | Matches OCaml's Opt.scalar_challenge.
optScalarChallenge
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => FVar f -- ^ endo constant
  -> OptSpongeM f (KimchiConstraint f) t m (SizedF 128 (FVar f))
optScalarChallenge endo = do
  x <- optSqueeze
  liftSnarky $ lowest128BitsInternal false endo x

-- | Convert OptSponge state to a regular Sponge for continuation (e.g., bulletproof check).
-- | Only valid when the OptSponge is in Squeezed state.
toRegularSponge
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => OptSpongeM f (KimchiConstraint f) t m (RegSponge.Sponge (FVar f))
toRegularSponge = wrap $ StateT \s -> case s.phase of
  OptSqueezed n ->
    pure $ Tuple
      { state: s.state, spongeState: RegSponge.Squeezed (unsafeFinite @3 n) }
      s
  Absorbing _ ->
    pure $ Tuple
      { state: s.state, spongeState: RegSponge.Absorbed (unsafeFinite @3 0) }
      s

-- Internal: lowest128Bits for use within OptSponge.
-- Inlined from Sponge.lowest128Bits' to avoid circular dependency.
lowest128BitsInternal
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => Boolean
  -> FVar f -- ^ endo constant
  -> FVar f -- ^ x
  -> Snarky (KimchiConstraint f) t m (SizedF 128 (FVar f))
lowest128BitsInternal constrainLowBits endo x = do
  UnChecked (Tuple lo hi) <- exists do
    F xVal <- read x
    let
      xBig = toBigInt xVal
      lo :: SizedF 128 (F f)
      lo = unsafePartial fromJust $ SizedF.fromField @128 $ fromBigInt $ mod xBig two128
      hi :: SizedF 128 (F f)
      hi = unsafePartial fromJust $ SizedF.fromField @128 $ fromBigInt $ div xBig two128
    pure $ UnChecked (Tuple lo hi)
  void $ EndoScalar.toField @8 hi endo
  when constrainLowBits $ void $ EndoScalar.toField @8 lo endo
  assertEqual_ x (add_ (SizedF.toField lo) (scale_ (fromBigInt two128) $ SizedF.toField hi))
  pure lo
  where
  two128 = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)
