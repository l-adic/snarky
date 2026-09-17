-- | A sponge whose absorptions happen only when a circuit flag is
-- | set. The rate position is a `BoolVar` rather than a compile-time
-- | index, because a conditional absorb makes it data-dependent.
module Pickles.OptSponge
  ( OptSponge
  , create
  , squeeze
  -- * Stateful sponge monad
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
import Effect.Exception.Unsafe (unsafeThrow)
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

-- | A fresh sponge with zero state.
create :: forall f. PrimeField f => OptSponge f
create =
  { state: Vector.replicate (const_ zero)
  , pos: false_
  , needsFinalPermuteIfEmpty: true
  }

-- | `state[0]` after absorbing `pending` and the final permutation.
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

-- | Add `x` to the rate slot selected by `pos`: `state[0]` when `pos`
-- | is false, `state[1]` when true.
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

-- | The Poseidon permutation of `state`, selected against `state`
-- | itself by `permute`. The permutation is emitted either way, so the
-- | constraint count does not depend on the flag.
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

-- | Absorb two flagged values, advancing the rate position by each
-- | flag. Absorptions are folded in pairs so that a pair costs exactly
-- | one permutation, whatever its flags.
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

  p' <- xor_ p b
  posAfter <- xor_ p' b'

  yMasked <- mul_ y (coerce b')

  -- `y` lands after the permutation only when `b`, `b'` and `p` hold.
  addInYAfter <- all_ [ b, b', p ]
  let addInYBefore = not_ addInYAfter

  xb <- mul_ x (coerce b)
  state1 <- addIn state p xb

  yBefore <- mul_ yMasked (coerce addInYBefore)
  state2 <- addIn state1 p' yBefore

  bOrB' <- or_ b b'
  pAndBOrB' <- and_ p bOrB'
  bAndB' <- and_ b b'
  permute <- or_ bAndB' pAndBOrB'

  state3 <- condPermute permute state2

  yAfter <- mul_ yMasked (coerce addInYAfter)
  state4 <- addIn state3 p' yAfter

  pure { state: state4, pos: posAfter }

-- | The state after absorbing every flagged value in `input`, with a
-- | final conditional permutation.
consume
  :: forall f r
   . PoseidonField f
  => PrimeField f
  => OptSponge f
  -> Array (Tuple (BoolVar f) (FVar f))
  -> Snarky f (KimchiConstraint f) r (Vector 3 (FVar f))
consume { state: initState, pos: startPos, needsFinalPermuteIfEmpty } input = do
  let
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

  { state, pos } <- foldM consumePair { state: initState, pos: startPos } pairs

  emptyInput <- not $ any_ (map fst input)

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
-- | Stateful sponge monad
-------------------------------------------------------------------------------

-- | Accumulating flagged absorptions, or squeezed with `n` rate
-- | elements already handed out.
data OptSpongePhase f
  = Absorbing { nextIndex :: BoolVar f, xs :: List (Tuple (BoolVar f) (FVar f)) }
  | OptSqueezed Int

-- | The sponge state threaded by `OptSpongeM`.
type OptSpongeState f =
  { state :: Vector 3 (FVar f)
  , phase :: OptSpongePhase f
  , needsFinalPermuteIfEmpty :: Boolean
  }

-- | A state monad over `Snarky` carrying an `OptSpongeState`.
newtype OptSpongeM f c r a = OptSpongeM (OptSpongeState f -> Snarky f c r (Tuple a (OptSpongeState f)))

derive instance Newtype (OptSpongeM f c r a) _

instance Functor (OptSpongeM f c r) where
  map f (OptSpongeM g) = OptSpongeM \s -> g s <#> \(Tuple a s') -> Tuple (f a) s'

instance Apply (OptSpongeM f c r) where
  apply = ap

instance Applicative (OptSpongeM f c r) where
  pure a = OptSpongeM \s -> pure (Tuple a s)

instance Bind (OptSpongeM f c r) where
  bind (OptSpongeM g) f = OptSpongeM \s -> g s >>= \(Tuple a s') -> unwrap (f a) s'

instance Monad (OptSpongeM f c r)

-- | Run a computation from a fresh zero-state sponge.
runOptSpongeM
  :: forall f r a
   . PrimeField f
  => OptSpongeM f (KimchiConstraint f) r a
  -> Snarky f (KimchiConstraint f) r (Tuple a (OptSpongeState f))
runOptSpongeM computation =
  unwrap computation initialOptState
  where
  initialOptState =
    { state: Vector.replicate (const_ zero)
    , phase: Absorbing { nextIndex: false_, xs: List.Nil }
    , needsFinalPermuteIfEmpty: true
    }

-- | Run a computation from the state of an existing regular sponge.
runOptSpongeFromSponge
  :: forall f r a
   . PoseidonField f
  => PrimeField f
  => RegSponge.Sponge (FVar f)
  -> OptSpongeM f (KimchiConstraint f) r a
  -> Snarky f (KimchiConstraint f) r (Tuple a (OptSpongeState f))
runOptSpongeFromSponge sponge computation = do
  initState <- ofSponge sponge
  unwrap computation initState

liftSnarky
  :: forall f r a
   . PrimeField f
  => Snarky f (KimchiConstraint f) r a
  -> OptSpongeM f (KimchiConstraint f) r a
liftSnarky ma = wrap \s -> ma <#> \a -> Tuple a s

-- | Queue a (flag, value) pair. Nothing is absorbed until the next
-- | squeeze.
optAbsorb
  :: forall f r
   . PrimeField f
  => Tuple (BoolVar f) (FVar f)
  -> OptSpongeM f (KimchiConstraint f) r Unit
optAbsorb pair = wrap \s -> pure $ Tuple unit case s.phase of
  Absorbing { nextIndex, xs } ->
    s { phase = Absorbing { nextIndex, xs: pair List.: xs } }
  OptSqueezed _ ->
    s { phase = Absorbing { nextIndex: false_, xs: List.singleton pair } }

-- | Queue both coordinates of a point unconditionally.
optAbsorbPoint
  :: forall f r
   . PrimeField f
  => AffinePoint (FVar f)
  -> OptSpongeM f (KimchiConstraint f) r Unit
optAbsorbPoint (AffinePoint { x, y }) = do
  optAbsorb (Tuple true_ x)
  optAbsorb (Tuple true_ y)

-- | The next rate element, absorbing anything queued first and
-- | permuting once the rate is exhausted.
optSqueeze
  :: forall f r
   . PoseidonField f
  => PrimeField f
  => OptSpongeM f (KimchiConstraint f) r (FVar f)
optSqueeze = wrap \s -> case s.phase of
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

-- | Absorb everything queued and return the resulting 3-element
-- | state, leaving the sponge in `OptSqueezed 0`. It emits the
-- | constraints the next squeeze would have emitted anyway, so a peek
-- | before a challenge adds nothing to the circuit.
peekPreSqueezeState
  :: forall f r
   . PoseidonField f
  => PrimeField f
  => OptSpongeM f (KimchiConstraint f) r (Vector 3 (FVar f))
peekPreSqueezeState = wrap \s -> case s.phase of
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

-- | A 128-bit challenge: the low half of a squeeze, with both halves
-- | range-checked.
optChallenge
  :: forall f r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => FVar f -- ^ endo constant
  -> OptSpongeM f (KimchiConstraint f) r (SizedF 128 (FVar f))
optChallenge endo = do
  x <- optSqueeze
  liftSnarky $ lowest128Bits' true endo x

-- | A 128-bit scalar challenge. Only the high half is range-checked; the
-- | split is asserted below the field modulus, so the result is the low
-- | half of the canonical representative, its consumers bounding it.
optScalarChallenge
  :: forall f r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => FVar f -- ^ endo constant
  -> OptSpongeM f (KimchiConstraint f) r (SizedF 128 (FVar f))
optScalarChallenge endo = do
  x <- optSqueeze
  liftSnarky $ lowest128Bits' false endo x

-- | The sponge as a regular `Sponge`, for code that continues on the
-- | unconditional interface. Only defined after a squeeze: a
-- | `RegSponge.Sponge` has no room for the queued flagged absorptions,
-- | so converting mid-absorb would drop them and silently continue on
-- | a different transcript.
toRegularSponge
  :: forall f r
   . PrimeField f
  => OptSpongeM f (KimchiConstraint f) r (RegSponge.Sponge (FVar f))
toRegularSponge = wrap \s -> case s.phase of
  OptSqueezed n ->
    pure $ Tuple
      { state: s.state, spongeState: RegSponge.Squeezed (unsafeFinite @3 n) }
      s
  Absorbing _ ->
    unsafeThrow "toRegularSponge: still absorbing; squeeze first"

-- | A regular sponge's state as an `OptSpongeState`. A sponge with
-- | both rate slots filled is permuted here, which is why that case
-- | alone clears `needsFinalPermuteIfEmpty`.
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
      permuted <- poseidon sponge.state
      pure
        { state: permuted
        , phase: Absorbing { nextIndex: false_, xs: List.Nil }
        , needsFinalPermuteIfEmpty: false
        }

