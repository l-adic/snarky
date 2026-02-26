-- | Monadic sponge interface for Pickles.
-- |
-- | This module provides a StateT-based wrapper around the Poseidon sponge,
-- | eliminating manual state threading when doing multiple absorbs/squeezes.
-- |
-- | Two versions are provided:
-- | - `SpongeM`: In-circuit version using Snarky
-- | - `PureSpongeM`: Pure version for testing/reference implementations
module Pickles.Sponge
  ( -- Typeclass
    class MonadSponge
  , absorb
  , squeeze
  -- Helpers
  , absorbPoint
  , absorbMany
  , squeezeScalarChallenge
  , squeezeScalarChallengePure
  , lowest128Bits
  , lowest128BitsPure
  -- In-circuit sponge monad
  , SpongeM(..)
  , runSpongeM
  , evalSpongeM
  , liftSnarky
  , getSponge
  , putSponge
  -- Pure sponge monad
  , PureSpongeM(..)
  , runPureSpongeM
  , evalPureSpongeM
  , getSpongeState
  , putSpongeState
  -- Initial state / restore
  , initialSponge
  , initialSpongeCircuit
  , spongeFromConstants
  ) where

import Prelude

import Control.Monad.State.Trans (StateT(..), evalStateT, get, put, runStateT)
import Data.Foldable (class Foldable)
import Data.Identity (Identity(..))
import Data.Maybe (fromJust)
import Data.Newtype (class Newtype, un, unwrap, wrap)
import Data.Traversable (traverse_)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import RandomOracle.Sponge (Sponge, create)
import RandomOracle.Sponge as PureSponge
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, SizedF, Snarky, UnChecked(..), add_, assertEqual_, const_, exists, fromField, read, scale_)
import Snarky.Circuit.DSL as SizedF
import Snarky.Circuit.Kimchi.EndoScalar as EndoScalar
import Snarky.Circuit.RandomOracle.Sponge as CircuitSponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint)

--------------------------------------------------------------------------------
-- | MonadSponge Typeclass
--------------------------------------------------------------------------------

-- | A typeclass for monads that can interact with a Fiat-Shamir sponge.
-- | This decouples the logic from the specific implementation (circuit vs pure).
class Monad m <= MonadSponge f m | m -> f where
  -- | Absorb a field element into the sponge
  absorb :: f -> m Unit
  -- | Squeeze a field element from the sponge
  squeeze :: m f

--------------------------------------------------------------------------------
-- | Helper functions
--------------------------------------------------------------------------------

-- | Absorb a curve point (x and y coordinates)
absorbPoint :: forall f m. MonadSponge f m => AffinePoint f -> m Unit
absorbPoint { x, y } = do
  absorb x
  absorb y

-- | Absorb multiple field elements
absorbMany :: forall f m t. MonadSponge f m => Foldable t => t f -> m Unit
absorbMany = traverse_ absorb

--------------------------------------------------------------------------------
-- | In-Circuit Sponge Monad: SpongeM
--------------------------------------------------------------------------------

-- | The in-circuit sponge monad.
-- | A newtype wrapper around StateT to manage sponge state within Snarky.
newtype SpongeM f c t m a = SpongeM (StateT (Sponge (FVar f)) (Snarky c t m) a)

derive instance Newtype (SpongeM f c t m a) _
derive newtype instance Functor (Snarky c t m) => Functor (SpongeM f c t m)
derive newtype instance (Monad (Snarky c t m)) => Apply (SpongeM f c t m)
derive newtype instance (Monad (Snarky c t m)) => Applicative (SpongeM f c t m)
derive newtype instance (Monad (Snarky c t m)) => Bind (SpongeM f c t m)
derive newtype instance (Monad (Snarky c t m)) => Monad (SpongeM f c t m)

-- | Run a SpongeM computation, returning both the result and final sponge state
runSpongeM
  :: forall f c t m a
   . Functor (Snarky c t m)
  => Sponge (FVar f)
  -> SpongeM f c t m a
  -> Snarky c t m (Tuple a (Sponge (FVar f)))
runSpongeM initialState computation = runStateT (unwrap computation) initialState

-- | Run a SpongeM computation, returning only the result
evalSpongeM
  :: forall f c t m a
   . Functor (Snarky c t m)
  => Monad (Snarky c t m)
  => Sponge (FVar f)
  -> SpongeM f c t m a
  -> Snarky c t m a
evalSpongeM initialState computation = evalStateT (unwrap computation) initialState

-- | Lift a Snarky computation into SpongeM
liftSnarky
  :: forall f c t m a
   . Functor (Snarky c t m)
  => Snarky c t m a
  -> SpongeM f c t m a
liftSnarky ma = wrap $ StateT \s -> ma <#> \a -> Tuple a s

-- | Get the current sponge state (for checkpointing)
getSponge
  :: forall f c t m
   . Monad (Snarky c t m)
  => SpongeM f c t m (Sponge (FVar f))
getSponge = wrap get

-- | Set the sponge state (for restoring from checkpoint)
putSponge
  :: forall f c t m
   . Monad (Snarky c t m)
  => Sponge (FVar f)
  -> SpongeM f c t m Unit
putSponge = wrap <<< put

-- | MonadSponge instance for the in-circuit sponge monad
instance
  ( PoseidonField f
  , CircuitM f (KimchiConstraint f) t m
  ) =>
  MonadSponge (FVar f) (SpongeM f (KimchiConstraint f) t m) where
  absorb x = wrap do
    sponge <- get
    newSponge <- lift $ CircuitSponge.absorb x sponge
    put newSponge
    where
    lift ma = StateT \s -> ma <#> \a -> Tuple a s

  squeeze = wrap do
    sponge <- get
    { result, sponge: newSponge } <- lift $ CircuitSponge.squeeze sponge
    put newSponge
    pure result
    where
    lift ma = StateT \s -> ma <#> \a -> Tuple a s

-- | Squeeze a scalar challenge (128 bits) from the sponge.
-- | This is the in-circuit version that returns a SizedF 128.
-- | Uses EndoScalar.toField as a 128-bit range check (matching OCaml's
-- | squeeze_challenge which calls lowest_128_bits with constrain_low_bits:true).
-- |
-- | Takes any record containing `endo :: FVar f` (the EndoScalar constant for
-- | challenge expansion, i.e. Wrap_inner_curve.scalar for Step, Step_inner_curve.scalar for Wrap).
squeezeScalarChallenge
  :: forall f t m r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => { endo :: FVar f | r }
  -> SpongeM f (KimchiConstraint f) t m (SizedF 128 (FVar f))
squeezeScalarChallenge params = do
  x <- squeeze
  liftSnarky $ lowest128Bits params.endo x

--------------------------------------------------------------------------------
-- | Pure Sponge Monad: PureSpongeM
--------------------------------------------------------------------------------

-- | Pure sponge monad for testing and reference implementations.
-- | A newtype wrapper around State.
newtype PureSpongeM f a = PureSpongeM (StateT (Sponge f) Identity a)

derive instance Newtype (PureSpongeM f a) _
derive newtype instance Functor (PureSpongeM f)
derive newtype instance Apply (PureSpongeM f)
derive newtype instance Applicative (PureSpongeM f)
derive newtype instance Bind (PureSpongeM f)
derive newtype instance Monad (PureSpongeM f)

-- | Run a pure sponge computation, returning both result and final state
runPureSpongeM
  :: forall f a
   . Sponge f
  -> PureSpongeM f a
  -> Tuple a (Sponge f)
runPureSpongeM initialState computation =
  un Identity $ runStateT (unwrap computation) initialState

-- | Run a pure sponge computation, returning only the result
evalPureSpongeM
  :: forall f a
   . Sponge f
  -> PureSpongeM f a
  -> a
evalPureSpongeM initialState computation =
  un Identity $ evalStateT (unwrap computation) initialState

-- | Get the current sponge state (pure version)
getSpongeState :: forall f. PureSpongeM f (Sponge f)
getSpongeState = wrap get

-- | Set the sponge state (pure version)
putSpongeState :: forall f. Sponge f -> PureSpongeM f Unit
putSpongeState = wrap <<< put

-- | MonadSponge instance for the pure sponge monad
instance PoseidonField f => MonadSponge f (PureSpongeM f) where
  absorb x = wrap do
    sponge <- get
    let newSponge = PureSponge.absorb x sponge
    put newSponge

  squeeze = wrap do
    sponge <- get
    let { result, sponge: newSponge } = PureSponge.squeeze sponge
    put newSponge
    pure result

-- | Squeeze a scalar challenge from the pure sponge (128 bits)
squeezeScalarChallengePure
  :: forall f
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => PureSpongeM f (SizedF 128 f)
squeezeScalarChallengePure = do
  x <- squeeze
  pure $ lowest128BitsPure x

--------------------------------------------------------------------------------
-- | lowest128Bits (circuit and pure)
--------------------------------------------------------------------------------

-- | Extract the lowest 128 bits of a field element, with range checking
-- | via EndoScalar gate decomposition.
-- |
-- | Matches OCaml's `lowest_128_bits ~constrain_low_bits:true`:
-- | 1. Witness lo, hi such that x = lo + hi * 2^128
-- | 2. Range-check hi via EndoScalar.toField (discarding result)
-- | 3. Range-check lo via EndoScalar.toField (discarding result)
-- | 4. Assert x = lo + hi * 2^128
-- | 5. Return lo
-- |
-- | The endo parameter is a raw FVar f (the EndoScalar constant for the circuit field).
lowest128Bits
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => FVar f -- ^ endo constant
  -> FVar f -- ^ x (sponge squeeze output)
  -> Snarky (KimchiConstraint f) t m (SizedF 128 (FVar f))
lowest128Bits endo x = do
  -- Witness lo (first) and hi (second), matching OCaml's Typ.(field * field)
  UnChecked (Tuple lo hi) <- exists do
    F xVal <- read x
    let
      xBig = toBigInt xVal

      lo :: SizedF 128 (F f)
      lo =
        unsafePartial fromJust
          $ SizedF.fromField @128
          $ fromBigInt
          $
            mod xBig two128

      hi :: SizedF 128 (F f)
      hi =
        unsafePartial fromJust
          $ SizedF.fromField @128
          $ fromBigInt
          $
            div xBig two128
    pure $ UnChecked (Tuple lo hi)
  -- Range check hi via EndoScalar (discard result) — hi first, matching OCaml
  void $ EndoScalar.toField hi endo
  -- Range check lo via EndoScalar (discard result)
  void $ EndoScalar.toField lo endo
  -- Assert x = lo + hi * 2^128
  assertEqual_ x (add_ (SizedF.toField lo) (scale_ (fromBigInt two128) $ SizedF.toField hi))
  pure lo
  where
  two128 = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)

-- | Pure version: extract lowest 128 bits of a field element.
lowest128BitsPure
  :: forall f
   . PrimeField f
  => FieldSizeInBits f 255
  => f
  -> SizedF 128 f
lowest128BitsPure x =
  let
    xBig = toBigInt x
    two128 = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)
    lo = fromBigInt (mod xBig two128)
  in
    unsafePartial fromJust $ fromField @128 lo

--------------------------------------------------------------------------------
-- | Initial States
--------------------------------------------------------------------------------

-- | Create an initial sponge with zero state (pure version)
initialSponge :: forall f. Semiring f => Sponge f
initialSponge = create $ Vector.generate (const zero)

-- | Create an initial sponge with zero state (circuit version)
initialSpongeCircuit :: forall f. PrimeField f => Sponge (FVar f)
initialSpongeCircuit = create $ Vector.generate (const $ const_ zero)

-- | Create a circuit sponge from constant field values and sponge state.
-- | Used to restore sponge state from a checkpoint (e.g., from Rust FFI).
spongeFromConstants
  :: forall f
   . PrimeField f
  => { state :: Vector 3 f, spongeState :: PureSponge.SpongeState }
  -> Sponge (FVar f)
spongeFromConstants { state, spongeState } =
  { state: map const_ state
  , spongeState
  }