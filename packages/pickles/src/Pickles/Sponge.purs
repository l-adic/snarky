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
  , squeezeScalar
  , squeezeScalarChallengePure
  -- In-circuit sponge monad
  , SpongeM(..)
  , evalSpongeM
  , liftSnarky
  , labelM
  , getSponge
  , putSponge
  , runSpongeM
  -- Pure sponge monad
  , PureSpongeM(..)
  , runPureSpongeM
  , evalPureSpongeM
  , getSpongeState
  -- Initial state / restore
  , initialSponge
  , initialSpongeCircuit
  , spongeFromConstants
  ) where

import Prelude

import Data.Foldable (class Foldable)
import Data.Newtype (class Newtype, unwrap)
import Data.Traversable (traverse_)
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector)
import Data.Vector as Vector
import Poseidon (class PoseidonField)
import RandomOracle.Sponge (Sponge, create)
import RandomOracle.Sponge as PureSponge
import Snarky.Circuit.DSL (FVar, SizedF, Snarky, const_, label)
import Snarky.Circuit.Kimchi.RangeCheck (lowest128Bits, lowest128Bits', lowest128BitsPure)
import Snarky.Circuit.RandomOracle.Sponge as CircuitSponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint(..))

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
absorbPoint (AffinePoint { x, y }) = do
  absorb x
  absorb y

-- | Absorb multiple field elements
absorbMany :: forall f m t. MonadSponge f m => Foldable t => t f -> m Unit
absorbMany = traverse_ absorb

--------------------------------------------------------------------------------
-- | In-Circuit Sponge Monad: SpongeM
--------------------------------------------------------------------------------

-- | The in-circuit sponge monad: a hand-rolled state monad over `Snarky`
-- | (replaces `StateT` from `transformers`).
newtype SpongeM f c r a = SpongeM (Sponge (FVar f) -> Snarky f c r (Tuple a (Sponge (FVar f))))

derive instance Newtype (SpongeM f c r a) _

instance Functor (SpongeM f c r) where
  map f (SpongeM g) = SpongeM \s -> g s <#> \(Tuple a s') -> Tuple (f a) s'

instance Apply (SpongeM f c r) where
  apply = ap

instance Applicative (SpongeM f c r) where
  pure a = SpongeM \s -> pure (Tuple a s)

instance Bind (SpongeM f c r) where
  bind (SpongeM g) f = SpongeM \s -> g s >>= \(Tuple a s') -> unwrap (f a) s'

instance Monad (SpongeM f c r)

-- | Run a SpongeM computation, returning result and final sponge
runSpongeM
  :: forall f c r a
   . Sponge (FVar f)
  -> SpongeM f c r a
  -> Snarky f c r (Tuple a (Sponge (FVar f)))
runSpongeM initialState computation = unwrap computation initialState

-- | Run a SpongeM computation, returning only the result
evalSpongeM
  :: forall f c r a
   . Sponge (FVar f)
  -> SpongeM f c r a
  -> Snarky f c r a
evalSpongeM initialState computation = map fst (unwrap computation initialState)

-- | Lift a Snarky computation into SpongeM
liftSnarky
  :: forall f c r a
   . Snarky f c r a
  -> SpongeM f c r a
liftSnarky ma = SpongeM \s -> ma <#> \a -> Tuple a s

-- | Label a SpongeM computation (lifts Snarky label through the state)
labelM
  :: forall f c r a
   . String
  -> SpongeM f c r a
  -> SpongeM f c r a
labelM s m = SpongeM \state -> label s (unwrap m state)

-- | Get the current sponge state (for checkpointing)
getSponge
  :: forall f c r
   . SpongeM f c r (Sponge (FVar f))
getSponge = SpongeM \s -> pure (Tuple s s)

-- | Set the sponge state (for restoring from checkpoint)
putSponge
  :: forall f c r
   . Sponge (FVar f)
  -> SpongeM f c r Unit
putSponge s' = SpongeM \_ -> pure (Tuple unit s')

-- | MonadSponge instance for the in-circuit sponge monad
instance
  ( PoseidonField f
  , PrimeField f
  ) =>
  MonadSponge (FVar f) (SpongeM f (KimchiConstraint f) r) where
  absorb x = SpongeM \sponge ->
    CircuitSponge.absorb x sponge <#> \newSponge -> Tuple unit newSponge

  squeeze = SpongeM \sponge ->
    CircuitSponge.squeeze sponge <#> \{ result, sponge: newSponge } -> Tuple result newSponge

-- | Squeeze a scalar challenge (128 bits) from the sponge.
-- | This is the in-circuit version that returns a SizedF 128.
-- | Uses EndoScalar.toField as a 128-bit range check (matching OCaml's
-- | squeeze_challenge which calls lowest_128_bits with constrain_low_bits:true).
-- |
-- | Takes any record containing `endo :: FVar f` (the EndoScalar constant for
-- | challenge expansion, i.e. Wrap_inner_curve.scalar for Step, Step_inner_curve.scalar for Wrap).
squeezeScalarChallenge
  :: forall f r cr
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => PrimeField f
  => { endo :: FVar f | r }
  -> SpongeM f (KimchiConstraint f) cr (SizedF 128 (FVar f))
squeezeScalarChallenge params = do
  x <- squeeze
  liftSnarky $ lowest128Bits params.endo x

-- | Squeeze a scalar challenge with constrain_low_bits:false.
-- |
-- | Matches OCaml's `squeeze_scalar` which calls `lowest_128_bits ~constrain_low_bits:false`.
-- | Only range-checks hi (not lo). Used in Wrap FOP for xi.
squeezeScalar
  :: forall f r cr
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => { endo :: FVar f | r }
  -> SpongeM f (KimchiConstraint f) cr (SizedF 128 (FVar f))
squeezeScalar params = do
  x <- squeeze
  liftSnarky $ lowest128Bits' false params.endo x

--------------------------------------------------------------------------------
-- | Pure Sponge Monad: PureSpongeM
--------------------------------------------------------------------------------

-- | Pure sponge monad for testing and reference implementations.
-- | A hand-rolled pure state monad over the sponge.
newtype PureSpongeM f a = PureSpongeM (Sponge f -> Tuple a (Sponge f))

derive instance Newtype (PureSpongeM f a) _

instance Functor (PureSpongeM f) where
  map f (PureSpongeM g) = PureSpongeM \s -> let Tuple a s' = g s in Tuple (f a) s'

instance Apply (PureSpongeM f) where
  apply = ap

instance Applicative (PureSpongeM f) where
  pure a = PureSpongeM \s -> Tuple a s

instance Bind (PureSpongeM f) where
  bind (PureSpongeM g) f = PureSpongeM \s -> let Tuple a s' = g s in unwrap (f a) s'

instance Monad (PureSpongeM f)

-- | Run a pure sponge computation, returning both result and final state
runPureSpongeM
  :: forall f a
   . Sponge f
  -> PureSpongeM f a
  -> Tuple a (Sponge f)
runPureSpongeM initialState computation = unwrap computation initialState

-- | Run a pure sponge computation, returning only the result
evalPureSpongeM
  :: forall f a
   . Sponge f
  -> PureSpongeM f a
  -> a
evalPureSpongeM initialState computation = fst (unwrap computation initialState)

-- | Get the current sponge state (pure version)
getSpongeState :: forall f. PureSpongeM f (Sponge f)
getSpongeState = PureSpongeM \s -> Tuple s s

-- | MonadSponge instance for the pure sponge monad
instance PoseidonField f => MonadSponge f (PureSpongeM f) where
  absorb x = PureSpongeM \sponge -> Tuple unit (PureSponge.absorb x sponge)

  squeeze = PureSpongeM \sponge ->
    let
      { result, sponge: newSponge } = PureSponge.squeeze sponge
    in
      Tuple result newSponge

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