-- | The Poseidon sponge as a monad, so a transcript can be written
-- | once and run either in-circuit (`SpongeM`) or on plain field
-- | elements (`PureSpongeM`).
module Pickles.Sponge
  ( -- * Interface
    class MonadSponge
  , absorb
  , squeeze
  -- * Helpers
  , absorbPoint
  , absorbMany
  , squeezeScalarChallenge
  , squeezeScalar
  , squeezeScalar'
  , squeezeScalarChallengePure
  -- * In-circuit sponge monad
  , SpongeM(..)
  , evalSpongeM
  , liftSnarky
  , labelM
  , getSponge
  , putSponge
  -- * Pure sponge monad
  , PureSpongeM(..)
  , runPureSpongeM
  , evalPureSpongeM
  , getSpongeState
  -- * Initial state and restore
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
import Snarky.Circuit.Kimchi.RangeCheck (lowest128Bits', lowest128BitsPure)
import Snarky.Circuit.RandomOracle.Sponge as CircuitSponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint(..))

--------------------------------------------------------------------------------
-- | Interface
--------------------------------------------------------------------------------

-- | Monads carrying a Fiat-Shamir sponge over `f`.
class Monad m <= MonadSponge f m | m -> f where
  absorb :: f -> m Unit
  squeeze :: m f

--------------------------------------------------------------------------------
-- | Helpers
--------------------------------------------------------------------------------

-- | Absorb a point as `x` then `y`.
absorbPoint :: forall f m. MonadSponge f m => AffinePoint f -> m Unit
absorbPoint (AffinePoint { x, y }) = do
  absorb x
  absorb y

absorbMany :: forall f m t. MonadSponge f m => Foldable t => t f -> m Unit
absorbMany = traverse_ absorb

--------------------------------------------------------------------------------
-- | In-circuit sponge monad
--------------------------------------------------------------------------------

-- | A state monad over `Snarky` carrying the sponge.
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

evalSpongeM
  :: forall f c r a
   . Sponge (FVar f)
  -> SpongeM f c r a
  -> Snarky f c r a
evalSpongeM initialState computation = map fst (unwrap computation initialState)

liftSnarky
  :: forall f c r a
   . Snarky f c r a
  -> SpongeM f c r a
liftSnarky ma = SpongeM \s -> ma <#> \a -> Tuple a s

-- | `label`, lifted through the sponge state.
labelM
  :: forall f c r a
   . String
  -> SpongeM f c r a
  -> SpongeM f c r a
labelM s m = SpongeM \state -> label s (unwrap m state)

-- | The current sponge, to be restored later with `putSponge`.
getSponge
  :: forall f c r
   . SpongeM f c r (Sponge (FVar f))
getSponge = SpongeM \s -> pure (Tuple s s)

putSponge
  :: forall f c r
   . Sponge (FVar f)
  -> SpongeM f c r Unit
putSponge s' = SpongeM \_ -> pure (Tuple unit s')

instance
  ( PoseidonField f
  , PrimeField f
  ) =>
  MonadSponge (FVar f) (SpongeM f (KimchiConstraint f) r) where
  absorb x = SpongeM \sponge ->
    CircuitSponge.absorb x sponge <#> \newSponge -> Tuple unit newSponge

  squeeze = SpongeM \sponge ->
    CircuitSponge.squeeze sponge <#> \{ result, sponge: newSponge } -> Tuple result newSponge

-- | A 128-bit challenge: the low half of a squeeze, with both halves
-- | range-checked.
squeezeScalarChallenge
  :: forall f r cr
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => { endo :: FVar f | r }
  -> SpongeM f (KimchiConstraint f) cr (SizedF 128 (FVar f))
squeezeScalarChallenge = squeezeScalar' true

-- | A 128-bit scalar challenge. Only the high half is range-checked,
-- | so the result is pinned only by `x = lo + hi * 2^128`.
squeezeScalar
  :: forall f r cr
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => { endo :: FVar f | r }
  -> SpongeM f (KimchiConstraint f) cr (SizedF 128 (FVar f))
squeezeScalar = squeezeScalar' false

-- | The shared body: squeeze, keep the low 128 bits, and range-check
-- | them only when `constrainLowBits` is set.
squeezeScalar'
  :: forall f r cr
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => Boolean
  -> { endo :: FVar f | r }
  -> SpongeM f (KimchiConstraint f) cr (SizedF 128 (FVar f))
squeezeScalar' constrainLowBits params = do
  x <- squeeze
  liftSnarky $ lowest128Bits' constrainLowBits params.endo x

--------------------------------------------------------------------------------
-- | Pure sponge monad
--------------------------------------------------------------------------------

-- | A pure state monad over the sponge, for transcripts run outside a
-- | circuit.
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

runPureSpongeM
  :: forall f a
   . Sponge f
  -> PureSpongeM f a
  -> Tuple a (Sponge f)
runPureSpongeM initialState computation = unwrap computation initialState

evalPureSpongeM
  :: forall f a
   . Sponge f
  -> PureSpongeM f a
  -> a
evalPureSpongeM initialState computation = fst (unwrap computation initialState)

getSpongeState :: forall f. PureSpongeM f (Sponge f)
getSpongeState = PureSpongeM \s -> Tuple s s

instance PoseidonField f => MonadSponge f (PureSpongeM f) where
  absorb x = PureSpongeM \sponge -> Tuple unit (PureSponge.absorb x sponge)

  squeeze = PureSpongeM \sponge ->
    let
      { result, sponge: newSponge } = PureSponge.squeeze sponge
    in
      Tuple result newSponge

-- | The low 128 bits of a squeeze, with no range check: the
-- | out-of-circuit counterpart of `squeezeScalarChallenge`.
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
-- | Initial state and restore
--------------------------------------------------------------------------------

-- | A sponge with zero state.
initialSponge :: forall f. Semiring f => Sponge f
initialSponge = create $ Vector.generate (const zero)

-- | A sponge with zero state, as circuit constants.
initialSpongeCircuit :: forall f. PrimeField f => Sponge (FVar f)
initialSpongeCircuit = create $ Vector.generate (const $ const_ zero)

-- | A circuit sponge whose state is constant, for resuming from a
-- | sponge state computed outside the circuit.
spongeFromConstants
  :: forall f
   . PrimeField f
  => { state :: Vector 3 f, spongeState :: PureSponge.SpongeState }
  -> Sponge (FVar f)
spongeFromConstants { state, spongeState } =
  { state: map const_ state
  , spongeState
  }