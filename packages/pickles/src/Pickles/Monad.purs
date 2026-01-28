-- | The Pickles monad for in-circuit verification.
-- |
-- | Combines:
-- | - Sponge state (for Fiat-Shamir challenges)
-- | - Writer for accumulated bulletproof challenges
-- |
-- | This allows verification logic to absorb/squeeze from the sponge
-- | and accumulate challenges without manual threading.
module Pickles.Monad
  ( -- Types
    PicklesState
  , PicklesMessages(..)
  , PicklesM(..)
  -- Running
  , runPicklesM
  , evalPicklesM
  -- Sponge operations (re-exported from Pickles.Sponge)
  , module SpongeExports
  , absorbPoint
  , absorbMany
  , squeezeScalarChallenge
  -- Challenge accumulation
  , tellChallenge
  , tellChallenges
  -- Lifting
  , liftSnarky
  -- Initial state
  , initialPicklesState
  -- Pure version for testing
  , PurePicklesM(..)
  , runPurePicklesM
  , evalPurePicklesM
  , initialPurePicklesState
  , tellChallengePure
  ) where

import Prelude

import Control.Monad.State.Trans (StateT(..), evalStateT, runStateT)
import Control.Monad.Writer.Trans (WriterT(..), runWriterT, tell)
import Data.Foldable (class Foldable)
import Data.Identity (Identity(..))
import Data.Newtype (class Newtype, un, wrap)
import Data.Traversable (traverse_)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Pickles.ScalarChallenge (lowest128Bits)
import Pickles.Sponge (class MonadSponge, absorb, squeeze)
import Pickles.Sponge (class MonadSponge, absorb, squeeze) as SpongeExports
import Poseidon (class PoseidonField)
import RandomOracle.Sponge (Sponge, create)
import RandomOracle.Sponge as PureSponge
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (Snarky)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Kimchi.EndoScalar (ScalarChallenge(..))
import Snarky.Circuit.RandomOracle.Sponge as CircuitSponge
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

--------------------------------------------------------------------------------
-- | Types
--------------------------------------------------------------------------------

-- | State for the Pickles monad (just sponge for now, extensible)
type PicklesState f = { sponge :: Sponge f }

-- | Messages accumulated during verification
newtype PicklesMessages f = PicklesMessages { bulletproofChallenges :: Array f }

derive instance Newtype (PicklesMessages f) _

instance Semigroup (PicklesMessages f) where
  append (PicklesMessages a) (PicklesMessages b) = PicklesMessages
    { bulletproofChallenges: a.bulletproofChallenges <> b.bulletproofChallenges }

instance Monoid (PicklesMessages f) where
  mempty = PicklesMessages { bulletproofChallenges: [] }

--------------------------------------------------------------------------------
-- | In-Circuit Pickles Monad
--------------------------------------------------------------------------------

-- | The in-circuit Pickles monad.
-- | Combines WriterT (for challenge accumulation) and StateT (for sponge).
newtype PicklesM f c t m a = PicklesM
  (WriterT (PicklesMessages (FVar f)) (StateT (PicklesState (FVar f)) (Snarky c t m)) a)

derive instance Newtype (PicklesM f c t m a) _
derive newtype instance Functor (Snarky c t m) => Functor (PicklesM f c t m)
derive newtype instance Monad (Snarky c t m) => Apply (PicklesM f c t m)
derive newtype instance Monad (Snarky c t m) => Applicative (PicklesM f c t m)
derive newtype instance Monad (Snarky c t m) => Bind (PicklesM f c t m)
derive newtype instance Monad (Snarky c t m) => Monad (PicklesM f c t m)

-- | Run a PicklesM computation, returning result, messages, and final state
runPicklesM
  :: forall f c t m a
   . Functor (Snarky c t m)
  => PicklesState (FVar f)
  -> PicklesM f c t m a
  -> Snarky c t m { result :: a, messages :: PicklesMessages (FVar f), state :: PicklesState (FVar f) }
runPicklesM initialState (PicklesM computation) =
  runStateT (runWriterT computation) initialState <#> \(Tuple (Tuple result messages) state) ->
    { result, messages, state }

-- | Run a PicklesM computation, returning result and messages
evalPicklesM
  :: forall f c t m a
   . Functor (Snarky c t m)
  => Monad (Snarky c t m)
  => PicklesState (FVar f)
  -> PicklesM f c t m a
  -> Snarky c t m { result :: a, messages :: PicklesMessages (FVar f) }
evalPicklesM initialState (PicklesM computation) =
  evalStateT (runWriterT computation) initialState <#> \(Tuple result messages) ->
    { result, messages }

-- | Lift a Snarky computation into PicklesM
liftSnarky
  :: forall f c t m a
   . Functor (Snarky c t m)
  => Snarky c t m a
  -> PicklesM f c t m a
liftSnarky ma = wrap $ WriterT $ StateT \s -> ma <#> \a -> Tuple (Tuple a mempty) s

-- | Initial state for PicklesM
initialPicklesState :: forall f. PrimeField f => PicklesState (FVar f)
initialPicklesState = { sponge: create $ Vector.generate (const $ const_ zero) }

--------------------------------------------------------------------------------
-- | Sponge Operations
--------------------------------------------------------------------------------

-- | MonadSponge instance for PicklesM
instance
  ( PoseidonField f
  , CircuitM f (KimchiConstraint f) t m
  ) =>
  MonadSponge (FVar f) (PicklesM f (KimchiConstraint f) t m) where
  absorb x = wrap $ WriterT $ StateT \s -> do
    newSponge <- CircuitSponge.absorb x s.sponge
    pure $ Tuple (Tuple unit mempty) (s { sponge = newSponge })

  squeeze = wrap $ WriterT $ StateT \s -> do
    { result, sponge: newSponge } <- CircuitSponge.squeeze s.sponge
    pure $ Tuple (Tuple result mempty) (s { sponge = newSponge })

-- | Absorb a curve point
absorbPoint :: forall f m. MonadSponge f m => AffinePoint f -> m Unit
absorbPoint { x, y } = do
  absorb x
  absorb y

-- | Absorb multiple values
absorbMany :: forall f m g. MonadSponge f m => Foldable g => g f -> m Unit
absorbMany = traverse_ absorb

-- | Squeeze a scalar challenge (128 bits)
squeezeScalarChallenge
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => PicklesM f (KimchiConstraint f) t m (ScalarChallenge (FVar f))
squeezeScalarChallenge = do
  x <- squeeze
  truncated <- liftSnarky $ lowest128Bits x
  pure $ ScalarChallenge truncated

--------------------------------------------------------------------------------
-- | Challenge Accumulation
--------------------------------------------------------------------------------

-- | Record a bulletproof challenge
tellChallenge
  :: forall f c t m
   . Monad (Snarky c t m)
  => FVar f
  -> PicklesM f c t m Unit
tellChallenge c = wrap $ tell $ PicklesMessages { bulletproofChallenges: [c] }

-- | Record multiple bulletproof challenges
tellChallenges
  :: forall f c t m
   . Monad (Snarky c t m)
  => Array (FVar f)
  -> PicklesM f c t m Unit
tellChallenges cs = wrap $ tell $ PicklesMessages { bulletproofChallenges: cs }

--------------------------------------------------------------------------------
-- | Pure Version for Testing
--------------------------------------------------------------------------------

-- | Pure Pickles monad for testing/reference implementations
newtype PurePicklesM f a = PurePicklesM
  (WriterT (PicklesMessages f) (StateT (PicklesState f) Identity) a)

derive instance Newtype (PurePicklesM f a) _
derive newtype instance Functor (PurePicklesM f)
derive newtype instance Apply (PurePicklesM f)
derive newtype instance Applicative (PurePicklesM f)
derive newtype instance Bind (PurePicklesM f)
derive newtype instance Monad (PurePicklesM f)

-- | Run pure Pickles computation
runPurePicklesM
  :: forall f a
   . PicklesState f
  -> PurePicklesM f a
  -> { result :: a, messages :: PicklesMessages f, state :: PicklesState f }
runPurePicklesM initialState (PurePicklesM computation) =
  let Tuple (Tuple result messages) state = un Identity $ runStateT (runWriterT computation) initialState
  in { result, messages, state }

-- | Evaluate pure Pickles computation
evalPurePicklesM
  :: forall f a
   . PicklesState f
  -> PurePicklesM f a
  -> { result :: a, messages :: PicklesMessages f }
evalPurePicklesM initialState (PurePicklesM computation) =
  let Tuple result messages = un Identity $ evalStateT (runWriterT computation) initialState
  in { result, messages }

-- | Initial state for pure version
initialPurePicklesState :: forall f. Semiring f => PicklesState f
initialPurePicklesState = { sponge: create $ Vector.generate (const zero) }

-- | MonadSponge instance for pure version
instance PoseidonField f => MonadSponge f (PurePicklesM f) where
  absorb x = wrap $ WriterT $ StateT \s ->
    let newSponge = PureSponge.absorb x s.sponge
    in Identity $ Tuple (Tuple unit mempty) (s { sponge = newSponge })

  squeeze = wrap $ WriterT $ StateT \s ->
    let { result, sponge: newSponge } = PureSponge.squeeze s.sponge
    in Identity $ Tuple (Tuple result mempty) (s { sponge = newSponge })

-- | Record a challenge (pure version)
tellChallengePure :: forall f. f -> PurePicklesM f Unit
tellChallengePure c = wrap $ tell $ PicklesMessages { bulletproofChallenges: [c] }
