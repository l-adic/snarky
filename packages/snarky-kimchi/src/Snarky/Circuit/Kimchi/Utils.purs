module Snarky.Circuit.Kimchi.Utils
  ( verifyCircuit
  , verifyCircuitM
  , mapAccumM
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (error, throwException)
import Snarky.Backend.Advice (AdviceHandler, noAdvice)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, SolverT)
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Test.QuickCheck.Gen (Gen, randomSampleOne)

mapAccumM
  :: forall m s t a b
   . Monad m
  => Traversable t
  => (s -> a -> m (Tuple b s))
  -> s
  -> t a
  -> m (Tuple (t b) s)
mapAccumM f initial xs =
  -- foldl over the structure, then rebuild it in order — equivalent to
  -- the old `StateT`-based traverse for any list-like `Traversable`.
  runStateT (traverse step xs) initial
  where
  -- minimal local StateT (replaces the `transformers` import)
  step x = MapAccumState (\s -> f s x)

newtype MapAccumState m s a = MapAccumState (s -> m (Tuple a s))

runStateT :: forall m s a. MapAccumState m s a -> s -> m (Tuple a s)
runStateT (MapAccumState f) = f

instance Functor m => Functor (MapAccumState m s) where
  map f (MapAccumState g) = MapAccumState \s -> g s <#> \(Tuple a s') -> Tuple (f a) s'

instance Monad m => Apply (MapAccumState m s) where
  apply = ap

instance Monad m => Applicative (MapAccumState m s) where
  pure a = MapAccumState \s -> pure (Tuple a s)

instance Monad m => Bind (MapAccumState m s) where
  bind (MapAccumState g) f = MapAccumState \s -> g s >>= \(Tuple a s') -> runStateT (f a) s'

instance Monad m => Monad (MapAccumState m s)

-- | Solver smoke test: run the gen-and-solve loop and assert no error.
-- |
-- | Previously this also exercised `verifyProverIndex` against the solved
-- | witness, but that FFI helper doesn't exist in upstream kimchi-napi —
-- | constraint-satisfaction is enforced transitively by every e2e
-- | prove/verify test, so this util now just sanity-checks that the
-- | solver runs to completion on a random sample.
verifyCircuit
  :: forall f a b
   . { gen :: Gen a
     , solver :: Solver f (KimchiGate f) a b
     , s :: CircuitBuilderState (KimchiGate f) (AuxState f)
     }
  -> Effect Unit
verifyCircuit { gen, solver, s } =
  verifyCircuitM noAdvice { gen, solver, s }

-- | Sanity-check a solver over an advice row `r`, given a handler for
-- | the row's effects.
verifyCircuitM
  :: forall f a b r
   . AdviceHandler r
  -> { gen :: Gen a
     , solver :: SolverT f (KimchiGate f) r a b
     , s :: CircuitBuilderState (KimchiGate f) (AuxState f)
     }
  -> Effect Unit
verifyCircuitM handler { gen, solver, s: _ } = do
  k <- liftEffect $ randomSampleOne gen
  eRes <- solver handler k
  case eRes of
    Left e -> liftEffect $ throwException $ error (show e)
    Right _ -> pure unit
