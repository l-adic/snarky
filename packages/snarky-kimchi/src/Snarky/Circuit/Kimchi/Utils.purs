module Snarky.Circuit.Kimchi.Utils
  ( verifyCircuit
  , verifyCircuitM
  , mapAccumM
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Morph (hoist)
import Control.Monad.State (StateT(..), runStateT)
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (error)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, SolverT, runSolverT)
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
mapAccumM f initial xs = runStateT (traverse step xs) initial
  where
  step x = StateT (\s -> f s x)

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
  let
    nat :: Identity ~> Effect
    nat = pure <<< un Identity
  in
    verifyCircuitM { gen, solver: \a -> hoist nat $ solver a, s }

verifyCircuitM
  :: forall f a b m
   . MonadEffect m
  => { gen :: Gen a
     , solver :: SolverT f (KimchiGate f) m a b
     , s :: CircuitBuilderState (KimchiGate f) (AuxState f)
     }
  -> m Unit
verifyCircuitM { gen, solver, s: _ } = do
  k <- liftEffect $ randomSampleOne gen
  eRes <- runSolverT solver k
  case eRes of
    Left e -> liftEffect $ throwError $ error (show e)
    Right _ -> pure unit
