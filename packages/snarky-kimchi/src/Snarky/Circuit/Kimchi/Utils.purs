module Snarky.Circuit.Kimchi.Utils
  ( verifyCircuit
  , verifyCircuitM
  , mapAccumM
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Morph (hoist)
import Control.Monad.State (StateT(..), runStateT)
import Data.Array (concatMap)
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (error)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, SolverT, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createCRS, createProverIndex, verifyProverIndex)
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (class HasEndo, endoBase)
import Test.QuickCheck.Gen (Gen, randomSampleOne)
import Test.Spec.Assertions (shouldEqual)

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

verifyCircuit
  :: forall f f' g' a b
   . HasEndo f f'
  => CircuitGateConstructor f g'
  => { gen :: Gen a
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
  :: forall f f' g' a b m
   . HasEndo f f'
  => CircuitGateConstructor f g'
  => MonadEffect m
  => { gen :: Gen a
     , solver :: SolverT f (KimchiGate f) m a b
     , s :: CircuitBuilderState (KimchiGate f) (AuxState f)
     }
  -> m Unit
verifyCircuitM { gen, solver, s } = do
  k <- liftEffect $ randomSampleOne gen
  crs <- liftEffect $ createCRS
  eRes <- runSolverT solver k
  case eRes of
    Left e -> liftEffect $ throwError $ error (show e)
    Right (Tuple _ assignments) -> do
      let
        { constraintSystem, constraints } = makeConstraintSystem @f
          { constraints: concatMap toKimchiRows s.constraints
          , publicInputs: s.publicInputs
          , unionFind: (un AuxState s.aux).wireState.unionFind
          }
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables constraints
          , publicInputs: s.publicInputs
          }
        endo = endoBase
        proverIndex = createProverIndex
          { endo
          , constraintSystem
          , crs
          }
        result = verifyProverIndex
          { proverIndex
          , witness
          , publicInputs
          }
      liftEffect $ result `shouldEqual` true