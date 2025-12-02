module Snarky.Backend.Bulletproof.Compile
  ( compile
  , compilePure
  , makeSolver
  ) where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Snarky.Backend.Bulletproof.Gate (Gates, Witness, makeGates, makeMulGates, makeWitness)
import Snarky.Backend.Compile (SolverT)
import Snarky.Backend.Compile as Compile
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Constraint.R1CS (R1CS)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

compilePure
  :: forall f a b avar bvar
   . PrimeField f
  => CircuitType f a avar
  => CircuitType f b bvar
  => Proxy a
  -> Proxy b
  -> (forall t. CircuitM f (R1CS f) t Identity => avar -> Snarky t Identity bvar)
  -> Gates f
compilePure pa pb circuit = un Identity $ compile pa pb circuit

compile
  :: forall f m a b avar bvar
   . PrimeField f
  => CircuitType f a avar
  => CircuitType f b bvar
  => Monad m
  => Proxy a
  -> Proxy b
  -> (forall t. CircuitM f (R1CS f) t m => avar -> Snarky t m bvar)
  -> m (Gates f)
compile pa pb circuit =
  Compile.compile pa pb circuit <#> \{ constraints } ->
    makeGates constraints

makeSolver
  :: forall f a b m avar bvar
   . PrimeField f
  => CircuitType f a avar
  => CircuitType f b bvar
  => Monad m
  => Array (R1CS f)
  -> (forall t. CircuitM f (R1CS f) t m => avar -> Snarky t m bvar)
  -> SolverT f (R1CS f) m a { result :: b, witness :: Witness f }
makeSolver constraints circuit = \inputs -> do
  let
    standardSolver :: SolverT f (R1CS f) m a b
    standardSolver = Compile.makeSolver (Proxy @(R1CS f)) circuit
  Tuple result assignments <- standardSolver inputs
  witness <- makeWitness { assignments, mulGates }
  pure $ Tuple { result, witness } assignments
  where
  mulGates = makeMulGates constraints