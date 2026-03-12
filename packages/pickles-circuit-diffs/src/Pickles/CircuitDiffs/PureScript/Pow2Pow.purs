module Pickles.CircuitDiffs.PureScript.Pow2Pow
  ( parsePow2PowInput
  , pow2PowCircuit
  , compilePow2Pow
  ) where

import Prelude

import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, compiledCircuit)
import Pickles.Step.Domain (pow2PowSquare)
import Pickles.Types (StepField)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

parsePow2PowInput :: Vector 1 (FVar StepField) -> FVar StepField
parsePow2PowInput = Vector.head

pow2PowCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (FVar StepField)
pow2PowCircuit x = pow2PowSquare x 16

compilePow2Pow :: CompiledCircuit StepField
compilePow2Pow = compiledCircuit @StepField $
  compilePure (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ pow2PowCircuit (parsePow2PowInput inputs))
    Kimchi.initialState
