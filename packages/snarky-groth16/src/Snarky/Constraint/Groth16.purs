module Snarky.Constraint.Groth16
  ( R1CS(..)
  , genWithAssignments
  , eval
  ) where

import Prelude

import Data.Map (Map)
import Snarky.Backend.Builder (class CompileCircuit, class Finalizer, CircuitBuilderT, appendConstraint)
import Snarky.Backend.Prover (class SolveCircuit, ProverT)
import Snarky.Circuit.CVar (CVar)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class ConstraintM, Variable, const_)
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck.Gen (Gen)
import Type.Proxy (Proxy)

newtype R1CS f = R1CS { left :: (CVar f Variable), right :: (CVar f Variable), output :: (CVar f Variable) }

derive newtype instance Show f => Show (R1CS f)

instance ConstraintM (ProverT f) (R1CS f) where
  addConstraint' _ = pure unit

instance ConstraintM (CircuitBuilderT (R1CS f) r) (R1CS f) where
  addConstraint' = appendConstraint

instance Finalizer (R1CS f) r where
  finalize = identity

instance PrimeField f => CompileCircuit f (R1CS f) (R1CS f) r

instance PrimeField f => SolveCircuit f (R1CS f)

genWithAssignments
  :: forall f
   . PrimeField f
  => Proxy f
  -> Gen
       { r1cs :: R1CS f
       , assignments :: Map Variable f
       }
genWithAssignments pf =
  Basic.genWithAssignments pf <#> \{ basic, assignments } ->
    { r1cs: Basic.fromBasic basic
    , assignments
    }

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> R1CS f
  -> m Boolean
eval lookup (R1CS c) = ado
  left <- CVar.eval lookup c.left
  right <- CVar.eval lookup c.right
  output <- CVar.eval lookup c.output
  in left * right == output

instance PrimeField f => Basic.BasicSystem f (R1CS f) where
  r1cs { left, right, output } = R1CS { left, right, output }
  square a c = R1CS { left: a, right: a, output: c }
  boolean v = R1CS { left: v, right: v, output: v }
  -- NB: DO NOT CHANGE THIS TO 1 * (a - b) = zero
  equal a b = R1CS { left: a, right: const_ one, output: b }