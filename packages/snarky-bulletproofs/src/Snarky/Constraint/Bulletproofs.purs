module Snarky.Constraint.Bulletproofs
  ( R1CS(..)
  , genWithAssignments
  , eval
  ) where

import Prelude

import Data.Map (Map)
import Snarky.Backend.Builder (CircuitBuilderT, appendConstraint)
import Snarky.Backend.Prover (ProverT)
import Snarky.Circuit.CVar (CVar, Variable, const_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck.Gen (Gen)
import Type.Proxy (Proxy)

newtype R1CS f = R1CS { left :: (CVar f Variable), right :: (CVar f Variable), output :: (CVar f Variable) }

derive newtype instance Show f => Show (R1CS f)

instance ConstraintM (ProverT f) (R1CS f) where
  addConstraint' _ = pure unit

instance ConstraintM (CircuitBuilderT (R1CS f)) (R1CS f) where
  addConstraint' = appendConstraint

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
  boolean v = R1CS { left: v, right: v, output: v }
  -- NB: DO NOT CHANGE THIS TO 1 * (a - b) = zero
  equal a b = R1CS { left: a, right: const_ one, output: b }