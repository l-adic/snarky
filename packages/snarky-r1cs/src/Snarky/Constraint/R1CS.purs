module Snarky.Constraint.R1CS
  ( R1CS(..)
  , genWithAssignments
  , eval
  ) where

import Prelude

import Data.Map (Map)
import Snarky.Circuit.CVar (CVar, Variable, const_, sub_)
import Snarky.Circuit.CVar as CVar
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck.Gen (Gen)
import Type.Proxy (Proxy)

data R1CS f = R1CS (CVar f Variable) (CVar f Variable) (CVar f Variable)

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
eval lookup (R1CS l r o) = ado
  left <- CVar.eval lookup l
  right <- CVar.eval lookup r
  output <- CVar.eval lookup o
  in left * right == output

instance PrimeField f => Basic.BasicSystem f (R1CS f) where
  r1cs { left, right, output } = R1CS left right output
  boolean v = R1CS v v v
  equal a b = R1CS (const_ one) (sub_ a b) (const_ zero)