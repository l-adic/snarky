module Snarky.Circuit.Constraint.R1CS where

import Prelude

import Snarky.Circuit.CVar (CVar, Variable, const_, sub_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint (class BasicSystem)
import Snarky.Curves.Class (class PrimeField)

data R1CS f = R1CS (CVar f Variable) (CVar f Variable) (CVar f Variable)

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

instance PrimeField f => BasicSystem f (R1CS f) where
  r1cs { left, right, output } = R1CS left right output
  boolean v = R1CS v v v
  equal a b = R1CS (const_ one) (sub_ a b) (const_ zero)