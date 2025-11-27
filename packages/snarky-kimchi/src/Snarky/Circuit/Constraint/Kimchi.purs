module Snarky.Circuit.Constraint.Kimchi where

import Prelude

import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.Constraint (class BasicSystem)
import Snarky.Circuit.Constraint.Basic (Basic(..))
import Snarky.Circuit.Constraint.Basic as Basic
import Snarky.Circuit.Constraint.Kimchi.AddComplete (AddComplete)
import Snarky.Circuit.Constraint.Kimchi.AddComplete as AddComplete
import Snarky.Circuit.Constraint.Kimchi.GenericPlonk (GenericPlonkConstraint)
import Snarky.Circuit.Constraint.Kimchi.GenericPlonk as GenericPlonk
import Snarky.Curves.Class (class PrimeField)

data KimchiConstraint f
  = KimchiBasic (Basic f)
  | KimchiPlonk (GenericPlonkConstraint f)
  | KimchiAddComplete (AddComplete f)

eval
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> KimchiConstraint f
  -> m Boolean
eval lookup = case _ of
  KimchiBasic c -> Basic.eval lookup c
  KimchiPlonk c -> GenericPlonk.eval lookup c
  KimchiAddComplete c -> AddComplete.eval lookup c

instance BasicSystem f (KimchiConstraint f) where
  r1cs = KimchiBasic <<< R1CS
  equal a b = KimchiBasic $ Equal a b
  boolean = KimchiBasic <<< Boolean