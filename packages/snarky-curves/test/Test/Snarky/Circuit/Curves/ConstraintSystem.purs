module Test.Snarky.Circuit.Curves.ConstraintSystem where

import Prelude

import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.Constraint (class BasicSystem)
import Snarky.Circuit.Constraint.Basic (Basic(..), evalBasicConstraint)
import Snarky.Circuit.Curves.Constraint (class ECSystem, ECConstraint(..), evalECConstraint)
import Snarky.Curves.Class (class PrimeField)

data TestConstraintSystem f
  = CSBasic (Basic f)
  | CSECS (ECConstraint f)

instance BasicSystem f (TestConstraintSystem f) where
  r1cs = CSBasic <<< R1CS
  boolean = CSBasic <<< Boolean
  equal a b = CSBasic $ Equal a b

instance ECSystem f (TestConstraintSystem f) where
  ecAddComplete = CSECS <<< ECAddComplete

evalTestConstraint
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> TestConstraintSystem f
  -> m Boolean
evalTestConstraint lookup c =
  case c of
    CSBasic c' -> evalBasicConstraint lookup c'
    CSECS c' -> evalECConstraint lookup c'