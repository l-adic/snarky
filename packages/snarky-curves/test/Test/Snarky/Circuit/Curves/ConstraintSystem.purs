module Test.Snarky.Circuit.Curves.ConstraintSystem where

import Prelude

import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.Constraint (class R1CSSystem, R1CS(..), evalR1CSConstraint)
import Snarky.Circuit.Curves.Constraint (class ECSystem, ECConstraint(..), evalECConstraint)
import Snarky.Curves.Class (class PrimeField)

data TestConstraintSystem f
  = CSR1CS (R1CS f)
  | CSECS (ECConstraint f)

instance R1CSSystem f (TestConstraintSystem f) where
  r1cs = CSR1CS <<< R1CS
  boolean = CSR1CS <<< Boolean

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
    CSR1CS c' -> evalR1CSConstraint lookup c'
    CSECS c' -> evalECConstraint lookup c'