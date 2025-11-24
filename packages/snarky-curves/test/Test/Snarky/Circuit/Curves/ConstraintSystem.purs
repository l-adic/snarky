module Test.Snarky.Circuit.Curves.ConstraintSystem where

import Prelude

import Snarky.Circuit.Constraint (R1CS(..), evalR1CSConstraint)
import Snarky.Circuit.Constraint.Class (class R1CSSystem)
import Snarky.Circuit.Curves.Constraint (class ECSystem, ECConstraint(..), evalECConstraint)
import Snarky.Circuit.Types (FVar, Variable)
import Snarky.Curves.Class (class PrimeField)

data TestConstraintSystem f
  = CSR1CS (R1CS f Variable)
  | CSECS (ECConstraint f Variable)

instance R1CSSystem (FVar f) (TestConstraintSystem f) where
  r1cs = CSR1CS <<< R1CS
  boolean = CSR1CS <<< Boolean

instance ECSystem (FVar f) (TestConstraintSystem f) where
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