module Snarky.Constraint.Kimchi.Types
  ( GenericPlonkConstraint
  ) where

import Snarky.Circuit.CVar (Variable)

-- Generic Plonk constraint representation
-- Represents: cl * vl + cr * vr + co * vo + m * vl * vr + c = 0
type GenericPlonkConstraint f =
  { cl :: f -- Left coefficient
  , vl :: Variable -- Left variable
  , cr :: f -- Right coefficient  
  , vr :: Variable -- Right variable
  , co :: f -- Output coefficient
  , vo :: Variable -- Output variable
  , m :: f -- Multiplication coefficient  
  , c :: f -- Constant term
  }