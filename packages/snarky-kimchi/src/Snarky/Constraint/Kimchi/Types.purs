module Snarky.Constraint.Kimchi.Types
  ( GenericPlonkConstraint
  ) where

import Data.Maybe (Maybe)
import Snarky.Circuit.CVar (Variable)

-- Generic Plonk constraint representation
-- Represents: cl * vl + cr * vr + co * vo + m * vl * vr + c = 0
type GenericPlonkConstraint f =
  { cl :: f -- Left coefficient
  , vl :: Maybe Variable -- Left variable
  , cr :: f -- Right coefficient  
  , vr :: Maybe Variable -- Right variable
  , co :: f -- Output coefficient
  , vo :: Maybe Variable -- Output variable
  , m :: f -- Multiplication coefficient  
  , c :: f -- Constant term
  }