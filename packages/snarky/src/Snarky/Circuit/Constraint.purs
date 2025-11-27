module Snarky.Circuit.Constraint
  ( class BasicSystem
  , r1cs
  , equal
  , boolean
  , class ConstraintM
  , addConstraint'
  , module ReExports
  ) where

import Prelude

import Snarky.Circuit.CVar (CVar, Variable)
import Snarky.Circuit.Constraint.Basic (Basic(..))
import Snarky.Circuit.Constraint.Basic (Basic(..)) as ReExports

class BasicSystem f c | c -> f where
  r1cs :: { left :: CVar f Variable, right :: CVar f Variable, output :: CVar f Variable } -> c
  equal :: CVar f Variable -> CVar f Variable -> c
  boolean :: CVar f Variable -> c

instance BasicSystem f (Basic f) where
  r1cs = R1CS
  equal = Equal
  boolean = Boolean

class Monad m <= ConstraintM m c | m -> c where
  addConstraint' :: c -> m Unit