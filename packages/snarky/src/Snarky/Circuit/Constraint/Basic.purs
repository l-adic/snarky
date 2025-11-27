module Snarky.Circuit.Constraint.Basic
  ( Basic(..)
  , eval
  ) where

import Prelude

import Control.Apply (lift2)
import Data.Generic.Rep (class Generic)
import Snarky.Circuit.CVar (CVar, Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Curves.Class (class PrimeField)

data Basic f
  = R1CS
      { left :: CVar f Variable
      , right :: CVar f Variable
      , output :: CVar f Variable
      }
  | Equal (CVar f Variable) (CVar f Variable)
  | Boolean (CVar f Variable)

derive instance Functor Basic
derive instance Generic (Basic f) _

eval
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> Basic f
  -> m Boolean
eval lookup gate = do
  case gate of
    R1CS { left, right, output } -> do
      lval <- CVar.eval lookup left
      rval <- CVar.eval lookup right
      oval <- CVar.eval lookup output
      pure $ lval * rval == oval
    Equal a b ->
      lift2 eq (CVar.eval lookup a) (CVar.eval lookup b)
    Boolean i -> do
      CVar.eval lookup i <#> \inp ->
        inp == zero || inp == one