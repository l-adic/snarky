module Snarky.Circuit.Constraint
  ( Basic(..)
  , evalBasicConstraint
  , BasicCircuit(..)
  , evalBasicCircuit
  , class BasicSystem
  , r1cs
  , boolean
  ) where

import Prelude

import Control.Apply (lift2)
import Data.Array (foldM)
import Data.Generic.Rep (class Generic)
import Data.Monoid.Conj (Conj(..))
import Data.Newtype (un)
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

evalBasicConstraint
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> Basic f
  -> m Boolean
evalBasicConstraint lookup gate = do
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

newtype BasicCircuit f = BasicCircuit (Array (Basic f))

evalBasicCircuit
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> BasicCircuit f
  -> m Boolean
evalBasicCircuit lookup (BasicCircuit gates) = un Conj <$>
  foldM
    ( \acc c ->
        evalBasicConstraint lookup c <#> \cVal ->
          acc <> Conj cVal
    )
    mempty
    gates

class BasicSystem f c | c -> f where
  r1cs :: { left :: CVar f Variable, right :: CVar f Variable, output :: CVar f Variable } -> c
  boolean :: CVar f Variable -> c

instance BasicSystem f (Basic f) where
  r1cs = R1CS
  boolean = Boolean
