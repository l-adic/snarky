module Snarky.Circuit.Constraint
  ( R1CS(..)
  , evalR1CSConstraint
  , R1CSCircuit(..)
  , evalR1CSCircuit
  , class R1CSSystem
  , r1cs
  , boolean
  ) where

import Prelude

import Data.Array (foldM)
import Data.Generic.Rep (class Generic)
import Data.Monoid.Conj (Conj(..))
import Data.Newtype (un)
import Snarky.Circuit.CVar (CVar, Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Curves.Class (class PrimeField)

data R1CS f
  = R1CS
      { left :: CVar f Variable
      , right :: CVar f Variable
      , output :: CVar f Variable
      }
  | Boolean (CVar f Variable)

derive instance Functor R1CS
derive instance Generic (R1CS f) _

evalR1CSConstraint
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> R1CS f
  -> m Boolean
evalR1CSConstraint lookup gate = do
  case gate of
    R1CS { left, right, output } -> do
      lval <- CVar.eval lookup left
      rval <- CVar.eval lookup right
      oval <- CVar.eval lookup output
      pure $ lval * rval == oval
    Boolean i -> do
      inp <- CVar.eval lookup i
      pure $ inp == zero || inp == one

newtype R1CSCircuit f = R1CSCircuit (Array (R1CS f))

evalR1CSCircuit
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> R1CSCircuit f
  -> m Boolean
evalR1CSCircuit lookup (R1CSCircuit gates) = un Conj <$>
  foldM
    ( \acc c ->
        evalR1CSConstraint lookup c <#> \cVal ->
          acc <> Conj cVal
    )
    mempty
    gates

class R1CSSystem f c | c -> f where
  r1cs :: { left :: CVar f Variable, right :: CVar f Variable, output :: CVar f Variable } -> c
  boolean :: CVar f Variable -> c

instance R1CSSystem f (R1CS f) where
  r1cs = R1CS
  boolean = Boolean
