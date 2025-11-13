module Snarky.Circuit.Constraint
  ( R1CS(..)
  , R1CSCircuit(..)
  , evalR1CSCircuit
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Data.Array (foldM)
import Data.Bifunctor (class Bifunctor)
import Data.Monoid.Conj (Conj(..))
import Data.Newtype (un)
import Data.Traversable (class Foldable, class Traversable)
import Snarky.Circuit.CVar (CVar, EvaluationError)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint.Class (class R1CSSystem)
import Snarky.Curves.Class (class PrimeField)

data R1CS f i
  = R1CS
      { left :: CVar f i
      , right :: CVar f i
      , output :: CVar f i
      }
  | Boolean (CVar f i)

derive instance Functor (R1CS f)
derive instance Foldable (R1CS f)
derive instance Traversable (R1CS f)
derive instance Bifunctor R1CS

evalConstraint
  :: forall f i m
   . PrimeField f
  => MonadThrow (EvaluationError i) m
  => (i -> m f)
  -> R1CS f i
  -> m Boolean
evalConstraint lookup gate =
  case gate of
    R1CS { left, right, output } -> do
      lval <- CVar.eval lookup left
      rval <- CVar.eval lookup right
      oval <- CVar.eval lookup output
      pure $ lval * rval == oval
    Boolean i -> do
      inp <- CVar.eval lookup i
      pure $ inp == zero || inp == one

newtype R1CSCircuit f i = R1CSCircuit (Array (R1CS f i))

evalR1CSCircuit
  :: forall i f m
   . PrimeField f
  => MonadThrow (EvaluationError i) m
  => (i -> m f)
  -> R1CSCircuit f i
  -> m Boolean
evalR1CSCircuit lookup (R1CSCircuit gates) = un Conj <$>
  foldM
    ( \acc c ->
        evalConstraint lookup c <#> \cVal ->
          acc <> Conj cVal
    )
    mempty
    gates

instance R1CSSystem (CVar f i) (R1CS f i) where
  r1cs = R1CS
  boolean = Boolean