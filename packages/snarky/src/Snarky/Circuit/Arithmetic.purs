module Snarky.Circuit.Constraint where

import Prelude

import Data.Array (foldl)
import Data.Bifunctor (class Bifunctor)
import Data.Foldable (class Foldable)
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.Affine (AffineCircuit)
import Snarky.Circuit.Affine as AffineCircuit

data Gate f i
  = Mul
      { left :: AffineCircuit f i
      , right :: AffineCircuit f i
      , output :: i
      }
  | Equal
      { input :: i
      , magic :: i
      , output :: i
      }
  | Boolean i

derive instance Functor (Gate f)
derive instance Foldable (Gate f)
derive instance Traversable (Gate f)
derive instance Bifunctor Gate

-- | Evaluate a single gate
eval
  :: forall f i vars
   . Field f
  => Eq f
  => Show f
  => Show i
  => (i -> vars -> Maybe f)
  -> (i -> f -> vars -> vars)
  -> vars
  -> Gate f i
  -> vars
eval lookup update vars gate =
  case gate of
    Mul { left, right, output } ->
      let
        lval = AffineCircuit.eval lookup vars left
        rval = AffineCircuit.eval lookup vars right
        res = lval * rval
      in
        update output res vars
    Equal { input, magic, output } ->
      case lookup input vars of
        Nothing ->
          unsafeCrashWith ("evalGate: missing var " <> show input)
        Just inp ->
          let
            res = if inp == zero then zero else one
            mid = if inp == zero then zero else recip inp
          in
            update output res $
              update magic mid vars
    Boolean i ->
      case lookup i vars of
        Nothing ->
          unsafeCrashWith ("evalGate: missing var " <> show i)
        Just inp ->
          if not (inp == zero || inp == one) then unsafeCrashWith $ "evalGate: boolean input is not 0 or 1: " <> show inp
          else vars

newtype ArithCircuit f i = ArithCircuit (Array (Gate f i))

-- | Evaluate an arithmetic circuit on a given environment containing
-- the inputs. Outputs the entire environment (outputs, intermediate
-- values and inputs).
evalArithCircuit
  :: forall i f vars
   . Field f
  => Eq f
  => Show f
  => Show i
  => (i -> vars -> Maybe f)
  -> (i -> f -> vars -> vars)
  -> ArithCircuit f i
  -> vars
  -> vars
evalArithCircuit _lookupVar _updateVar (ArithCircuit gates) vars =
  foldl (eval _lookupVar _updateVar) vars gates