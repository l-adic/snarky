module Snarky.Circuit.CVar
  ( CVar(..)
  , add_
  , sub_
  , scale_
  , eval
  , reduce
  , AffineExpression
  , evalAffineExpression
  , EvaluationError(..)
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Data.Array.NonEmpty as NEA
import Data.Bifunctor (class Bifunctor)
import Data.Foldable (class Foldable)
import Data.FoldableWithIndex (foldWithIndexM)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable)
import Data.Tuple (Tuple(..))
import Snarky.Curves.Types (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (frequency, sized)

-- An CVar is an expression that can be reduced to
-- c + \sum a_i * x_i. This is the most generic formulation.
data CVar f i
  = Add (CVar f i) (CVar f i)
  | ScalarMul f (CVar f i)
  | Const f
  | Var i

derive instance Functor (CVar f)

derive instance Foldable (CVar f)

derive instance Traversable (CVar f)

derive instance Bifunctor CVar

instance (Arbitrary f, Arbitrary i) => Arbitrary (CVar f i) where
  arbitrary = sized go
    where
    go 0 = frequency $ NEA.cons'
      (Tuple 1.0 (Const <$> arbitrary))
      [ Tuple 1.0 (Var <$> arbitrary) ]
    go n = frequency $ NEA.cons'
      (Tuple 1.0 (Const <$> arbitrary))
      [ Tuple 1.0 (Var <$> arbitrary)
      , Tuple 4.0 (Add <$> subCircuit <*> subCircuit)
      , Tuple 4.0 (ScalarMul <$> arbitrary <*> subCircuit)
      ]
      where
      subCircuit = go (n `div` 2)

instance PrimeField f => Semigroup (CVar f i) where
  append a b = case a, b of
    Const f, Const f' -> Const (f + f')
    Const f, c | f == zero -> c
    c, Const f | f == zero -> c
    _, _ -> Add a b

instance PrimeField f => Monoid (CVar f i) where
  mempty = Const zero

add_ :: forall f i. PrimeField f => CVar f i -> CVar f i -> CVar f i
add_ a b = case a, b of
  Const f, Const f' -> Const (f + f')
  _, _ -> Add a b

sub_ :: forall f i. PrimeField f => CVar f i -> CVar f i -> CVar f i
sub_ a b = case a, b of
  Const f, Const f' -> Const (f - f')
  _, _ -> a <> (scale_ (negate one) b)

scale_ :: forall f i. PrimeField f => f -> CVar f i -> CVar f i
scale_ f c
  | f == zero = Const zero
  | f == one = c
  | otherwise = ScalarMul f c

data EvaluationError i = MissingVariable i

derive instance Eq i => Eq (EvaluationError i)
derive instance Generic (EvaluationError i) _

instance Show i => Show (EvaluationError i) where
  show = genericShow

-- Given a way of looking up variable assignmetns 'i -> vars -> Maybe f', 
-- recursively evaluate the CVar
eval
  :: forall f i m
   . MonadThrow (EvaluationError i) m
  => PrimeField f
  => (i -> m f)
  -> CVar f i
  -> m f
eval lookup c = case c of
  Const f -> pure f
  Var i -> lookup i
  Add l r -> add <$> eval lookup l <*> eval lookup r
  ScalarMul scalar expr -> mul scalar <$> eval lookup expr

newtype AffineExpression f i = AffineExpression { constant :: f, terms :: Map i f }

-- Reduce the affine circuit to the unique form \sum_{i} a_i * x_i + c,
-- which we represent as {constant: c, terms: Map [(x_i, a_i)]}
reduce
  :: forall f i
   . PrimeField f
  => Show i
  => Ord i
  => CVar f i
  -> AffineExpression f i
reduce c = case c of
  Var i -> AffineExpression
    { constant: zero
    , terms: Map.singleton i one
    }
  Add l r -> AffineExpression
    { constant: constLeft + constRight
    , terms: Map.unionWith (+) termsLeft termsRight
    }
    where
    AffineExpression { constant: constLeft, terms: termsLeft } = reduce l
    AffineExpression { constant: constRight, terms: termsRight } = reduce r
  ScalarMul scalar e ->
    let
      AffineExpression { constant, terms } = reduce e
    in
      AffineExpression { constant: scalar * constant, terms: map (mul scalar) terms }
  Const f -> AffineExpression { constant: f, terms: Map.empty }

-- Evaluate the reduced form
evalAffineExpression
  :: forall f i m
   . PrimeField f
  => Ord i
  => MonadThrow (EvaluationError i) m
  => AffineExpression f i
  -> (i -> m f)
  -> m f
evalAffineExpression (AffineExpression { constant, terms }) lookup =
  foldWithIndexM
    ( \var acc coeff ->
        lookup var >>= \val -> pure $ acc + (coeff * val)
    )
    constant
    terms
