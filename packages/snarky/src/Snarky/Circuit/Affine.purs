module Snarky.Circuit.Affine where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Bifunctor (class Bifunctor)
import Data.Foldable (class Foldable, sum)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (frequency, sized)

-- An AffineCircuit is an expression that can be reduced to
-- c + \sum a_i * x_i. This is the most generic formulation.
data AffineCircuit f i
  = Add (AffineCircuit f i) (AffineCircuit f i)
  | ScalarMul f (AffineCircuit f i)
  | Const f
  | Var i

derive instance Functor (AffineCircuit f)

derive instance Foldable (AffineCircuit f)

derive instance Traversable (AffineCircuit f)

derive instance Bifunctor AffineCircuit

instance (Arbitrary f, Arbitrary i) => Arbitrary (AffineCircuit f i) where
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

-- Given a way of looking up variable assignmetns 'i -> vars -> Maybe f', 
-- recursively evaluate the AffineCircuit
eval
  :: forall f i vars
   . Field f
  => Show i
  => (i -> vars -> Maybe f)
  -> vars
  -> AffineCircuit f i
  -> f
eval lookup vars c = case c of
  Const f -> f
  Var i -> case lookup i vars of
    Nothing -> unsafeCrashWith $ "missing variable assignment: " <> show i
    Just v -> v
  Add l r -> eval lookup vars l + eval lookup vars r
  ScalarMul scalar expr -> eval lookup vars expr * scalar

newtype AffineExpression f i = AffineExpression { constant :: f, terms :: Map i f }

-- Reduce the affine circuit to the unique form \sum_{i} a_i * x_i + c,
-- which we represent as {constant: c, terms: Map [(x_i, a_i)]}
reduce
  :: forall f i
   . Field f
  => Show i
  => Ord i
  => AffineCircuit f i
  -> AffineExpression f i
reduce c = case c of
  Var i -> AffineExpression
    { constant: zero
    , terms: Map.singleton i one
    }
  Add l r -> AffineExpression
    { constant: constLeft + constRight
    , terms: Map.unionWith add termsLeft termsRight
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
  :: forall f i vars
   . Field f
  => Ord i
  => AffineExpression f i
  -> (i -> vars -> Maybe f)
  -> vars
  -> f
evalAffineExpression (AffineExpression { constant, terms }) lookup vars =
  let
    linearPart = Map.mapMaybeWithKey (\ix coeff -> mul coeff <$> lookup ix vars) terms
  in
    constant + sum linearPart
