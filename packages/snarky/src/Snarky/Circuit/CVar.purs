module Snarky.Circuit.CVar
  ( Variable
  , incrementVariable
  , v0
  , CVar(..)
  , add_
  , const_
  , sub_
  , negate_
  , scale_
  , eval
  , genWithAssignments
  , reduceToAffineExpression
  , AffineExpression(..)
  , evalAffineExpression
  , EvaluationError(..)
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Bifunctor (class Bifunctor)
import Data.Foldable (class Foldable, foldM, foldl)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, frequency, sized)
import Type.Proxy (Proxy)

newtype Variable = Variable Int

derive newtype instance Eq Variable
derive newtype instance Show Variable
derive newtype instance Ord Variable
derive newtype instance Arbitrary Variable

incrementVariable :: Variable -> Variable
incrementVariable (Variable n) = Variable (n + 1)

v0 :: Variable
v0 = Variable zero

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
derive instance (Eq f, Eq i) => Eq (CVar f i)

instance (Show f, Show i) => Show (CVar f i) where
  show x = genericShow x

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

derive instance Generic (CVar f i) _

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

const_ :: forall f i. PrimeField f => f -> CVar f i
const_ = Const

negate_ :: forall f i. PrimeField f => CVar f i -> CVar f i
negate_ = scale_ (negate one)

data EvaluationError f
  = MissingVariable Variable
  | DivisionByZero { numerator :: CVar f Variable, denominator :: CVar f Variable }

derive instance Eq f => Eq (EvaluationError f)
derive instance Generic (EvaluationError f) _

instance Show f => Show (EvaluationError f) where
  show x = genericShow x

-- Given a way of looking up variable assignmetns 'i -> vars -> Maybe f', 
-- recursively evaluate the CVar
eval
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> CVar f Variable
  -> m f
eval lookup c = case c of
  Const f -> pure f
  Var i -> lookup i
  Add l r -> add <$> eval lookup l <*> eval lookup r
  ScalarMul scalar expr -> mul scalar <$> eval lookup expr

newtype AffineExpression f = AffineExpression { constant :: Maybe f, terms :: Array (Tuple Variable f) }

-- Reduce the affine circuit to the unique form \sum_{i} a_i * x_i + c,
-- which we represent as {constant: c, terms: Map [(x_i, a_i)]}
reduceToAffineExpression
  :: forall f
   . PrimeField f
  => CVar f Variable
  -> AffineExpression f
reduceToAffineExpression c =
  let
    { terms, constant } = reduce' c
  in
    AffineExpression { terms: Map.toUnfoldable terms, constant }
  where
  reduce' a = case a of
    Var i ->
      { constant: Nothing
      , terms: Map.singleton i one
      }
    Add l r ->
      { constant: constLeft + constRight
      , terms: Map.unionWith (+) termsLeft termsRight
      }
      where
      { constant: constLeft, terms: termsLeft } = reduce' l
      { constant: constRight, terms: termsRight } = reduce' r
    ScalarMul scalar e ->
      let
        { constant, terms } = reduce' e
      in
        { constant: mul scalar <$> constant, terms: map (mul scalar) terms }
    Const f -> { constant: Just f, terms: Map.empty }

-- Evaluate the reduced form
evalAffineExpression
  :: forall f m
   . PrimeField f
  => Monad m
  => AffineExpression f
  -> (Variable -> m f)
  -> m f
evalAffineExpression (AffineExpression { constant, terms }) lookup =
  foldM
    ( \acc (Tuple var coeff) ->
        lookup var <#> \val -> acc + (coeff * val)
    )
    (fromMaybe zero constant)
    terms

genWithAssignments
  :: forall f
   . PrimeField f
  => Proxy f
  -> Gen
       { cvar :: CVar f Variable
       , assignments :: Map Variable f
       }
genWithAssignments _ = do
  cvar <- arbitrary @(CVar f Variable)
  assignments <- genAssignments $ collectVariables cvar
  pure
    { cvar
    , assignments
    }
  where
  collectVariables = foldl (flip Set.insert) Set.empty
  genAssignments vars = do
    let varArray = Set.toUnfoldable vars :: Array Variable
    assignments <- traverse (\_ -> arbitrary @f) varArray
    pure $ Map.fromFoldable $ Array.zip varArray assignments
