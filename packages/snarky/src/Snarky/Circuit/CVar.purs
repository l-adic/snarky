-- | Circuit variables and affine expressions.
-- |
-- | A `CVar f i` represents a circuit expression that can be reduced to affine
-- | form: `c + Σ(aᵢ × xᵢ)` where `c` is a constant and `xᵢ` are variables with
-- | coefficients `aᵢ`. This representation is fundamental to constraint systems
-- | and can be compiled to various backend formats (R1CS, Plonk gates, etc.).
-- |
-- | ```purescript
-- | -- Build expressions using smart constructors
-- | x :: CVar Field Variable
-- | x = add_ (scale_ 2 (Var v0)) (Const 5)  -- 2x₀ + 5
-- |
-- | -- Reduce to canonical affine form
-- | affine = reduceToAffineExpression x
-- | -- AffineExpression { constant: Just 5, terms: [(v0, 2)] }
-- | ```
module Snarky.Circuit.CVar
  ( Variable
  , incrementVariable
  , v0
  , getVariable
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
  , scaleAffineExpression
  , subAffineExpression
  , evalAffineExpression
  , EvaluationError(..)
  ) where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Bifunctor (class Bifunctor, rmap)
import Data.Foldable (class Foldable, foldM, foldl)
import Data.Generic.Rep (class Generic)
import Data.Map (Map, toUnfoldable)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust, fromMaybe)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, for)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, frequency, sized)
import Type.Proxy (Proxy)

derive newtype instance Eq Variable
derive newtype instance Show Variable
derive newtype instance Ord Variable
derive newtype instance Arbitrary Variable

incrementVariable :: Variable -> Variable
incrementVariable (Variable n) = Variable (n + 1)

v0 :: Variable
v0 = Variable zero

newtype Variable = Variable Int

getVariable :: Variable -> Int
getVariable (Variable i) = i

-- | A circuit variable expression over field `f` with variable type `i`.
-- |
-- | Every `CVar` can be reduced to an affine expression: `c + Σ(aᵢ × xᵢ)`.
-- | The constructors form an AST that is normalized via `reduceToAffineExpression`.
data CVar f i
  = Add (CVar f i) (CVar f i) -- ^ Sum of two expressions
  | ScalarMul f (CVar f i) -- ^ Scalar multiplication
  | Const f -- ^ Constant value
  | Var i -- ^ Variable reference

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
  _, _ -> add_ a (scale_ (negate one) b)

scale_ :: forall f i. PrimeField f => f -> CVar f i -> CVar f i
scale_ f c
  | f == zero = Const zero
  | f == one = c
  | otherwise = ScalarMul f c

const_ :: forall f i. PrimeField f => f -> CVar f i
const_ = Const

negate_ :: forall f i. PrimeField f => CVar f i -> CVar f i
negate_ = scale_ (negate one)

data EvaluationError
  = MissingVariable Variable
  | DivisionByZero { context :: String, expression :: Maybe String }
  | FailedAssertion String
  | WithContext String EvaluationError

derive instance Eq EvaluationError
derive instance Generic EvaluationError _

instance Show EvaluationError where
  show = case _ of
    WithContext ctx inner -> "[" <> ctx <> "] " <> show inner
    x -> genericShow x

-- Given a way of looking up variable assignmetns 'i -> vars -> Maybe f', 
-- recursively evaluate the CVar
eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> CVar f Variable
  -> m f
eval lookup c = case c of
  Const f -> pure f
  Var i -> lookup i
  Add l r -> add <$> eval lookup l <*> eval lookup r
  ScalarMul scalar expr -> mul scalar <$> eval lookup expr

newtype AffineExpression f = AffineExpression { constant :: Maybe f, terms :: Array (Tuple Variable f) }

derive newtype instance Show f => Show (AffineExpression f)

instance PrimeField f => Semigroup (AffineExpression f) where
  append (AffineExpression e1) (AffineExpression e2) =
    AffineExpression
      { constant:
          case e1.constant, e2.constant of
            Nothing, Nothing -> Nothing
            Just a, Nothing -> Just a
            Nothing, Just a -> Just a
            Just a, Just b -> Just $ a + b
      , terms: toUnfoldable $
          foldl
            ( \acc (Tuple var coeff) ->
                Map.insertWith add var coeff acc
            )
            Map.empty
            (e1.terms <> e2.terms)
      }

instance PrimeField f => Monoid (AffineExpression f) where
  mempty = AffineExpression { constant: Nothing, terms: mempty }

scaleAffineExpression
  :: forall f
   . PrimeField f
  => f
  -> AffineExpression f
  -> AffineExpression f
scaleAffineExpression f (AffineExpression { constant, terms }) =
  AffineExpression
    { constant: mul f <$> constant
    , terms: rmap (mul f) <$> terms
    }

subAffineExpression
  :: forall f
   . PrimeField f
  => AffineExpression f
  -> AffineExpression f
  -> AffineExpression f
subAffineExpression a b = a <> scaleAffineExpression (-one) b

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
  -> Variable
  -> Gen
       { cvar :: CVar f Variable
       , assignments :: Map Variable f
       , nextVariable :: Variable
       }
genWithAssignments _ nextVariable@(Variable i) = do
  _cvar <- arbitrary @(CVar f Variable)
  let
    collectVariables = foldl (flip Set.insert) mempty
    vars = Set.toUnfoldable $ collectVariables _cvar
  if Array.null vars then pure { cvar: _cvar, assignments: Map.empty, nextVariable }
  else do
    let
      lastVariableInt = i + Array.length vars - 1
      vars' = Variable <$> i .. lastVariableInt
      varMapping = Map.fromFoldable $ Array.zip vars vars'
      cvar = _cvar <#> \var ->
        unsafePartial $ fromJust $ Map.lookup var varMapping
    assignments <- Map.fromFoldable <$> for vars' \v ->
      Tuple v <$> arbitrary @f
    pure $ { assignments, cvar, nextVariable: Variable $ 1 + lastVariableInt }