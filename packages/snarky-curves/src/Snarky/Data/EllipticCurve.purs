module Snarky.Data.EllipticCurve
  ( CurveParams
  , AffinePoint(..)
  , genAffinePoint
  , Point(..)
  , addAffine
  , fromAffine
  , genPoint
  , mkPoint
  , toAffine
  , double
  , negate_
  , WeierstrassAffinePoint(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..), fromJust, isJust)
import Data.Newtype (class Newtype)
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Simple.JSON (class ReadForeign, class WriteForeign)
import Snarky.Circuit.DSL (class AssertEqual, class CheckedType, class CircuitType, class IfThenElse, F(..), FVar, add_, assertEqGeneric, assertSquare_, const_, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, if_, isEqualGeneric, mul_, scale_, square_)
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, curveParams)
import Snarky.Curves.Class as Snarky.Curves.Class
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Type.Proxy (Proxy(..))

type CurveParams f = { a :: f, b :: f }

newtype AffinePoint f = AffinePoint { x :: f, y :: f }

derive instance Newtype (AffinePoint f) _
derive instance Generic (AffinePoint f) _
derive newtype instance Eq f => Eq (AffinePoint f)
derive newtype instance Ord f => Ord (AffinePoint f)
derive newtype instance Show f => Show (AffinePoint f)
derive newtype instance Arbitrary f => Arbitrary (AffinePoint f)
derive instance Functor AffinePoint

-- | JSON codecs delegate to the inner `{ x, y }` record (the record had
-- | these — and `Ord`/`Arbitrary` — for free before `AffinePoint` became a
-- | newtype).
derive newtype instance WriteForeign f => WriteForeign (AffinePoint f)
derive newtype instance ReadForeign f => ReadForeign (AffinePoint f)

-- | Value side is the raw field `f`; `F f` is only the internal leaf
-- | marker the generic deriving needs (reached by `coerce`).
instance CircuitType f (AffinePoint f) (AffinePoint (FVar f)) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy :: Proxy (AffinePoint (F f)))
  valueToFields a = genericValueToFields (coerce a :: AffinePoint (F f))
  fieldsToValue fs = coerce (genericFieldsToValue fs :: AffinePoint (F f))
  varToFields = genericVarToFields @(AffinePoint (F f))
  fieldsToVar = genericFieldsToVar @(AffinePoint (F f))

instance CheckedType f c (AffinePoint (FVar f)) where
  check = genericCheck

instance AssertEqual f c (AffinePoint (FVar f)) where
  assertEq = assertEqGeneric
  isEqual = isEqualGeneric

instance IfThenElse f c (AffinePoint (FVar f)) where
  if_ b (AffinePoint t) (AffinePoint e) = AffinePoint <$> if_ b t e

genAffinePoint
  :: forall g f
   . Arbitrary f
  => Arbitrary g
  => WeierstrassCurve f g
  => Proxy g
  -> Gen (AffinePoint f)
genAffinePoint _ = do
  mp <- (Snarky.Curves.Class.toAffine @f @g <$> arbitrary) `suchThat` isJust
  let { x, y } = unsafePartial $ fromJust mp
  pure (AffinePoint { x, y })

newtype Point f = Point { x :: f, y :: f, z :: f }

derive instance Generic (Point f) _

instance (PrimeField f) => Show (Point f) where
  show p = case toAffine p of
    Nothing -> show $ { x: zero @f, y: one @f, z: one @f }
    Just (AffinePoint { x, y }) -> show { x, y, z: one @f }

instance CircuitType f (Point f) (Point (FVar f)) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy :: Proxy (Point (F f)))
  valueToFields a = genericValueToFields (coerce a :: Point (F f))
  fieldsToValue fs = coerce (genericFieldsToValue fs :: Point (F f))
  varToFields = genericVarToFields @(Point (F f))
  fieldsToVar = genericFieldsToVar @(Point (F f))

instance CheckedType f c (Point (FVar f)) where
  check = genericCheck

genPoint
  :: forall f g
   . WeierstrassCurve f g
  => Arbitrary g
  => Proxy g
  -> Gen (Point (F f))
genPoint _ =
  arbitrary @g <#> \g ->
    case Snarky.Curves.Class.toAffine g of
      Just { x, y } -> Point { x: F x, y: F y, z: one }
      Nothing -> infinity_

mkPoint
  :: forall f
   . PrimeField f
  => CurveParams f
  -> { x :: f
     , y :: f
     , z :: f
     }
  -> Maybe (Point f)
mkPoint { a, b } p@{ x, y, z }
  | z == zero && x == zero && y == one = Just infinity_
  | z /= zero && y * y == x * x * x + a * x + b = Just (Point p)
  | otherwise = Nothing

toAffine :: forall f. PrimeField f => Point f -> Maybe (AffinePoint f)
toAffine (Point { x, y, z })
  | z == zero = Nothing
  | otherwise = Just (AffinePoint { x: x / z, y: y / z })

fromAffine :: forall f. PrimeField f => AffinePoint f -> Point f
fromAffine (AffinePoint { x, y }) = Point { x, y, z: one }

instance PrimeField f => Eq (Point f) where
  eq (Point p1) (Point p2)
    | (p1.z /= zero && p2.z /= zero) =
        (p1.x / p1.z) == (p2.x / p2.z) &&
          (p2.y / p2.z) == (p2.y / p2.z)
    | p1.z == zero && p2.z == zero =
        p1.x == zero && p2.x == zero
    | otherwise = false

infinity_ :: forall f. PrimeField f => Point f
infinity_ = Point { x: zero, y: one, z: zero }

double :: forall f. PrimeField f => CurveParams f -> AffinePoint (F f) -> AffinePoint (F f)
double { a } (AffinePoint { x, y }) =
  let
    lambda = (three * x * x + F a) / (two * y)
    x' = lambda * lambda - two * x
    y' = lambda * (x - x') - y
    two = F (one + one)
    three = F (one + one + one)
  in
    AffinePoint { x: x', y: y' }

negate_
  :: forall f
   . PrimeField f
  => AffinePoint f
  -> AffinePoint f
negate_ (AffinePoint { x, y }) = AffinePoint { x, y: negate y }

addAffine
  :: forall f
   . Partial
  => PrimeField f
  => AffinePoint f
  -> AffinePoint f
  -> Point f
addAffine (AffinePoint p1) (AffinePoint p2)
  | p1.x == p2.x && p1.y == negate p2.y = infinity_
  | otherwise =
      let
        { x, y } = unsafeAdd p1 p2
      in
        Point { x, y, z: one }
      where
      unsafeAdd { x: x1, y: y1 } { x: x2, y: y2 } =
        let
          lambda = (y2 - y1) / (x2 - x1)
          x3 = (lambda * lambda) - x1 - x2
          y3 = lambda * (x1 - x3) - y1
        in
          { x: x3, y: y3 }

newtype WeierstrassAffinePoint :: Type -> Type -> Type
newtype WeierstrassAffinePoint g f = WeierstrassAffinePoint { x :: f, y :: f }

derive instance Generic (WeierstrassAffinePoint g f) _

-- | NOTE: `WeierstrassAffinePoint` keeps its value side `F`-leaved (unlike
-- | `Point`/`AffinePoint`, which drop `F`). It is composed inside pickles'
-- | generic-derived `PerProofWitness`/`ProofState` *under a shared type param*
-- | that is also used for bare scalar leaves (`Vector ds f`). One shared param
-- | can't be raw `f` for the point and `F f` for the leaves at once, so WAP
-- | must match the leaves and stay `F`-leaved.
instance CircuitType f (WeierstrassAffinePoint g (F f)) (WeierstrassAffinePoint g (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(WeierstrassAffinePoint g (F f))
  fieldsToVar = genericFieldsToVar @(WeierstrassAffinePoint g (F f))

instance (PrimeField f, WeierstrassCurve f g) => CheckedType f c (WeierstrassAffinePoint g (FVar f)) where
  -- | assert_on_curve: y² = x³ + ax + b
  -- | Matches OCaml's snarky_curve.ml assert_on_curve exactly:
  -- |   x2 = square x; x3 = x2 * x; assert_square y (x3 + ax + b)
  -- | Uses square_ (not mul_ x x) to match OCaml's Square constraint (cm=1, co=-1).
  -- | x2*x is built as a compound CVar via mul_ (witnessing x3),
  -- | then assert_square embeds the rhs expression into a single constraint.
  check (WeierstrassAffinePoint { x, y }) = do
    let { a, b } = curveParams (Proxy @g)
    x2 <- square_ x
    x3 <- mul_ x2 x
    assertSquare_ y (x3 `add_` scale_ a x `add_` const_ b)