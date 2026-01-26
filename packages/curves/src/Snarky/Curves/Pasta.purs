module Snarky.Curves.Pasta
  ( -- Pallas exports
    PallasScalarField
  , PallasBaseField
  , PallasG
  , -- Vesta exports
    VestaScalarField
  , VestaBaseField
  , VestaG
  , -- Hex serialization (for test vectors)
    vestaScalarFieldFromHexLe
  , vestaScalarFieldToHexLe
  , -- Group map FFI (for testing against Rust implementation)
    pallasGroupMap
  , vestaGroupMap
  ) where

import Prelude

import Data.Array as Array
import Data.Function.Uncurried (Fn3, runFn3)
import Data.Maybe (Maybe(..), fromJust)
import JS.BigInt (BigInt)
import Partial.Unsafe (unsafePartial)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasBW19, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve, toBigInt)
import Test.QuickCheck (class Arbitrary, arbitrary)

-- ============================================================================
-- PALLAS CURVE DEFINITIONS
-- ============================================================================

-- Pallas Scalar Field
foreign import data PallasScalarField :: Type
foreign import _pallasZero :: Unit -> PallasScalarField
foreign import _pallasOne :: Unit -> PallasScalarField
foreign import _pallasAdd :: PallasScalarField -> PallasScalarField -> PallasScalarField
foreign import _pallasMul :: PallasScalarField -> PallasScalarField -> PallasScalarField
foreign import _pallasSub :: PallasScalarField -> PallasScalarField -> PallasScalarField
foreign import _pallasDiv :: PallasScalarField -> PallasScalarField -> PallasScalarField
foreign import _pallasInvert :: PallasScalarField -> PallasScalarField
foreign import _pallasEq :: PallasScalarField -> PallasScalarField -> Boolean
foreign import _pallasToString :: PallasScalarField -> String
foreign import _pallasRand :: Int -> PallasScalarField
foreign import _pallasFromBigInt :: BigInt -> PallasScalarField
foreign import _pallasToBigInt :: PallasScalarField -> BigInt
foreign import _pallasModulus :: Unit -> BigInt
foreign import _pallasPow :: PallasScalarField -> BigInt -> PallasScalarField
foreign import _pallasEndoBase :: Unit -> VestaScalarField
foreign import _pallasEndoScalar :: Unit -> PallasScalarField
foreign import _pallasIsSquare :: PallasScalarField -> Boolean
foreign import _pallasSqrt :: forall a. (a -> Maybe a) -> Maybe a -> PallasScalarField -> Maybe PallasScalarField

instance Semiring PallasScalarField where
  add = _pallasAdd
  mul = _pallasMul
  zero = _pallasZero unit
  one = _pallasOne unit

instance Ring PallasScalarField where
  sub = _pallasSub

instance CommutativeRing PallasScalarField

instance EuclideanRing PallasScalarField where
  degree _ = 1
  div = _pallasDiv
  mod _ _ = zero

instance DivisionRing PallasScalarField where
  recip = _pallasInvert

instance Eq PallasScalarField where
  eq = _pallasEq

instance Show PallasScalarField where
  show = _pallasToString

instance Arbitrary PallasScalarField where
  arbitrary = _pallasRand <$> arbitrary

instance PrimeField PallasScalarField where
  fromBigInt = _pallasFromBigInt
  toBigInt = _pallasToBigInt
  modulus = _pallasModulus unit
  pow = _pallasPow

instance FieldSizeInBits PallasScalarField 255

instance HasSqrt PallasScalarField where
  sqrt = _pallasSqrt Just Nothing
  isSquare = _pallasIsSquare

-- Pallas Base Field (= Vesta Scalar Field via cross-wiring)
type PallasBaseField = VestaScalarField

-- Pallas Group
foreign import data PallasG :: Type
foreign import _pallasGroupAdd :: PallasG -> PallasG -> PallasG
foreign import _pallasGroupIdentity :: Unit -> PallasG
foreign import _pallasGroupGenerator :: Unit -> PallasG
foreign import _pallasGroupRand :: Int -> PallasG
foreign import _pallasGroupEq :: PallasG -> PallasG -> Boolean
foreign import _pallasGroupToString :: PallasG -> String
foreign import _pallasGroupNeg :: PallasG -> PallasG
foreign import _pallasGroupScale :: PallasScalarField -> PallasG -> PallasG
foreign import _pallasWeierstrassA :: Unit -> VestaScalarField
foreign import _pallasWeierstrassB :: Unit -> VestaScalarField

instance Semigroup PallasG where
  append = _pallasGroupAdd

instance Monoid PallasG where
  mempty = _pallasGroupIdentity unit

instance Eq PallasG where
  eq = _pallasGroupEq

instance Show PallasG where
  show = _pallasGroupToString

instance Arbitrary PallasG where
  arbitrary = _pallasGroupRand <$> arbitrary

instance FrModule PallasScalarField PallasG where
  scalarMul = _pallasGroupScale
  inverse = _pallasGroupNeg

instance WeierstrassCurve PallasBaseField PallasG where
  curveParams _ =
    { a: _pallasWeierstrassA unit
    , b: _pallasWeierstrassB unit
    }
  toAffine x = f <$> runFn3 _pallasToAffine Just Nothing x
    where
    f as =
      { x: unsafePartial $ fromJust $ as Array.!! 0
      , y: unsafePartial $ fromJust $ as Array.!! 1
      }
  fromAffine = _pallasFromAffine
  generator = _pallasGroupGenerator unit

foreign import _pallasToAffine
  :: forall a
   . Fn3
       (a -> Maybe a)
       (Maybe a)
       PallasG
       (Maybe a)

-- BW19 parameters for Pallas (returns array of base field elements)
foreign import _pallasBW19Params :: Unit -> Array VestaScalarField

instance HasBW19 PallasBaseField PallasG where
  bw19Params _ =
    let
      arr = _pallasBW19Params unit
    in
      { u: unsafePartial $ fromJust $ arr Array.!! 0
      , fu: unsafePartial $ fromJust $ arr Array.!! 1
      , sqrtNeg3U2MinusUOver2: unsafePartial $ fromJust $ arr Array.!! 2
      , sqrtNeg3U2: unsafePartial $ fromJust $ arr Array.!! 3
      , inv3U2: unsafePartial $ fromJust $ arr Array.!! 4
      }

-- ============================================================================
-- VESTA CURVE DEFINITIONS
-- ============================================================================

-- Vesta Scalar Field
foreign import data VestaScalarField :: Type
foreign import _vestaScalarFieldZero :: Unit -> VestaScalarField
foreign import _vestaScalarFieldOne :: Unit -> VestaScalarField
foreign import _vestaScalarFieldAdd :: VestaScalarField -> VestaScalarField -> VestaScalarField
foreign import _vestaScalarFieldMul :: VestaScalarField -> VestaScalarField -> VestaScalarField
foreign import _vestaScalarFieldSub :: VestaScalarField -> VestaScalarField -> VestaScalarField
foreign import _vestaScalarFieldDiv :: VestaScalarField -> VestaScalarField -> VestaScalarField
foreign import _vestaScalarFieldInvert :: VestaScalarField -> VestaScalarField
foreign import _vestaScalarFieldEq :: VestaScalarField -> VestaScalarField -> Boolean
foreign import _vestaScalarFieldToString :: VestaScalarField -> String
foreign import _vestaScalarFieldRand :: Int -> VestaScalarField
foreign import _vestaScalarFieldFromBigInt :: BigInt -> VestaScalarField
foreign import _vestaScalarFieldToBigInt :: VestaScalarField -> BigInt
foreign import _vestaScalarFieldPow :: VestaScalarField -> BigInt -> VestaScalarField
foreign import _vestaScalarFieldModulus :: Unit -> BigInt
foreign import _vestaScalarFieldFromHexLe :: String -> VestaScalarField
foreign import _vestaScalarFieldToHexLe :: VestaScalarField -> String
foreign import _vestaEndoBase :: Unit -> PallasScalarField
foreign import _vestaEndoScalar :: Unit -> VestaScalarField
foreign import _vestaScalarFieldIsSquare :: VestaScalarField -> Boolean
foreign import _vestaScalarFieldSqrt :: forall a. (a -> Maybe a) -> Maybe a -> VestaScalarField -> Maybe VestaScalarField

instance Semiring VestaScalarField where
  add = _vestaScalarFieldAdd
  mul = _vestaScalarFieldMul
  zero = _vestaScalarFieldZero unit
  one = _vestaScalarFieldOne unit

instance Ring VestaScalarField where
  sub = _vestaScalarFieldSub

instance CommutativeRing VestaScalarField

instance EuclideanRing VestaScalarField where
  degree _ = 1
  div = _vestaScalarFieldDiv
  mod _ _ = zero

instance DivisionRing VestaScalarField where
  recip = _vestaScalarFieldInvert

instance Eq VestaScalarField where
  eq = _vestaScalarFieldEq

instance Show VestaScalarField where
  show = _vestaScalarFieldToString

instance Arbitrary VestaScalarField where
  arbitrary = _vestaScalarFieldRand <$> arbitrary

instance PrimeField VestaScalarField where
  fromBigInt = _vestaScalarFieldFromBigInt
  toBigInt = _vestaScalarFieldToBigInt
  pow = _vestaScalarFieldPow
  modulus = _vestaScalarFieldModulus unit

instance FieldSizeInBits VestaScalarField 255

instance HasSqrt VestaScalarField where
  sqrt = _vestaScalarFieldSqrt Just Nothing
  isSquare = _vestaScalarFieldIsSquare

-- | Parse a VestaScalarField (= PallasBaseField) from little-endian hex string
vestaScalarFieldFromHexLe :: String -> VestaScalarField
vestaScalarFieldFromHexLe = _vestaScalarFieldFromHexLe

-- | Serialize a VestaScalarField (= PallasBaseField) to little-endian hex string
vestaScalarFieldToHexLe :: VestaScalarField -> String
vestaScalarFieldToHexLe = _vestaScalarFieldToHexLe

-- Vesta Base Field (= Pallas Scalar Field via cross-wiring)
type VestaBaseField = PallasScalarField

-- Vesta Group
foreign import data VestaG :: Type
foreign import _vestaGroupAdd :: VestaG -> VestaG -> VestaG
foreign import _vestaGroupIdentity :: Unit -> VestaG
foreign import _vestaGroupGenerator :: Unit -> VestaG
foreign import _vestaGroupRand :: Int -> VestaG
foreign import _vestaGroupEq :: VestaG -> VestaG -> Boolean
foreign import _vestaGroupToString :: VestaG -> String
foreign import _vestaGroupNeg :: VestaG -> VestaG
foreign import _vestaGroupScale :: VestaScalarField -> VestaG -> VestaG
foreign import _vestaWeierstrassA :: Unit -> PallasScalarField
foreign import _vestaWeierstrassB :: Unit -> PallasScalarField

instance Semigroup VestaG where
  append = _vestaGroupAdd

instance Monoid VestaG where
  mempty = _vestaGroupIdentity unit

instance Eq VestaG where
  eq = _vestaGroupEq

instance Show VestaG where
  show = _vestaGroupToString

instance Arbitrary VestaG where
  arbitrary = _vestaGroupRand <$> arbitrary

instance FrModule VestaScalarField VestaG where
  scalarMul = _vestaGroupScale
  inverse = _vestaGroupNeg

instance WeierstrassCurve VestaBaseField VestaG where
  curveParams _ =
    { a: _vestaWeierstrassA unit
    , b: _vestaWeierstrassB unit
    }
  toAffine x = f <$> runFn3 _vestaToAffine Just Nothing x
    where
    f as =
      { x: unsafePartial $ fromJust $ as Array.!! 0
      , y: unsafePartial $ fromJust $ as Array.!! 1
      }
  fromAffine = _vestaFromAffine
  generator = _vestaGroupGenerator unit

foreign import _vestaToAffine
  :: forall a
   . Fn3
       (a -> Maybe a)
       (Maybe a)
       VestaG
       (Maybe a)

foreign import _vestaFromAffine :: { x :: VestaBaseField, y :: VestaBaseField } -> VestaG

foreign import _pallasFromAffine :: { x :: PallasBaseField, y :: PallasBaseField } -> PallasG

instance Ord VestaScalarField where
  compare x y = compare (toBigInt x) (toBigInt y)

instance Ord PallasScalarField where
  compare x y = compare (toBigInt x) (toBigInt y)

instance HasEndo VestaScalarField PallasScalarField where
  endoBase = _pallasEndoBase unit
  endoScalar = _pallasEndoScalar unit

instance HasEndo PallasScalarField VestaScalarField where
  endoBase = _vestaEndoBase unit
  endoScalar = _vestaEndoScalar unit

-- BW19 parameters for Vesta (returns array of base field elements)
foreign import _vestaBW19Params :: Unit -> Array PallasScalarField

instance HasBW19 VestaBaseField VestaG where
  bw19Params _ =
    let
      arr = _vestaBW19Params unit
    in
      { u: unsafePartial $ fromJust $ arr Array.!! 0
      , fu: unsafePartial $ fromJust $ arr Array.!! 1
      , sqrtNeg3U2MinusUOver2: unsafePartial $ fromJust $ arr Array.!! 2
      , sqrtNeg3U2: unsafePartial $ fromJust $ arr Array.!! 3
      , inv3U2: unsafePartial $ fromJust $ arr Array.!! 4
      }

-- ============================================================================
-- GROUP MAP (Hash-to-Curve) FFI - Reference implementations for testing
-- ============================================================================

-- | Returns (x, y) as a tuple array [x, y]
foreign import _pallasGroupMap :: PallasBaseField -> Array PallasBaseField
foreign import _vestaGroupMap :: VestaBaseField -> Array VestaBaseField

-- | Hash a field element to a point on the Pallas curve using Rust's BW19 implementation
-- | For testing against our PureScript implementation
pallasGroupMap :: PallasBaseField -> { x :: PallasBaseField, y :: PallasBaseField }
pallasGroupMap t =
  let
    arr = _pallasGroupMap t
  in
    { x: unsafePartial $ fromJust $ arr Array.!! 0
    , y: unsafePartial $ fromJust $ arr Array.!! 1
    }

-- | Hash a field element to a point on the Vesta curve using Rust's BW19 implementation
-- | For testing against our PureScript implementation
vestaGroupMap :: VestaBaseField -> { x :: VestaBaseField, y :: VestaBaseField }
vestaGroupMap t =
  let
    arr = _vestaGroupMap t
  in
    { x: unsafePartial $ fromJust $ arr Array.!! 0
    , y: unsafePartial $ fromJust $ arr Array.!! 1
    }
