module Test.Snarky.Circuit.Types (spec) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple)
import Data.Tuple.Nested (Tuple3)
import Data.Vector (Vector)
import Data.Vector as Vector
import Snarky.Circuit.CVar (CVar, Variable)
import Snarky.Circuit.Types (class CheckedType, class CircuitType, Bool, F, UnChecked, fieldsToValue, fieldsToVar, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, valueToFields, varToFields)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary, (===))
import Test.QuickCheck.Gen (Gen)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck')
import Type.Proxy (Proxy(..))

-- Custom datatype to test generic deriving
data Point f = Point f f

derive instance Generic (Point f) _
derive instance Eq f => Eq (Point f)

instance Show f => Show (Point f) where
  show = genericShow

instance Arbitrary f => Arbitrary (Point f) where
  arbitrary = Point <$> arbitrary <*> arbitrary

-- Generic instance using the generic functions
instance CircuitType f (Point (F f)) (Point (CVar f Variable)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(Point (F f))
  fieldsToVar = genericFieldsToVar @(Point (F f))

-- Another custom type with more complex structure
data MyRecord f bool = MyRecord
  { x :: f
  , y :: f
  , flag :: bool
  , vec :: Vector 2 f
  }

derive instance Generic (MyRecord f bool) _
derive instance (Eq f, Eq bool) => Eq (MyRecord f bool)

instance (Show f, Show bool) => Show (MyRecord f bool) where
  show = genericShow

instance (Arbitrary f, Arbitrary bool) => Arbitrary (MyRecord f bool) where
  arbitrary = MyRecord <$>
    ( { x: _, y: _, flag: _, vec: _ }
        <$> arbitrary
        <*> arbitrary
        <*> arbitrary
        <*> Vector.generator (Proxy @2) arbitrary
    )

instance
  PrimeField f =>
  CircuitType f (MyRecord (F f) Boolean) (MyRecord (CVar f Variable) (CVar f (Bool Variable))) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(MyRecord (F f) Boolean)
  fieldsToVar = genericFieldsToVar @(MyRecord (F f) Boolean)

instance (BasicSystem f c) => CheckedType (MyRecord (CVar f Variable) (CVar f (Bool Variable))) c where
  check = genericCheck

-- Generic test suite for any CircuitType
testCircuitType
  :: forall f a avar
   . CircuitType f a avar
  => Arbitrary a
  => Arbitrary avar
  => Eq a
  => Eq avar
  => Show a
  => Show avar
  => PrimeField f
  => String
  -> Proxy f
  -> Proxy a
  -> Spec Unit
testCircuitType typeName _ _ =
  describe typeName do
    it "valueToFields/fieldsToValue round trip" $
      quickCheck' 10 \(value :: a) ->
        let
          fields = valueToFields @f @a value
          restored = fieldsToValue @f @a fields
        in
          restored === value

    it "varToFields/fieldsToVar round trip" $
      quickCheck' 10 \(var :: avar) ->
        let
          fields = varToFields @f @a var
          restored = fieldsToVar @f @a fields
        in
          restored === var

-- Generic test suite with custom generators
testCircuitTypeGen
  :: forall f a avar
   . CircuitType f a avar
  => Eq a
  => Eq avar
  => Show a
  => Show avar
  => PrimeField f
  => String
  -> Proxy f
  -> Proxy a
  -> Gen a
  -> Gen avar
  -> Spec Unit
testCircuitTypeGen typeName _ _ genA genAVar =
  describe typeName do
    it "valueToFields/fieldsToValue round trip" $
      quickCheck' 10 \(_ :: Unit) -> do
        value <- genA
        pure $
          let
            fields = valueToFields @f @a value
            restored = fieldsToValue @f @a fields
          in
            restored === value

    it "varToFields/fieldsToVar round trip" $
      quickCheck' 10 \(_ :: Unit) -> do
        var <- genAVar
        pure $
          let
            fields = varToFields @f @a var
            restored = fieldsToVar @f @a fields
          in
            restored === var

spec :: forall f. PrimeField f => Proxy f -> Spec Unit
spec pf = describe "CircuitType Round Trip Tests" do

  testCircuitType "F type" pf (Proxy @(F f))

  testCircuitType "Boolean type" pf (Proxy @Boolean)

  testCircuitType "UnChecked F" pf (Proxy @(UnChecked (F f)))

  testCircuitType "UnChecked Boolean" pf (Proxy @(UnChecked Boolean))

  testCircuitType "Tuple (F f) (F f)" pf (Proxy @(Tuple (F f) (F f)))

  testCircuitType "Tuple Boolean Boolean" pf (Proxy @(Tuple Boolean Boolean))

  testCircuitType "Tuple (F f) Boolean" pf (Proxy @(Tuple (F f) Boolean))

  testCircuitType "Tuple (Tuple 3 (F f) (F f) Boolean" pf (Proxy @(Tuple3 (F f) (F f) Boolean))

  -- Vector types (using custom generators)
  testCircuitTypeGen "Vector 3 (F f)" pf (Proxy @(Vector 3 (F f)))
    (Vector.generator (Proxy @3) arbitrary)
    (Vector.generator (Proxy @3) arbitrary)

  testCircuitTypeGen "Vector 2 Boolean" pf (Proxy @(Vector 2 Boolean))
    (Vector.generator (Proxy @2) arbitrary)
    (Vector.generator (Proxy @2) arbitrary)

  testCircuitTypeGen "Vector 4 (UnChecked (F f))" pf (Proxy @(Vector 4 (UnChecked (F f))))
    (Vector.generator (Proxy @4) arbitrary)
    (Vector.generator (Proxy @4) arbitrary)

  testCircuitType "Point (custom type)" pf (Proxy @(Point (F f)))

  testCircuitType "MyRecord (complex custom type)" pf (Proxy @(MyRecord (F f) Boolean))

  testCircuitType "Plain record { a :: F f, b :: Boolean }" pf
    (Proxy @{ a :: F f, b :: Boolean })

  testCircuitType "Complex record with Point" pf
    (Proxy @{ point :: Point (F f), value :: F f })

  -- Record with vector field (needs custom generator for Vector)
  testCircuitTypeGen "Record with vector" pf
    (Proxy @{ values :: Vector 3 (F f), flag :: Boolean })
    ({ values: _, flag: _ } <$> Vector.generator (Proxy @3) arbitrary <*> arbitrary)
    ({ values: _, flag: _ } <$> Vector.generator (Proxy @3) arbitrary <*> arbitrary)

  testCircuitType "Nested record" pf
    (Proxy @{ outer :: { inner :: F f, flag :: Boolean }, value :: F f })

  -- Very complex nested record (needs custom generator for Vector)
  testCircuitTypeGen "Complex nested record" pf
    ( Proxy
        @{ point :: Point (F f)
        , vec :: Vector 2 Boolean
        , nested :: { x :: F f, y :: F f, data :: { z :: Boolean } }
        }
    )
    ( do
        point <- arbitrary
        vec <- Vector.generator (Proxy @2) arbitrary
        x <- arbitrary
        y <- arbitrary
        z <- arbitrary
        pure { point, vec, nested: { x, y, data: { z } } }
    )
    ( do
        point <- arbitrary
        vec <- Vector.generator (Proxy @2) arbitrary
        x <- arbitrary
        y <- arbitrary
        z <- arbitrary
        pure { point, vec, nested: { x, y, data: { z } } }
    )