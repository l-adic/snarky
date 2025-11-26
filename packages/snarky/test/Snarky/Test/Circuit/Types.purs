module Test.Snarky.Circuit.Types (spec) where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple)
import Data.Tuple.Nested (Tuple3)
import Snarky.Circuit.CVar (CVar, Variable, const_)
import Snarky.Circuit.Constraint (Basic, class BasicSystem)
import Snarky.Circuit.Types (class CheckedType, class CircuitType, Bool, F, UnChecked(..), check, fieldsToValue, fieldsToVar, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, valueToFields, varToFields)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
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
  varToFields = genericVarToFields (Proxy @(Point (F f)))
  fieldsToVar = genericFieldsToVar (Proxy @(Point (F f)))

instance CheckedType (Point (CVar f Variable)) c where
  check = genericCheck

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
  varToFields = genericVarToFields (Proxy @(MyRecord (F f) Boolean))
  fieldsToVar = genericFieldsToVar (Proxy @(MyRecord (F f) Boolean))

instance (PrimeField f, BasicSystem f c) => CheckedType (MyRecord (CVar f Variable) (CVar f (Bool Variable))) c where
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

spec :: forall f. Arbitrary f => PrimeField f => Proxy f -> Spec Unit
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

  -- CheckedType constraint accumulation tests
  describe "CheckedType constraint tests" do

    it "F type has no constraints" $
      quickCheck' 10 \(value :: f) ->
        let
          cvar = const_ value :: CVar f Variable
          constraints = check @(CVar f Variable) @(Basic f) cvar
        in
          Array.null constraints === true

    it "Boolean type has exactly one constraint" $
      quickCheck' 10 \(_ :: Unit) ->
        let
          cvar = const_ (zero @f) :: CVar f (Bool Variable)
          constraints = check @(CVar f (Bool Variable)) @(Basic f) cvar
        in
          Array.length constraints === 1

    it "Unit type has no constraints" $
      quickCheck' 10 \(_ :: Unit) ->
        let
          constraints = check @Unit @(Basic f) unit
        in
          Array.null constraints === true

    it "UnChecked F has no constraints" $
      quickCheck' 10 \(value :: f) ->
        let
          uncheckedVar = UnChecked (const_ value :: CVar f Variable)
          constraints = check @(UnChecked (CVar f Variable)) @(Basic f) uncheckedVar
        in
          Array.null constraints === true

    it "UnChecked Boolean has no constraints" $
      quickCheck' 10 \(_ :: Unit) ->
        let
          uncheckedVar = UnChecked (const_ (zero @f) :: CVar f (Bool Variable))
          constraints = check @(UnChecked (CVar f (Bool Variable))) @(Basic f) uncheckedVar
        in
          Array.null constraints === true

    -- Compound type constraint tests
    it "Record with F and Boolean accumulates constraints correctly" $
      quickCheck' 10 \(fval :: f) ->
        let
          record = { a: const_ fval :: CVar f Variable, b: const_ (zero @f) :: CVar f (Bool Variable) }
          constraints = check @{ a :: CVar f Variable, b :: CVar f (Bool Variable) } @(Basic f) record
        in
          Array.length constraints === 1 -- Only the Boolean should contribute a constraint

    it "Point with F fields has no constraints" $
      quickCheck' 10 \(x :: f) (y :: f) ->
        let
          point = Point (const_ x) (const_ y) :: Point (CVar f Variable)
          constraints = check @(Point (CVar f Variable)) @(Basic f) point
        in
          Array.null constraints === true

    it "Record with multiple Booleans accumulates all constraints" $
      quickCheck' 10 \(_ :: Unit) ->
        let
          record = { flag1: const_ (zero @f) :: CVar f (Bool Variable), flag2: const_ (one @f) :: CVar f (Bool Variable) }
          constraints = check @{ flag1 :: CVar f (Bool Variable), flag2 :: CVar f (Bool Variable) } @(Basic f) record
        in
          Array.length constraints === 2 -- Both Booleans should contribute constraints
