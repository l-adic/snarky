module Test.Snarky.Types.Shifted where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import JS.BigInt as BigInt
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky)
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, modulus)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Types.Shifted (class Shifted, Type1(..), Type2(..), fieldSizeBits, fromShifted, fromShiftedType1Circuit, fromShiftedType2Circuit, joinField, splitField, toShifted)
import Test.QuickCheck (Result, (===))
import Test.QuickCheck.Gen (Gen, chooseInt, oneOf)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- splitField / joinField roundtrip (within same field)
--------------------------------------------------------------------------------

splitJoinRoundtrip :: forall @f. PrimeField f => F f -> Result
splitJoinRoundtrip x =
  let
    Type2 { sDiv2: F d, sOdd } = splitField x
    reconstructed = F (joinField { sDiv2: d, sOdd })
  in
    reconstructed === x

--------------------------------------------------------------------------------
-- Type1 roundtrip: fromShifted (toShifted s) == s
--------------------------------------------------------------------------------

type1ShiftRoundtrip
  :: forall @f @f'
   . PrimeField f
  => Shifted (F f) (Type1 (F f'))
  => F f
  -> Result
type1ShiftRoundtrip s =
  let
    shifted :: Type1 (F f')
    shifted = toShifted s
  in
    fromShifted shifted === s

--------------------------------------------------------------------------------
-- Type2: fromShifted (toShifted s) == s + 2^n (mod field)
--------------------------------------------------------------------------------

type2ShiftRoundtrip
  :: forall @f @f' n
   . FieldSizeInBits f n
  => Shifted (F f) (Type2 (F f') Boolean)
  => F f
  -> Result
type2ShiftRoundtrip s =
  let
    shifted :: Type2 (F f') Boolean
    shifted = toShifted s
    unshifted = fromShifted shifted
    n = fieldSizeBits (Proxy :: Proxy f)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
    expected = case s of F x -> F (x + twoToN)
  in
    unshifted === expected

--------------------------------------------------------------------------------
-- Danger zone generators
--------------------------------------------------------------------------------

genDangerZone :: forall @f. PrimeField f => Gen (F f)
genDangerZone =
  let
    m = modulus @f
    two = BigInt.fromInt 2

    genNearZero = do
      small <- chooseInt 0 1000
      pure $ F (fromBigInt (BigInt.fromInt small))

    genNearMax = do
      offset <- chooseInt 1 1000
      pure $ F (fromBigInt (m - BigInt.fromInt offset))

    genNearHalf = do
      offset <- chooseInt 0 1000
      pure $ F (fromBigInt (m / two + BigInt.fromInt offset))

    genEven = do
      k <- chooseInt 1 10000
      pure $ F (fromBigInt (two * BigInt.fromInt k))
  in
    oneOf $ NEA.cons' genNearZero [ genNearMax, genNearHalf, genEven ]

--------------------------------------------------------------------------------
-- Circuit-level tests for fromShiftedType1Circuit and fromShiftedType2Circuit
--------------------------------------------------------------------------------

-- | Circuit that computes fromShiftedType1Circuit (cross-field: Vesta.BaseField).
type1Circuit
  :: forall t
   . CircuitM Vesta.BaseField (KimchiConstraint Vesta.BaseField) t Identity
  => Type1 (FVar Vesta.BaseField)
  -> Snarky (KimchiConstraint Vesta.BaseField) t Identity (FVar Vesta.BaseField)
type1Circuit shifted = pure $ fromShiftedType1Circuit shifted

-- | Circuit that computes fromShiftedType1Circuit (same-field: Vesta.ScalarField).
type1SameFieldCircuit
  :: forall t
   . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
  => Type1 (FVar Vesta.ScalarField)
  -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity (FVar Vesta.ScalarField)
type1SameFieldCircuit shifted = pure $ fromShiftedType1Circuit shifted

-- | Circuit that computes fromShiftedType2Circuit.
type2Circuit
  :: forall t
   . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
  => Type2 (FVar Pallas.BaseField) (BoolVar Pallas.BaseField)
  -> Snarky (KimchiConstraint Pallas.BaseField) t Identity (FVar Pallas.BaseField)
type2Circuit shifted = pure $ fromShiftedType2Circuit shifted

-- | Pure computation for Type1 (cross-field): s = 2*t + 2^n + 1
type1Expected :: Type1 (F Vesta.BaseField) -> F Vesta.BaseField
type1Expected (Type1 (F t)) =
  let
    n = fieldSizeBits (Proxy :: Proxy Vesta.BaseField)
    two = fromBigInt (BigInt.fromInt 2)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
  in
    F (two * t + twoToN + one)

-- | Pure computation for Type1 (same-field): s = 2*t + 2^n + 1
type1SameFieldExpected :: Type1 (F Vesta.ScalarField) -> F Vesta.ScalarField
type1SameFieldExpected (Type1 (F t)) =
  let
    n = fieldSizeBits (Proxy :: Proxy Vesta.ScalarField)
    two = fromBigInt (BigInt.fromInt 2)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
  in
    F (two * t + twoToN + one)

-- | Pure computation for Type2: s = 2*sDiv2 + sOdd + 2^n
type2Expected :: Type2 (F Pallas.BaseField) Boolean -> F Pallas.BaseField
type2Expected (Type2 { sDiv2: F d, sOdd }) =
  let
    n = fieldSizeBits (Proxy :: Proxy Pallas.BaseField)
    two = fromBigInt (BigInt.fromInt 2)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
  in
    F (two * d + (if sOdd then one else zero) + twoToN)

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Snarky.Types.Shifted" do
    describe "splitField / joinField" do
      it "roundtrips in Vesta.BaseField" $
        quickCheck (splitJoinRoundtrip @Vesta.BaseField)
      it "roundtrips in Vesta.ScalarField" $
        quickCheck (splitJoinRoundtrip @Vesta.ScalarField)

    describe "Type1 Shifted (crossField)" do
      it "fromShifted (toShifted s) == s" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.BaseField)
      it "fromShifted (toShifted s) == s (danger zone)" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.BaseField <$> genDangerZone)

    describe "Type1 Shifted (sameField)" do
      it "fromShifted (toShifted s) == s" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.ScalarField)
      it "fromShifted (toShifted s) == s (danger zone)" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.ScalarField <$> genDangerZone)

    describe "Type2 Shifted (crossField)" do
      it "fromShifted (toShifted s) == s" $
        quickCheck (type2ShiftRoundtrip @Vesta.BaseField @Vesta.ScalarField)
      it "fromShifted (toShifted s) == s + 2^n (danger zone)" $
        quickCheck (type2ShiftRoundtrip @Vesta.BaseField @Vesta.ScalarField <$> genDangerZone)

    describe "fromShiftedType1Circuit" do
      it "circuit matches pure implementation" do
        let
          gen = toShifted <$> genDangerZone @Vesta.ScalarField
          st = compilePure
            (Proxy @(Type1 (F Vesta.BaseField)))
            (Proxy @(F Vesta.BaseField))
            (Proxy @(KimchiConstraint Vesta.BaseField))
            type1Circuit
            Kimchi.initialState
          solver = makeSolver (Proxy @(KimchiConstraint Vesta.BaseField)) type1Circuit
        circuitSpecPure' 100
          { builtState: st
          , checker: Kimchi.eval
          , solver: solver
          , testFunction: satisfied type1Expected
          , postCondition: Kimchi.postCondition
          }
          gen

    describe "fromShiftedType1Circuit (sameField)" do
      it "circuit matches pure implementation" do
        let
          gen = toShifted <$> genDangerZone @Vesta.ScalarField
          st = compilePure
            (Proxy @(Type1 (F Vesta.ScalarField)))
            (Proxy @(F Vesta.ScalarField))
            (Proxy @(KimchiConstraint Vesta.ScalarField))
            type1SameFieldCircuit
            Kimchi.initialState
          solver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) type1SameFieldCircuit
        circuitSpecPure' 100
          { builtState: st
          , checker: Kimchi.eval
          , solver: solver
          , testFunction: satisfied type1SameFieldExpected
          , postCondition: Kimchi.postCondition
          }
          gen

    describe "fromShiftedType2Circuit" do
      it "circuit matches pure implementation" do
        let
          gen = toShifted <$> genDangerZone @Pallas.ScalarField
          st = compilePure
            (Proxy @(Type2 (F Pallas.BaseField) Boolean))
            (Proxy @(F Pallas.BaseField))
            (Proxy @(KimchiConstraint Pallas.BaseField))
            type2Circuit
            Kimchi.initialState
          solver = makeSolver (Proxy @(KimchiConstraint Pallas.BaseField)) type2Circuit
        circuitSpecPure' 100
          { builtState: st
          , checker: Kimchi.eval
          , solver: solver
          , testFunction: satisfied type2Expected
          , postCondition: Kimchi.postCondition
          }
          gen
