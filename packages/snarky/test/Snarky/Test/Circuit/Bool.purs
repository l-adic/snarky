module Test.Snarky.Test.Circuit.Bool (spec) where

import Prelude

import Data.Array (foldMap)
import Data.Identity (Identity(..))
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, uncurry3)
import Snarky.Circuit.Compile (compile, makeSolver)
import Snarky.Circuit.DSL.Boolean (all_, and_, any_, ifThenElse_, not_, or_, xor_)
import Snarky.Circuit.Types (FieldElem)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector, unVector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.Snarky.Test.Circuit.Utils (ConstraintSystem, circuitSpec, circuitSpec')
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: forall f. PrimeField f => Arbitrary f => Proxy f -> Spec Unit
spec _ = describe "Boolean Circuit Specs" do

  it "not Circuit is Valid" $
    let

      f :: Boolean -> Boolean
      f = not
      solver = makeSolver (Proxy @(ConstraintSystem f)) (pure <<< not_)
      { constraints } = un Identity $
        compile
          (Proxy @Boolean)
          (Proxy @Boolean)
          (pure <<< not_)
    in
      circuitSpec constraints solver f

  it "and Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (&&)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry and_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          (uncurry and_)
    in
      circuitSpec constraints solver f

  it "or Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (||)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry or_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          (uncurry or_)
    in
      circuitSpec constraints solver f

  it "xor Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f (Tuple a b) = (a && not b) || (not a && b)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry xor_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          (uncurry xor_)
    in
      circuitSpec constraints solver f

  it "ifThenElse Circuit is Valid" $
    let
      f :: Tuple3 Boolean (FieldElem f) (FieldElem f) -> FieldElem f
      f = uncurry3 \b t e ->
        if b then t else e
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry3 ifThenElse_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple3 Boolean (FieldElem f) (FieldElem f)))
          (Proxy @(FieldElem f))
          (uncurry3 ifThenElse_)
    in
      circuitSpec constraints solver f

  it "all Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Conj <<< foldMap Conj <<< unVector
      solver = makeSolver (Proxy @(ConstraintSystem f)) (all_ <<< unVector)
      { constraints } = un Identity $
        compile
          (Proxy @(Vector 10 Boolean))
          (Proxy @Boolean)
          (all_ <<< unVector)
    in
      circuitSpec' constraints solver f (Vector.generator (Proxy @10) arbitrary)

  it "any Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Disj <<< foldMap Disj <<< unVector
      solver = makeSolver (Proxy @(ConstraintSystem f)) (any_ <<< unVector)
      { constraints } = un Identity $
        compile
          (Proxy @(Vector 10 Boolean))
          (Proxy @Boolean)
          (any_ <<< unVector)
    in
      circuitSpec' constraints solver f (Vector.generator (Proxy @10) arbitrary)