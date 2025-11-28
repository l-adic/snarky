module Test.Snarky.Circuit.Boolean (spec) where

import Prelude

import Data.Array (foldMap)
import Data.Identity (Identity(..))
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, uncurry3)
import Snarky.Circuit.Backend.Compile (compile, makeSolver)
import Test.Snarky.Circuit.Utils (circuitSpecPure, circuitSpecPure', satisfied)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Circuit.DSL (F, Variable, all_, and_, any_, if_, not_, or_, xor_)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector, unVector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (arbitrary)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall f c
   . PrimeField f
  => BasicSystem f c
  => Proxy f
  -> Proxy c
  -> ( forall m
        . Applicative m
       => (Variable -> m f)
       -> c
       -> m Boolean
     )
  -> Spec Unit
spec _ pc eval = describe "Boolean Circuit Specs" do

  it "not Circuit is Valid" $
    let

      f :: Boolean -> Boolean
      f = not
      solver = makeSolver pc (pure <<< not_)
      { constraints } = un Identity $
        compile
          (Proxy @Boolean)
          (Proxy @Boolean)
          (pure <<< not_)
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "and Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (&&)
      solver = makeSolver pc (uncurry and_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          (uncurry and_)
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "or Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (||)
      solver = makeSolver pc (uncurry or_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          (uncurry or_)
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "xor Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f (Tuple a b) = (a && not b) || (not a && b)
      solver = makeSolver pc (uncurry xor_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          (uncurry xor_)
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "if Circuit is Valid" $
    let
      f :: Tuple3 Boolean (F f) (F f) -> F f
      f = uncurry3 \b t e ->
        if b then t else e
      solver = makeSolver pc (uncurry3 if_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple3 Boolean (F f) (F f)))
          (Proxy @(F f))
          (uncurry3 if_)
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "all Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Conj <<< foldMap Conj <<< unVector
      solver = makeSolver pc (all_ <<< unVector)
      { constraints } = un Identity $
        compile
          (Proxy @(Vector 10 Boolean))
          (Proxy @Boolean)
          (all_ <<< unVector)
    in
      circuitSpecPure' constraints eval solver (satisfied f) (Vector.generator (Proxy @10) arbitrary)

  it "any Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Disj <<< foldMap Disj <<< unVector
      solver = makeSolver pc (any_ <<< unVector)
      { constraints } = un Identity $
        compile
          (Proxy @(Vector 10 Boolean))
          (Proxy @Boolean)
          (any_ <<< unVector)
    in
      circuitSpecPure' constraints eval solver (satisfied f) (Vector.generator (Proxy @10) arbitrary)