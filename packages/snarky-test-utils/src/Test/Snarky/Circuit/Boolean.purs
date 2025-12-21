module Test.Snarky.Circuit.Boolean (spec) where

import Prelude

import Data.Array (foldMap)
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, uncurry3)
import Snarky.Backend.Builder (CircuitBuilderState, CircuitBuilderT)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Prover (ProverT)
import Snarky.Circuit.DSL (F, Variable, all_, and_, any_, if_, not_, or_, xor_)
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector, unVector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (circuitSpecPure, circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall f c c' r
   . PrimeField f
  => BasicSystem f c'
  => ConstraintM (CircuitBuilderT c r) c'
  => ConstraintM (ProverT f) c'
  => Proxy f
  -> Proxy c'
  -> ( forall m
        . Applicative m
       => (Variable -> m f)
       -> c
       -> m Boolean
     )
  -> CircuitBuilderState c r
  -> Spec Unit
spec _ pc eval initialState = describe "Boolean Circuit Specs" do

  it "not Circuit is Valid" $
    let

      f :: Boolean -> Boolean
      f = not
      solver = makeSolver pc (pure <<< not_)
      { constraints } =
        compilePure
          (Proxy @Boolean)
          (Proxy @Boolean)
          pc
          (pure <<< not_)
          initialState
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "and Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (&&)
      solver = makeSolver pc (uncurry and_)
      { constraints } =
        compilePure
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          pc
          (uncurry and_)
          initialState
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "or Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (||)
      solver = makeSolver pc (uncurry or_)
      { constraints } =
        compilePure
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          pc
          (uncurry or_)
          initialState
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "xor Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f (Tuple a b) = (a && not b) || (not a && b)
      solver = makeSolver pc (uncurry xor_)
      { constraints } =
        compilePure
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          pc
          (uncurry xor_)
          initialState
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "if Circuit is Valid" $
    let
      f :: Tuple3 Boolean (F f) (F f) -> F f
      f = uncurry3 \b t e ->
        if b then t else e
      solver = makeSolver pc (uncurry3 if_)
      { constraints } =
        compilePure
          (Proxy @(Tuple3 Boolean (F f) (F f)))
          (Proxy @(F f))
          pc
          (uncurry3 if_)
          initialState
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "all Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Conj <<< foldMap Conj <<< unVector
      solver = makeSolver pc (all_ <<< unVector)
      { constraints } =
        compilePure
          (Proxy @(Vector 10 Boolean))
          (Proxy @Boolean)
          pc
          (all_ <<< unVector)
          initialState
    in
      circuitSpecPure' constraints eval solver (satisfied f) (Vector.generator (Proxy @10) arbitrary)

  it "any Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Disj <<< foldMap Disj <<< unVector
      solver = makeSolver pc (any_ <<< unVector)
      { constraints } =
        compilePure
          (Proxy @(Vector 10 Boolean))
          (Proxy @Boolean)
          pc
          (any_ <<< unVector)
          initialState
    in
      circuitSpecPure' constraints eval solver (satisfied f) (Vector.generator (Proxy @10) arbitrary)