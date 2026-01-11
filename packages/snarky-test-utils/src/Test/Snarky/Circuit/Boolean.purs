module Test.Snarky.Circuit.Boolean (spec) where

import Prelude

import Data.Foldable (foldMap)
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, uncurry3)
import Snarky.Backend.Builder (class CompileCircuit, CircuitBuilderState)
import Snarky.Backend.Compile (Checker, compilePure, makeSolver)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.DSL (F, all_, and_, any_, if_, not_, or_, xor_)
import Data.Vector (Vector)
import Data.Vector as Vector
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (PostCondition, circuitSpecPure, circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall f c c' r
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => Proxy c'
  -> Checker f c
  -> PostCondition f c r
  -> CircuitBuilderState c r
  -> Spec Unit
spec pc eval postCondition initialState = describe "Boolean Circuit Specs" do

  it "not Circuit is Valid" $
    let

      f :: Boolean -> Boolean
      f = not
      solver = makeSolver pc (pure <<< not_)
      s =
        compilePure @f
          (Proxy @Boolean)
          (Proxy @Boolean)
          pc
          (pure <<< not_)
          initialState
    in
      circuitSpecPure
        { builtState: s
        , checker: eval
        , solver: solver
        , testFunction: satisfied f
        , postCondition: postCondition
        }

  it "and Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (&&)
      solver = makeSolver pc (uncurry and_)
      s =
        compilePure @f
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          pc
          (uncurry and_)
          initialState
    in
      circuitSpecPure
        { builtState: s
        , checker: eval
        , solver: solver
        , testFunction: satisfied f
        , postCondition: postCondition
        }

  it "or Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (||)
      solver = makeSolver pc (uncurry or_)
      s =
        compilePure @f
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          pc
          (uncurry or_)
          initialState
    in
      circuitSpecPure
        { builtState: s
        , checker: eval
        , solver: solver
        , testFunction: satisfied f
        , postCondition: postCondition
        }

  it "xor Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f (Tuple a b) = (a && not b) || (not a && b)
      solver = makeSolver pc (uncurry xor_)
      s =
        compilePure @f
          (Proxy @(Tuple Boolean Boolean))
          (Proxy @Boolean)
          pc
          (uncurry xor_)
          initialState
    in
      circuitSpecPure
        { builtState: s
        , checker: eval
        , solver: solver
        , testFunction: satisfied f
        , postCondition: postCondition
        }

  it "if Circuit is Valid" $
    let
      f :: Tuple3 Boolean (F f) (F f) -> F f
      f = uncurry3 \b t e ->
        if b then t else e
      solver = makeSolver pc (uncurry3 if_)
      s =
        compilePure
          (Proxy @(Tuple3 Boolean (F f) (F f)))
          (Proxy @(F f))
          pc
          (uncurry3 if_)
          initialState
    in
      circuitSpecPure
        { builtState: s
        , checker: eval
        , solver: solver
        , testFunction: satisfied f
        , postCondition: postCondition
        }

  it "all Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Conj <<< foldMap Conj
      solver = makeSolver pc (all_ <<< Vector.toUnfoldable)
      s =
        compilePure @f
          (Proxy @(Vector 10 Boolean))
          (Proxy @Boolean)
          pc
          (all_ <<< Vector.toUnfoldable)
          initialState
    in
      circuitSpecPure'
        { builtState: s
        , checker: eval
        , solver: solver
        , testFunction: satisfied f
        , postCondition: postCondition
        }
        (Vector.generator (Proxy @10) arbitrary)

  it "any Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Disj <<< foldMap Disj
      solver = makeSolver pc (any_ <<< Vector.toUnfoldable)
      s =
        compilePure @f
          (Proxy @(Vector 10 Boolean))
          (Proxy @Boolean)
          pc
          (any_ <<< Vector.toUnfoldable)
          initialState
    in
      circuitSpecPure'
        { builtState: s
        , checker: eval
        , solver: solver
        , testFunction: satisfied f
        , postCondition: postCondition
        }
        (Vector.generator (Proxy @10) arbitrary)