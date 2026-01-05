module Test.Snarky.Circuit.Assert (spec) where

import Prelude

import Data.Tuple (Tuple(..), uncurry)
import Snarky.Backend.Builder (class Finalizer, CircuitBuilderState, CircuitBuilderT)
import Snarky.Backend.Compile (Checker, compilePure, makeSolver)
import Snarky.Backend.Prover (ProverT)
import Snarky.Circuit.DSL (F(..), assertEqual_, assertNonZero_, assertNotEqual_, assertSquare_)
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Constraint.Basic (class BasicSystem)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (suchThat)
import Test.Snarky.Circuit.Utils (PostCondition, circuitSpecPure', expectDivideByZero, satisfied_, unsatisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall f c r c'
   . BasicSystem f c'
  => ConstraintM (CircuitBuilderT c r) c'
  => ConstraintM (ProverT f) c'
  => Finalizer c r
  => Proxy f
  -> Proxy c'
  -> Checker f c
  -> PostCondition f c r
  -> CircuitBuilderState c r
  -> Spec Unit
spec _ pc eval postCondition initialState = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $
    let
      solver = makeSolver pc assertNonZero_
      s =
        compilePure
          (Proxy @(F f))
          (Proxy @Unit)
          pc
          assertNonZero_
          initialState
      gen = do
        a <- arbitrary `suchThat` (_ /= zero)
        pure $ F a
    in
      do
        circuitSpecPure'
          { builtState: s
          , checker: eval
          , solver: solver
          , testFunction: satisfied_
          , postCondition: postCondition
          }
          gen
        circuitSpecPure'
          { builtState: s
          , checker: eval
          , solver: solver
          , testFunction: expectDivideByZero
          , postCondition: postCondition
          }
          (pure zero)

  it "assertEqual Circuit is Valid" $
    let
      solver = makeSolver pc (uncurry assertEqual_)
      s =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          pc
          (uncurry assertEqual_)
          initialState
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (F a) (F b)
    in
      do
        circuitSpecPure'
          { builtState: s
          , checker: eval
          , solver: solver
          , testFunction: unsatisfied
          , postCondition: postCondition
          }
          distinct
        circuitSpecPure'
          { builtState: s
          , checker: eval
          , solver: solver
          , testFunction: satisfied_
          , postCondition: postCondition
          }
          same

  it "assertNotEqual Circuit is Valid" $
    let
      solver = makeSolver pc (uncurry assertNotEqual_)
      s =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          pc
          (uncurry assertNotEqual_)
          initialState
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (F a) (F b)
    in
      do
        circuitSpecPure'
          { builtState: s
          , checker: eval
          , solver: solver
          , testFunction: expectDivideByZero
          , postCondition: postCondition
          }
          same
        circuitSpecPure'
          { builtState: s
          , checker: eval
          , solver: solver
          , testFunction: satisfied_
          , postCondition: postCondition
          }
          distinct

  it "assertSquare Circuit is Valid" $
    let
      solver = makeSolver pc (uncurry assertSquare_)
      s =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          pc
          (uncurry assertSquare_)
          initialState
      squares = do
        x <- arbitrary
        pure $ Tuple (F x) (F (x * x))
      nonSquares = do
        x <- arbitrary
        y <- arbitrary `suchThat` \y -> y /= x * x
        pure $ Tuple (F x) (F y)
    in
      do
        circuitSpecPure'
          { builtState: s
          , checker: eval
          , solver: solver
          , testFunction: satisfied_
          , postCondition: postCondition
          }
          squares
        circuitSpecPure'
          { builtState: s
          , checker: eval
          , solver: solver
          , testFunction: unsatisfied
          , postCondition: postCondition
          }
          nonSquares