module Test.Snarky.Circuit.Field (spec) where

import Prelude

import Data.Foldable (sum)
import Data.Identity (Identity)
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Snarky.Backend.Builder (CircuitBuilderT)
import Snarky.Backend.Compile (SolverT, compilePure, makeSolver)
import Snarky.Backend.Prover (ProverT)
import Snarky.Circuit.DSL (Variable, div_, equals_, inv_, mul_, negate_, seal, sum_)
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector, unVector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (circuitSpecPure, circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall f c c'
   . PrimeField f
  => BasicSystem f c'
  => ConstraintM (CircuitBuilderT c) c'
  => ConstraintM (ProverT f) c'
  => Proxy f
  -> Proxy c'
  -> ( forall m
        . Applicative m
       => (Variable -> m f)
       -> c
       -> m Boolean
     )
  -> Spec Unit
spec _ pc eval = describe "Field Circuit Specs" do

  it "mul Circuit is Valid" $
    let
      f (Tuple (F a) (F b)) = F (a * b)

      solver :: SolverT f c' Identity (Tuple (F f) (F f)) (F f)
      solver = makeSolver pc (uncurry mul_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @(F f))
          pc
          (uncurry mul_)
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "eq Circuit is Valid" $
    let
      f :: Tuple (F f) (F f) -> Boolean
      f = uncurry (==)
      solver = makeSolver pc (uncurry equals_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Boolean)
          pc
          (uncurry equals_)
      same = do
        a <- arbitrary
        pure $ Tuple (F a) (F a)
      distinct = do
        a <- arbitrary
        b <- arbitrary
        pure $ Tuple (F a) (F b)
    in
      do
        circuitSpecPure' constraints eval solver (satisfied f) same
        circuitSpecPure' constraints eval solver (satisfied f) distinct

  it "inv Circuit is Valid" $
    let
      f (F a) =
        if a == zero then F zero
        else F @f (recip a)
      solver = makeSolver pc inv_
      { constraints } =
        compilePure
          (Proxy @(F f))
          (Proxy @(F f))
          pc
          inv_
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "div Circuit is Valid" $
    let
      f (Tuple (F a) (F b)) =
        if b == zero then F zero
        else F @f (a / b)
      solver = makeSolver pc (uncurry div_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @(F f))
          pc
          (uncurry div_)
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "sum Circuit is Valid" $
    let
      f :: Vector 10 (F f) -> F f
      f as = F $ sum (un F <$> as)
      solver = makeSolver pc (pure <<< sum_ <<< unVector)
      { constraints } =
        compilePure
          (Proxy @(Vector 10 (F f)))
          (Proxy @(F f))
          pc
          (pure <<< sum_ <<< unVector)
    in
      circuitSpecPure' constraints eval solver (satisfied f) (Vector.generator (Proxy @10) arbitrary)

  it "negate Circuit is Valid" $
    let
      f (F a) = F (negate a)
      solver = makeSolver pc (pure <<< negate_)
      { constraints } =
        compilePure
          (Proxy @(F f))
          (Proxy @(F f))
          pc
          (pure <<< negate_)
    in
      circuitSpecPure constraints eval solver (satisfied f)

  it "seal Circuit is Valid" $
    let
      f :: F f -> F f
      f = identity
      solver = makeSolver pc seal
      { constraints } =
        compilePure
          (Proxy @(F f))
          (Proxy @(F f))
          pc
          seal
    in
      circuitSpecPure constraints eval solver (satisfied f)