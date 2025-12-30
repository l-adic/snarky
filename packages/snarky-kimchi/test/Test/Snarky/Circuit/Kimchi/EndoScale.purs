module Test.Snarky.Circuit.Kimchi.EndoScale where

import Prelude

import Data.Identity (Identity)
import Data.Traversable (foldl)
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, add_, const_, Bool(..))
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Circuit.Kimchi.EndoScale (ScalarChallenge(..), toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, endoBase, fromInt)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector, (!!))
import Snarky.Data.Vector as Vector
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

toFieldConstant :: forall f n _l. PrimeField f => FieldSizeInBits f n => Add 128 _l n => f -> f -> f
toFieldConstant f endo =
  let
    bits :: Vector 128 Boolean
    bits = Vector.reverse $ Vector.take @128 $ unpackPure f

    chunks :: Vector 64 (Vector 2 Boolean)
    chunks = Vector.chunks @2 bits

    processChunk :: { a :: f, b :: f } -> Vector 2 Boolean  -> { a :: f, b :: f }
    processChunk { a, b } v =
      let
        bit_even = v !! unsafeFinite 1
        bit_odd = v !! unsafeFinite 0

        s = if bit_even then one else -one

        a2 = a + a
        b2 = b + b

      in
        if bit_odd then { a: a2 + s, b: b2 }
        else { a: a2, b: b2 + s }

    final = foldl processChunk { a: fromInt 2, b: fromInt 2 } chunks
  in
    final.a * endo + final.b

refEndoScale :: F Vesta.ScalarField -> F Vesta.ScalarField
refEndoScale (F f) =
  let
    endo = endoBase @Vesta.ScalarField

    result = toFieldConstant f endo
  in
    F result

circuit
  :: forall t
   . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
  => FVar Vesta.ScalarField
  -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity (FVar Vesta.ScalarField)
circuit scalarValue = do

  let 
    challenge = ScalarChallenge scalarValue
    endoCoeff = endoBase :: Vesta.ScalarField -- from HasEndo Vesta.ScalarField Pallas.ScalarField
    endoVar = const_ endoCoeff

  -- Apply the endoscale algorithm and return the FVar
  toField challenge endoVar

-- Generator for 128-bit boolean arrays (like OCaml QuickCheck test)
gen128BitElem :: Gen (F Vesta.ScalarField)
gen128BitElem = do 
  v <- Vector.generator (Proxy @128) arbitrary
  let v' = v `Vector.append` (Vector.generate $ const false)
  pure $ F $ packPure v'

-- Convert boolean array to scalar field element (LSB first)
boolArrayToScalar :: forall f n. PrimeField f => Vector n (BoolVar f) -> (FVar f)
boolArrayToScalar bits =
  foldl (\acc bit -> acc `add_` coerce bit) (const_ zero) bits

-- Test specification (following OCaml QuickCheck pattern)
spec :: Spec Unit
spec = do
  describe "EndoScale" do
    it "Circuit output matches constant implementation (like OCaml test)" $
      let
        -- Reference function: apply constant algorithm to boolean array
        f :: F Vesta.ScalarField -> F Vesta.ScalarField
        f = refEndoScale

        -- Solver and constraint compilation
        solver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit

        { constraints } = compilePure
          (Proxy @(F Vesta.ScalarField))
          (Proxy @(F Vesta.ScalarField))
          (Proxy @(KimchiConstraint Vesta.ScalarField))
          circuit
          Kimchi.initialState
      in
        -- Test that circuit matches reference on random 128-bit boolean arrays
        circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) gen128BitElem