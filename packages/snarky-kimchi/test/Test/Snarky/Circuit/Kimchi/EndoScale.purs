module Test.Snarky.Circuit.Kimchi.EndoScale where

import Prelude

import Data.Identity (Identity)
import Data.Newtype (over)
import Data.Traversable (foldl)
import Prim.Int (class Add)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
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

toFieldConstant
  :: forall f n _l
   . PrimeField f
  => FieldSizeInBits f n
  => Add 128 _l n
  => f
  -> f
  -> f
toFieldConstant f endo =
  let
    bits :: Vector 128 Boolean
    bits = Vector.reverse $ Vector.take @128 $ unpackPure f

    chunks :: Vector 64 (Vector 2 Boolean)
    chunks = Vector.chunks @2 bits

    processChunk
      :: { a :: f, b :: f }
      -> Vector 2 Boolean
      -> { a :: f, b :: f }
    processChunk st v =
      let
        bitEven = v !! unsafeFinite 1
        bitOdd = v !! unsafeFinite 0
        s = if bitEven then one else -one
      in
        if bitOdd then { a: double st.a + s, b: double st.b }
        else { a: double st.a, b: double st.b + s }

    { a, b } = foldl processChunk { a: fromInt 2, b: fromInt 2 } chunks
  in
    a * endo + b
  where
  double x = x + x

circuit
  :: forall t
   . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
  => FVar Vesta.ScalarField
  -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity (FVar Vesta.ScalarField)
circuit scalarValue =
  let
    endoVar = const_ (endoBase @Vesta.ScalarField)
  in
    toField (ScalarChallenge scalarValue) endoVar

gen128BitElem :: Gen (F Vesta.ScalarField)
gen128BitElem = do
  v <- Vector.generator (Proxy @128) arbitrary
  let v' = v `Vector.append` (Vector.generate $ const false)
  pure $ F $ packPure v'

spec :: Spec Unit
spec = do
  describe "EndoScale" do
    it "Circuit output matches constant implementation (like OCaml test)" $
      let
        f :: F Vesta.ScalarField -> F Vesta.ScalarField
        f =
          over F \x -> toFieldConstant x (endoBase @Vesta.ScalarField)

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