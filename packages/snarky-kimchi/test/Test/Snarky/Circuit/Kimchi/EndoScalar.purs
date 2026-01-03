module Test.Snarky.Circuit.Kimchi.EndoScalar
  ( circuit
  , spec
  , toFieldConstant
  ) where

import Prelude

import Data.Newtype (over)
import Data.Traversable (foldl)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.DSL.Bits (unpackPure)
import Snarky.Circuit.Kimchi.EndoScalar (ScalarChallenge(..), toField)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField, endoBase, fromInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector, (!!))
import Snarky.Data.Vector as Vector
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))
import Test.Snarky.Circuit.Kimchi.Utils (gen128BitElem)
import Prim.Int (class Add)

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
  :: forall f f' t m n _l
   . CircuitM f (KimchiConstraint f) t m
  => FieldSizeInBits f n
  => Add 128 _l n
  => HasEndo f f'
  => FVar f
  -> Snarky (KimchiConstraint f) t m (FVar f)
circuit scalarValue =
  let
    endoVar = const_ (endoBase @f @f')
  in
    toField (ScalarChallenge scalarValue) endoVar

spec'
  :: forall f f'
   . PrimeField f
  => FieldSizeInBits f 255
  => KimchiVerify f f'
  => Proxy f
  -> String
  -> Spec Unit
spec' _ curveName = do
  describe ("EndoScalar: " <> curveName) do
    it "Cicuit matches the reference implementation and satisfies constraints" $
      let
        f :: F f -> F f
        f =
          over F \x -> toFieldConstant x (endoBase @f @f')

        solver = makeSolver (Proxy @(KimchiConstraint f)) circuit

        s = compilePure
          (Proxy @(F f))
          (Proxy @(F f))
          (Proxy @(KimchiConstraint f))
          circuit
          Kimchi.initialState
      in
        -- Test that circuit matches reference on random 128-bit boolean arrays
        circuitSpecPure' s KimchiConstraint.eval solver (satisfied f) gen128BitElem Kimchi.postCondition

spec :: Spec Unit
spec = do
  spec' (Proxy @Vesta.ScalarField) "Vesta"
  spec' (Proxy @Pallas.ScalarField) "Pallas"