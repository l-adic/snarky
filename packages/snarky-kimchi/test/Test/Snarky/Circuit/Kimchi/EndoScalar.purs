module Test.Snarky.Circuit.Kimchi.EndoScalar
  ( circuit
  , spec
  ) where

import Prelude

import Data.Newtype (over)
import Effect.Class (liftEffect)
import Prim.Int (class Add)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi.EndoScalar (ScalarChallenge(..), toField, toFieldConstant)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, endoBase)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit.Kimchi.Utils (gen128BitElem)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

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
  :: forall f f' g'
   . FieldSizeInBits f 255
  => CircuitGateConstructor f g'
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
        do
          -- Test that circuit matches reference on random 128-bit boolean arrays
          circuitSpecPure' 100
            { builtState: s
            , checker: Kimchi.eval
            , solver: solver
            , testFunction: satisfied f
            , postCondition: Kimchi.postCondition
            }
            gen128BitElem

          liftEffect $ verifyCircuit { s, gen: gen128BitElem, solver }

spec :: Spec Unit
spec = do
  spec' (Proxy @Vesta.ScalarField) "Vesta"
  spec' (Proxy @Pallas.ScalarField) "Pallas"