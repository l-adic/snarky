module Test.Snarky.Circuit.Kimchi.EndoScalar
  ( circuit
  , spec
  ) where

import Prelude

import Effect.Class (liftEffect)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, const_)
import Snarky.Circuit.Kimchi.EndoScalar (toField, toFieldPure)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, endoScalar)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.SizedF (SizedF)
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

circuit
  :: forall f f' t m n
   . CircuitM f (KimchiConstraint f) t m
  => FieldSizeInBits f n
  => Compare 128 n LT
  => HasEndo f' f
  => SizedF 128 (FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
circuit scalarValue =
  let
    endoVar = const_ (endoScalar :: f)
  in
    toField scalarValue endoVar

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
        f :: SizedF 128 (F f) -> F f
        f x = toFieldPure (coerce x) (endoScalar @(F f') @(F f))

        solver = makeSolver (Proxy @(KimchiConstraint f)) circuit

        s = compilePure
          (Proxy @(SizedF 128 (F f)))
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
            arbitrary

          liftEffect $ verifyCircuit { s, gen: arbitrary, solver }

spec :: Spec Unit
spec = do
  spec' (Proxy @Vesta.ScalarField) "Vesta"
  spec' (Proxy @Pallas.ScalarField) "Pallas"
