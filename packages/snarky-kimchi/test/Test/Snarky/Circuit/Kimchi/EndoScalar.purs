module Test.Snarky.Circuit.Kimchi.EndoScalar
  ( circuit
  , spec
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Effect.Class (liftEffect)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, SizedF, Snarky, const_)
import Snarky.Circuit.Kimchi.EndoScalar (toField, toFieldPure)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, EndoScalar(..), endoScalar)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
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
    EndoScalar es = endoScalar @f' @f
    endoVar = const_ es
  in
    toField @8 scalarValue endoVar

spec'
  :: forall f f' g'
   . FieldSizeInBits f 255
  => CircuitGateConstructor f g'
  => KimchiVerify f f'
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> String
  -> Spec Unit
spec' cfg _ curveName = do
  describe ("EndoScalar: " <> curveName) do
    it "Cicuit matches the reference implementation and satisfies constraints" $ do
      let
        f :: SizedF 128 (F f) -> F f
        f x = let EndoScalar e = endoScalar @(F f') @(F f) in toFieldPure (coerce x) e

        circuit'
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => SizedF 128 (FVar f)
          -> Snarky (KimchiConstraint f) t Identity (FVar f)
        circuit' = circuit

      { builtState, solver } <- circuitTest' @f
        cfg
        ( NEA.singleton
            { testFunction: satisfied f
            , input: QuickCheck 100 arbitrary
            }
        )
        circuit'

      liftEffect $ verifyCircuit { s: builtState, gen: arbitrary, solver }

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> Spec Unit
spec cfg = do
  spec' cfg (Proxy @Vesta.ScalarField) "Vesta"
  spec' cfg (Proxy @Pallas.ScalarField) "Pallas"
