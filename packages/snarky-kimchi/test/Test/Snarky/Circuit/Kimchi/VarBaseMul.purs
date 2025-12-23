module Test.Snarky.Circuit.Kimchi.VarBaseMul where

import Prelude

import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..), uncurry)
import Partial.Unsafe (unsafePartial)
import Poseidon.Class (class PoseidonField)
import Prim.Int (class Mul)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky)
import Snarky.Circuit.Kimchi.VarBaseMul (varBaseMul)
import Snarky.Circuit.Types (F, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class PrimeField, class WeierstrassCurve, fromAffine, scalarMul, toAffine)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall g f f' k n
   . PrimeField f
  => PoseidonField f
  => Arbitrary g
  => WeierstrassCurve f g
  => FrModule f' g
  => FieldSizeInBits f n
  => Mul 5 k n
  => Reflectable k Int
  => Proxy g
  -> Proxy (KimchiConstraint f)
  -> Spec Unit
spec pg pc =
  describe "VarBaseMul" do

    it "varBaseMul Circuit is Valid" $ unsafePartial $
      let
        f :: Tuple (AffinePoint (F f)) (F f) -> AffinePoint (F f)
        f (Tuple { x: F x, y: F y } (F t)) =
          let
            { x, y } = unsafePartial $ fromJust $ toAffine @f @g $ scalarMul t (fromAffine { x, y })
          in
            { x: F x, y: F y }

        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => AffinePoint (FVar f)
          -> FVar f
          -> Snarky (KimchiConstraint f) t Identity (AffinePoint (FVar f))
        circuit p t = do
          { g, k: (Proxy :: Proxy k) } <- varBaseMul p t
          pure g
        { constraints } =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (F f)))
            (Proxy @(AffinePoint (F f)))
            pc
            (uncurry circuit)
            Kimchi.initialState

        gen = do
          p <- EC.genAffinePoint pg
          t <- arbitrary
          pure $ Tuple p t
      in
        do
          circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) gen