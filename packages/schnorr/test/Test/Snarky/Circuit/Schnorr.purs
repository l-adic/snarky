module Test.Snarky.Circuit.Schnorr
  ( spec
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Schnorr.Gen (genValidSignature)
import Data.Vector (Vector)
import Data.Vector as Vector
import Mina.ChainId (ChainId(..), signaturePrefix)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, assert_)
import Snarky.Circuit.Schnorr (Signature(..), pallasParams, shiftConst, verifies)
import Snarky.Circuit.Schnorr.Shifted (createShifted)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied_)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-- | Var-side of the verifier input. The value side (what
-- | `genValidSignature` produces, `Data.Schnorr.Gen.VerifyInput n (F f)`)
-- | bridges to this automatically via the generic `CircuitType`
-- | instances (`Record`, `Vector n`, `F ↔ FVar`, `Boolean ↔ BoolVar`),
-- | so `circuitTest'` feeds generated signatures straight in.
type VerifyInputVar n f =
  { signature ::
      { r :: FVar f
      , sBits :: Vector 255 (BoolVar f)
      }
  , publicKey :: AffinePoint (FVar f)
  , message :: Vector n (FVar f)
  }

spec
  :: TestConfig Pallas.BaseField (KimchiGate Pallas.BaseField)
       (AuxState Pallas.BaseField)
  -> Spec Unit
spec cfg = describe "Snarky.Circuit.Schnorr" do
  it "verifies accepts a valid signature in-circuit" do
    let
      circuit'
        :: forall t
         . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
        => VerifyInputVar 1 Pallas.BaseField
        -> Snarky (KimchiConstraint Pallas.BaseField) t Identity Unit
      circuit' { signature: { r, sBits }, publicKey, message } = do
        shifted <- createShifted pallasParams shiftConst
        verified <- verifies (signaturePrefix Mainnet) shifted
          { publicKey, signature: Signature { r, s: sBits }, message: Vector.toUnfoldable message }
        assert_ verified

      gen = genValidSignature (signaturePrefix Mainnet) (Proxy @PallasG)
        (Proxy @1)

    void $ circuitTest' @Pallas.BaseField
      cfg
      (NEA.singleton { testFunction: satisfied_, input: QuickCheck 10 gen })
      circuit'
