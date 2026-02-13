module Test.Pickles.PublicInputCommitment (spec) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reifyType)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Pickles.PublicInputCommitment (publicInputCommitment)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, varToFields)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams, fromBigInt, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext as E2E
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))

-- | The x_hat circuit runs on Fq (= Pallas.ScalarField = Vesta.BaseField).
-- | Lagrange commitments from the Schnorr (Fp) verifier are Vesta points (Fq coords).
type CircuitField = Pallas.ScalarField

-------------------------------------------------------------------------------
-- Test context
-------------------------------------------------------------------------------

type TestContext =
  { stepCtx :: E2E.StepProofContext
  , lagrangeComms :: Array (AffinePoint (F CircuitField))
  , blindingH :: AffinePoint (F CircuitField)
  }

-- | Generate Fp-range values embedded as Fq.
-- | Fp < Fq in Pasta, so this is always safe.
fpRangeGen :: Gen (F CircuitField)
fpRangeGen = (\(F x) -> F (fromBigInt (toBigInt x))) <$> (arbitrary :: Gen (F Pallas.BaseField))

setupTestContext :: Aff TestContext
setupTestContext = do
  stepCtx <- E2E.createStepProofContext E2E.BaseCase
  let numPublic = Array.length stepCtx.publicInputs
  pure
    { stepCtx
    , lagrangeComms: coerce $ ProofFFI.pallasLagrangeCommitments stepCtx.verifierIndex numPublic
    , blindingH: coerce $ ProofFFI.pallasProverIndexBlindingGenerator stepCtx.verifierIndex
    }

-------------------------------------------------------------------------------
-- Test spec
-------------------------------------------------------------------------------

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll setupTestContext $
  describe "PublicInputCommitment" do
    it "circuit matches proof-systems reference" \ctx ->
      reifyType (Array.length ctx.stepCtx.publicInputs) (go ctx)
  where
  go
    :: forall nPublic
     . Reflectable nPublic Int
    => TestContext
    -> Proxy nPublic
    -> Aff Unit
  go ctx _ = do
    let
      -- Ground truth: Rust proof-systems public_comm (computes -MSM + H).
      -- Convert Fq scalars back to Fp for pallasPublicComm (safe since values are Fp-range).
      rustFn :: Vector nPublic (F CircuitField) -> AffinePoint (F CircuitField)
      rustFn scalars = unsafePartial $
        let
          fpScalars :: Array Pallas.BaseField
          fpScalars = map (\(F x) -> fromBigInt (toBigInt x)) (Vector.toUnfoldable scalars)
          -- we call head here because we only have one chunk
          { x, y } = fromJust $ Array.head $ ProofFFI.pallasPublicComm ctx.stepCtx.verifierIndex fpScalars
        in
          { x: F x, y: F y }

      circuit
        :: forall t
         . CircuitM CircuitField (KimchiConstraint CircuitField) t Identity
        => Vector nPublic (FVar CircuitField)
        -> Snarky (KimchiConstraint CircuitField) t Identity (AffinePoint (FVar CircuitField))
      circuit inputs =
        let
          pairs =
            unsafePartial fromJust
              $ NEA.fromArray
              $
                Array.zipWith
                  (\scalar base -> { scalar, base })
                  (varToFields @CircuitField @(Vector nPublic (F CircuitField)) inputs)
                  (ctx.lagrangeComms)
        in
          publicInputCommitment @51 (curveParams (Proxy @Vesta.G)) pairs ctx.blindingH

      solver = makeSolver (Proxy @(KimchiConstraint CircuitField)) circuit

      s = compilePure
        (Proxy @(Vector nPublic (F CircuitField)))
        (Proxy @(AffinePoint (F CircuitField)))
        (Proxy @(KimchiConstraint CircuitField))
        circuit
        Kimchi.initialState

      gen = Vector.generator (Proxy @nPublic) fpRangeGen

    -- QuickCheck: circuit output matches Rust proof-systems for random inputs
    circuitSpecPure' 2
      { builtState: s
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied rustFn
      , postCondition: Kimchi.postCondition
      }
      gen

    -- Full end-to-end verification with random inputs
    liftEffect $ verifyCircuit
      { s
      , gen
      , solver
      }
