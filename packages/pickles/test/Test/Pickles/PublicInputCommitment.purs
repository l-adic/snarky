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
import Pickles.PublicInputCommit (publicInputCommit)
import Pickles.PublicInputCommitment (publicInputCommitment)
import Pickles.Step.Circuit (StepStatement)
import Pickles.Types (StepIPARounds, WrapIPARounds)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, fieldsToValue, valueToFields, varToFields)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams, fromBigInt, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (Type2)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (InductiveTestContext)
import Test.Pickles.TestContext as E2E
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (SpecT, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- Step x_hat (Fq circuit, Vesta commitments)
-------------------------------------------------------------------------------

-- | The step x_hat circuit runs on Fq (= Pallas.ScalarField = Vesta.BaseField).
-- | Lagrange commitments from the Step (Fp) verifier index are Vesta points (Fq coords).
type StepCircuitField = Pallas.ScalarField

type StepTestContext =
  { stepCtx :: E2E.StepProofContext
  , lagrangeComms :: Array (AffinePoint (F StepCircuitField))
  , blindingH :: AffinePoint (F StepCircuitField)
  }

-- | Step public input type for x_hat circuit (value level, in StepCircuitField = Fq).
-- | The x_hat computation happens in the Wrap circuit (Fq), so types are parameterized by Fq.
-- | Now just StepStatement (the Step circuit's public input no longer includes StepInput).
type StepFullXhat =
  StepStatement 1 StepIPARounds WrapIPARounds
    (F StepCircuitField)
    (Type2 (F StepCircuitField) Boolean)
    Boolean

-- | Step public input type for x_hat circuit (variable level).
type StepFullXhatVar =
  StepStatement 1 StepIPARounds WrapIPARounds
    (FVar StepCircuitField)
    (Type2 (FVar StepCircuitField) (BoolVar StepCircuitField))
    (BoolVar StepCircuitField)

-- | Generate Fp-range values embedded as Fq.
-- | Fp < Fq in Pasta, so this is always safe.
fpRangeGen :: Gen (F StepCircuitField)
fpRangeGen = (\(F x) -> F (fromBigInt (toBigInt x))) <$> (arbitrary :: Gen (F Pallas.BaseField))

-------------------------------------------------------------------------------
-- Wrap x_hat (Fp circuit, Pallas commitments)
-------------------------------------------------------------------------------

-- | The wrap x_hat circuit runs on Fp (= Vesta.ScalarField = Pallas.BaseField).
-- | Lagrange commitments from the Wrap (Fq) verifier index are Pallas points (Fp coords).
type WrapCircuitField = Vesta.ScalarField

type WrapTestContext =
  { wrapCtx :: E2E.WrapProofContext
  , lagrangeComms :: Array (AffinePoint (F WrapCircuitField))
  , blindingH :: AffinePoint (F WrapCircuitField)
  }

-------------------------------------------------------------------------------
-- Test spec
-------------------------------------------------------------------------------

spec :: SpecT Aff InductiveTestContext Aff Unit
spec =
  describe "PublicInputCommitment" do
    it "old publicInputCommitment matches proof-systems reference (step0)" \{ step0 } -> do
      let ctx = mkStepCtx step0
      reifyType (Array.length step0.publicInputs) (goOldStep ctx)

    it "new PublicInputCommit (Vector) matches proof-systems reference (step0)" \{ step0 } -> do
      let ctx = mkStepCtx step0
      reifyType (Array.length step0.publicInputs) (goNewStep ctx)

    it "PublicInputCommit StepStatement matches reference (step0)" \{ step0 } -> do
      let ctx = mkStepCtx step0
      goStructuredStep ctx

    it "new PublicInputCommit (Vector) matches proof-systems reference (wrap0)" \{ wrap0 } -> do
      let ctx = mkWrapCtx wrap0
      reifyType (Array.length wrap0.publicInputs) (goNewWrap ctx)

  where
  -- Step helpers

  mkStepCtx :: E2E.StepProofContext -> StepTestContext
  mkStepCtx step0 =
    { stepCtx: step0
    , lagrangeComms: coerce $ ProofFFI.pallasLagrangeCommitments step0.verifierIndex (Array.length step0.publicInputs)
    , blindingH: coerce $ ProofFFI.pallasProverIndexBlindingGenerator step0.verifierIndex
    }

  -- | Ground truth: Rust proof-systems public_comm for Step proof (Pallas SRS).
  rustFnStep :: forall nPublic. StepTestContext -> Vector nPublic (F StepCircuitField) -> AffinePoint (F StepCircuitField)
  rustFnStep ctx scalars = unsafePartial $
    let
      fpScalars :: Array Pallas.BaseField
      fpScalars = map (\(F x) -> fromBigInt (toBigInt x)) (Vector.toUnfoldable scalars)
      -- we call head here because we only have one chunk
      { x, y } = fromJust $ Array.head $ ProofFFI.pallasPublicComm ctx.stepCtx.verifierIndex fpScalars
    in
      { x: F x, y: F y }

  goOldStep
    :: forall nPublic
     . Reflectable nPublic Int
    => StepTestContext
    -> Proxy nPublic
    -> Aff Unit
  goOldStep ctx _ = do
    let
      circuit
        :: forall t
         . CircuitM StepCircuitField (KimchiConstraint StepCircuitField) t Identity
        => Vector nPublic (FVar StepCircuitField)
        -> Snarky (KimchiConstraint StepCircuitField) t Identity (AffinePoint (FVar StepCircuitField))
      circuit inputs =
        let
          pairs =
            unsafePartial fromJust
              $ NEA.fromArray
              $
                Array.zipWith
                  (\scalar base -> { scalar, base })
                  (varToFields @StepCircuitField @(Vector nPublic (F StepCircuitField)) inputs)
                  (ctx.lagrangeComms)
        in
          publicInputCommitment @51 @254 (curveParams (Proxy @Vesta.G)) pairs ctx.blindingH

      solver = makeSolver (Proxy @(KimchiConstraint StepCircuitField)) circuit

      s = compilePure
        (Proxy @(Vector nPublic (F StepCircuitField)))
        (Proxy @(AffinePoint (F StepCircuitField)))
        (Proxy @(KimchiConstraint StepCircuitField))
        circuit
        Kimchi.initialState

      gen = Vector.generator (Proxy @nPublic) fpRangeGen

    circuitSpecPure' 2
      { builtState: s
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied (rustFnStep ctx)
      , postCondition: Kimchi.postCondition
      }
      gen

    liftEffect $ verifyCircuit { s, gen, solver }

  goNewStep
    :: forall nPublic
     . Reflectable nPublic Int
    => StepTestContext
    -> Proxy nPublic
    -> Aff Unit
  goNewStep ctx _ = do
    let
      circuit
        :: forall t
         . CircuitM StepCircuitField (KimchiConstraint StepCircuitField) t Identity
        => Vector nPublic (FVar StepCircuitField)
        -> Snarky (KimchiConstraint StepCircuitField) t Identity (AffinePoint (FVar StepCircuitField))
      circuit inputs =
        publicInputCommit (curveParams (Proxy @Vesta.G)) inputs ctx.lagrangeComms ctx.blindingH

      solver = makeSolver (Proxy @(KimchiConstraint StepCircuitField)) circuit

      s = compilePure
        (Proxy @(Vector nPublic (F StepCircuitField)))
        (Proxy @(AffinePoint (F StepCircuitField)))
        (Proxy @(KimchiConstraint StepCircuitField))
        circuit
        Kimchi.initialState

      gen = Vector.generator (Proxy @nPublic) fpRangeGen

    circuitSpecPure' 2
      { builtState: s
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied (rustFnStep ctx)
      , postCondition: Kimchi.postCondition
      }
      gen

    liftEffect $ verifyCircuit { s, gen, solver }

  -- | Test that PublicInputCommit on the Step public input type (StepStatement)
  -- | matches the Rust ground truth.
  -- | This exercises leaf instances: FVar, SizedF 128, BoolVar, Type2,
  -- | plus Record/Vector walking.
  -- |
  -- | Uses real values from the Step → Wrap → Step test context chain,
  -- | reconstructed via fieldsToValue from step0.publicInputs.
  goStructuredStep :: StepTestContext -> Aff Unit
  goStructuredStep ctx = do
    let
      -- Reconstruct structured type from flat public inputs.
      -- step0.publicInputs is Array StepField (Fp); convert to Fq (lossless, Fp < Fq).
      fqValues :: Array StepCircuitField
      fqValues = map (\x -> fromBigInt (toBigInt x)) ctx.stepCtx.publicInputs

      structuredInput :: StepFullXhat
      structuredInput = fieldsToValue @StepCircuitField fqValues

      circuit
        :: forall t
         . CircuitM StepCircuitField (KimchiConstraint StepCircuitField) t Identity
        => StepFullXhatVar
        -> Snarky (KimchiConstraint StepCircuitField) t Identity (AffinePoint (FVar StepCircuitField))
      circuit inputs =
        publicInputCommit (curveParams (Proxy @Vesta.G)) inputs ctx.lagrangeComms ctx.blindingH

      solver = makeSolver (Proxy @(KimchiConstraint StepCircuitField)) circuit

      s = compilePure
        (Proxy @StepFullXhat)
        (Proxy @(AffinePoint (F StepCircuitField)))
        (Proxy @(KimchiConstraint StepCircuitField))
        circuit
        Kimchi.initialState

      rustFn :: StepFullXhat -> AffinePoint (F StepCircuitField)
      rustFn tup = unsafePartial $
        let
          fpScalars :: Array Pallas.BaseField
          fpScalars = map (\x -> fromBigInt (toBigInt x)) (valueToFields @StepCircuitField tup)
          { x, y } = fromJust $ Array.head $ ProofFFI.pallasPublicComm ctx.stepCtx.verifierIndex fpScalars
        in
          { x: F x, y: F y }

      gen = pure structuredInput

    circuitSpecPure' 1
      { builtState: s
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied rustFn
      , postCondition: Kimchi.postCondition
      }
      gen

  -- Wrap helpers

  mkWrapCtx :: E2E.WrapProofContext -> WrapTestContext
  mkWrapCtx wrap0 =
    { wrapCtx: wrap0
    , lagrangeComms: coerce $ ProofFFI.vestaLagrangeCommitments wrap0.verifierIndex (Array.length wrap0.publicInputs)
    , blindingH: coerce $ ProofFFI.vestaProverIndexBlindingGenerator wrap0.verifierIndex
    }

  -- | Ground truth: Rust proof-systems public_comm for Wrap proof (Vesta SRS).
  -- | Converts Fp scalars to Fq for the Rust FFI (lossless since Fp < Fq).
  rustFnWrap :: forall nPublic. WrapTestContext -> Vector nPublic (F WrapCircuitField) -> AffinePoint (F WrapCircuitField)
  rustFnWrap ctx scalars = unsafePartial $
    let
      -- Wrap public inputs are Fq, but our test scalars are Fp (Step circuit field).
      -- Convert Fp → Fq for the Rust FFI. Lossless since Fp < Fq in Pasta.
      fqScalars :: Array Vesta.BaseField
      fqScalars = map (\(F x) -> fromBigInt (toBigInt x)) (Vector.toUnfoldable scalars)
      { x, y } = fromJust $ Array.head $ ProofFFI.vestaPublicComm ctx.wrapCtx.verifierIndex fqScalars
    in
      { x: F x, y: F y }

  goNewWrap
    :: forall nPublic
     . Reflectable nPublic Int
    => WrapTestContext
    -> Proxy nPublic
    -> Aff Unit
  goNewWrap ctx _ = do
    let
      circuit
        :: forall t
         . CircuitM WrapCircuitField (KimchiConstraint WrapCircuitField) t Identity
        => Vector nPublic (FVar WrapCircuitField)
        -> Snarky (KimchiConstraint WrapCircuitField) t Identity (AffinePoint (FVar WrapCircuitField))
      circuit inputs =
        publicInputCommit (curveParams (Proxy @Pallas.G)) inputs ctx.lagrangeComms ctx.blindingH

      solver = makeSolver (Proxy @(KimchiConstraint WrapCircuitField)) circuit

      s = compilePure
        (Proxy @(Vector nPublic (F WrapCircuitField)))
        (Proxy @(AffinePoint (F WrapCircuitField)))
        (Proxy @(KimchiConstraint WrapCircuitField))
        circuit
        Kimchi.initialState

      gen = Vector.generator (Proxy @nPublic) (arbitrary :: Gen (F WrapCircuitField))

    circuitSpecPure' 2
      { builtState: s
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied (rustFnWrap ctx)
      , postCondition: Kimchi.postCondition
      }
      gen

    liftEffect $ verifyCircuit { s, gen, solver }
