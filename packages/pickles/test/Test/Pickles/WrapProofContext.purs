module Test.Pickles.WrapProofContext
  ( createWrapProofContext
  , mkWrapIpaContext
  ) where

-- | Real-data generation for the Wrap-side verifier.
-- | Drives the Step verifier tests with real proofs from the wrapCircuit.

import Prelude

import Data.Array as Array
import Data.Fin (unsafeFinite)
import Data.Identity (Identity)
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Exception.Unsafe (unsafeThrow)
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (type1ScalarOps)
import Pickles.Sponge (evalPureSpongeM, initialSponge, runPureSpongeM)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams)
import Pickles.Verify.FqSpongeTranscript (FqSpongeInput, spongeTranscriptPure)
import Pickles.Wrap.Circuit (wrapCircuit)
import RandomOracle.Sponge as RandomOracle
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (Type1, Type2(..), toShifted)
import Snarky.Circuit.Kimchi as Kimchi
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (fromBigInt, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (IPAContext', StepProofContext, WrapProofContext, createStepProofContext, createTestContext')
import Test.Pickles.WrapInputBuilder (WrapCircuitInput, WrapCircuitParams, buildWrapCircuitInput, buildWrapCircuitParams, buildWrapClaimedDigest)
import Type.Proxy (Proxy(..))

-- | Create a Wrap test context (Pallas proof verifying Vesta Step proof).
-- | Padded to domain 2^15 to match Pickles Wrap conventions.
createWrapProofContext :: Aff WrapProofContext
createWrapProofContext = do
  -- 1. Create a real Step proof first
  stepCtx <- createStepProofContext

  -- 2. Transform Step proof data into Wrap circuit inputs
  let
    params :: WrapCircuitParams
    params = buildWrapCircuitParams stepCtx

    input :: WrapCircuitInput
    input = buildWrapCircuitInput stepCtx

    claimedDigest :: Pallas.ScalarField
    claimedDigest = buildWrapClaimedDigest stepCtx

    -- Define the specialized wrap circuit for this proof
    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => IncrementallyVerifyProofInput 9 0 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
    circuit inVar =
      wrapCircuit
        type1ScalarOps
        (Kimchi.groupMapParams (Proxy @Vesta.G))
        params
        claimedDigest
        inVar

  -- 3. Run the wrap circuit to produce an Fq proof
  let
    solver :: Solver Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) WrapCircuitInput Unit
    solver = makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit

  createTestContext'
    { builtState: compilePure
        (Proxy @WrapCircuitInput)
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        KimchiConstraint.initialState
    , solver
    , input
    , targetDomainLog2: 15
    }

mkWrapIpaContext :: WrapProofContext -> IPAContext' Pallas.ScalarField Vesta.ScalarField
mkWrapIpaContext ctx =
  let
    commitments = ProofFFI.vestaProofCommitments ctx.proof
    publicCommArray = ProofFFI.vestaPublicComm ctx.verifierIndex ctx.publicInputs

    spongeInput :: FqSpongeInput 0 7 Vesta.ScalarField
    spongeInput =
      { indexDigest: ProofFFI.vestaVerifierIndexDigest ctx.verifierIndex
      , sgOld: Vector.nil
      , publicComm: unsafePartial fromJust $ Array.head publicCommArray
      , wComm: commitments.wComm
      , zComm: commitments.zComm
      , tComm: unsafePartial fromJust $ Vector.toVector @7 commitments.tComm
      }

    -- Run sponge transcript, then absorb shift_scalar(CIP)
    Tuple _ computedSponge = runPureSpongeM initialSponge do
      _ <- spongeTranscriptPure spongeInput
      let Type2 { sDiv2: F d, sOdd } = toShifted (F ctx.oracles.combinedInnerProduct) :: Type2 (F Vesta.ScalarField) Boolean
      Pickles.Sponge.absorb d
      Pickles.Sponge.absorb (if sOdd then one else zero)
      pure unit

    ffiSponge =
      let
        -- Get sponge checkpoint (state before L/R processing)
        checkpoint = ProofFFI.vestaSpongeCheckpointBeforeChallenges ctx.verifierIndex
          { proof: ctx.proof, publicInput: ctx.publicInputs }

        -- Parse checkpoint into sponge state
        spongeMode = case checkpoint.spongeMode of
          "Absorbed" -> RandomOracle.Absorbed (unsafeFinite checkpoint.modeCount)
          _ -> RandomOracle.Squeezed (unsafeFinite checkpoint.modeCount)
      in
        { state: checkpoint.state, spongeState: spongeMode }
  in
    if ffiSponge /= computedSponge then unsafeThrow "Mismatch between ffiSponge and computedSponge" -- Fail early if mismatch
    else
      let
        combinedPolynomial :: AffinePoint Vesta.ScalarField
        combinedPolynomial = ProofFFI.vestaCombinedPolynomialCommitment ctx.verifierIndex
          { proof: ctx.proof, publicInput: ctx.publicInputs }

        challengesArray = ProofFFI.proofBulletproofChallenges ctx.verifierIndex
          { proof: ctx.proof, publicInput: ctx.publicInputs }
        omega = ProofFFI.domainGenerator ctx.domainLog2
      in
        { challenges: unsafePartial $ fromJust $ Vector.toVector @16 challengesArray
        , spongeState: computedSponge
        , combinedPolynomial
        , omega
        }
