module Test.Pickles.Wrap.SubCircuits (spec) where

-- | Real-data circuit tests for the Wrap-side verifier (IPA checks).
-- | These tests run on Fq (Pallas.ScalarField) and verify portions of the
-- | verifier logic using data derived from a real Schnorr Step proof.

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception.Unsafe (unsafeThrow)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (CheckBulletproofInput, IpaFinalCheckInput)
import Pickles.IPA as IPA
import Pickles.PlonkChecks.Permutation (permScalar)
import Pickles.Sponge (evalPureSpongeM, evalSpongeM, initialSponge, initialSpongeCircuit, liftSnarky)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Types (StepIPARounds, StepStatement)
import Pickles.Verify (IncrementallyVerifyProofInput, incrementallyVerifyProof, verify)
import Pickles.Verify.FqSpongeTranscript as FqSpongeTranscript
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, assert_, coerceViaBits, const_, false_, fieldsToValue, toField)
import Snarky.Circuit.Kimchi (Type1(..), Type2, expandToEndoScalar, fromShifted, groupMapParams, toShifted)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (fromAffine, fromBigInt, generator, pow, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (InductiveTestContext, StepProofContext, WrapIPARounds, buildWrapCircuitParams, coerceStepPlonkChallenges, extractStepRawBpChallenges, mkStepIpaContext, toVectorOrThrow, wrapEndo, zkRows)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied, satisfied_)
import Test.Spec (SpecT, describe, it)
import Type.Proxy (Proxy(..))

-- | In-circuit test for challenge extraction.
-- | Circuit runs over Pallas.ScalarField (Fq) where the sponge operates.
-- | Extracts 128-bit scalar challenges, verifies circuit matches pure sponge,
-- | and validates endo-mapped values match Rust.
extractChallengesCircuitTest :: TestConfig Pallas.ScalarField (KimchiGate Pallas.ScalarField) (AuxState Pallas.ScalarField) -> StepProofContext -> Aff Unit
extractChallengesCircuitTest cfg ctx = do
  let
    { spongeState, challenges: rustChallenges } = mkStepIpaContext ctx

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => Vector StepIPARounds (IPA.LrPair (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (Vector StepIPARounds (SizedF 128 (FVar Pallas.ScalarField)))
    circuit pairs =
      Pickles.Sponge.evalSpongeM (Pickles.Sponge.spongeFromConstants spongeState) do
        _ <- Pickles.Sponge.squeeze -- Squeeze for u first
        IPA.extractScalarChallenges { endo: const_ wrapEndo } pairs

    testFn :: Vector StepIPARounds (IPA.LrPair (F Pallas.ScalarField)) -> Vector StepIPARounds (SizedF 128 (F Pallas.ScalarField))
    testFn pairs =
      let
        challenges :: Vector StepIPARounds (SizedF 128 Pallas.ScalarField)
        challenges = Pickles.Sponge.evalPureSpongeM spongeState do
          _ <- Pickles.Sponge.squeeze
          IPA.extractScalarChallengesPure (coerce pairs)

        endoMappedChallenges :: Array Pallas.BaseField
        endoMappedChallenges = Vector.toUnfoldable $ map
          (\c -> expandToEndoScalar c :: Pallas.BaseField)
          challenges
      in
        if endoMappedChallenges /= Vector.toUnfoldable rustChallenges then unsafeThrow "unexpected endoMappedChallenges"
        else coerce challenges

  void $ circuitTest' @Pallas.ScalarField
    cfg
    (NEA.singleton { testFunction: satisfied testFn, input: Exact (NEA.singleton $ coerce $ toVectorOrThrow @StepIPARounds "pallasProofOpeningLr" $ ProofFFI.pallasProofOpeningLr ctx.proof) })
    circuit

-- | In-circuit test for bullet reduce (lr_prod computation).
-- | Circuit runs over Pallas.ScalarField (Fq) where the L/R points are.
-- | Extracts 128-bit scalar challenges, computes lr_prod, and verifies
-- | result matches Rust FFI.
bulletReduceCircuitTest :: TestConfig Pallas.ScalarField (KimchiGate Pallas.ScalarField) (AuxState Pallas.ScalarField) -> StepProofContext -> Aff Unit
bulletReduceCircuitTest cfg ctx = do
  let
    { spongeState } = mkStepIpaContext ctx

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => Vector StepIPARounds (IPA.LrPair (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (AffinePoint (FVar Pallas.ScalarField))
    circuit pairs =
      Pickles.Sponge.evalSpongeM (Pickles.Sponge.spongeFromConstants spongeState) do
        _ <- Pickles.Sponge.squeeze
        challenges <- IPA.extractScalarChallenges { endo: const_ wrapEndo } pairs
        { p } <- liftSnarky $ IPA.bulletReduceCircuit @Pallas.ScalarField @Vesta.G { pairs, challenges }
        pure p

    testFn :: Vector StepIPARounds (IPA.LrPair (F Pallas.ScalarField)) -> AffinePoint (F Pallas.ScalarField)
    testFn pairs =
      let
        challenges :: Vector StepIPARounds (SizedF 128 Pallas.ScalarField)
        challenges = Pickles.Sponge.evalPureSpongeM spongeState do
          _ <- Pickles.Sponge.squeeze
          IPA.extractScalarChallengesPure (coerce pairs)

        lrProd :: Vesta.G
        lrProd = IPA.bulletReduce @Pallas.ScalarField @Vesta.G { pairs: coerce pairs, challenges }
        computedAffine = unsafePartial $ fromJust $ toAffine lrProd
        expectedLrProd = ProofFFI.pallasProofLrProd ctx.verifierIndex
          { proof: ctx.proof, publicInput: ctx.publicInputs }
      in
        if computedAffine /= expectedLrProd then unsafeThrow "bulletReduce lr_prod doesn't match Rust"
        else coerce computedAffine

  void $ circuitTest' @Pallas.ScalarField
    cfg
    (NEA.singleton { testFunction: satisfied testFn, input: Exact (NEA.singleton $ coerce $ toVectorOrThrow @StepIPARounds "pallasProofOpeningLr" $ ProofFFI.pallasProofOpeningLr ctx.proof) })
    circuit

-- | In-circuit test for IPA final check.
-- | Tests the full IPA verification equation: c*Q + delta = z1*(sg + b*u) + z2*H
ipaFinalCheckCircuitTest :: TestConfig Pallas.ScalarField (KimchiGate Pallas.ScalarField) (AuxState Pallas.ScalarField) -> StepProofContext -> Aff Unit
ipaFinalCheckCircuitTest cfg ctx = do
  let
    { challenges, spongeState, combinedPolynomial, omega } = mkStepIpaContext ctx

    circuitInput :: IpaFinalCheckInput StepIPARounds (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
      , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
      , lr: coerce $ toVectorOrThrow @StepIPARounds "pallasProofOpeningLr" $ ProofFFI.pallasProofOpeningLr ctx.proof
      , z1: toShifted $ F $ ProofFFI.pallasProofOpeningZ1 ctx.proof
      , z2: toShifted $ F $ ProofFFI.pallasProofOpeningZ2 ctx.proof
      , combinedPolynomial: coerce combinedPolynomial
      , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
      , b: toShifted $ F $ ProofFFI.computeB0
          { challenges: Vector.toUnfoldable challenges
          , zeta: ctx.oracles.zeta
          , zetaOmega: ctx.oracles.zeta * omega
          , evalscale: ctx.oracles.u
          }
      , blindingGenerator: coerce $ ProofFFI.pallasProverIndexBlindingGenerator ctx.verifierIndex
      }

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => IpaFinalCheckInput StepIPARounds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
    circuit input = do
      { success } <- evalSpongeM (Pickles.Sponge.spongeFromConstants spongeState) $
        IPA.ipaFinalCheckCircuit @Pallas.ScalarField @Vesta.G
          IPA.type1ScalarOps
          { endo: const_ wrapEndo, groupMapParams: groupMapParams $ Proxy @Vesta.G }
          input
      assert_ success

  void $ circuitTest' @Pallas.ScalarField
    cfg
    (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton circuitInput) })
    circuit

-- | Debug verification test: prints intermediate IPA values to stderr.
-- | Also tests scaleFast1 with z1 and the generator point.
debugVerifyTest :: TestConfig Pallas.ScalarField (KimchiGate Pallas.ScalarField) (AuxState Pallas.ScalarField) -> StepProofContext -> Aff Unit
debugVerifyTest cfg ctx = do
  let
    _ = ProofFFI.pallasDebugVerify ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    z1Raw = ProofFFI.pallasProofOpeningZ1 ctx.proof

    z1Shifted :: Type1 (F Pallas.ScalarField)
    z1Shifted = toShifted (F z1Raw)

    z1Recovered :: F Pallas.BaseField
    z1Recovered = fromShifted z1Shifted

    genPoint = unsafePartial fromJust $ toAffine (generator @_ @Vesta.G)
    expectedAffine = unsafePartial fromJust $ toAffine $ scalarMul z1Raw (generator @_ @Vesta.G)

  liftEffect do
    log $ "z1Raw from FFI: " <> show z1Raw
    log $ "z1Shifted (Type1 t): " <> show z1Shifted
    log $ "z1Recovered (fromShifted): " <> show z1Recovered
    log $ "Roundtrip matches: " <> show (F z1Raw == z1Recovered)
    log $ "Expected z1*G: (" <> show expectedAffine.x <> ", " <> show expectedAffine.y <> ")"

  let
    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => Tuple (AffinePoint (FVar Pallas.ScalarField)) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (AffinePoint (FVar Pallas.ScalarField))
    circuit (Tuple p t) = IPA.type1ScalarOps.scaleByShifted p t

    testFn
      :: Tuple (AffinePoint (F Pallas.ScalarField)) (Type1 (F Pallas.ScalarField))
      -> AffinePoint (F Pallas.ScalarField)
    testFn (Tuple p scalar_) =
      let
        scalar :: Pallas.BaseField
        scalar = case fromShifted scalar_ of F a -> a
      in
        coerce $ unsafePartial fromJust $ toAffine @Pallas.ScalarField $
          scalarMul scalar (fromAffine @Pallas.ScalarField @Vesta.G (coerce p))

  void $ circuitTest' @Pallas.ScalarField
    cfg
    (NEA.singleton { testFunction: satisfied testFn, input: Exact (NEA.singleton $ Tuple (coerce genPoint) z1Shifted) })
    circuit

  liftEffect $ log "scaleFast1 mini test passed!"

-- | Full bulletproof check test: composes sponge transcript → checkBulletproof.
-- | Tests the "right half" of incrementallyVerifyProof.
checkBulletproofTest :: TestConfig Pallas.ScalarField (KimchiGate Pallas.ScalarField) (AuxState Pallas.ScalarField) -> StepProofContext -> Aff Unit
checkBulletproofTest cfg ctx = do
  let
    commitments = ProofFFI.pallasProofCommitments ctx.proof
    publicComm = unsafePartial fromJust $ Array.head $
      ProofFFI.pallasPublicComm ctx.verifierIndex ctx.publicInputs
    ftComm = ProofFFI.pallasFtComm ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }
    columnCommsRaw = ProofFFI.pallasVerifierIndexColumnComms ctx.verifierIndex

    indexComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    indexComms = unsafePartial fromJust $ Vector.toVector $ Array.take 6 columnCommsRaw

    coeffComms :: Vector 15 (AffinePoint Pallas.ScalarField)
    coeffComms = unsafePartial fromJust $ Vector.toVector $ Array.take 15 $ Array.drop 6 columnCommsRaw

    sigmaComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    sigmaComms = unsafePartial fromJust $ Vector.toVector $ Array.drop 21 columnCommsRaw

    -- Assemble all 45 commitment bases in to_batch order (as circuit variables)
    allBases :: Vector 45 (AffinePoint (FVar Pallas.ScalarField))
    allBases = map constPt $
      (publicComm :< ftComm :< commitments.zComm :< Vector.nil)
        `Vector.append` indexComms
        `Vector.append` commitments.wComm
        `Vector.append` coeffComms
        `Vector.append` sigmaComms

    -- xi from oracles (convert from Fp to Fq representation)
    xiChalFq :: SizedF 128 Pallas.ScalarField
    xiChalFq = coerceViaBits ctx.oracles.vChal

    omega = ProofFFI.domainGenerator ctx.domainLog2

    -- Sponge input for transcript (constant data)
    spongeInput :: FqSpongeTranscript.FqSpongeInput 0 7 Pallas.ScalarField
    spongeInput =
      { indexDigest: ProofFFI.pallasVerifierIndexDigest ctx.verifierIndex
      , sgOld: Vector.nil
      , publicComm
      , wComm: commitments.wComm
      , zComm: commitments.zComm
      , tComm: unsafePartial fromJust $ Vector.toVector @7 commitments.tComm
      }

    -- Convert sponge input to circuit constants
    constPt :: AffinePoint Pallas.ScalarField -> AffinePoint (FVar Pallas.ScalarField)
    constPt { x, y } = { x: const_ x, y: const_ y }

    spongeInputCircuit :: FqSpongeTranscript.FqSpongeInput 0 7 (FVar Pallas.ScalarField)
    spongeInputCircuit =
      { indexDigest: const_ spongeInput.indexDigest
      , sgOld: Vector.nil
      , publicComm: constPt spongeInput.publicComm
      , wComm: map constPt spongeInput.wComm
      , zComm: constPt spongeInput.zComm
      , tComm: map constPt spongeInput.tComm
      }

    -- Rust ground truth for bulletproof challenges
    rustChallenges :: Vector StepIPARounds Vesta.ScalarField
    rustChallenges = unsafePartial fromJust $ Vector.toVector $
      ProofFFI.proofBulletproofChallenges ctx.verifierIndex
        { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Build circuit input for checkBulletproof
    circuitInput :: CheckBulletproofInput StepIPARounds (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { xi: coerce xiChalFq
      , delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
      , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
      , lr: coerce $ toVectorOrThrow @StepIPARounds "pallasProofOpeningLr" $ ProofFFI.pallasProofOpeningLr ctx.proof
      , z1: toShifted $ F $ ProofFFI.pallasProofOpeningZ1 ctx.proof
      , z2: toShifted $ F $ ProofFFI.pallasProofOpeningZ2 ctx.proof
      , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
      , b: toShifted $ F $ ProofFFI.computeB0
          { challenges: Vector.toUnfoldable rustChallenges
          , zeta: ctx.oracles.zeta
          , zetaOmega: ctx.oracles.zeta * omega
          , evalscale: ctx.oracles.u
          }
      , blindingGenerator: coerce $ ProofFFI.pallasProverIndexBlindingGenerator ctx.verifierIndex
      }

    -- Circuit returns extracted challenges (for validation against Rust)
    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => CheckBulletproofInput StepIPARounds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (Vector StepIPARounds (SizedF 128 (FVar Pallas.ScalarField)))
    circuit input = do
      let endoParams = { endo: const_ wrapEndo, groupMapParams: groupMapParams $ Proxy @Vesta.G }
      { success, challenges } <- evalSpongeM initialSpongeCircuit do
        _ <- FqSpongeTranscript.spongeTranscriptCircuit endoParams spongeInputCircuit
        IPA.checkBulletproof @Pallas.ScalarField @Vesta.G
          IPA.type1ScalarOps
          endoParams
          allBases
          input
      assert_ success
      pure challenges

    -- Pure test function: replays sponge, extracts challenges, validates against Rust FFI
    testFn
      :: CheckBulletproofInput StepIPARounds (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
      -> Vector StepIPARounds (SizedF 128 (F Pallas.ScalarField))
    testFn input =
      let
        -- Run pure sponge: transcript → absorb CIP → squeeze u → extract challenges
        challenges :: Vector StepIPARounds (SizedF 128 Pallas.ScalarField)
        challenges = evalPureSpongeM initialSponge do
          _ <- FqSpongeTranscript.spongeTranscriptPure spongeInput
          -- Absorb CIP (same as checkBulletproof does)
          let Type1 (F cipField) = input.combinedInnerProduct
          Pickles.Sponge.absorb cipField
          -- Squeeze for u (consumed by ipaFinalCheckCircuit)
          _ <- Pickles.Sponge.squeeze
          -- Extract scalar challenges from LR pairs
          IPA.extractScalarChallengesPure (coerce input.lr)

        -- Endo-expand to full field elements and validate against Rust
        endoMapped :: Array Pallas.BaseField
        endoMapped = Vector.toUnfoldable $ map
          (\c -> expandToEndoScalar c :: Pallas.BaseField)
          challenges

        -- Verify challenge polynomial commitment matches proof sg
        computedSg = ProofFFI.pallasChallengePolyCommitment ctx.verifierIndex endoMapped
        expectedSg = ProofFFI.pallasProofOpeningSg ctx.proof
      in
        if endoMapped /= Vector.toUnfoldable rustChallenges then unsafeThrow "checkBulletproof: extracted challenges don't match Rust"
        else if computedSg /= expectedSg then unsafeThrow "checkBulletproof: challenge poly commitment doesn't match proof sg"
        else coerce challenges

  void $ circuitTest' @Pallas.ScalarField
    cfg
    (NEA.singleton { testFunction: satisfied testFn, input: Exact (NEA.singleton circuitInput) })
    circuit

-------------------------------------------------------------------------------
-- | incrementallyVerifyProof test
-------------------------------------------------------------------------------

-- | Structural public input type for the Step circuit (value level, in Fq).
-- | Now just StepStatement (the Step circuit's public input no longer includes StepInput).
type StepPublicInput =
  StepStatement 1 StepIPARounds WrapIPARounds (F Pallas.ScalarField) (Type2 (F Pallas.ScalarField) Boolean) Boolean

-- | Structural public input type for the Step circuit (variable level, in Fq).
-- | CircuitType maps: F f → FVar f, Boolean → BoolVar f, Type2 (F f) Boolean → Type2 (FVar f) (BoolVar f)
type StepPublicInputVar =
  StepStatement 1 StepIPARounds WrapIPARounds (FVar Pallas.ScalarField) (Type2 (FVar Pallas.ScalarField) (BoolVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField)

-- | Build the structural public input from a StepProofContext's flat field array.
buildStepPublicInput :: StepProofContext -> StepPublicInput
buildStepPublicInput ctx = fieldsToValue @Pallas.ScalarField
  (map (\fp -> fromBigInt (toBigInt fp) :: Pallas.ScalarField) ctx.publicInputs)

-- | Full incrementallyVerifyProof circuit test.
-- | Wires together publicInputCommitment, sponge transcript, ftComm, and
-- | checkBulletproof in a single circuit and verifies satisfiability.
incrementallyVerifyProofTest :: TestConfig Pallas.ScalarField (KimchiGate Pallas.ScalarField) (AuxState Pallas.ScalarField) -> StepProofContext -> Aff Unit
incrementallyVerifyProofTest cfg ctx = do
  let
    params = buildWrapCircuitParams ctx
    commitments = ProofFFI.pallasProofCommitments ctx.proof

    -- Compute deferred values from oracles
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    maxPolySize = ProofFFI.pallasVerifierIndexMaxPolySize ctx.verifierIndex
    omega = ProofFFI.domainGenerator ctx.domainLog2

    -- Perm scalar (pure, using expanded plonk values from oracles)
    zetaToNMinus1 = pow ctx.oracles.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)
    permInput =
      { w: map _.zeta (Vector.take @7 (ProofFFI.proofWitnessEvals ctx.proof))
      , sigma: map _.zeta (ProofFFI.proofSigmaEvals ctx.proof)
      , z: ProofFFI.proofZEvals ctx.proof
      , shifts: ProofFFI.proverIndexShifts ctx.proverIndex
      , alpha: ctx.oracles.alpha
      , beta: toField ctx.oracles.beta
      , gamma: toField ctx.oracles.gamma
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: ctx.oracles.zeta
      }
    perm = permScalar permInput

    -- b value from FFI
    { challenges: rustChallenges } = mkStepIpaContext ctx
    bValue = ProofFFI.computeB0
      { challenges: Vector.toUnfoldable rustChallenges
      , zeta: ctx.oracles.zeta
      , zetaOmega: ctx.oracles.zeta * omega
      , evalscale: ctx.oracles.u
      }

    -- Bulletproof challenges (raw 128-bit from IPA sponge, coerced to Fq)
    bulletproofChallenges :: Vector StepIPARounds (SizedF 128 (F Pallas.ScalarField))
    bulletproofChallenges = coerce (extractStepRawBpChallenges ctx)

    -- Xi challenge in Fq (coerced from Fp)
    xiChalFq :: SizedF 128 (F Pallas.ScalarField)
    xiChalFq = coerce (coerceViaBits ctx.oracles.vChal :: SizedF 128 Pallas.ScalarField)

    -- Build circuit input
    tComm :: Vector 7 (AffinePoint (F Pallas.ScalarField))
    tComm = unsafePartial fromJust $ Vector.toVector @7 $ coerce commitments.tComm

    circuitInput :: IncrementallyVerifyProofInput StepPublicInput 0 StepIPARounds (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { publicInput: buildStepPublicInput ctx
      , sgOld: Vector.nil
      , deferredValues:
          let
            stepPlonk = coerceStepPlonkChallenges ctx
          in
            { plonk:
                { alpha: stepPlonk.alpha
                , beta: stepPlonk.beta
                , gamma: stepPlonk.gamma
                , zeta: stepPlonk.zeta
                , perm: toShifted $ F perm
                , zetaToSrsLength: toShifted $ F (pow ctx.oracles.zeta (BigInt.fromInt maxPolySize))
                , zetaToDomainSize: toShifted $ F (pow ctx.oracles.zeta n)
                }
            , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
            , xi: xiChalFq
            , bulletproofChallenges
            , b: toShifted $ F bValue
            }
      , wComm: coerce commitments.wComm
      , zComm: coerce commitments.zComm
      , tComm
      , opening:
          { delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
          , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
          , lr: coerce $ toVectorOrThrow @StepIPARounds "pallasProofOpeningLr" $ ProofFFI.pallasProofOpeningLr ctx.proof
          , z1: toShifted $ F $ ProofFFI.pallasProofOpeningZ1 ctx.proof
          , z2: toShifted $ F $ ProofFFI.pallasProofOpeningZ2 ctx.proof
          }
      }

    circuit
      :: forall t
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t Identity
      => IncrementallyVerifyProofInput StepPublicInputVar 0 StepIPARounds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t Identity Unit
    circuit input = do
      { success } <- evalSpongeM initialSpongeCircuit $
        incrementallyVerifyProof @Vesta.G
          IPA.type1ScalarOps
          params
          input
      assert_ success

  void $ circuitTest' @Pallas.ScalarField
    cfg
    (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton circuitInput) })
    circuit

-------------------------------------------------------------------------------
-- | verify test
-------------------------------------------------------------------------------

-- | Full verify circuit test.
-- | Wraps incrementallyVerifyProof with digest and challenge assertions.
verifyTest :: TestConfig Pallas.ScalarField (KimchiGate Pallas.ScalarField) (AuxState Pallas.ScalarField) -> StepProofContext -> Aff Unit
verifyTest cfg ctx = do
  let
    params = buildWrapCircuitParams ctx
    commitments = ProofFFI.pallasProofCommitments ctx.proof

    -- Compute deferred values from oracles
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    maxPolySize = ProofFFI.pallasVerifierIndexMaxPolySize ctx.verifierIndex
    omega = ProofFFI.domainGenerator ctx.domainLog2

    -- Perm scalar (pure, using expanded plonk values from oracles)
    zetaToNMinus1 = pow ctx.oracles.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)
    permInput =
      { w: map _.zeta (Vector.take @7 (ProofFFI.proofWitnessEvals ctx.proof))
      , sigma: map _.zeta (ProofFFI.proofSigmaEvals ctx.proof)
      , z: ProofFFI.proofZEvals ctx.proof
      , shifts: ProofFFI.proverIndexShifts ctx.proverIndex
      , alpha: ctx.oracles.alpha
      , beta: toField ctx.oracles.beta
      , gamma: toField ctx.oracles.gamma
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: ctx.oracles.zeta
      }
    perm = permScalar permInput

    -- b value from FFI
    { challenges: rustChallenges } = mkStepIpaContext ctx
    bValue = ProofFFI.computeB0
      { challenges: Vector.toUnfoldable rustChallenges
      , zeta: ctx.oracles.zeta
      , zetaOmega: ctx.oracles.zeta * omega
      , evalscale: ctx.oracles.u
      }

    -- Bulletproof challenges (raw 128-bit from IPA sponge, coerced to Fq)
    bulletproofChallenges :: Vector StepIPARounds (SizedF 128 (F Pallas.ScalarField))
    bulletproofChallenges = coerce (extractStepRawBpChallenges ctx)

    -- Xi challenge in Fq (coerced from Fp)
    xiChalFq :: SizedF 128 (F Pallas.ScalarField)
    xiChalFq = coerce (coerceViaBits ctx.oracles.vChal :: SizedF 128 Pallas.ScalarField)

    -- Build circuit input
    tComm :: Vector 7 (AffinePoint (F Pallas.ScalarField))
    tComm = unsafePartial fromJust $ Vector.toVector @7 $ coerce commitments.tComm

    circuitInput :: IncrementallyVerifyProofInput StepPublicInput 0 StepIPARounds (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { publicInput: buildStepPublicInput ctx
      , sgOld: Vector.nil
      , deferredValues:
          let
            stepPlonk = coerceStepPlonkChallenges ctx
          in
            { plonk:
                { alpha: stepPlonk.alpha
                , beta: stepPlonk.beta
                , gamma: stepPlonk.gamma
                , zeta: stepPlonk.zeta
                , perm: toShifted $ F perm
                , zetaToSrsLength: toShifted $ F (pow ctx.oracles.zeta (BigInt.fromInt maxPolySize))
                , zetaToDomainSize: toShifted $ F (pow ctx.oracles.zeta n)
                }
            , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
            , xi: xiChalFq
            , bulletproofChallenges
            , b: toShifted $ F bValue
            }
      , wComm: coerce commitments.wComm
      , zComm: coerce commitments.zComm
      , tComm
      , opening:
          { delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
          , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
          , lr: coerce $ toVectorOrThrow @StepIPARounds "pallasProofOpeningLr" $ ProofFFI.pallasProofOpeningLr ctx.proof
          , z1: toShifted $ F $ ProofFFI.pallasProofOpeningZ1 ctx.proof
          , z2: toShifted $ F $ ProofFFI.pallasProofOpeningZ2 ctx.proof
          }
      }

    -- Claimed sponge digest: coerce from Vesta.ScalarField to Pallas.ScalarField
    claimedDigestFq :: Pallas.ScalarField
    claimedDigestFq = fromBigInt (toBigInt ctx.oracles.fqDigest)

    circuit
      :: forall t
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t Identity
      => IncrementallyVerifyProofInput StepPublicInputVar 0 StepIPARounds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t Identity Unit
    circuit input = do
      success <- evalSpongeM initialSpongeCircuit $
        verify @Vesta.G
          IPA.type1ScalarOps
          params
          input
          false_ -- isBaseCase (real proof, not base case)
          (const_ claimedDigestFq)
      assert_ success

  void $ circuitTest' @Pallas.ScalarField
    cfg
    (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton circuitInput) })
    circuit

spec :: TestConfig Pallas.ScalarField (KimchiGate Pallas.ScalarField) (AuxState Pallas.ScalarField) -> SpecT Aff InductiveTestContext Aff Unit
spec cfg =
  describe "Wrap Sub-circuits (Real Data)" do
    it "extractScalarChallenges circuit matches pure and Rust" \{ step0 } -> extractChallengesCircuitTest cfg step0
    it "bulletReduceCircuit matches Rust lr_prod" \{ step0 } -> bulletReduceCircuitTest cfg step0
    it "debug verify traces intermediate IPA values" \{ step0 } -> debugVerifyTest cfg step0
    it "ipaFinalCheckCircuit verifies with Rust proof values" \{ step0 } -> ipaFinalCheckCircuitTest cfg step0
    it "checkBulletproof composes transcript and IPA verification" \{ step0 } -> checkBulletproofTest cfg step0
    it "incrementallyVerifyProof wires all components together" \{ step0 } -> incrementallyVerifyProofTest cfg step0
    it "verify wires IVP + deferred value assertions" \{ step0 } -> verifyTest cfg step0
