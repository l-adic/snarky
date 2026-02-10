module Test.Pickles.Wrap.SubCircuits (spec) where

-- | Real-data circuit tests for the Wrap-side verifier (IPA checks).
-- | These tests run on Fq (Pallas.ScalarField) and verify portions of the
-- | verifier logic using data derived from a real Schnorr Step proof.

import Prelude

import Data.Array as Array
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
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams, incrementallyVerifyProof, verify)
import Pickles.Verify.FqSpongeTranscript (spongeTranscriptCircuit, spongeTranscriptPure)
import RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, SizedF, Snarky, assert_, coerceViaBits, const_, false_, toField, wrapF)
import Snarky.Circuit.Kimchi (Type1, Type1(..), expandToEndoScalar, groupMapParams, toShifted)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams, fromAffine, fromBigInt, generator, pow, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (VestaTestContext, createVestaTestContext, mkIpaTestContext, zkRows)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied, satisfied_)
import Test.Spec (SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))

-- | In-circuit test for challenge extraction.
-- | Circuit runs over Pallas.ScalarField (Fq) where the sponge operates.
-- | Extracts 128-bit scalar challenges, verifies circuit matches pure sponge,
-- | and validates endo-mapped values match Rust.
extractChallengesCircuitTest :: VestaTestContext -> Aff Unit
extractChallengesCircuitTest ctx = do
  let
    { spongeState, challenges: rustChallenges } = mkIpaTestContext ctx

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => Vector 16 (IPA.LrPair (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (Vector 16 (SizedF 128 (FVar Pallas.ScalarField)))
    circuit pairs =
      Pickles.Sponge.evalSpongeM (Pickles.Sponge.spongeFromConstants spongeState) do
        _ <- Pickles.Sponge.squeeze -- Squeeze for u first
        IPA.extractScalarChallenges pairs

    testFn :: Vector 16 (IPA.LrPair (F Pallas.ScalarField)) -> Vector 16 (SizedF 128 (F Pallas.ScalarField))
    testFn pairs =
      let
        challenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
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

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(Vector 16 (IPA.LrPair (F Pallas.ScalarField))))
        (Proxy @(Vector 16 (SizedF 128 (F Pallas.ScalarField))))
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied testFn
    , postCondition: Kimchi.postCondition
    }
    [ coerce $ ProofFFI.pallasProofOpeningLr ctx.proof ]

-- | In-circuit test for bullet reduce (lr_prod computation).
-- | Circuit runs over Pallas.ScalarField (Fq) where the L/R points are.
-- | Extracts 128-bit scalar challenges, computes lr_prod, and verifies
-- | result matches Rust FFI.
bulletReduceCircuitTest :: VestaTestContext -> Aff Unit
bulletReduceCircuitTest ctx = do
  let
    { spongeState } = mkIpaTestContext ctx

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => Vector 16 (IPA.LrPair (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (AffinePoint (FVar Pallas.ScalarField))
    circuit pairs =
      Pickles.Sponge.evalSpongeM (Pickles.Sponge.spongeFromConstants spongeState) do
        _ <- Pickles.Sponge.squeeze
        challenges <- IPA.extractScalarChallenges pairs
        { p } <- liftSnarky $ IPA.bulletReduceCircuit @Pallas.ScalarField @Vesta.G { pairs, challenges }
        pure p

    testFn :: Vector 16 (IPA.LrPair (F Pallas.ScalarField)) -> AffinePoint (F Pallas.ScalarField)
    testFn pairs =
      let
        challenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
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

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(Vector 16 (IPA.LrPair (F Pallas.ScalarField))))
        (Proxy @(AffinePoint (F Pallas.ScalarField)))
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied testFn
    , postCondition: Kimchi.postCondition
    }
    [ coerce $ ProofFFI.pallasProofOpeningLr ctx.proof ]

-- | In-circuit test for IPA final check.
-- | Tests the full IPA verification equation: c*Q + delta = z1*(sg + b*u) + z2*H
ipaFinalCheckCircuitTest :: VestaTestContext -> Aff Unit
ipaFinalCheckCircuitTest ctx = do
  let
    { challenges, spongeState, combinedPolynomial, omega } = mkIpaTestContext ctx

    circuitInput :: IpaFinalCheckInput 16 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
      , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
      , lr: coerce $ ProofFFI.pallasProofOpeningLr ctx.proof
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
      => IpaFinalCheckInput 16 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
    circuit input = do
      { success } <- evalSpongeM (Pickles.Sponge.spongeFromConstants spongeState) $
        IPA.ipaFinalCheckCircuit @Pallas.ScalarField @Vesta.G
          IPA.type1ScalarOps
          (groupMapParams $ Proxy @Vesta.G)
          input
      assert_ success

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(IpaFinalCheckInput 16 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-- | Debug verification test: prints intermediate IPA values to stderr.
-- | Also tests scaleFast1 with z1 and the generator point.
debugVerifyTest :: VestaTestContext -> Aff Unit
debugVerifyTest ctx = do
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

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(Tuple (AffinePoint (F Pallas.ScalarField)) (Type1 (F Pallas.ScalarField))))
        (Proxy @(AffinePoint (F Pallas.ScalarField)))
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied testFn
    , postCondition: Kimchi.postCondition
    }
    [ Tuple (coerce genPoint) z1Shifted ]

  liftEffect $ log "scaleFast1 mini test passed!"

-- | Full bulletproof check test: composes sponge transcript → checkBulletproof.
-- | Tests the "right half" of incrementallyVerifyProof.
checkBulletproofTest :: VestaTestContext -> Aff Unit
checkBulletproofTest ctx = do
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
    spongeInput :: Pickles.Verify.FqSpongeTranscript.FqSpongeInput 0 7 Pallas.ScalarField
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

    spongeInputCircuit :: Pickles.Verify.FqSpongeTranscript.FqSpongeInput 0 7 (FVar Pallas.ScalarField)
    spongeInputCircuit =
      { indexDigest: const_ spongeInput.indexDigest
      , sgOld: Vector.nil
      , publicComm: constPt spongeInput.publicComm
      , wComm: map constPt spongeInput.wComm
      , zComm: constPt spongeInput.zComm
      , tComm: map constPt spongeInput.tComm
      }

    -- Rust ground truth for bulletproof challenges
    rustChallenges :: Vector 16 Vesta.ScalarField
    rustChallenges = unsafePartial fromJust $ Vector.toVector $
      ProofFFI.proofBulletproofChallenges ctx.verifierIndex
        { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Build circuit input for checkBulletproof
    circuitInput :: CheckBulletproofInput 16 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { xi: coerce xiChalFq
      , delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
      , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
      , lr: coerce $ ProofFFI.pallasProofOpeningLr ctx.proof
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
      => CheckBulletproofInput 16 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (Vector 16 (SizedF 128 (FVar Pallas.ScalarField)))
    circuit input = do
      { success, challenges } <- evalSpongeM initialSpongeCircuit do
        _ <- Pickles.Verify.FqSpongeTranscript.spongeTranscriptCircuit spongeInputCircuit
        IPA.checkBulletproof @Pallas.ScalarField @Vesta.G
          IPA.type1ScalarOps
          (groupMapParams $ Proxy @Vesta.G)
          allBases
          input
      assert_ success
      pure challenges

    -- Pure test function: replays sponge, extracts challenges, validates against Rust FFI
    testFn
      :: CheckBulletproofInput 16 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
      -> Vector 16 (SizedF 128 (F Pallas.ScalarField))
    testFn input =
      let
        -- Run pure sponge: transcript → absorb CIP → squeeze u → extract challenges
        challenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
        challenges = evalPureSpongeM initialSponge do
          _ <- Pickles.Verify.FqSpongeTranscript.spongeTranscriptPure spongeInput
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

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(CheckBulletproofInput 16 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))))
        (Proxy @(Vector 16 (SizedF 128 (F Pallas.ScalarField))))
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied testFn
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-------------------------------------------------------------------------------
-- | incrementallyVerifyProof test
-------------------------------------------------------------------------------

-- | Full incrementallyVerifyProof circuit test.
-- | Wires together publicInputCommitment, sponge transcript, ftComm, and
-- | checkBulletproof in a single circuit and verifies satisfiability.
incrementallyVerifyProofTest :: VestaTestContext -> Aff Unit
incrementallyVerifyProofTest ctx = do
  let
    commitments = ProofFFI.pallasProofCommitments ctx.proof
    numPublic = Array.length ctx.publicInputs
    columnCommsRaw = ProofFFI.pallasVerifierIndexColumnComms ctx.verifierIndex

    indexComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    indexComms = unsafePartial fromJust $ Vector.toVector $ Array.take 6 columnCommsRaw

    coeffComms :: Vector 15 (AffinePoint Pallas.ScalarField)
    coeffComms = unsafePartial fromJust $ Vector.toVector $ Array.take 15 $ Array.drop 6 columnCommsRaw

    sigmaComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    sigmaComms = unsafePartial fromJust $ Vector.toVector $ Array.drop 21 columnCommsRaw

    -- Build params (compile-time constants)
    params :: IncrementallyVerifyProofParams 9 Pallas.ScalarField
    params =
      { curveParams: curveParams (Proxy @Vesta.G)
      , lagrangeComms: unsafePartial fromJust $ Vector.toVector $
          coerce (ProofFFI.pallasLagrangeCommitments ctx.verifierIndex numPublic)
      , blindingH: coerce $ ProofFFI.pallasProverIndexBlindingGenerator ctx.verifierIndex
      , sigmaCommLast: coerce $ ProofFFI.pallasSigmaCommLast ctx.verifierIndex
      , columnComms:
          { index: coerce indexComms
          , coeff: coerce coeffComms
          , sigma: coerce sigmaComms
          }
      , indexDigest: ProofFFI.pallasVerifierIndexDigest ctx.verifierIndex
      }

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
    { challenges: rustChallenges } = mkIpaTestContext ctx
    bValue = ProofFFI.computeB0
      { challenges: Vector.toUnfoldable rustChallenges
      , zeta: ctx.oracles.zeta
      , zetaOmega: ctx.oracles.zeta * omega
      , evalscale: ctx.oracles.u
      }

    -- Bulletproof challenges (raw 128-bit from IPA sponge, coerced to Fq)
    { spongeState } = mkIpaTestContext ctx

    rawBpChallenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
    rawBpChallenges = Pickles.Sponge.evalPureSpongeM spongeState do
      _ <- Pickles.Sponge.squeeze -- squeeze for u
      IPA.extractScalarChallengesPure (coerce $ ProofFFI.pallasProofOpeningLr ctx.proof)

    bulletproofChallenges :: Vector 16 (SizedF 128 (F Pallas.ScalarField))
    bulletproofChallenges = coerce rawBpChallenges

    -- Xi challenge in Fq (coerced from Fp)
    xiChalFq :: SizedF 128 (F Pallas.ScalarField)
    xiChalFq = coerce (coerceViaBits ctx.oracles.vChal :: SizedF 128 Pallas.ScalarField)

    -- Build circuit input
    tComm :: Vector 7 (AffinePoint (F Pallas.ScalarField))
    tComm = unsafePartial fromJust $ Vector.toVector @7 $ coerce commitments.tComm

    circuitInput :: IncrementallyVerifyProofInput 9 0 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { publicInput: unsafePartial fromJust $ Vector.toVector $
          map (\fp -> F (fromBigInt (toBigInt fp) :: Pallas.ScalarField)) ctx.publicInputs
      , sgOld: Vector.nil
      , deferredValues:
          { plonk:
              { alpha: wrapF (coerceViaBits ctx.oracles.alphaChal :: SizedF 128 Pallas.ScalarField)
              , beta: wrapF (coerceViaBits ctx.oracles.beta :: SizedF 128 Pallas.ScalarField)
              , gamma: wrapF (coerceViaBits ctx.oracles.gamma :: SizedF 128 Pallas.ScalarField)
              , zeta: wrapF (coerceViaBits ctx.oracles.zetaChal :: SizedF 128 Pallas.ScalarField)
              }
          , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
          , xi: xiChalFq
          , bulletproofChallenges
          , b: toShifted $ F bValue
          , perm: toShifted $ F perm
          , zetaToSrsLength: toShifted $ F (pow ctx.oracles.zeta (BigInt.fromInt maxPolySize))
          , zetaToDomainSize: toShifted $ F (pow ctx.oracles.zeta n)
          }
      , wComm: coerce commitments.wComm
      , zComm: coerce commitments.zComm
      , tComm
      , opening:
          { delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
          , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
          , lr: coerce $ ProofFFI.pallasProofOpeningLr ctx.proof
          , z1: toShifted $ F $ ProofFFI.pallasProofOpeningZ1 ctx.proof
          , z2: toShifted $ F $ ProofFFI.pallasProofOpeningZ2 ctx.proof
          }
      }

    circuit
      :: forall t
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t Identity
      => IncrementallyVerifyProofInput 9 0 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t Identity Unit
    circuit input = do
      { success } <- evalSpongeM initialSpongeCircuit $
        incrementallyVerifyProof @51 @Vesta.G
          IPA.type1ScalarOps
          (groupMapParams $ Proxy @Vesta.G)
          params
          input
      assert_ success

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(IncrementallyVerifyProofInput 9 0 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-------------------------------------------------------------------------------
-- | verify test
-------------------------------------------------------------------------------

-- | Full verify circuit test.
-- | Wraps incrementallyVerifyProof with digest and challenge assertions.
verifyTest :: VestaTestContext -> Aff Unit
verifyTest ctx = do
  let
    commitments = ProofFFI.pallasProofCommitments ctx.proof
    numPublic = Array.length ctx.publicInputs
    columnCommsRaw = ProofFFI.pallasVerifierIndexColumnComms ctx.verifierIndex

    indexComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    indexComms = unsafePartial fromJust $ Vector.toVector $ Array.take 6 columnCommsRaw

    coeffComms :: Vector 15 (AffinePoint Pallas.ScalarField)
    coeffComms = unsafePartial fromJust $ Vector.toVector $ Array.take 15 $ Array.drop 6 columnCommsRaw

    sigmaComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    sigmaComms = unsafePartial fromJust $ Vector.toVector $ Array.drop 21 columnCommsRaw

    -- Build params (compile-time constants)
    params :: IncrementallyVerifyProofParams 9 Pallas.ScalarField
    params =
      { curveParams: curveParams (Proxy @Vesta.G)
      , lagrangeComms: unsafePartial fromJust $ Vector.toVector $
          coerce (ProofFFI.pallasLagrangeCommitments ctx.verifierIndex numPublic)
      , blindingH: coerce $ ProofFFI.pallasProverIndexBlindingGenerator ctx.verifierIndex
      , sigmaCommLast: coerce $ ProofFFI.pallasSigmaCommLast ctx.verifierIndex
      , columnComms:
          { index: coerce indexComms
          , coeff: coerce coeffComms
          , sigma: coerce sigmaComms
          }
      , indexDigest: ProofFFI.pallasVerifierIndexDigest ctx.verifierIndex
      }

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
    { challenges: rustChallenges } = mkIpaTestContext ctx
    bValue = ProofFFI.computeB0
      { challenges: Vector.toUnfoldable rustChallenges
      , zeta: ctx.oracles.zeta
      , zetaOmega: ctx.oracles.zeta * omega
      , evalscale: ctx.oracles.u
      }

    -- Bulletproof challenges (raw 128-bit from IPA sponge, coerced to Fq)
    { spongeState } = mkIpaTestContext ctx

    rawBpChallenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
    rawBpChallenges = Pickles.Sponge.evalPureSpongeM spongeState do
      _ <- Pickles.Sponge.squeeze -- squeeze for u
      IPA.extractScalarChallengesPure (coerce $ ProofFFI.pallasProofOpeningLr ctx.proof)

    bulletproofChallenges :: Vector 16 (SizedF 128 (F Pallas.ScalarField))
    bulletproofChallenges = coerce rawBpChallenges

    -- Xi challenge in Fq (coerced from Fp)
    xiChalFq :: SizedF 128 (F Pallas.ScalarField)
    xiChalFq = coerce (coerceViaBits ctx.oracles.vChal :: SizedF 128 Pallas.ScalarField)

    -- Build circuit input
    tComm :: Vector 7 (AffinePoint (F Pallas.ScalarField))
    tComm = unsafePartial fromJust $ Vector.toVector @7 $ coerce commitments.tComm

    circuitInput :: IncrementallyVerifyProofInput 9 0 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { publicInput: unsafePartial fromJust $ Vector.toVector $
          map (\fp -> F (fromBigInt (toBigInt fp) :: Pallas.ScalarField)) ctx.publicInputs
      , sgOld: Vector.nil
      , deferredValues:
          { plonk:
              { alpha: wrapF (coerceViaBits ctx.oracles.alphaChal :: SizedF 128 Pallas.ScalarField)
              , beta: wrapF (coerceViaBits ctx.oracles.beta :: SizedF 128 Pallas.ScalarField)
              , gamma: wrapF (coerceViaBits ctx.oracles.gamma :: SizedF 128 Pallas.ScalarField)
              , zeta: wrapF (coerceViaBits ctx.oracles.zetaChal :: SizedF 128 Pallas.ScalarField)
              }
          , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
          , xi: xiChalFq
          , bulletproofChallenges
          , b: toShifted $ F bValue
          , perm: toShifted $ F perm
          , zetaToSrsLength: toShifted $ F (pow ctx.oracles.zeta (BigInt.fromInt maxPolySize))
          , zetaToDomainSize: toShifted $ F (pow ctx.oracles.zeta n)
          }
      , wComm: coerce commitments.wComm
      , zComm: coerce commitments.zComm
      , tComm
      , opening:
          { delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
          , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
          , lr: coerce $ ProofFFI.pallasProofOpeningLr ctx.proof
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
      => IncrementallyVerifyProofInput 9 0 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t Identity Unit
    circuit input = do
      success <- evalSpongeM initialSpongeCircuit $
        verify @51 @Vesta.G
          IPA.type1ScalarOps
          (groupMapParams $ Proxy @Vesta.G)
          params
          input
          false_ -- isBaseCase (real proof, not base case)
          (const_ claimedDigestFq)
      assert_ success

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(IncrementallyVerifyProofInput 9 0 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll createVestaTestContext $
  describe "Wrap Sub-circuits (Real Data)" do
    it "extractScalarChallenges circuit matches pure and Rust" extractChallengesCircuitTest
    it "bulletReduceCircuit matches Rust lr_prod" bulletReduceCircuitTest
    it "debug verify traces intermediate IPA values" debugVerifyTest
    it "ipaFinalCheckCircuit verifies with Rust proof values" ipaFinalCheckCircuitTest
    it "checkBulletproof composes transcript and IPA verification" checkBulletproofTest
    it "incrementallyVerifyProof wires all components together" incrementallyVerifyProofTest
    it "verify wires IVP + deferred value assertions" verifyTest
