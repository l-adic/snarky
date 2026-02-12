module Test.Pickles.TestContext
  ( StepProofContext
  , WrapProofContext
  , TestContext'
  , StepIPAContext
  , IPAContext'
  , computePublicEval
  , createStepProofContext
  , createTestContext'
  , mkStepIpaContext
  , schnorrBuiltState
  , schnorrCircuit
  , schnorrSolver
  , padToMinDomain
  , pow2
  , zeroRow
  , zkRows
  , WrapCircuitInput
  , WrapCircuitParams
  , createWrapProofContext
  , mkWrapIpaContext
  , buildWrapCircuitInput
  , buildWrapCircuitParams
  , buildWrapClaimedDigest
  , coerceStepPlonkChallenges
  , extractStepRawBpChallenges
  , buildFinalizeParams
  , buildFinalizeInput
  , StepField
  , WrapField
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Morph (hoist)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Foldable (foldl)
import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (un)
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception (error)
import Effect.Exception.Unsafe (unsafeThrow)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Commitments (combinedInnerProduct)
import Pickles.IPA (computeB, extractScalarChallengesPure, type1ScalarOps)
import Pickles.Linearization as Linearization
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (class LinearizationFFI, PointEval, evalSelectorPolys, proverIndexDomainLog2, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Vesta as VestaTokens
import Pickles.PlonkChecks.FtEval (ftEval0)
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint, parseHex)
import Pickles.PlonkChecks.Permutation (permContribution, permScalar)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, emptyPrevChallengeDigest, frSpongeChallengesPure)
import Pickles.Sponge (initialSponge, runPureSpongeM)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, FinalizeOtherProofParams)
import Pickles.Verify.FqSpongeTranscript (FqSpongeInput, spongeTranscriptPure)
import Pickles.Verify.Types (PlonkMinimal, expandPlonkMinimal)
import Pickles.Wrap.Circuit (WrapInput, WrapParams, wrapCircuit)
import RandomOracle.Sponge (Sponge)
import RandomOracle.Sponge as RandomOracle
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createCRS, createProverIndex, createVerifierIndex, verifyProverIndex)
import Snarky.Backend.Kimchi.Types (ProverIndex, VerifierIndex)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, coerceViaBits, const_, toField, wrapF)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..), toFieldPure, toShifted)
import Snarky.Circuit.Kimchi (groupMapParams) as Kimchi
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi (initialState) as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Constraint.Kimchi.Types (GateKind(..)) as GateKind
import Snarky.Curves.Class (class HasEndo, class PrimeField, EndoBase(..), EndoScalar(..), curveParams, endoBase, endoScalar, fromBigInt, generator, pow, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.ProofFFI (class ProofFFI, OraclesResult, Proof, createProof, proofOracles)
import Test.Pickles.ProofFFI as ProofFFI
import Test.QuickCheck.Gen (randomSampleOne)
import Type.Proxy (Proxy(..))

-- | Standard Kimchi constants
zkRows :: Int
zkRows = 3

-------------------------------------------------------------------------------
-- | Schnorr circuit setup
-------------------------------------------------------------------------------

-- | The Schnorr verification circuit over Vesta.ScalarField (= Pallas.BaseField = Fp).
schnorrCircuit
  :: forall t
   . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
  => VerifyInput 4 (FVar Vesta.ScalarField)
  -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity (BoolVar Vesta.ScalarField)
schnorrCircuit { signature: { r: sigR, s: sigS }, publicKey, message } =
  let
    genPointVar :: AffinePoint (FVar Vesta.ScalarField)
    genPointVar =
      let
        { x, y } = unsafePartial fromJust $ toAffine (generator @_ @Pallas.G)
      in
        { x: const_ x, y: const_ y }
    signature = SignatureVar { r: sigR, s: sigS }
  in
    verifies (pallasScalarOps @51) genPointVar { signature, publicKey, message }

-- | Compiled circuit state for the Schnorr circuit.
schnorrBuiltState :: CircuitBuilderState (KimchiGate Vesta.ScalarField) (AuxState Vesta.ScalarField)
schnorrBuiltState = compilePure
  (Proxy @(VerifyInput 4 (F Vesta.ScalarField)))
  (Proxy @Boolean)
  (Proxy @(KimchiConstraint Vesta.ScalarField))
  schnorrCircuit
  Kimchi.initialState

-- | Solver for the Schnorr circuit.
schnorrSolver :: Solver Vesta.ScalarField (KimchiGate Vesta.ScalarField) (VerifyInput 4 (F Vesta.ScalarField)) Boolean
schnorrSolver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) schnorrCircuit

-------------------------------------------------------------------------------
-- | Test setup types
-------------------------------------------------------------------------------

-- | Generic test context, parameterized by circuit field `f` and commitment curve `g`.
type TestContext' f g =
  { proverIndex :: ProverIndex g f
  , verifierIndex :: VerifierIndex g f
  , witness :: Vector 15 (Array f)
  , publicInputs :: Array f
  , domainLog2 :: Int
  , proof :: Proof g f
  , oracles :: OraclesResult f
  }

-- | Test context for Fp circuits producing Vesta proofs (step side).
type StepProofContext = TestContext' Vesta.ScalarField Vesta.G

-- | Test context for Fq circuits producing Pallas proofs (wrap side).
type WrapProofContext = TestContext' Pallas.ScalarField Pallas.G

-- | Integer power of 2.
pow2 :: Int -> Int
pow2 0 = 1
pow2 n = 2 * pow2 (n - 1)

-- | A Zero-gate padding row with no variable references.
zeroRow :: forall f. KimchiRow f
zeroRow =
  { kind: GateKind.Zero
  , variables: Vector.generate (const Nothing)
  , coeffs: []
  }

-- | Pad an array of Kimchi rows to reach at least targetDomainLog2.
-- | The domain must be a power of 2 that fits: publicInputs + constraints + zkRows.
padToMinDomain
  :: forall f
   . Int -- target domain log2
  -> Int -- number of public input rows
  -> Array (KimchiRow f)
  -> Array (KimchiRow f)
padToMinDomain targetDomainLog2_ nPublicInputRows rows =
  let
    targetRows = pow2 targetDomainLog2_ - nPublicInputRows - zkRows
    currentRows = Array.length rows
    padding = max 0 (targetRows - currentRows)
  in
    rows <> Array.replicate padding zeroRow

-- | Create a test context from any circuit.
-- | Given compiled circuit state, a solver, and an input, creates a proof
-- | and oracle results for testing.
-- | The targetDomainLog2 pads the circuit to a minimum domain size. In Pickles,
-- | Step circuits use domain 2^16 and Wrap circuits use 2^15.
createTestContext'
  :: forall f f' g a b
   . CircuitGateConstructor f g
  => HasEndo f f'
  => ProofFFI f g
  => LinearizationFFI f g
  => { builtState :: CircuitBuilderState (KimchiGate f) (AuxState f)
     , solver :: Solver f (KimchiGate f) a b
     , input :: a
     , targetDomainLog2 :: Int
     }
  -> Aff (TestContext' f g)
createTestContext' { builtState, solver, input, targetDomainLog2 } = do
  crs <- liftEffect $ createCRS @f

  let
    nat :: Identity ~> Aff
    nat = pure <<< un Identity

  eRes <- runSolverT (\a -> hoist nat $ solver a) input
  case eRes of
    Left e -> liftEffect $ throwError $ error (show e)
    Right (Tuple _ assignments) -> do
      let
        nPublicInputRows = Array.length builtState.publicInputs
        kimchiRows = concatMap toKimchiRows builtState.constraints
        paddedRows = padToMinDomain targetDomainLog2 nPublicInputRows kimchiRows
        { constraintSystem, constraints } = makeConstraintSystem @f
          { constraints: paddedRows
          , publicInputs: builtState.publicInputs
          , unionFind: (un AuxState builtState.aux).wireState.unionFind
          }
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables constraints
          , publicInputs: builtState.publicInputs
          }
        endo = let EndoBase e = endoBase @f @f' in e
        proverIndex = createProverIndex @f @g { endo, constraintSystem, crs }
        verifierIndex = createVerifierIndex @f @g proverIndex
        domainLog2 = proverIndexDomainLog2 proverIndex
        verified = verifyProverIndex @f @g { proverIndex, witness, publicInputs }

      liftEffect $ log $ "[createTestContext'] domainLog2: " <> show domainLog2
      liftEffect $ log $ "[createTestContext'] verifyProverIndex: " <> show verified

      let
        proof = createProof { proverIndex, witness }
        proofVerified = ProofFFI.verifyOpeningProof verifierIndex { proof, publicInput: publicInputs }

      liftEffect $ unless proofVerified
        $ throwError
        $ error
        $ "[createTestContext'] verifyOpeningProof: " <> show proofVerified

      let oracles = proofOracles verifierIndex { proof, publicInput: publicInputs }

      pure { proverIndex, verifierIndex, witness, publicInputs, domainLog2, proof, oracles }

-- | Create a Vesta test context using the fixed Schnorr signature.
-- | Padded to domain 2^16 to match Pickles Step proof conventions.
createStepProofContext :: Aff StepProofContext
createStepProofContext = do
  input <- liftEffect $ randomSampleOne $ genValidSignature (Proxy @PallasG) (Proxy @4)
  createTestContext'
    { builtState: schnorrBuiltState
    , solver: schnorrSolver
    , input
    , targetDomainLog2: 16
    }

-------------------------------------------------------------------------------
-- | Permutation helper
-------------------------------------------------------------------------------

-- | Compute the public input polynomial evaluation at zeta.
-- | p(zeta) = (Z_H(zeta) / n) * sum_i (omega^i * publicInput[i] / (zeta - omega^i))
-- | where Z_H(zeta) = zeta^n - 1, n = 2^domainLog2, omega = domain generator.
-- | The omega^i factor comes from the Lagrange basis: L_i(x) = omega^i * (x^n - 1) / (n * (x - omega^i))
computePublicEval
  :: forall f
   . PrimeField f
  => { publicInputs :: Array f
     , domainLog2 :: Int
     , omega :: f
     , zeta :: f
     }
  -> f
computePublicEval { publicInputs, domainLog2, omega, zeta } =
  let
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt domainLog2)
    zetaToNMinus1 = pow zeta n - one
    { acc } = foldl
      ( \{ acc: a, omegaPow } p ->
          { acc: a + omegaPow * p / (zeta - omegaPow)
          , omegaPow: omegaPow * omega
          }
      )
      { acc: zero, omegaPow: one }
      publicInputs
  in
    zetaToNMinus1 * acc / fromBigInt n

--------------------------------------------------------------------------------
type StepIPAContext = IPAContext' Vesta.ScalarField Pallas.ScalarField

type IPAContext' f f' =
  { challenges :: Vector 16 f
  , spongeState :: Sponge f'
  , combinedPolynomial :: AffinePoint f'
  , omega :: f
  }

mkStepIpaContext :: StepProofContext -> StepIPAContext
mkStepIpaContext ctx =
  let
    commitments = ProofFFI.pallasProofCommitments ctx.proof
    publicCommArray = ProofFFI.pallasPublicComm ctx.verifierIndex ctx.publicInputs

    spongeInput :: FqSpongeInput 0 7 Pallas.ScalarField
    spongeInput =
      { indexDigest: ProofFFI.pallasVerifierIndexDigest ctx.verifierIndex
      , sgOld: Vector.nil
      , publicComm: unsafePartial fromJust $ Array.head publicCommArray
      , wComm: commitments.wComm
      , zComm: commitments.zComm
      , tComm: unsafePartial fromJust $ Vector.toVector @7 commitments.tComm
      }

    -- Run sponge transcript, then absorb shift_scalar(CIP)
    Tuple _ computedSponge = runPureSpongeM initialSponge do
      _ <- spongeTranscriptPure spongeInput
      let Type1 (F absorbValue) = toShifted (F ctx.oracles.combinedInnerProduct)
      Pickles.Sponge.absorb absorbValue
      pure unit

    ffiSponge =
      let

        -- Get sponge checkpoint (state before L/R processing)
        checkpoint = ProofFFI.pallasSpongeCheckpointBeforeChallenges ctx.verifierIndex
          { proof: ctx.proof, publicInput: ctx.publicInputs }

        -- Parse checkpoint into sponge state
        spongeMode = case checkpoint.spongeMode of
          "Absorbed" -> RandomOracle.Absorbed (unsafeFinite checkpoint.modeCount)
          _ -> RandomOracle.Squeezed (unsafeFinite checkpoint.modeCount)
      in
        { state: checkpoint.state, spongeState: spongeMode }
  in

    if ffiSponge /= computedSponge then unsafeThrow "Mismatch between ffiSponge and computedSpong"
    else
      let
        combinedPolynomial :: AffinePoint Pallas.ScalarField
        combinedPolynomial = ProofFFI.pallasCombinedPolynomialCommitment ctx.verifierIndex
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

--------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- | Cross-field coercion helpers (Fp → Fq)
-------------------------------------------------------------------------------

-- | Wrap circuit field (Fq = Pallas.ScalarField = Vesta.BaseField)
type WrapField = Pallas.ScalarField

-- | Step proof field (Fp = Vesta.ScalarField = Pallas.BaseField)
type StepField = Vesta.ScalarField

-- | Coerce an Fp value to Fq via BigInt roundtrip.
-- | Always safe because Fp < Fq, so every Fp value is a valid Fq value.
coerceFp :: StepField -> WrapField
coerceFp fp = fromBigInt (toBigInt fp)

-- | Coerce a PointEval from Fp to Fq.
coercePointEval :: PointEval StepField -> PointEval WrapField
coercePointEval pe = { zeta: coerceFp pe.zeta, omegaTimesZeta: coerceFp pe.omegaTimesZeta }

-- | Endo scalar coefficient for challenge expansion (Pallas.endo_scalar ∈ Fq).
-- | This is `Step_inner_curve.scalar` in OCaml endo.ml.
wrapEndo :: WrapField
wrapEndo = let EndoScalar e = endoScalar @Pallas.BaseField @Pallas.ScalarField in e

-------------------------------------------------------------------------------
-- | Build WrapCircuitParams from a StepProofContext
-------------------------------------------------------------------------------

type WrapCircuitInput = WrapInput 9 0 (F WrapField) (Type1 (F WrapField)) Boolean

-- | Compile-time parameters for the Wrap circuit.
type WrapCircuitParams = WrapParams 9 Pallas.ScalarField

buildWrapCircuitParams :: StepProofContext -> WrapCircuitParams
buildWrapCircuitParams ctx =
  let
    numPublic = Array.length ctx.publicInputs
    columnCommsRaw = ProofFFI.pallasVerifierIndexColumnComms ctx.verifierIndex

    indexComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    indexComms = unsafePartial fromJust $ Vector.toVector $ Array.take 6 columnCommsRaw

    coeffComms :: Vector 15 (AffinePoint Pallas.ScalarField)
    coeffComms = unsafePartial fromJust $ Vector.toVector $ Array.take 15 $ Array.drop 6 columnCommsRaw

    sigmaComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    sigmaComms = unsafePartial fromJust $ Vector.toVector $ Array.drop 21 columnCommsRaw
  in
    { ivpParams:
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
    , finalizeParams: buildFinalizeParams ctx
    }

-------------------------------------------------------------------------------
-- | Build claimed Fq-sponge digest for the Wrap circuit
-------------------------------------------------------------------------------

-- | Extract the claimed Fq-sponge digest from the Step proof's oracles,
-- | coerced to the Wrap circuit field (Pallas.ScalarField = Fq).
-- |
-- | The Rust FFI returns fqDigest as Vesta.ScalarField (= Fp) because
-- | Kimchi's FqSponge::digest() converts BaseField → ScalarField via BigInt.
-- | For values >= Fp, Kimchi returns zero (see mina_poseidon FqSponge impl).
-- | Since P(squeeze ∈ [Fp, Fq)) ≈ 2^{-177}, the integer roundtrip is safe.
buildWrapClaimedDigest :: StepProofContext -> Pallas.ScalarField
buildWrapClaimedDigest ctx = fromBigInt (toBigInt ctx.oracles.fqDigest)

-------------------------------------------------------------------------------
-- | Shared Step→Wrap coercion helpers
-------------------------------------------------------------------------------

-- | Coerce Step proof plonk challenges (Fp) to Wrap circuit field (Fq) via 128-bit representation.
coerceStepPlonkChallenges :: StepProofContext -> PlonkMinimal (F Pallas.ScalarField)
coerceStepPlonkChallenges ctx =
  { alpha: wrapF (coerceViaBits ctx.oracles.alphaChal :: SizedF 128 Pallas.ScalarField)
  , beta: wrapF (coerceViaBits ctx.oracles.beta :: SizedF 128 Pallas.ScalarField)
  , gamma: wrapF (coerceViaBits ctx.oracles.gamma :: SizedF 128 Pallas.ScalarField)
  , zeta: wrapF (coerceViaBits ctx.oracles.zetaChal :: SizedF 128 Pallas.ScalarField)
  }

-- | Extract raw 128-bit bulletproof challenges from a Step proof.
-- | Uses the IPA sponge state from mkStepIpaContext, squeezes u, then
-- | extracts scalar challenges from the L/R pairs.
extractStepRawBpChallenges :: StepProofContext -> Vector 16 (SizedF 128 Pallas.ScalarField)
extractStepRawBpChallenges ctx =
  let
    { spongeState } = mkStepIpaContext ctx
  in
    Pickles.Sponge.evalPureSpongeM spongeState do
      _ <- Pickles.Sponge.squeeze -- squeeze for u
      extractScalarChallengesPure (coerce $ ProofFFI.pallasProofOpeningLr ctx.proof)

-------------------------------------------------------------------------------
-- | Build FinalizeOtherProofParams
-------------------------------------------------------------------------------

-- | Build compile-time parameters for the FinalizeOtherProof circuit.
buildFinalizeParams :: StepProofContext -> FinalizeOtherProofParams WrapField
buildFinalizeParams stepCtx =
  { domain:
      { generator: (ProofFFI.domainGenerator stepCtx.domainLog2 :: WrapField)
      , shifts: map coerceFp (ProofFFI.proverIndexShifts stepCtx.proverIndex)
      }
  , endo: wrapEndo
  , zkRows
  , linearizationPoly: Linearization.vesta
  }

-------------------------------------------------------------------------------
-- | Build FinalizeOtherProofInput
-------------------------------------------------------------------------------

-- | Build FinalizeOtherProof circuit test input from a StepProofContext.
-- |
-- | Coerces Step proof data (Fp) to Wrap circuit field (Fq), expands plonk
-- | challenges, computes domain values, runs Fr-sponge, and assembles all
-- | deferred values and witness data.
buildFinalizeInput :: { prevChallengeDigest :: WrapField, stepCtx :: StepProofContext } -> FinalizeOtherProofInput (F WrapField) (Type1 (F WrapField)) Boolean
buildFinalizeInput { prevChallengeDigest: prevChallengeDigest_, stepCtx } =
  let
    -- Coerce sponge digest
    spongeDigest = coerceFp stepCtx.oracles.fqDigest

    -- Coerce PlonkMinimal challenges (128-bit cross-field)
    plonk = coerceStepPlonkChallenges stepCtx

    -- Expand plonk and compute domain values
    plonkExpanded = expandPlonkMinimal wrapEndo plonk
    omega = (ProofFFI.domainGenerator stepCtx.domainLog2 :: WrapField)
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt stepCtx.domainLog2)
    zetaToNMinus1 = pow plonkExpanded.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: stepCtx.domainLog2, zkRows, pt: plonkExpanded.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)
    vanishesOnZk = vanishesOnZkAndPreviousRows
      { domainLog2: stepCtx.domainLog2, zkRows, pt: plonkExpanded.zeta }
    lagrangeFalse0 = unnormalizedLagrangeBasis
      { domainLog2: stepCtx.domainLog2, zkRows: 0, offset: 0, pt: plonkExpanded.zeta }
    lagrangeTrue1 = unnormalizedLagrangeBasis
      { domainLog2: stepCtx.domainLog2, zkRows, offset: -1, pt: plonkExpanded.zeta }

    -- Coerce polynomial evaluations (Fp → Fq)
    witnessEvals = map coercePointEval (ProofFFI.proofWitnessEvals stepCtx.proof)
    zEvals = coercePointEval (ProofFFI.proofZEvals stepCtx.proof)
    sigmaEvals = map coercePointEval (ProofFFI.proofSigmaEvals stepCtx.proof)
    coeffEvals = map coercePointEval (ProofFFI.proofCoefficientEvals stepCtx.proof)
    indexEvals = map coercePointEval (evalSelectorPolys stepCtx.proverIndex stepCtx.oracles.zeta)

    publicEvals :: PointEval WrapField
    publicEvals =
      { zeta: coerceFp stepCtx.oracles.publicEvalZeta
      , omegaTimesZeta: coerceFp stepCtx.oracles.publicEvalZetaOmega
      }
    ftEval1 = coerceFp stepCtx.oracles.ftEval1

    -- Run Fq Fr-sponge → xi, r, polyscale, evalscale
    frInput :: FrSpongeInput WrapField
    frInput =
      { fqDigest: spongeDigest
      , prevChallengeDigest: prevChallengeDigest_
      , ftEval1
      , publicEvals
      , zEvals
      , indexEvals
      , witnessEvals
      , coeffEvals
      , sigmaEvals
      , endo: wrapEndo
      }
    frResult = frSpongeChallengesPure frInput

    -- Compute publicEvalForFt
    publicEvalForFt = computePublicEval
      { publicInputs: map coerceFp stepCtx.publicInputs
      , domainLog2: stepCtx.domainLog2
      , omega
      , zeta: plonkExpanded.zeta
      }

    -- Compute ftEval0 in Fq
    permInput =
      { w: map _.zeta (Vector.take @7 witnessEvals)
      , sigma: map _.zeta sigmaEvals
      , z: zEvals
      , shifts: map coerceFp (ProofFFI.proverIndexShifts stepCtx.proverIndex)
      , alpha: plonkExpanded.alpha
      , beta: plonkExpanded.beta
      , gamma: plonkExpanded.gamma
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: plonkExpanded.zeta
      }
    permContrib = permContribution permInput

    evalPoint = buildEvalPoint
      { witnessEvals
      , coeffEvals: map _.zeta coeffEvals
      , indexEvals
      , defaultVal: zero
      }
    challenges = buildChallenges
      { alpha: plonkExpanded.alpha
      , beta: plonkExpanded.beta
      , gamma: plonkExpanded.gamma
      , jointCombiner: zero
      , vanishesOnZk
      , lagrangeFalse0
      , lagrangeTrue1
      }
    env = fieldEnv evalPoint challenges parseHex
    gateConstraints = evaluate VestaTokens.constantTermTokens env

    ftEval0Value = ftEval0
      { permContribution: permContrib
      , publicEval: publicEvalForFt
      , gateConstraints
      }

    -- Build 45-element eval vector, compute CIP
    ftPointEval :: PointEval WrapField
    ftPointEval = { zeta: ftEval0Value, omegaTimesZeta: ftEval1 }

    allEvals45 :: Vector 45 (PointEval WrapField)
    allEvals45 =
      (publicEvals :< ftPointEval :< zEvals :< Vector.nil)
        `Vector.append` indexEvals
        `Vector.append` witnessEvals
        `Vector.append` coeffEvals
        `Vector.append` sigmaEvals

    cip = combinedInnerProduct
      { polyscale: frResult.xi
      , evalscale: frResult.evalscale
      , evals: allEvals45
      }

    -- Extract bulletproof challenges
    rawBpChallenges = extractStepRawBpChallenges stepCtx

    bulletproofChallenges :: Vector 16 (SizedF 128 (F WrapField))
    bulletproofChallenges = coerce rawBpChallenges

    -- Compute b and perm
    expandedChals :: Vector 16 WrapField
    expandedChals = map
      (\c -> toFieldPure c wrapEndo)
      rawBpChallenges

    b = computeB expandedChals
      { zeta: plonkExpanded.zeta
      , zetaOmega: plonkExpanded.zeta * omega
      , evalscale: frResult.evalscale
      }

    perm = permScalar permInput

    -- Compute zetaToSrsLength, zetaToDomainSize
    maxPolySize = ProofFFI.pallasVerifierIndexMaxPolySize stepCtx.verifierIndex
    zetaToSrsLength = pow plonkExpanded.zeta (BigInt.fromInt maxPolySize)
    zetaToDomainSize = pow plonkExpanded.zeta n

  in
    { unfinalized:
        { deferredValues:
            { plonk
            , combinedInnerProduct: toShifted (F cip)
            , xi: coerce frResult.rawXi
            , bulletproofChallenges
            , b: toShifted (F b)
            , perm: toShifted (F perm)
            , zetaToSrsLength: toShifted (F zetaToSrsLength)
            , zetaToDomainSize: toShifted (F zetaToDomainSize)
            }
        , shouldFinalize: true
        , spongeDigestBeforeEvaluations: F spongeDigest
        }
    , witness:
        { allEvals:
            { ftEval1: F ftEval1
            , publicEvals: coerce publicEvals
            , zEvals: coerce zEvals
            , indexEvals: coerce indexEvals
            , witnessEvals: coerce witnessEvals
            , coeffEvals: coerce coeffEvals
            , sigmaEvals: coerce sigmaEvals
            }
        , domainValues:
            { zkPolynomial: F zkPoly
            , zetaToNMinus1: F zetaToNMinus1
            , omegaToMinusZkRows: F omegaToMinusZkRows
            , vanishesOnZk: F vanishesOnZk
            , lagrangeFalse0: F lagrangeFalse0
            , lagrangeTrue1: F lagrangeTrue1
            }
        , publicEvalForFt: F publicEvalForFt
        }
    , prevChallengeDigest: F prevChallengeDigest_
    }

-------------------------------------------------------------------------------
-- | Build WrapCircuitInput from a StepProofContext
-------------------------------------------------------------------------------

buildWrapCircuitInput :: StepProofContext -> WrapCircuitInput
buildWrapCircuitInput ctx =
  let
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
    bulletproofChallenges :: Vector 16 (SizedF 128 (F WrapField))
    bulletproofChallenges = coerce (extractStepRawBpChallenges ctx)

    -- Xi challenge in Fq (coerced from Fp)
    xiChalFq :: SizedF 128 (F WrapField)
    xiChalFq = coerce (coerceViaBits ctx.oracles.vChal :: SizedF 128 WrapField)

    -- Build circuit input
    tComm :: Vector 7 (AffinePoint (F WrapField))
    tComm = unsafePartial fromJust $ Vector.toVector @7 $ coerce commitments.tComm

    -- IVP deferred values (Fp-origin, cross-field shifted)
    ivpCIP = toShifted $ F ctx.oracles.combinedInnerProduct :: Type1 (F WrapField)
    ivpB = toShifted $ F bValue :: Type1 (F WrapField)
    ivpPerm = toShifted $ F perm :: Type1 (F WrapField)
    ivpZetaToSrs = toShifted $ F (pow ctx.oracles.zeta (BigInt.fromInt maxPolySize)) :: Type1 (F WrapField)
    ivpZetaToDomain = toShifted $ F (pow ctx.oracles.zeta n) :: Type1 (F WrapField)

    -- Build finalize input (computed in Fq, separate from IVP deferred values)
    finalizeInput = buildFinalizeInput
      { prevChallengeDigest: emptyPrevChallengeDigest
      , stepCtx: ctx
      }
  in
    { ivpInput:
        { publicInput: unsafePartial fromJust $ Vector.toVector $
            map (\fp -> F (fromBigInt (toBigInt fp) :: WrapField)) ctx.publicInputs
        , sgOld: Vector.nil
        , deferredValues:
            { plonk: coerceStepPlonkChallenges ctx
            , combinedInnerProduct: ivpCIP
            , xi: xiChalFq
            , bulletproofChallenges
            , b: ivpB
            , perm: ivpPerm
            , zetaToSrsLength: ivpZetaToSrs
            , zetaToDomainSize: ivpZetaToDomain
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
    , finalizeInput
    }

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
      => WrapInput 9 0 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField)
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
