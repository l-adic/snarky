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
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception (error)
import Effect.Exception.Unsafe (unsafeThrow)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (type1ScalarOps)
import Pickles.IPA as IPA
import Pickles.Linearization.FFI (class LinearizationFFI, proverIndexDomainLog2)
import Pickles.PlonkChecks.Permutation (permScalar)
import Pickles.Sponge (initialSponge, runPureSpongeM)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams)
import Pickles.Verify.FqSpongeTranscript (FqSpongeInput, spongeTranscriptPure)
import Pickles.Wrap.Circuit (wrapCircuit)
import RandomOracle.Sponge (Sponge)
import RandomOracle.Sponge as RandomOracle
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createCRS, createProverIndex, createVerifierIndex, verifyProverIndex)
import Snarky.Backend.Kimchi.Types (ProverIndex, VerifierIndex)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, coerceViaBits, const_, toField, wrapF)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..), toShifted)
import Snarky.Circuit.Kimchi (groupMapParams) as Kimchi
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi (initialState) as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Constraint.Kimchi.Types (GateKind(..)) as GateKind
import Snarky.Curves.Class (class HasEndo, class PrimeField, EndoBase(..), curveParams, endoBase, fromBigInt, generator, pow, toAffine, toBigInt)
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
-- | Build WrapCircuitParams from a StepProofContext
-------------------------------------------------------------------------------

type WrapCircuitInput = IncrementallyVerifyProofInput 9 0 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))

-- | Compile-time parameters for the Wrap circuit.
type WrapCircuitParams = IncrementallyVerifyProofParams 9 Pallas.ScalarField

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
    { spongeState } = mkStepIpaContext ctx

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
  in
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
