module Test.Pickles.TestContext
  ( InductiveTestContext
  , createInductiveTestContext
  , StepProofContext
  , WrapProofContext
  , TestContext'
  , StepIPAContext
  , IPAContext'
  , StepCase(..)
  , SchnorrInput
  , SchnorrInputVar
  , StepSchnorrInput
  , StepSchnorrInputVar
  , StepProverM(..)
  , runStepProverM
  , WrapPrivateData
  , WrapProverM(..)
  , runWrapProverM
  , computePublicEval
  , createStepProofContext
  , createTestContext'
  , mkStepIpaContext
  , schnorrBuiltState
  , schnorrCircuit
  , schnorrSolver
  , stepSchnorrAppCircuit
  , zkRows
  , createWrapProofContext
  , mkWrapIpaContext
  , buildWrapCircuitInput
  , buildWrapProverWitness
  , buildWrapCircuitParams
  , buildWrapClaimedDigest
  , coerceStepPlonkChallenges
  , extractStepRawBpChallenges
  , buildFinalizeParams
  , buildFinalizeInput
  , buildStepFinalizeParams
  , buildStepFinalizeInput
  , module Pickles.Types
  , toVectorOrThrow
  ) where

import Prelude

import Control.Monad.Reader.Trans (ReaderT, ask, runReaderT)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console (debug)
import Effect.Class.Console as Console
import Effect.Exception (throw)
import Effect.Exception.Unsafe (unsafeThrow)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Commitments (combinedInnerProduct)
import Pickles.IPA (computeB, extractScalarChallengesPure, type1ScalarOps, type2ScalarOps)
import Pickles.Linearization as Linearization
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (class LinearizationFFI, PointEval, evalSelectorPolys, proverIndexDomainLog2, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.Linearization.Vesta as VestaTokens
import Pickles.PlonkChecks.FtEval (ftEval0)
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint, parseHex)
import Pickles.PlonkChecks.Permutation (permContribution, permScalar)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, emptyPrevChallengeDigest, frSpongeChallengesPure)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Sponge (initialSponge, runPureSpongeM)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Step.Advice (class StepWitnessM)
import Pickles.Step.Circuit (AppCircuitInput, AppCircuitOutput, StepInput, stepCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams, dummyProofWitness, dummyUnfinalizedProof)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, FinalizeOtherProofParams)
import Pickles.Types (StepField, StepIPARounds, WrapField, WrapIPARounds)
import Pickles.Verify.FqSpongeTranscript (FqSpongeInput, spongeTranscriptPure)
import Pickles.Verify.Types (PlonkMinimal, UnfinalizedProof, expandPlonkMinimal)
import Pickles.Wrap.Advice (class WrapWitnessM)
import Pickles.Wrap.Circuit (WrapInput, WrapParams, wrapCircuit)
import RandomOracle.Sponge (Sponge)
import RandomOracle.Sponge as RandomOracle
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, SolverT, compile, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createCRS, createProverIndex, createVerifierIndex, crsSize, verifyProverIndex)
import Snarky.Backend.Kimchi.Types (CRS, ProverIndex, VerifierIndex)
import Snarky.Circuit.CVar (EvaluationError, Variable)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, assert_, coerceViaBits, const_, false_, toField, true_, wrapF)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..), toFieldPure, toShifted)
import Snarky.Circuit.Kimchi (groupMapParams) as Kimchi
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi (initialState) as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
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
-- | Shared inductive test context
-------------------------------------------------------------------------------

-- | Shared context for all tests that need real proof data.
-- | Created once and shared across test groups via `beforeAll`.
-- | Field names follow the inductive chain: step0 → wrap0 → step1 → ...
type InductiveTestContext =
  { step0 :: StepProofContext -- ^ Base case Step proof (Schnorr circuit)
  , wrap0 :: WrapProofContext -- ^ Wrap proof verifying step0
  }

-- | Create the shared inductive test context.
-- | Builds the full chain: Step(base) → Wrap → ...
createInductiveTestContext :: Aff InductiveTestContext
createInductiveTestContext = do
  Console.debug "[createInductiveTestContext]"
  Console.info "Creating step0 proof (BaseCase)"
  step0 <- createStepProofContext BaseCase
  Console.info "Creating wrap0 proof"
  wrap0 <- createWrapProofContext step0
  pure { step0, wrap0 }

-------------------------------------------------------------------------------
-- | StepProverM: prove-time advisory monad
-------------------------------------------------------------------------------

-- | Prove-time monad: provides real proof witness data via ReaderT.
newtype StepProverM (n :: Int) f a = StepProverM (ReaderT (Vector n (ProofWitness (F f))) Effect a)

derive instance Newtype (StepProverM n f a) _
derive newtype instance Functor (StepProverM n f)
derive newtype instance Apply (StepProverM n f)
derive newtype instance Applicative (StepProverM n f)
derive newtype instance Bind (StepProverM n f)
derive newtype instance Monad (StepProverM n f)

runStepProverM :: forall n f a. Vector n (ProofWitness (F f)) -> StepProverM n f a -> Effect a
runStepProverM witnesses (StepProverM m) = runReaderT m witnesses

instance StepWitnessM n (StepProverM n f) f where
  getProofWitnesses _ = StepProverM $ ask

-------------------------------------------------------------------------------
-- | WrapProverM: prove-time advisory monad for the Wrap circuit
-------------------------------------------------------------------------------

-- | Private witness data for the Wrap circuit prover.
-- | Combines polynomial evaluations (for finalize) and protocol commitments (for IVP).
type WrapPrivateData (ds :: Int) f =
  { evals :: ProofWitness (F f)
  , messages ::
      { wComm :: Vector 15 (AffinePoint (F f))
      , zComm :: AffinePoint (F f)
      , tComm :: Vector 7 (AffinePoint (F f))
      }
  , openingProof ::
      { delta :: AffinePoint (F f)
      , sg :: AffinePoint (F f)
      , lr :: Vector ds { l :: AffinePoint (F f), r :: AffinePoint (F f) }
      , z1 :: Type1 (F f)
      , z2 :: Type1 (F f)
      }
  }

-- | Prove-time monad for Wrap: provides private witness data via ReaderT.
newtype WrapProverM (ds :: Int) f a = WrapProverM (ReaderT (WrapPrivateData ds f) Effect a)

derive instance Newtype (WrapProverM ds f a) _
derive newtype instance Functor (WrapProverM ds f)
derive newtype instance Apply (WrapProverM ds f)
derive newtype instance Applicative (WrapProverM ds f)
derive newtype instance Bind (WrapProverM ds f)
derive newtype instance Monad (WrapProverM ds f)

runWrapProverM :: forall ds f a. WrapPrivateData ds f -> WrapProverM ds f a -> Effect a
runWrapProverM privateData (WrapProverM m) = runReaderT m privateData

instance (Reflectable ds Int, PrimeField f) => WrapWitnessM ds (WrapProverM ds f) f where
  getEvals _ = WrapProverM $ map _.evals ask
  getMessages _ = WrapProverM $ map _.messages ask
  getOpeningProof _ = WrapProverM $ map _.openingProof ask

-------------------------------------------------------------------------------
-- | Schnorr circuit setup
-------------------------------------------------------------------------------

-- | The Schnorr verification circuit over Vesta.ScalarField (= Pallas.BaseField = Fp).
schnorrCircuit
  :: forall t m
   . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
  => VerifyInput 4 (FVar Vesta.ScalarField)
  -> Snarky (KimchiConstraint Vesta.ScalarField) t m (BoolVar Vesta.ScalarField)
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
-- | Step combinator circuit setup
-------------------------------------------------------------------------------

-- | The application circuit input for the Step combinator: Schnorr verification.
type SchnorrInput = VerifyInput 4 (F StepField)
type SchnorrInputVar = VerifyInput 4 (FVar StepField)

-- | Full Step combinator circuit input.
type StepSchnorrInput =
  StepInput 1 SchnorrInput Unit StepIPARounds WrapIPARounds (F StepField) (Type2 (F StepField) Boolean) Boolean

type StepSchnorrInputVar =
  StepInput 1 SchnorrInputVar Unit StepIPARounds WrapIPARounds (FVar StepField) (Type2 (FVar StepField) (BoolVar StepField)) (BoolVar StepField)

-- | Schnorr application circuit embedded in the Step combinator.
-- | The `mustVerify` parameter controls whether previous proofs are verified:
-- | - BaseCase: mustVerify = false (no real proofs to verify)
-- | - InductiveCase: mustVerify = true (verify the previous Wrap proof)
stepSchnorrAppCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Boolean
  -> AppCircuitInput 1 SchnorrInputVar Unit
  -> Snarky (KimchiConstraint StepField) t m (AppCircuitOutput 1 Unit Unit StepField)
stepSchnorrAppCircuit mustVerify { appInput } = do
  verified <- schnorrCircuit appInput
  assert_ verified
  let mv = if mustVerify then true_ else false_
  pure
    { mustVerify: mv :< Vector.nil
    , publicOutput: unit
    , auxiliaryOutput: unit
    }

-- | Which case of the Step recursion to run.
data StepCase
  = BaseCase
  | InductiveCase WrapProofContext

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

-- | Create a test context from any circuit.
-- | Given compiled circuit state, a solver, and an input, creates a proof
-- | and oracle results for testing.
-- | Step circuits use domain 2^16 and Wrap circuits use 2^15.
createTestContext'
  :: forall f f' g a b
   . CircuitGateConstructor f g
  => HasEndo f f'
  => ProofFFI f g
  => LinearizationFFI f g
  => { builtState :: CircuitBuilderState (KimchiGate f) (AuxState f)
     , solver :: a -> Aff (Either EvaluationError (Tuple b (Map Variable f)))
     , input :: a
     , crs :: CRS g
     }
  -> Aff (TestContext' f g)
createTestContext' { builtState, solver, input, crs } = do
  debug "[createTestContext]"
  eRes <- solver input
  case eRes of
    Left e -> do
      Console.error "Failed to run solver"
      liftEffect $ throw (show e)
    Right (Tuple _ assignments) -> do
      Console.debug "Ran solver and calculated assignments"
      let
        nPublicInputRows = Array.length builtState.publicInputs
        kimchiRows = concatMap toKimchiRows builtState.constraints
        { constraintSystem, constraints } = makeConstraintSystem @f
          { constraints: kimchiRows
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

      Console.info $ "Circuit has " <> show nPublicInputRows <> " public inputs"
      Console.info $ "Circuit has " <> show (Array.length kimchiRows) <> " constraint rows"
      Console.debug $ "proverIndex.domainLog2: " <> show domainLog2
      Console.debug $ "Circuit satisfied for proverIndex: " <> show verified

      let
        proof = createProof { proverIndex, witness }
        proofVerified = ProofFFI.verifyOpeningProof verifierIndex { proof, publicInput: publicInputs }

      if proofVerified then pure unit
      else liftEffect $ throw "Proof failed to verify"

      let
        oracles = proofOracles verifierIndex { proof, publicInput: publicInputs }

      pure { proverIndex, verifierIndex, witness, publicInputs, domainLog2, proof, oracles }

-- | Create a Step proof context using the Step combinator circuit.
-- |
-- | For BaseCase: uses dummy previous proof data, mustVerify = false.
-- | For InductiveCase: uses real Wrap proof data, mustVerify = true.
-- | Padded to domain 2^16 to match Pickles Step proof conventions.
-- |
-- | The circuit is compiled with Identity (StepWitnessM returns dummy witnesses,
-- | but exists ignores advisory during constraint collection). Witness generation
-- | uses StepProverM to provide real proof witnesses as private auxiliary data.
createStepProofContext :: StepCase -> Aff StepProofContext
createStepProofContext stepCase = do
  Console.debug "[createStepProofContext]"
  schnorrInput <- liftEffect $ randomSampleOne $ genValidSignature (Proxy @PallasG) (Proxy @4)
  Tuple mustVerify params <- case stepCase of
    BaseCase -> do
      Console.info "creating Step proof for BaseCase"
      pure $ Tuple false dummyFinalizeOtherProofParams
    InductiveCase wrapCtx -> do
      Console.info "creating Step proof for Inductive Step"
      pure $ Tuple true (buildStepFinalizeParams wrapCtx)

  let
    -- Circuit polymorphic in m: compiled with Identity, solved with StepProverM
    circuit
      :: forall t m
       . CircuitM StepField (KimchiConstraint StepField) t m
      => StepWitnessM 1 m StepField
      => StepSchnorrInputVar
      -> Snarky (KimchiConstraint StepField) t m Unit
    circuit i = do
      void $ stepCircuit type2ScalarOps params (stepSchnorrAppCircuit mustVerify) i

  -- Compile with Identity (StepWitnessM 1 Identity StepField resolved from global instance)
  builtState <- liftEffect $ compile
    (Proxy @StepSchnorrInput)
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    circuit
    Kimchi.initialState
  let
    -- Solver with StepProverM to provide real witnesses
    rawSolver :: SolverT StepField (KimchiConstraint StepField) (StepProverM 1 StepField) StepSchnorrInput Unit
    rawSolver = makeSolver (Proxy @(KimchiConstraint StepField))
      (circuit :: forall t. CircuitM StepField (KimchiConstraint StepField) t (StepProverM 1 StepField) => StepSchnorrInputVar -> Snarky (KimchiConstraint StepField) t (StepProverM 1 StepField) Unit)

    -- Witness data for the advisory monad
    witnessData :: Vector 1 (ProofWitness (F StepField))
    witnessData = case stepCase of
      BaseCase -> dummyProofWitness :< Vector.nil
      InductiveCase wrapCtx ->
        let
          fopInput = buildStepFinalizeInput { prevChallengeDigest: emptyPrevChallengeDigest, wrapCtx }
        in
          fopInput.witness :< Vector.nil

    -- Wrap solver: StepProverM → Aff
    solver input_ = liftEffect $ runStepProverM witnessData (runSolverT rawSolver input_)

    -- Public-only input (no proofWitnesses)
    input :: StepSchnorrInput
    input = case stepCase of
      BaseCase ->
        let
          unfinalizedProof :: UnfinalizedProof WrapIPARounds (F StepField) (Type2 (F StepField) Boolean) Boolean
          unfinalizedProof = dummyUnfinalizedProof @WrapIPARounds @StepField @Pallas.ScalarField
        in
          { appInput: schnorrInput
          , previousProofInputs: unit :< Vector.nil
          , unfinalizedProofs: unfinalizedProof :< Vector.nil
          , prevChallengeDigests: zero :< Vector.nil
          }
      InductiveCase wrapCtx ->
        let
          fopInput = buildStepFinalizeInput
            { prevChallengeDigest: emptyPrevChallengeDigest
            , wrapCtx
            }
        in
          { appInput: schnorrInput
          -- TODO: why unit here ?
          , previousProofInputs: unit :< Vector.nil
          , unfinalizedProofs: fopInput.unfinalized :< Vector.nil
          , prevChallengeDigests: fopInput.prevChallengeDigest :< Vector.nil
          }
  Console.debug "Creating CRS for Step circuit"
  crs <- liftEffect $ createCRS @StepField
  Console.info $ "Created CRS of size " <> show (crsSize crs) <> " for Step circuit"
  createTestContext'
    { builtState
    , solver
    , input
    , crs
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
type StepIPAContext = IPAContext' StepIPARounds Vesta.ScalarField Pallas.ScalarField

type IPAContext' d f f' =
  { challenges :: Vector d f
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
        { challenges: toVectorOrThrow @StepIPARounds "mkStepIpaContext proofBulletproofChallenges" challengesArray
        , spongeState: computedSponge
        , combinedPolynomial
        , omega
        }

--------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- | Cross-field coercion helpers (Fp → Fq)
-------------------------------------------------------------------------------

-- StepField, WrapField, StepIPARounds, WrapIPARounds are imported from Pickles.Types

-- | Convert an Array to a sized Vector, throwing an informative error on length mismatch.
toVectorOrThrow :: forall @n a. Reflectable n Int => String -> Array a -> Vector n a
toVectorOrThrow label arr = case Vector.toVector @n arr of
  Just v -> v
  Nothing -> unsafeThrow $ label <> ": expected " <> show (reflectType (Proxy :: Proxy n)) <> " elements, got " <> show (Array.length arr)

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

buildWrapCircuitParams :: forall @nPublic. Reflectable nPublic Int => StepProofContext -> WrapParams nPublic Pallas.ScalarField
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
extractStepRawBpChallenges :: StepProofContext -> Vector StepIPARounds (SizedF 128 Pallas.ScalarField)
extractStepRawBpChallenges ctx =
  let
    { spongeState } = mkStepIpaContext ctx
    lr = toVectorOrThrow @StepIPARounds "extractStepRawBpChallenges pallasProofOpeningLr" $
      ProofFFI.pallasProofOpeningLr ctx.proof
  in
    Pickles.Sponge.evalPureSpongeM spongeState do
      _ <- Pickles.Sponge.squeeze -- squeeze for u
      extractScalarChallengesPure (coerce lr)

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
buildFinalizeInput :: { prevChallengeDigest :: WrapField, stepCtx :: StepProofContext } -> FinalizeOtherProofInput StepIPARounds (F WrapField) (Type1 (F WrapField)) Boolean
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

    bulletproofChallenges :: Vector StepIPARounds (SizedF 128 (F WrapField))
    bulletproofChallenges = coerce rawBpChallenges

    -- Compute b and perm
    expandedChals :: Vector StepIPARounds WrapField
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

buildWrapCircuitInput :: forall @nPublic. Reflectable nPublic Int => StepProofContext -> WrapInput nPublic 0 StepIPARounds WrapIPARounds (F WrapField) (Type1 (F WrapField)) Boolean
buildWrapCircuitInput ctx =
  let
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
    bulletproofChallenges :: Vector StepIPARounds (SizedF 128 (F WrapField))
    bulletproofChallenges = coerce (extractStepRawBpChallenges ctx)

    -- Xi challenge in Fq (coerced from Fp)
    xiChalFq :: SizedF 128 (F WrapField)
    xiChalFq = coerce (coerceViaBits ctx.oracles.vChal :: SizedF 128 WrapField)

    -- IVP deferred values (Fp-origin, cross-field shifted)
    ivpCIP = toShifted $ F ctx.oracles.combinedInnerProduct :: Type1 (F WrapField)
    ivpB = toShifted $ F bValue :: Type1 (F WrapField)
    ivpPerm = toShifted $ F perm :: Type1 (F WrapField)
    ivpZetaToSrs = toShifted $ F (pow ctx.oracles.zeta (BigInt.fromInt maxPolySize)) :: Type1 (F WrapField)
    ivpZetaToDomain = toShifted $ F (pow ctx.oracles.zeta n) :: Type1 (F WrapField)

    -- Build finalize input (computed in Fq, separate from IVP deferred values)
    fullFinalizeInput = buildFinalizeInput
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
        }
    , finalizeInput:
        { unfinalized: fullFinalizeInput.unfinalized
        , prevChallengeDigest: fullFinalizeInput.prevChallengeDigest
        }
    }

-- | Extract the private witness data for WrapProverM from a StepProofContext.
-- | Includes both polynomial evaluations (for finalize) and protocol commitments (for IVP).
buildWrapProverWitness :: StepProofContext -> WrapPrivateData StepIPARounds WrapField
buildWrapProverWitness ctx =
  let
    fullFinalizeInput = buildFinalizeInput
      { prevChallengeDigest: emptyPrevChallengeDigest
      , stepCtx: ctx
      }
    commitments = ProofFFI.pallasProofCommitments ctx.proof

    tComm :: Vector 7 (AffinePoint (F WrapField))
    tComm = toVectorOrThrow @7 "buildWrapProverWitness tComm" $ coerce commitments.tComm
  in
    { evals: fullFinalizeInput.witness
    , messages:
        { wComm: coerce commitments.wComm
        , zComm: coerce commitments.zComm
        , tComm
        }
    , openingProof:
        { delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
        , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
        , lr: coerce $ toVectorOrThrow @StepIPARounds "buildWrapProverWitness pallasProofOpeningLr" $
            ProofFFI.pallasProofOpeningLr ctx.proof
        , z1: toShifted $ F $ ProofFFI.pallasProofOpeningZ1 ctx.proof
        , z2: toShifted $ F $ ProofFFI.pallasProofOpeningZ2 ctx.proof
        }
    }

-- | Create a Wrap test context (Pallas proof verifying Vesta Step proof).
-- | Padded to domain 2^15 to match Pickles Wrap conventions.
-- | Uses reifyType to derive nPublic from the Step proof's public input count.
createWrapProofContext :: StepProofContext -> Aff WrapProofContext
createWrapProofContext stepCtx = do
  Console.debug "[createWrapProofContext]"
  reifyType (Array.length stepCtx.publicInputs) go
  where
  go :: forall nPublic. Reflectable nPublic Int => Proxy nPublic -> Aff WrapProofContext
  go _ = do
    let
      params = buildWrapCircuitParams @nPublic stepCtx
      input = buildWrapCircuitInput @nPublic stepCtx
      witnessData = buildWrapProverWitness stepCtx
      claimedDigest = buildWrapClaimedDigest stepCtx

      circuit
        :: forall t m
         . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
        => WrapWitnessM StepIPARounds m Pallas.ScalarField
        => WrapInput nPublic 0 StepIPARounds WrapIPARounds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField)
        -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
      circuit inVar =
        wrapCircuit
          type1ScalarOps
          (Kimchi.groupMapParams (Proxy @Vesta.G))
          params
          claimedDigest
          inVar

      rawSolver :: SolverT Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) (WrapProverM StepIPARounds Pallas.ScalarField) (WrapInput nPublic 0 StepIPARounds WrapIPARounds (F WrapField) (Type1 (F WrapField)) Boolean) Unit
      rawSolver = makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField))
        (circuit :: forall t. CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t (WrapProverM StepIPARounds Pallas.ScalarField) => WrapInput nPublic 0 StepIPARounds WrapIPARounds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField) -> Snarky (KimchiConstraint Pallas.ScalarField) t (WrapProverM StepIPARounds Pallas.ScalarField) Unit)

    builtState <- liftEffect $ compile
      (Proxy @(WrapInput nPublic 0 StepIPARounds WrapIPARounds (F WrapField) (Type1 (F WrapField)) Boolean))
      (Proxy @Unit)
      (Proxy @(KimchiConstraint Pallas.ScalarField))
      circuit
      KimchiConstraint.initialState

    Console.debug "Creating CRS for Wrap circuit"
    crs <- liftEffect $ createCRS @WrapField
    Console.info $ "Created CRS of size " <> show (crsSize crs) <> " for Wrap circuit"
    createTestContext'
      { builtState
      , solver: \a -> liftEffect $ runWrapProverM witnessData (runSolverT rawSolver a)
      , input
      , crs
      }

mkWrapIpaContext :: WrapProofContext -> IPAContext' WrapIPARounds Pallas.ScalarField Vesta.ScalarField
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
        { challenges: toVectorOrThrow @WrapIPARounds "mkWrapIpaContext proofBulletproofChallenges" challengesArray
        , spongeState: computedSponge
        , combinedPolynomial
        , omega
        }

-------------------------------------------------------------------------------
-- | Step-side cross-field coercion helpers (Fq → Fp)
-------------------------------------------------------------------------------

-- | Coerce an Fq value to Fp via BigInt roundtrip.
-- | Safe because |Fq - Fp| ≈ 2^78, so P(Fq value >= Fp) ≈ 2^{-177}.
coerceFq :: WrapField -> StepField
coerceFq fq = fromBigInt (toBigInt fq)

-- | Coerce a PointEval from Fq to Fp.
coercePointEvalFq :: PointEval WrapField -> PointEval StepField
coercePointEvalFq pe = { zeta: coerceFq pe.zeta, omegaTimesZeta: coerceFq pe.omegaTimesZeta }

-- | Endo scalar coefficient for challenge expansion (Vesta.endo_scalar ∈ Fp).
-- | This is `Wrap_inner_curve.scalar` in OCaml endo.ml.
stepEndo :: StepField
stepEndo = let EndoScalar e = endoScalar @Vesta.BaseField @Vesta.ScalarField in e

-------------------------------------------------------------------------------
-- | Build Step-side FinalizeOtherProofParams from a WrapProofContext
-------------------------------------------------------------------------------

-- | Build compile-time parameters for the Step FinalizeOtherProof circuit.
-- | Takes a WrapProofContext (Fq data) and produces Fp parameters.
buildStepFinalizeParams :: WrapProofContext -> FinalizeOtherProofParams StepField
buildStepFinalizeParams wrapCtx =
  { domain:
      { generator: (ProofFFI.domainGenerator wrapCtx.domainLog2 :: StepField)
      , shifts: map coerceFq (ProofFFI.proverIndexShifts wrapCtx.proverIndex)
      }
  , endo: stepEndo
  , zkRows
  , linearizationPoly: Linearization.pallas
  }

-------------------------------------------------------------------------------
-- | Build Step-side FinalizeOtherProofInput from a WrapProofContext
-------------------------------------------------------------------------------

-- | Build FinalizeOtherProof circuit test input from a WrapProofContext.
-- | Coerces Wrap proof data (Fq) to Step circuit field (Fp).
buildStepFinalizeInput :: { prevChallengeDigest :: StepField, wrapCtx :: WrapProofContext } -> FinalizeOtherProofInput WrapIPARounds (F StepField) (Type2 (F StepField) Boolean) Boolean
buildStepFinalizeInput { prevChallengeDigest: prevChallengeDigest_, wrapCtx } =
  let
    -- Coerce sponge digest
    spongeDigest = coerceFq wrapCtx.oracles.fqDigest

    -- Coerce PlonkMinimal challenges (128-bit cross-field)
    plonk =
      { alpha: wrapF (coerceViaBits wrapCtx.oracles.alphaChal :: SizedF 128 StepField)
      , beta: wrapF (coerceViaBits wrapCtx.oracles.beta :: SizedF 128 StepField)
      , gamma: wrapF (coerceViaBits wrapCtx.oracles.gamma :: SizedF 128 StepField)
      , zeta: wrapF (coerceViaBits wrapCtx.oracles.zetaChal :: SizedF 128 StepField)
      }

    -- Expand plonk and compute domain values
    plonkExpanded = expandPlonkMinimal stepEndo plonk
    omega = (ProofFFI.domainGenerator wrapCtx.domainLog2 :: StepField)
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt wrapCtx.domainLog2)
    zetaToNMinus1 = pow plonkExpanded.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: wrapCtx.domainLog2, zkRows, pt: plonkExpanded.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)
    vanishesOnZk = vanishesOnZkAndPreviousRows
      { domainLog2: wrapCtx.domainLog2, zkRows, pt: plonkExpanded.zeta }
    lagrangeFalse0 = unnormalizedLagrangeBasis
      { domainLog2: wrapCtx.domainLog2, zkRows: 0, offset: 0, pt: plonkExpanded.zeta }
    lagrangeTrue1 = unnormalizedLagrangeBasis
      { domainLog2: wrapCtx.domainLog2, zkRows, offset: -1, pt: plonkExpanded.zeta }

    -- Coerce polynomial evaluations (Fq → Fp)
    witnessEvals = map coercePointEvalFq (ProofFFI.proofWitnessEvals wrapCtx.proof)
    zEvals = coercePointEvalFq (ProofFFI.proofZEvals wrapCtx.proof)
    sigmaEvals = map coercePointEvalFq (ProofFFI.proofSigmaEvals wrapCtx.proof)
    coeffEvals = map coercePointEvalFq (ProofFFI.proofCoefficientEvals wrapCtx.proof)
    indexEvals = map coercePointEvalFq (evalSelectorPolys wrapCtx.proverIndex wrapCtx.oracles.zeta)

    publicEvals :: PointEval StepField
    publicEvals =
      { zeta: coerceFq wrapCtx.oracles.publicEvalZeta
      , omegaTimesZeta: coerceFq wrapCtx.oracles.publicEvalZetaOmega
      }
    ftEval1 = coerceFq wrapCtx.oracles.ftEval1

    -- Run Fp Fr-sponge → xi, r, polyscale, evalscale
    frInput :: FrSpongeInput StepField
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
      , endo: stepEndo
      }
    frResult = frSpongeChallengesPure frInput

    -- Compute publicEvalForFt
    publicEvalForFt = computePublicEval
      { publicInputs: map coerceFq wrapCtx.publicInputs
      , domainLog2: wrapCtx.domainLog2
      , omega
      , zeta: plonkExpanded.zeta
      }

    -- Compute ftEval0 in Fp
    permInput =
      { w: map _.zeta (Vector.take @7 witnessEvals)
      , sigma: map _.zeta sigmaEvals
      , z: zEvals
      , shifts: map coerceFq (ProofFFI.proverIndexShifts wrapCtx.proverIndex)
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
    challenges_ = buildChallenges
      { alpha: plonkExpanded.alpha
      , beta: plonkExpanded.beta
      , gamma: plonkExpanded.gamma
      , jointCombiner: zero
      , vanishesOnZk
      , lagrangeFalse0
      , lagrangeTrue1
      }
    env = fieldEnv evalPoint challenges_ parseHex
    gateConstraints = evaluate PallasTokens.constantTermTokens env

    ftEval0Value = ftEval0
      { permContribution: permContrib
      , publicEval: publicEvalForFt
      , gateConstraints
      }

    -- Build 45-element eval vector, compute CIP
    ftPointEval :: PointEval StepField
    ftPointEval = { zeta: ftEval0Value, omegaTimesZeta: ftEval1 }

    allEvals45 :: Vector 45 (PointEval StepField)
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
    { spongeState } = mkWrapIpaContext wrapCtx

    lr = toVectorOrThrow @WrapIPARounds "buildStepFinalizeInput vestaProofOpeningLr" $
      ProofFFI.vestaProofOpeningLr wrapCtx.proof

    rawBpChallenges :: Vector WrapIPARounds (SizedF 128 StepField)
    rawBpChallenges = Pickles.Sponge.evalPureSpongeM spongeState do
      _ <- Pickles.Sponge.squeeze -- squeeze for u
      extractScalarChallengesPure (coerce lr)

    bulletproofChallenges :: Vector WrapIPARounds (SizedF 128 (F StepField))
    bulletproofChallenges = coerce rawBpChallenges

    -- Compute b and perm
    expandedChals :: Vector WrapIPARounds StepField
    expandedChals = map
      (\c -> toFieldPure c stepEndo)
      rawBpChallenges

    b = computeB expandedChals
      { zeta: plonkExpanded.zeta
      , zetaOmega: plonkExpanded.zeta * omega
      , evalscale: frResult.evalscale
      }

    perm = permScalar permInput

    -- Compute zetaToSrsLength, zetaToDomainSize
    maxPolySize = ProofFFI.vestaVerifierIndexMaxPolySize wrapCtx.verifierIndex
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
