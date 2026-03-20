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
  , WrapSchnorrInput
  , WrapSchnorrInputVar
  , WrapSchnorrStepIOVal
  , WrapSchnorrStepIOVar
  , existsSchnorrStepIO
  , existsSchnorrStepInput
  , StepSchnorrInput
  , StepSchnorrInputVar
  , StepSchnorrOutput
  , StepSchnorrOutputVar
  , StepAdvice
  , StepProverM(..)
  , runStepProverM
  , WrapAdvice
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
  , coerceStepPlonkChallenges
  , extractStepRawBpChallenges
  , unsafeFqToFp
  , coerceWrapPlonkChallenges
  , stepPlonkChallenges
  , extractWrapRawBpChallenges
  , buildFinalizeParams
  , buildFinalizeInput
  , buildStepFinalizeParams
  , buildStepFinalizeInput
  , computeStepChallengeDigest
  , computeStepSgEvals
  , buildStepProverWitness
  , buildStepIVPParams
  , buildStepIVPVkInput
  , buildStepIVPInput
  , stepEndo
  , wrapEndo
  , type1ToType2SF
  , module Pickles.Types
  , toVectorOrThrow
  ) where

import Prelude

import Control.Monad.Reader.Trans (ReaderT, ask, runReaderT)
import Control.Monad.Trans.Class (lift)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable, reflectType)
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
import Pickles.Dummy (dummyFinalizeOtherProofParams, dummyIpaChallenges, dummyProofWitness, dummyStepAdvice, stepDummyUnfinalizedProof, wrapDummyUnfinalizedProof) as Dummy
import Pickles.IPA (bPoly, computeB, extractScalarChallengesPure)
import Pickles.Linearization as Linearization
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (class LinearizationFFI, PointEval, domainShifts, evalSelectorPolys, proverIndexDomainLog2, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.Linearization.Vesta as VestaTokens
import Pickles.PlonkChecks.FtEval (ftEval0)
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint)
import Pickles.PlonkChecks.Permutation (permContribution, permScalar)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, emptyPrevChallengeDigest, frSpongeChallengesPure)
import Pickles.ProofWitness (ProofWitness)
import Pickles.PublicInputCommit (CorrectionMode(..))
import Record as Record
import Pickles.Sponge (initialSponge, runPureSpongeM)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Step.Advice (class StepWitnessM, getStepInputFields)
import Pickles.Step.Circuit (AppCircuitInput, AppCircuitOutput, WrapStatementPublicInput, stepCircuit)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, FinalizeOtherProofParams)
import Pickles.Types (MaxProofsVerified, StepField, StepIPARounds, StepInput, StepStatement, WrapField, WrapIPARounds)
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams)
import Pickles.Verify.FqSpongeTranscript (FqSpongeInput, spongeTranscriptPure)
import Pickles.Verify.Types (PlonkMinimal, UnfinalizedProof, expandPlonkMinimal)
import Pickles.Wrap.Advice (class WrapWitnessM, getStepIOFields)
import Pickles.Wrap.Circuit (StepPublicInput, WrapInput, WrapInputVar, WrapParams, wrapCircuit)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProof)
import RandomOracle.Sponge (Sponge)
import RandomOracle.Sponge as RandomOracle
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, SolverT, compile, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createCRS, createProverIndex, createVerifierIndex, crsCreate, crsSize, verifyProverIndex)
import Snarky.Backend.Kimchi.Types (CRS, ProverIndex, VerifierIndex)
import Snarky.Circuit.CVar (EvaluationError, Variable)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, assert_, coerceViaBits, const_, exists, false_, fieldsToValue, sizeInFields, toField, true_, valueToFields, wrapF)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2, fromShifted, toFieldPure, toShifted)
import Snarky.Circuit.Kimchi (groupMapParams) as Kimchi
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi (initialState) as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (class HasEndo, class PrimeField, EndoBase(..), EndoScalar(..), curveParams, endoBase, endoScalar, fromBigInt, fromInt, generator, pow, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Backend.Kimchi.Impl.Pallas (createCRS) as PallasImpl
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

-- | Reader environment for StepProverM: all data the Step advisory monad provides.
-- | Bundles the Step circuit input fields (as private witness), polynomial
-- | evaluations (for finalize) and protocol commitments + opening proof (for IVP),
-- | for each of the `n` previous Wrap proofs.
type StepAdvice (n :: Int) (ds :: Int) (dw :: Int) f =
  { stepInputFields :: Array (F f)
  , evals :: Vector n (ProofWitness (F f))
  , prevChallenges :: Vector n (Vector ds (F f))
  , messages ::
      Vector n
        { wComm :: Vector 15 (AffinePoint (F f))
        , zComm :: AffinePoint (F f)
        , tComm :: Vector 7 (AffinePoint (F f))
        }
  , openingProofs ::
      Vector n
        { delta :: AffinePoint (F f)
        , sg :: AffinePoint (F f)
        , lr :: Vector dw { l :: AffinePoint (F f), r :: AffinePoint (F f) }
        , z1 :: Type2 (SplitField (F f) Boolean)
        , z2 :: Type2 (SplitField (F f) Boolean)
        }
  -- | FOP proof states (Type1, from Per_proof_witness.proof_state).
  -- | These provide the private witness for finalizeOtherProof, distinct
  -- | from the public input's Type2(SplitField) unfinalized proofs.
  , fopProofStates :: Vector n (UnfinalizedProof ds (F f) (Type1 (F f)) Boolean)
  , messagesForNextWrapProof :: Vector n (F f)
  , wrapVerifierIndex ::
      { sigmaCommLast :: AffinePoint (F f)
      , columnComms ::
          { index :: Vector 6 (AffinePoint (F f))
          , coeff :: Vector 15 (AffinePoint (F f))
          , sigma :: Vector 6 (AffinePoint (F f))
          }
      }
  , sgOld :: Vector n (AffinePoint (F f))
  }

-- | Prove-time monad: provides real proof witness data via ReaderT.
newtype StepProverM (n :: Int) (ds :: Int) (dw :: Int) f a = StepProverM (ReaderT (StepAdvice n ds dw f) Effect a)

derive instance Newtype (StepProverM n ds dw f a) _
derive newtype instance Functor (StepProverM n ds dw f)
derive newtype instance Apply (StepProverM n ds dw f)
derive newtype instance Applicative (StepProverM n ds dw f)
derive newtype instance Bind (StepProverM n ds dw f)
derive newtype instance Monad (StepProverM n ds dw f)

runStepProverM :: forall n ds dw f a. StepAdvice n ds dw f -> StepProverM n ds dw f a -> Effect a
runStepProverM privateData (StepProverM m) = runReaderT m privateData

instance StepWitnessM n ds dw (StepProverM n ds dw f) f where
  getStepInputFields _ = StepProverM $ map _.stepInputFields ask
  getProofWitnesses _ = StepProverM $ map _.evals ask
  getPrevChallenges _ = StepProverM $ map _.prevChallenges ask
  getMessages _ = StepProverM $ map _.messages ask
  getOpeningProof _ = StepProverM $ map _.openingProofs ask
  getFopProofStates _ = StepProverM $ map _.fopProofStates ask
  getMessagesForNextWrapProof _ = StepProverM $ map _.messagesForNextWrapProof ask
  getWrapVerifierIndex _ = StepProverM $ map _.wrapVerifierIndex ask
  getSgOld _ = StepProverM $ map _.sgOld ask

-------------------------------------------------------------------------------
-- | WrapProverM: prove-time advisory monad for the Wrap circuit
-------------------------------------------------------------------------------

-- | Reader environment for WrapProverM: all data the Wrap advisory monad provides.
-- | Bundles polynomial evaluations (for finalize), protocol commitments (for IVP),
-- | unfinalized proof (for finalize, with Fq-recomputed deferred values),
-- | and previous challenge digest.
-- | WrapStatement public input provides Fp-origin deferred values for IVP.
type WrapAdvice (mpv :: Int) (ds :: Int) (dw :: Int) f =
  { evals :: Vector mpv (ProofWitness (F f))
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
  , unfinalizedProofs :: Vector mpv (UnfinalizedProof dw (F f) (Type2 (F f)) Boolean)
  , stepAccs :: Vector mpv (AffinePoint (F f))
  , oldBpChallenges :: Vector mpv (Vector dw (F f))
  , stepIOFields :: Array (F f)
  }

-- | Prove-time monad for Wrap: provides private witness data via ReaderT.
newtype WrapProverM (mpv :: Int) (ds :: Int) (dw :: Int) f a = WrapProverM (ReaderT (WrapAdvice mpv ds dw f) Effect a)

derive instance Newtype (WrapProverM mpv ds dw f a) _
derive newtype instance Functor (WrapProverM mpv ds dw f)
derive newtype instance Apply (WrapProverM mpv ds dw f)
derive newtype instance Applicative (WrapProverM mpv ds dw f)
derive newtype instance Bind (WrapProverM mpv ds dw f)
derive newtype instance Monad (WrapProverM mpv ds dw f)

runWrapProverM :: forall mpv ds dw f a. WrapAdvice mpv ds dw f -> WrapProverM mpv ds dw f a -> Effect a
runWrapProverM privateData (WrapProverM m) = runReaderT m privateData

instance (Reflectable mpv Int, Reflectable ds Int, Reflectable dw Int, PrimeField f) => WrapWitnessM mpv ds dw (WrapProverM mpv ds dw f) f where
  getStepIOFields _ = WrapProverM $ map _.stepIOFields ask
  getEvals _ = WrapProverM $ map _.evals ask
  getMessages _ = WrapProverM $ map _.messages ask
  getOpeningProof _ = WrapProverM $ map _.openingProof ask
  getUnfinalizedProofs _ = WrapProverM $ map _.unfinalizedProofs ask
  getStepAccs _ = WrapProverM $ map _.stepAccs ask
  getOldBpChallenges _ = WrapProverM $ map _.oldBpChallenges ask

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
  StepInput 1 SchnorrInput Unit StepIPARounds WrapIPARounds (F StepField) (Type2 (SplitField (F StepField) Boolean)) Boolean

type StepSchnorrInputVar =
  StepInput 1 SchnorrInputVar Unit StepIPARounds WrapIPARounds (FVar StepField) (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (BoolVar StepField)

-- | Step circuit output type (value level).
type StepSchnorrOutput =
  StepStatement 1 StepIPARounds WrapIPARounds (F StepField) (Type2 (SplitField (F StepField) Boolean)) Boolean

-- | Step circuit output type (variable level).
type StepSchnorrOutputVar =
  StepStatement 1 StepIPARounds WrapIPARounds (FVar StepField) (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (BoolVar StepField)

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

-- | Schnorr input coerced to Wrap field (Fq).
-- | Same structure as SchnorrInput but with F WrapField instead of F StepField.
-- | Used in WrapInput type where all field elements are WrapField.
type WrapSchnorrInput = VerifyInput 4 (F WrapField)

-- | Variable-level form of WrapSchnorrInput (CircuitType maps F f → FVar f).
type WrapSchnorrInputVar = VerifyInput 4 (FVar WrapField)

-- | Step proof public input types for the Schnorr Wrap circuit — value and variable level.
-- | These are StepStatement only (not full Step I/O), matching OCaml's approach
-- | where x_hat is computed over the packed Step.Statement.
type WrapSchnorrStepIOVal = StepPublicInput 1 StepIPARounds WrapIPARounds (F WrapField) Boolean
type WrapSchnorrStepIOVar = StepPublicInput 1 StepIPARounds WrapIPARounds (FVar WrapField) (BoolVar WrapField)

-- | Allocation action for the Step proof's public input (StepStatement only).
-- | Constructed here (where concrete types are known) so CircuitType resolves.
-- | Uses getStepIOFields from the advisory monad and reconstructs the
-- | structural type via fieldsToValue.
existsSchnorrStepIO
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => WrapWitnessM MaxProofsVerified StepIPARounds WrapIPARounds m WrapField
  => Snarky (KimchiConstraint WrapField) t m WrapSchnorrStepIOVar
existsSchnorrStepIO = exists $ lift $
  map (fieldsToValue @WrapField @WrapSchnorrStepIOVal <<< (coerce :: Array (F WrapField) -> Array WrapField))
    (getStepIOFields @MaxProofsVerified @StepIPARounds @WrapIPARounds unit)

-- | Allocation action for the Step circuit input (private witness).
-- | In OCaml, the Step input enters via Req.App_state + Req.Unfinalized_proofs.
-- | Here we reconstruct the structural type from flat fields via fieldsToValue.
existsSchnorrStepInput
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepWitnessM 1 StepIPARounds WrapIPARounds m StepField
  => Snarky (KimchiConstraint StepField) t m StepSchnorrInputVar
existsSchnorrStepInput = exists $ lift $
  map (fieldsToValue @StepField @StepSchnorrInput <<< (coerce :: Array (F StepField) -> Array StepField))
    (getStepInputFields @1 @StepIPARounds @WrapIPARounds unit)

-- | Which case of the Step recursion to run.
data StepCase
  = BaseCase
  | InductiveCase StepProofContext WrapProofContext

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
        kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
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
      -- The IVP verifies a Wrap proof on the Pallas curve, so lagrange comms
      -- come from the Vesta SRS (Wrap circuit SRS). Domain log2 = WrapIPARounds = 15.
      -- numPublic = number of fields consumed by publicInputCommit on WrapStatementPublicInput = 30.
      -- The Step circuit verifies Wrap proofs. Lagrange comms come from the
      -- Step SRS (CRS PallasG) via vestaSrsLagrangeCommitments, matching the
      -- convention in the circuit-diffs tests.
      stepSrs <- liftEffect $ PallasImpl.createCRS
      let
        wrapDomainLog2 = reflectType (Proxy @WrapIPARounds)
        numPublic = sizeInFields (Proxy @StepField) (Proxy @(WrapStatementPublicInput StepIPARounds (F StepField)))
        baseCaseIvpParams =
          { curveParams: curveParams (Proxy @Pallas.G)
          , lagrangeComms: (coerce (ProofFFI.vestaSrsLagrangeCommitments stepSrs wrapDomainLog2 numPublic)) :: Array (AffinePoint (F StepField))
          , blindingH: (coerce (ProofFFI.vestaSrsBlindingGenerator stepSrs)) :: AffinePoint (F StepField)
          , groupMapParams: Kimchi.groupMapParams (Proxy @Pallas.G)
          , correctionMode: PureCorrections
          , useOptSponge: false
          }
      pure $ Tuple false (Record.merge Dummy.dummyFinalizeOtherProofParams baseCaseIvpParams)
    InductiveCase stepCtx wrapCtx -> do
      Console.info "creating Step proof for Inductive Step"
      pure $ Tuple true (Record.merge (buildStepFinalizeParams stepCtx) (buildStepIVPParams wrapCtx))

  let
    -- Circuit polymorphic in m: compiled with Unit input, StepInput enters via advisory monad.
    -- In OCaml, the Step circuit takes Step.Statement as public input and gets
    -- application data via Req.App_state. Here, Unit input means the Step proof's
    -- public input is just StepSchnorrOutput (= StepStatement), reducing x_hat MSM cost.
    circuit
      :: forall t m
       . CircuitM StepField (KimchiConstraint StepField) t m
      => StepWitnessM 1 StepIPARounds WrapIPARounds m StepField
      => Unit
      -> Snarky (KimchiConstraint StepField) t m StepSchnorrOutputVar
    circuit _ = do
      i <- existsSchnorrStepInput
      stepCircuit @StepIPARounds params (stepSchnorrAppCircuit mustVerify) i

  -- Compile with Unit input — Step proof public input = StepStatement only
  builtState <- liftEffect $ compile
    (Proxy @Unit)
    (Proxy @StepSchnorrOutput)
    (Proxy @(KimchiConstraint StepField))
    circuit
    Kimchi.initialState
  let
    -- Solver with StepProverM to provide real witnesses
    solverCircuit
      :: forall t
       . CircuitM StepField (KimchiConstraint StepField) t (StepProverM 1 StepIPARounds WrapIPARounds StepField)
      => Unit
      -> Snarky (KimchiConstraint StepField) t (StepProverM 1 StepIPARounds WrapIPARounds StepField) StepSchnorrOutputVar
    solverCircuit = circuit

    rawSolver :: SolverT StepField (KimchiConstraint StepField) (StepProverM 1 StepIPARounds WrapIPARounds StepField) Unit StepSchnorrOutput
    rawSolver = makeSolver (Proxy @(KimchiConstraint StepField)) solverCircuit

  Tuple witnessData stepInput <- case stepCase of
    BaseCase -> liftEffect do
      pure $ Tuple Dummy.dummyStepAdvice
        { appInput: schnorrInput
        , previousProofInputs: unit :< Vector.nil
        , unfinalizedProofs: Dummy.stepDummyUnfinalizedProof :< Vector.nil
        , prevChallengeDigests: zero :< Vector.nil
        }
    InductiveCase stepCtx wrapCtx ->
      let
        challengeDigest = computeStepChallengeDigest stepCtx
        sgEvals = computeStepSgEvals stepCtx
        fopInput = buildStepFinalizeInput
          { prevChallengeDigest: challengeDigest
          , sgPointEvals: sgEvals
          , stepCtx
          , wrapCtx
          }
        -- Public input unfinalized proof uses N=15 Wrap bp challenges,
        -- while FOP state uses N=16 Step bp challenges. Reconstruct with Wrap bp chals.
        wrapBpChals :: Vector WrapIPARounds (SizedF 128 (F StepField))
        wrapBpChals = coerce (extractWrapRawBpChallenges wrapCtx)
        fopDv = fopInput.unfinalized.deferredValues
        publicUnfinalized = type1ToType2SF
          { deferredValues:
              { plonk: fopDv.plonk
              , combinedInnerProduct: fopDv.combinedInnerProduct
              , xi: fopDv.xi
              , bulletproofChallenges: wrapBpChals
              , b: fopDv.b
              }
          , shouldFinalize: fopInput.unfinalized.shouldFinalize
          , spongeDigestBeforeEvaluations: fopInput.unfinalized.spongeDigestBeforeEvaluations
          }
      in
        pure $ Tuple (buildStepProverWitness stepCtx wrapCtx)
          { appInput: schnorrInput
          -- TODO: why unit here ?
          , previousProofInputs: unit :< Vector.nil
          , unfinalizedProofs: publicUnfinalized :< Vector.nil
          , prevChallengeDigests: F emptyPrevChallengeDigest :< Vector.nil
          }

  let
    -- StepInput fields for advisory monad (private witness)
    stepInputFields = map F (valueToFields @StepField @StepSchnorrInput stepInput)
    witnessDataWithInput = witnessData { stepInputFields = stepInputFields }
    -- Wrap solver: StepProverM → Aff
    solver input_ = liftEffect $ runStepProverM witnessDataWithInput (runSolverT rawSolver input_)
  Console.debug "Creating CRS for Step circuit"
  crs <- liftEffect $ createCRS @StepField
  Console.info $ "Created CRS of size " <> show (crsSize crs) <> " for Step circuit"
  createTestContext'
    { builtState
    , solver
    , input: unit
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

buildWrapCircuitParams :: StepProofContext -> WrapParams Pallas.ScalarField
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
    , lagrangeComms: coerce (ProofFFI.pallasLagrangeCommitments ctx.verifierIndex numPublic)
    , blindingH: coerce $ ProofFFI.pallasProverIndexBlindingGenerator ctx.verifierIndex
    , sigmaCommLast: coerce $ ProofFFI.pallasSigmaCommLast ctx.verifierIndex
    , columnComms:
        { index: coerce indexComms
        , coeff: coerce coeffComms
        , sigma: coerce sigmaComms
        }
    , indexDigest: ProofFFI.pallasVerifierIndexDigest ctx.verifierIndex
    , endo: wrapEndo
    , domain:
        { generator: (ProofFFI.domainGenerator ctx.domainLog2 :: Pallas.ScalarField)
        , shifts: (domainShifts ctx.domainLog2 :: Vector 7 WrapField)
        }
    , domainLog2: ctx.domainLog2
    , srsLengthLog2: ctx.domainLog2
    , linearizationPoly: Linearization.vesta
    , groupMapParams: Kimchi.groupMapParams (Proxy @Vesta.G)
    , correctionMode: InCircuitCorrections
    , useOptSponge: true
    }

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
buildFinalizeParams :: StepProofContext -> FinalizeOtherProofParams WrapField ()
buildFinalizeParams stepCtx =
  { domain:
      { generator: (ProofFFI.domainGenerator stepCtx.domainLog2 :: WrapField)
      , shifts: (domainShifts stepCtx.domainLog2 :: Vector 7 WrapField)
      }
  , domainLog2: stepCtx.domainLog2
  , endo: wrapEndo
  , srsLengthLog2: stepCtx.domainLog2
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
buildFinalizeInput :: { prevChallengeDigest :: WrapField, stepCtx :: StepProofContext } -> FinalizeOtherProofInput 0 StepIPARounds (F WrapField) (Type2 (F WrapField)) Boolean
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

    -- Compute ftEval0 in Fq
    permInput =
      { w: map _.zeta (Vector.take @7 witnessEvals)
      , sigma: map _.zeta sigmaEvals
      , z: zEvals
      , shifts: (domainShifts stepCtx.domainLog2 :: Vector 7 WrapField)
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
    env = fieldEnv evalPoint challenges
    gateConstraints = evaluate VestaTokens.constantTermTokens env

    ftEval0Value = ftEval0
      { permContribution: permContrib
      , publicEval: negate publicEvals.zeta
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
            { plonk:
                { alpha: plonk.alpha
                , beta: plonk.beta
                , gamma: plonk.gamma
                , zeta: plonk.zeta
                , perm: toShifted (F perm)
                , zetaToSrsLength: toShifted (F zetaToSrsLength)
                , zetaToDomainSize: toShifted (F zetaToDomainSize)
                }
            , combinedInnerProduct: toShifted (F cip)
            , xi: coerce frResult.rawXi
            , bulletproofChallenges
            , b: toShifted (F b)
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
        }
    , mask: Vector.nil
    , prevChallenges: Vector.nil
    , domainLog2Var: F (fromInt stepCtx.domainLog2 :: WrapField)
    }

-------------------------------------------------------------------------------
-- | Build WrapCircuitInput from a StepProofContext
-------------------------------------------------------------------------------

buildWrapCircuitInput
  :: StepProofContext
  -> WrapInput StepIPARounds
buildWrapCircuitInput ctx =
  let
    -- Fp-origin deferred values for IVP (cross-field shifted Fp → Type1 Fq).
    -- These use raw Fp oracle values, matching how the prover computed the proof.
    -- Distinct from the Fq-recomputed values used by finalizeOtherProof.
    plonk = coerceStepPlonkChallenges ctx

    -- CIP from raw Fp oracle (cross-field Shifted: F Fp → Type1 (F Fq))
    combinedInnerProduct = toShifted (F ctx.oracles.combinedInnerProduct)

    -- Xi challenge coerced via 128-bit representation
    xi :: SizedF 128 (F WrapField)
    xi = coerce (coerceViaBits ctx.oracles.vChal :: SizedF 128 WrapField)

    -- Bulletproof challenges from IPA sponge
    bulletproofChallenges :: Vector StepIPARounds (SizedF 128 (F WrapField))
    bulletproofChallenges = coerce (extractStepRawBpChallenges ctx)

    -- b from FFI (Fp computation, cross-field shifted)
    omega = ProofFFI.domainGenerator ctx.domainLog2
    { challenges: rustChallenges } = mkStepIpaContext ctx
    bValue = ProofFFI.computeB0
      { challenges: Vector.toUnfoldable rustChallenges
      , zeta: ctx.oracles.zeta
      , zetaOmega: ctx.oracles.zeta * omega
      , evalscale: ctx.oracles.u
      }
    b = toShifted (F bValue)

    -- Perm scalar in Fp (cross-field shifted)
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
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
    perm = toShifted (F (permScalar permInput))

    -- Zeta powers (Fp, cross-field shifted)
    maxPolySize = ProofFFI.pallasVerifierIndexMaxPolySize ctx.verifierIndex
    zetaToSrsLength = toShifted (F (pow ctx.oracles.zeta (BigInt.fromInt maxPolySize)))
    zetaToDomainSize = toShifted (F (pow ctx.oracles.zeta n))

    -- Sponge digest (coerced Fp → Fq)
    spongeDigest = coerceFp ctx.oracles.fqDigest

    -- Compute messagesForNextWrapProof hash.
    -- The circuit hashes expandedChallenges from finalizeOtherProof, which expands
    -- the unfinalized proof's bp challenges via endo. We must use the SAME bp
    -- challenges here: from the decoded Step output's unfinalized proof.
    stepOutput :: WrapSchnorrStepIOVal
    stepOutput = fieldsToValue @WrapField
      (map (\fp -> fromBigInt (toBigInt fp) :: WrapField) ctx.publicInputs)
    stepUnfinalized = Vector.head stepOutput.proofState.unfinalizedProofs

    -- Expand bp challenges via endo (same as circuit's finalizeOtherProof does)
    unfinalizedBpChallenges :: Vector WrapIPARounds (SizedF 128 WrapField)
    unfinalizedBpChallenges = coerce stepUnfinalized.deferredValues.bulletproofChallenges

    expandedChallengesForHash :: Vector WrapIPARounds WrapField
    expandedChallengesForHash = map (\c -> toFieldPure c wrapEndo) unfinalizedBpChallenges

    -- sg from opening proof
    sg :: AffinePoint WrapField
    sg = ProofFFI.pallasProofOpeningSg ctx.proof

    -- Hash: [dummyChallenges..., expandedChallenges..., sg.x, sg.y]
    messageHash = hashMessagesForNextWrapProof
      { sg, expandedChallenges: expandedChallengesForHash, dummyChallenges: Dummy.dummyIpaChallenges.wrapExpanded }
  in
    { proofState:
        { deferredValues:
            { plonk:
                { alpha: plonk.alpha
                , beta: plonk.beta
                , gamma: plonk.gamma
                , zeta: plonk.zeta
                , perm
                , zetaToSrsLength
                , zetaToDomainSize
                }
            , combinedInnerProduct
            , xi
            , bulletproofChallenges
            , b
            }
        , spongeDigestBeforeEvaluations: F spongeDigest
        , messagesForNextWrapProof: F messageHash
        }
    , messagesForNextStepProof: zero -- stub
    }

-- | Convert an UnfinalizedProof from Type2 (SplitField) to Type2 (single field) representation.
-- | Used to provide the Step proof's forwarded unfinalized proof (Type2 SplitField) to
-- | the Wrap circuit's finalize (which uses Type2 shift ops).
-- | The conversion is out-of-circuit: fromShifted recovers the raw value,
-- | toShifted re-encodes it as Type2 (single field).
convertUnfinalized
  :: forall d
   . UnfinalizedProof d (F WrapField) (Type2 (SplitField (F WrapField) Boolean)) Boolean
  -> UnfinalizedProof d (F WrapField) (Type2 (F WrapField)) Boolean
convertUnfinalized u =
  let
    conv :: Type2 (SplitField (F WrapField) Boolean) -> Type2 (F WrapField)
    conv t2sf = toShifted (fromShifted t2sf :: F WrapField)
    d = u.deferredValues
  in
    { deferredValues:
        { plonk:
            { alpha: d.plonk.alpha
            , beta: d.plonk.beta
            , gamma: d.plonk.gamma
            , zeta: d.plonk.zeta
            , perm: conv d.plonk.perm
            , zetaToSrsLength: conv d.plonk.zetaToSrsLength
            , zetaToDomainSize: conv d.plonk.zetaToDomainSize
            }
        , combinedInnerProduct: conv d.combinedInnerProduct
        , xi: d.xi
        , bulletproofChallenges: d.bulletproofChallenges
        , b: conv d.b
        }
    , shouldFinalize: u.shouldFinalize
    , spongeDigestBeforeEvaluations: u.spongeDigestBeforeEvaluations
    }

-- | Convert a Type1 UnfinalizedProof to Type2(SplitField) for the Step public input.
-- | The underlying scalar values are the same, just encoded differently.
-- | Type1 is used by the FOP private witness, Type2(SplitField) by the public input.
type1ToType2SF
  :: forall d
   . UnfinalizedProof d (F StepField) (Type1 (F StepField)) Boolean
  -> UnfinalizedProof d (F StepField) (Type2 (SplitField (F StepField) Boolean)) Boolean
type1ToType2SF u =
  let
    conv :: Type1 (F StepField) -> Type2 (SplitField (F StepField) Boolean)
    conv t1 = toShifted (fromShifted t1 :: F StepField)
    d = u.deferredValues
  in
    { deferredValues:
        { plonk:
            { alpha: d.plonk.alpha
            , beta: d.plonk.beta
            , gamma: d.plonk.gamma
            , zeta: d.plonk.zeta
            , perm: conv d.plonk.perm
            , zetaToSrsLength: conv d.plonk.zetaToSrsLength
            , zetaToDomainSize: conv d.plonk.zetaToDomainSize
            }
        , combinedInnerProduct: conv d.combinedInnerProduct
        , xi: d.xi
        , bulletproofChallenges: d.bulletproofChallenges
        , b: conv d.b
        }
    , shouldFinalize: u.shouldFinalize
    , spongeDigestBeforeEvaluations: u.spongeDigestBeforeEvaluations
    }

-- | Extract the private witness data for WrapProverM from a StepProofContext.
-- | Decodes the Step proof's public output to obtain the forwarded unfinalized proof,
-- | converts Type2(SplitField)→Type2(single field) shifted values, and provides
-- | polynomial evaluations for finalize.
-- | WrapStatement public input provides Fp-origin deferred values for IVP.
buildWrapProverWitness :: StepProofContext -> WrapAdvice MaxProofsVerified StepIPARounds WrapIPARounds WrapField
buildWrapProverWitness ctx =
  let
    -- Decode the Step proof's public output to get the forwarded unfinalized proofs.
    -- In OCaml, the Wrap prover gets this via Req.Proof_state (private witness).
    -- The Step output already has Vector 2 (padded to max_proofs_verified).
    stepOutput :: WrapSchnorrStepIOVal
    stepOutput = fieldsToValue @WrapField
      (map (\fp -> fromBigInt (toBigInt fp) :: WrapField) ctx.publicInputs)

    -- Convert the real unfinalized proof and pad to MaxProofsVerified with a dummy.
    -- The Step output has Vector 1 (n=1 branch), but the Wrap circuit expects Vector 2.
    realUnfinalized = convertUnfinalized (Vector.head stepOutput.proofState.unfinalizedProofs)
    dummyUnfinalized = Dummy.wrapDummyUnfinalizedProof
    unfinalizedProofs = realUnfinalized :< dummyUnfinalized :< Vector.nil

    -- Polynomial evaluations for finalize: real evals for slot 0, dummy for slot 1
    fullFinalizeInput = buildFinalizeInput
      { prevChallengeDigest: emptyPrevChallengeDigest, stepCtx: ctx }

    commitments = ProofFFI.pallasProofCommitments ctx.proof

    tComm :: Vector 7 (AffinePoint (F WrapField))
    tComm = toVectorOrThrow @7 "buildWrapProverWitness tComm" $ coerce commitments.tComm

    -- Step accumulators: base case has no real previous sg points, use dummy
    dummySgPoint :: AffinePoint (F WrapField)
    dummySgPoint = { x: zero, y: zero }

    -- Old bulletproof challenges: base case has none, use zeros
    dummyBpChals :: Vector WrapIPARounds (F WrapField)
    dummyBpChals = Vector.generate \_ -> zero
  in
    { evals: fullFinalizeInput.witness :< Dummy.dummyProofWitness :< Vector.nil
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
    , unfinalizedProofs
    , stepAccs: dummySgPoint :< dummySgPoint :< Vector.nil
    , oldBpChallenges: dummyBpChals :< dummyBpChals :< Vector.nil
    , stepIOFields: map (\fp -> F (fromBigInt (toBigInt fp) :: WrapField)) ctx.publicInputs
    }

-- | Create a Wrap test context (Pallas proof verifying Vesta Step proof).
-- | Uses concrete structural type WrapInput 1 WrapSchnorrInput Unit ...
createWrapProofContext :: StepProofContext -> Aff WrapProofContext
createWrapProofContext stepCtx = do
  Console.debug "[createWrapProofContext]"
  let
    params = buildWrapCircuitParams stepCtx
    input = buildWrapCircuitInput stepCtx
    witnessData = buildWrapProverWitness stepCtx

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => WrapWitnessM MaxProofsVerified StepIPARounds WrapIPARounds m Pallas.ScalarField
      => WrapInputVar StepIPARounds
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
    circuit =
      wrapCircuit @MaxProofsVerified @1 @StepIPARounds
        params

    solverCircuit
      :: forall t
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t (WrapProverM MaxProofsVerified StepIPARounds WrapIPARounds Pallas.ScalarField)
      => WrapInputVar StepIPARounds
      -> Snarky (KimchiConstraint Pallas.ScalarField) t (WrapProverM MaxProofsVerified StepIPARounds WrapIPARounds Pallas.ScalarField) Unit
    solverCircuit = circuit

    rawSolver :: SolverT Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) (WrapProverM MaxProofsVerified StepIPARounds WrapIPARounds Pallas.ScalarField) (WrapInput StepIPARounds) Unit
    rawSolver = makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) solverCircuit

  builtState <- liftEffect $ compile
    (Proxy @(WrapInput StepIPARounds))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint Pallas.ScalarField))
    circuit
    KimchiConstraint.initialState

  Console.debug "Creating CRS for Wrap circuit"
  let crs = crsCreate @WrapField (pow2 15)
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
      let SplitField { sDiv2: F d, sOdd } = toShifted (F ctx.oracles.combinedInnerProduct) :: SplitField (F Vesta.ScalarField) Boolean
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

-- | WARNING: Cross-field coercion (Fq → Fp) via integer reinterpretation.
-- | This mirrors OCaml's Digest.Constant machinery (digest.ml / limb_vector/constant.ml):
-- |   Fq → of_tock_field → Digest.Constant.t (4×Int64 limbs) → Digest.typ → Fp
-- | The limb packing is a prover-side storage optimization; it has no effect on the
-- | circuit. Both paths preserve the integer value, which is safe because Fp and Fq
-- | are ~2^255 primes and these values (hashes, packed challenges) are random 255-bit
-- | numbers. P(random Fq >= Fp) ≈ 2^{-177}.
unsafeFqToFp :: WrapField -> StepField
unsafeFqToFp fq = fromBigInt (toBigInt fq)

-- | Endo scalar coefficient for challenge expansion (Vesta.endo_scalar ∈ Fp).
-- | This is `Wrap_inner_curve.scalar` in OCaml endo.ml.
stepEndo :: StepField
stepEndo = let EndoScalar e = endoScalar @Vesta.BaseField @Vesta.ScalarField in e

-- | Coerce Wrap proof plonk challenges (Fq) to Step circuit field (Fp) via 128-bit representation.
coerceWrapPlonkChallenges :: WrapProofContext -> PlonkMinimal (F StepField)
coerceWrapPlonkChallenges ctx =
  { alpha: wrapF (coerceViaBits ctx.oracles.alphaChal :: SizedF 128 StepField)
  , beta: wrapF (coerceViaBits ctx.oracles.beta :: SizedF 128 StepField)
  , gamma: wrapF (coerceViaBits ctx.oracles.gamma :: SizedF 128 StepField)
  , zeta: wrapF (coerceViaBits ctx.oracles.zetaChal :: SizedF 128 StepField)
  }

-- | Step proof plonk challenges (native Fp, no cross-field coercion needed).
-- | The Step proof's oracles are already in Fp = Vesta.ScalarField = StepField.
stepPlonkChallenges :: StepProofContext -> PlonkMinimal (F StepField)
stepPlonkChallenges ctx =
  { alpha: wrapF ctx.oracles.alphaChal
  , beta: wrapF ctx.oracles.beta
  , gamma: wrapF ctx.oracles.gamma
  , zeta: wrapF ctx.oracles.zetaChal
  }

-- | Extract raw 128-bit bulletproof challenges from a Wrap proof.
-- | Uses the IPA sponge state from mkWrapIpaContext, squeezes u, then
-- | extracts scalar challenges from the L/R pairs.
extractWrapRawBpChallenges :: WrapProofContext -> Vector WrapIPARounds (SizedF 128 StepField)
extractWrapRawBpChallenges ctx =
  let
    { spongeState } = mkWrapIpaContext ctx
    lr = toVectorOrThrow @WrapIPARounds "extractWrapRawBpChallenges vestaProofOpeningLr" $
      ProofFFI.vestaProofOpeningLr ctx.proof
  in
    Pickles.Sponge.evalPureSpongeM spongeState do
      _ <- Pickles.Sponge.squeeze -- squeeze for u
      extractScalarChallengesPure (coerce lr)

-------------------------------------------------------------------------------
-- | Build Step-side FinalizeOtherProofParams from a WrapProofContext
-------------------------------------------------------------------------------

-- | Build compile-time parameters for the Step FinalizeOtherProof circuit.
-- | Takes a StepProofContext (native Fp data) for the inner Step proof's domain.
buildStepFinalizeParams :: StepProofContext -> FinalizeOtherProofParams StepField ()
buildStepFinalizeParams stepCtx =
  { domain:
      { generator: (ProofFFI.domainGenerator stepCtx.domainLog2 :: StepField)
      , shifts: (domainShifts stepCtx.domainLog2 :: Vector 7 StepField)
      }
  , domainLog2: stepCtx.domainLog2
  , endo: stepEndo
  , srsLengthLog2: stepCtx.domainLog2
  , linearizationPoly: Linearization.pallas
  }

-------------------------------------------------------------------------------
-- | Build Step-side FinalizeOtherProofInput from a WrapProofContext
-------------------------------------------------------------------------------

-- | Build FinalizeOtherProof circuit test input.
-- | Uses StepProofContext for polynomial evaluations (native Fp) and
-- | WrapProofContext for bulletproof challenges (from Wrap proof's IPA).
buildStepFinalizeInput :: { prevChallengeDigest :: StepField, sgPointEvals :: Array (PointEval StepField), stepCtx :: StepProofContext, wrapCtx :: WrapProofContext } -> FinalizeOtherProofInput 0 StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
buildStepFinalizeInput { prevChallengeDigest: prevChallengeDigest_, sgPointEvals, stepCtx, wrapCtx: _ } =
  let
    -- Sponge digest (native Fp, no coercion)
    spongeDigest = stepCtx.oracles.fqDigest

    -- PlonkMinimal challenges (native Fp)
    plonk = stepPlonkChallenges stepCtx

    -- Expand plonk and compute domain values
    plonkExpanded = expandPlonkMinimal stepEndo plonk
    omega = (ProofFFI.domainGenerator stepCtx.domainLog2 :: StepField)
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

    -- Polynomial evaluations (native Fp, no coercion)
    witnessEvals = ProofFFI.proofWitnessEvals stepCtx.proof
    zEvals = ProofFFI.proofZEvals stepCtx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals stepCtx.proof
    coeffEvals = ProofFFI.proofCoefficientEvals stepCtx.proof
    indexEvals = evalSelectorPolys stepCtx.proverIndex stepCtx.oracles.zeta

    publicEvals :: PointEval StepField
    publicEvals =
      { zeta: stepCtx.oracles.publicEvalZeta
      , omegaTimesZeta: stepCtx.oracles.publicEvalZetaOmega
      }
    ftEval1 = stepCtx.oracles.ftEval1

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

    -- Compute ftEval0 in Fp
    permInput =
      { w: map _.zeta (Vector.take @7 witnessEvals)
      , sigma: map _.zeta sigmaEvals
      , z: zEvals
      , shifts: (domainShifts stepCtx.domainLog2 :: Vector 7 StepField)
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
    env = fieldEnv evalPoint challenges_
    gateConstraints = evaluate PallasTokens.constantTermTokens env

    ftEval0Value = ftEval0
      { permContribution: permContrib
      , publicEval: negate publicEvals.zeta
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

    -- CIP includes sgPointEvals (from bPoly on prev_challenges) prepended to the 45 regular evals.
    -- With sgPointEvals=[] (standalone FOP test, n=0), this matches the circuit.
    -- With sgPointEvals=[sgPointEval] (Step.Circuit test, n=1), matches circuit's buildEvalList.
    cipAllEvals = sgPointEvals <> Array.fromFoldable allEvals45
    cipStep { result, scale } eval =
      let
        term = eval.zeta + frResult.evalscale * eval.omegaTimesZeta
      in
        { result: result + scale * term, scale: scale * frResult.xi }
    cip = (Array.foldl cipStep { result: zero, scale: one } cipAllEvals).result

    -- Extract bulletproof challenges from Step IPA (N16, stored in Wrap proof's proof_state)
    rawStepBpChallenges = extractStepRawBpChallenges stepCtx

    -- Coerce from Pallas.ScalarField (Fq) to StepField (Fp) via bit representation
    stepBpChallenges :: Vector StepIPARounds (SizedF 128 StepField)
    stepBpChallenges = map coerceViaBits rawStepBpChallenges

    bulletproofChallenges :: Vector StepIPARounds (SizedF 128 (F StepField))
    bulletproofChallenges = coerce stepBpChallenges

    -- Compute b and perm
    expandedChals :: Vector StepIPARounds StepField
    expandedChals = map (\c -> toFieldPure c stepEndo) stepBpChallenges

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
            { plonk:
                { alpha: plonk.alpha
                , beta: plonk.beta
                , gamma: plonk.gamma
                , zeta: plonk.zeta
                , perm: toShifted (F perm)
                , zetaToSrsLength: toShifted (F zetaToSrsLength)
                , zetaToDomainSize: toShifted (F zetaToDomainSize)
                }
            , combinedInnerProduct: toShifted (F cip)
            , xi: coerce frResult.rawXi
            , bulletproofChallenges
            , b: toShifted (F b)
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
        }
    , mask: Vector.nil
    , prevChallenges: Vector.nil
    , domainLog2Var: F (fromInt stepCtx.domainLog2 :: StepField)
    }

-- | Compute the challenge digest for Step-side verification of a Wrap proof.
-- | This is the pure-side equivalent of what the circuit computes via OptSponge.
-- | With mask=all-true, OptSponge is equivalent to a regular Poseidon sponge.
-- | Uses Step IPA challenges (N16) from the inner Step proof.
computeStepChallengeDigest :: StepProofContext -> StepField
computeStepChallengeDigest stepCtx =
  let
    rawBpChallenges = extractStepRawBpChallenges stepCtx

    stepBpChallenges :: Vector StepIPARounds (SizedF 128 StepField)
    stepBpChallenges = map coerceViaBits rawBpChallenges

    expandedChals :: Vector StepIPARounds StepField
    expandedChals = map (\c -> toFieldPure c stepEndo) stepBpChallenges
    sponge = foldl (\s c -> RandomOracle.absorb c s) (initialSponge :: Sponge StepField) expandedChals
  in
    (RandomOracle.squeeze sponge).result

-- | Compute the sg (challenge polynomial) evaluations for Step-side CIP.
-- | These are bPoly(expandedChals, zeta) and bPoly(expandedChals, zetaw),
-- | which the circuit includes in the combined inner product Horner fold.
-- | stepCtx provides zeta, omega, and Step IPA bp challenges.
computeStepSgEvals :: StepProofContext -> Array (PointEval StepField)
computeStepSgEvals stepCtx =
  let
    rawBpChallenges = extractStepRawBpChallenges stepCtx
    stepBpChallenges :: Vector StepIPARounds (SizedF 128 StepField)
    stepBpChallenges = map coerceViaBits rawBpChallenges
    expandedChals = map (\c -> toFieldPure c stepEndo) stepBpChallenges
    plonk = stepPlonkChallenges stepCtx
    plonkExpanded = expandPlonkMinimal stepEndo plonk
    omega = (ProofFFI.domainGenerator stepCtx.domainLog2 :: StepField)
  in
    [ { zeta: bPoly expandedChals plonkExpanded.zeta
      , omegaTimesZeta: bPoly expandedChals (plonkExpanded.zeta * omega)
      }
    ]

-------------------------------------------------------------------------------
-- | Build Step-side private witness data from a WrapProofContext
-------------------------------------------------------------------------------

-- | Extract the private witness data for StepProverM from proof contexts.
-- | stepCtx provides polynomial evaluations (native Fp) for the inner Step proof.
-- | wrapCtx provides commitments, opening proof, and bp challenges from the Wrap proof.
-- | The FOP proof states use the correct challengeDigest and sgPointEvals so that
-- | the FOP circuit's computed CIP/b match the claimed values.
buildStepProverWitness :: StepProofContext -> WrapProofContext -> StepAdvice 1 StepIPARounds WrapIPARounds StepField
buildStepProverWitness stepCtx wrapCtx =
  let
    -- Compute correct challengeDigest and sgEvals for the FOP proof state
    challengeDigest = computeStepChallengeDigest stepCtx
    sgEvals = computeStepSgEvals stepCtx
    fopInput = buildStepFinalizeInput
      { prevChallengeDigest: challengeDigest
      , sgPointEvals: sgEvals
      , stepCtx
      , wrapCtx
      }
    commitments = ProofFFI.vestaProofCommitments wrapCtx.proof

    tComm :: Vector 7 (AffinePoint (F StepField))
    tComm = toVectorOrThrow @7 "buildStepProverWitness tComm" $ coerce commitments.tComm

    -- Expanded Step IPA challenges (N16) for challenge_digest and sg_eval
    rawStepBpChallenges = extractStepRawBpChallenges stepCtx

    stepBpChallenges :: Vector StepIPARounds (SizedF 128 StepField)
    stepBpChallenges = map coerceViaBits rawStepBpChallenges

    expandedChals :: Vector StepIPARounds (F StepField)
    expandedChals = map (\c -> F (toFieldPure c stepEndo)) stepBpChallenges
  in
    { stepInputFields: [] -- StepInput fields provided by createStepProofContext
    , evals: fopInput.witness :< Vector.nil
    , prevChallenges: expandedChals :< Vector.nil
    , messages:
        { wComm: coerce commitments.wComm
        , zComm: coerce commitments.zComm
        , tComm
        } :< Vector.nil
    , openingProofs:
        { delta: coerce $ ProofFFI.vestaProofOpeningDelta wrapCtx.proof
        , sg: coerce $ ProofFFI.vestaProofOpeningSg wrapCtx.proof
        , lr: coerce $ toVectorOrThrow @WrapIPARounds "buildStepProverWitness vestaProofOpeningLr" $
            ProofFFI.vestaProofOpeningLr wrapCtx.proof
        , z1: toShifted $ F $ ProofFFI.vestaProofOpeningZ1 wrapCtx.proof
        , z2: toShifted $ F $ ProofFFI.vestaProofOpeningZ2 wrapCtx.proof
        } :< Vector.nil
    , fopProofStates: fopInput.unfinalized :< Vector.nil
    -- TODO: compute real wrap proof message digest
    , messagesForNextWrapProof: F zero :< Vector.nil
    , wrapVerifierIndex: buildStepIVPVkInput wrapCtx
    , sgOld: (coerce $ ProofFFI.vestaProofOpeningSg wrapCtx.proof) :< Vector.nil
    }

-------------------------------------------------------------------------------
-- | Build Step-side IVP params and input from a WrapProofContext
-------------------------------------------------------------------------------

-- | Build SRS-derived compile-time parameters for the Step IVP circuit.
-- | Only contains true environment data (SRS lagrange commitments, blinding generator).
-- | VK data (columnComms, sigmaCommLast) is NOT here — it goes in the input
-- | as circuit variables, matching OCaml's exists ~request:(Req.Wrap_index).
buildStepIVPParams :: WrapProofContext -> IncrementallyVerifyProofParams StepField ()
buildStepIVPParams ctx =
  let
    numPublic = Array.length ctx.publicInputs
  in
    { curveParams: curveParams (Proxy @Pallas.G)
    , lagrangeComms: coerce (ProofFFI.vestaLagrangeCommitments ctx.verifierIndex numPublic)
    , blindingH: coerce $ ProofFFI.vestaProverIndexBlindingGenerator ctx.verifierIndex
    , endo: stepEndo
    , groupMapParams: Kimchi.groupMapParams (Proxy @Pallas.G)
    , correctionMode: PureCorrections
    , useOptSponge: false
    }

-- | Extract Wrap VK data for the Step IVP input (circuit variables, not constants).
-- | In OCaml this enters via exists ~request:(Req.Wrap_index) (step_main.ml:345-348).
buildStepIVPVkInput
  :: WrapProofContext
  -> { sigmaCommLast :: AffinePoint (F StepField)
     , columnComms ::
         { index :: Vector 6 (AffinePoint (F StepField))
         , coeff :: Vector 15 (AffinePoint (F StepField))
         , sigma :: Vector 6 (AffinePoint (F StepField))
         }
     }
buildStepIVPVkInput ctx =
  let
    columnCommsRaw = ProofFFI.vestaVerifierIndexColumnComms ctx.verifierIndex

    indexComms :: Vector 6 (AffinePoint Vesta.ScalarField)
    indexComms = toVectorOrThrow @6 "buildStepIVPVkInput indexComms" $ Array.take 6 columnCommsRaw

    coeffComms :: Vector 15 (AffinePoint Vesta.ScalarField)
    coeffComms = toVectorOrThrow @15 "buildStepIVPVkInput coeffComms" $ Array.take 15 $ Array.drop 6 columnCommsRaw

    sigmaComms :: Vector 6 (AffinePoint Vesta.ScalarField)
    sigmaComms = toVectorOrThrow @6 "buildStepIVPVkInput sigmaComms" $ Array.drop 21 columnCommsRaw
  in
    { sigmaCommLast: coerce $ ProofFFI.vestaSigmaCommLast ctx.verifierIndex
    , columnComms:
        { index: coerce indexComms
        , coeff: coerce coeffComms
        , sigma: coerce sigmaComms
        }
    }

-- | Build IVP circuit input for an Fp circuit verifying a Wrap (Pallas) proof.
buildStepIVPInput
  :: forall @nPublic
   . Reflectable nPublic Int
  => WrapProofContext
  -> IncrementallyVerifyProofInput (Vector nPublic (F StepField)) 0 WrapIPARounds (F StepField) (Type2 (SplitField (F StepField) Boolean))
buildStepIVPInput ctx =
  let
    vk = buildStepIVPVkInput ctx
    commitments = ProofFFI.vestaProofCommitments ctx.proof

    -- Compute deferred values from oracles
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    maxPolySize = ProofFFI.vestaVerifierIndexMaxPolySize ctx.verifierIndex
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
    { challenges: rustChallenges } = mkWrapIpaContext ctx
    bValue = ProofFFI.computeB0
      { challenges: Vector.toUnfoldable rustChallenges
      , zeta: ctx.oracles.zeta
      , zetaOmega: ctx.oracles.zeta * omega
      , evalscale: ctx.oracles.u
      }

    -- Bulletproof challenges (raw 128-bit from IPA sponge, coerced to Fp)
    bulletproofChallenges :: Vector WrapIPARounds (SizedF 128 (F StepField))
    bulletproofChallenges = coerce (extractWrapRawBpChallenges ctx)

    -- Xi challenge in Fp (coerced from Fq)
    xiChalFp :: SizedF 128 (F StepField)
    xiChalFp = coerce (coerceViaBits ctx.oracles.vChal :: SizedF 128 StepField)

    -- Build circuit input
    tComm :: Vector 7 (AffinePoint (F StepField))
    tComm = toVectorOrThrow @7 "buildStepIVPInput tComm" $ coerce commitments.tComm
  in
    { publicInput: toVectorOrThrow @nPublic "buildStepIVPInput publicInput" $
        map (\fq -> F (unsafeFqToFp fq)) ctx.publicInputs
    , sgOld: Vector.nil
    -- VK data (circuit variables in OCaml, F f here for test input)
    , sigmaCommLast: vk.sigmaCommLast
    , columnComms: vk.columnComms
    , deferredValues:
        let
          wrapPlonk = coerceWrapPlonkChallenges ctx
        in
          { plonk:
              { alpha: wrapPlonk.alpha
              , beta: wrapPlonk.beta
              , gamma: wrapPlonk.gamma
              , zeta: wrapPlonk.zeta
              , perm: toShifted $ F perm
              , zetaToSrsLength: toShifted $ F (pow ctx.oracles.zeta (BigInt.fromInt maxPolySize))
              , zetaToDomainSize: toShifted $ F (pow ctx.oracles.zeta n)
              }
          , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
          , xi: xiChalFp
          , bulletproofChallenges
          , b: toShifted $ F bValue
          }
    , wComm: coerce commitments.wComm
    , zComm: coerce commitments.zComm
    , tComm
    , opening:
        { delta: coerce $ ProofFFI.vestaProofOpeningDelta ctx.proof
        , sg: coerce $ ProofFFI.vestaProofOpeningSg ctx.proof
        , lr: coerce $ toVectorOrThrow @WrapIPARounds "buildStepIVPInput vestaProofOpeningLr" $
            ProofFFI.vestaProofOpeningLr ctx.proof
        , z1: toShifted $ F $ ProofFFI.vestaProofOpeningZ1 ctx.proof
        , z2: toShifted $ F $ ProofFFI.vestaProofOpeningZ2 ctx.proof
        }
    }
