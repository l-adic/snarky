module Test.Pickles.TestContext
  ( VestaTestContext
  , TestContext'
  , IPATestContext
  , computePublicEval
  , createVestaTestContext
  , createTestContext'
  , mkIpaTestContext
  , schnorrBuiltState
  , schnorrCircuit
  , schnorrSolver
  , fixedValidSignature
  , padToMinDomain
  , pow2
  , zeroRow
  , zkRows
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Morph (hoist)
import Data.Array (concatMap, (:))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Foldable (foldl)
import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (un)
import Data.Schnorr (isEven, truncateFieldCoerce)
import Data.Schnorr.Gen (VerifyInput)
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
import Pickles.Linearization.FFI (class LinearizationFFI, proverIndexDomainLog2)
import Pickles.Sponge (initialSponge, runPureSpongeM)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Verify.FqSpongeTranscript (FqSpongeInput, spongeTranscriptPure)
import Poseidon as Poseidon
import RandomOracle.Sponge (Sponge)
import RandomOracle.Sponge as RandomOracle
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createCRS, createProverIndex, createVerifierIndex, verifyProverIndex)
import Snarky.Backend.Kimchi.Types (ProverIndex, VerifierIndex)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (Type1(..), fieldSizeBits, toShifted)
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Constraint.Kimchi.Types (GateKind(..)) as GateKind
import Snarky.Curves.Class (class HasEndo, EndoBase(..), endoBase, fromBigInt, generator, pow, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.ProofFFI (class ProofFFI, OraclesResult, Proof, createProof, proofOracles)
import Test.Pickles.ProofFFI as ProofFFI
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
type VestaTestContext = TestContext' Vesta.ScalarField Vesta.G

-- | Create a fixed valid Schnorr signature for deterministic testing.
-- | Uses constant private key and message to ensure reproducible results.
fixedValidSignature :: VerifyInput 4 (F Vesta.ScalarField)
fixedValidSignature =
  let
    -- Fixed private key (arbitrary non-zero scalar)
    privateKey :: Pallas.ScalarField
    privateKey = fromBigInt (BigInt.fromInt 12345)

    -- Fixed message (4 field elements)
    message :: Vector 4 Vesta.ScalarField
    message = unsafePartial $ fromJust $ Vector.toVector
      [ fromBigInt (BigInt.fromInt 1)
      , fromBigInt (BigInt.fromInt 2)
      , fromBigInt (BigInt.fromInt 3)
      , fromBigInt (BigInt.fromInt 4)
      ]

    -- Compute public key = privateKey * generator
    publicKey :: AffinePoint Vesta.ScalarField
    publicKey = unsafePartial fromJust $ toAffine $ scalarMul privateKey (generator @_ @Pallas.G)

    -- Compute k' = H(pk.x, pk.y, message)
    kPrimeBase = Poseidon.hash $ publicKey.x : publicKey.y : Vector.toUnfoldable message

    kPrime :: Pallas.ScalarField
    kPrime = truncateFieldCoerce kPrimeBase

    -- R = k' * G
    { x: r, y: ry } = unsafePartial fromJust $ toAffine $ scalarMul kPrime (generator @_ @Pallas.G)

    -- Adjust k for even y coordinate
    k = if isEven ry then kPrime else negate kPrime

    -- e = H(pk.x, pk.y, r, message)
    eBase = Poseidon.hash $ publicKey.x : publicKey.y : r : Vector.toUnfoldable message

    -- The circuit uses scaleFast2' which computes [value + 2^n] * base.
    -- For Schnorr: [s + 2^n]*G - [e + 2^n]*Pk = k*G
    -- So: s = k + (e + 2^n)*d - 2^n
    n = fieldSizeBits (Proxy @Vesta.ScalarField)

    twoToN :: Pallas.ScalarField
    twoToN = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)

    e :: Pallas.ScalarField
    e = fromBigInt (toBigInt eBase) + twoToN

    s :: Pallas.ScalarField
    s = k + e * privateKey - twoToN
  in
    { signature: { r: F r, s: F $ fromBigInt $ toBigInt s }
    , publicKey: { x: F publicKey.x, y: F publicKey.y }
    , message: map F message
    }

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
createVestaTestContext :: Aff VestaTestContext
createVestaTestContext = createTestContext'
  { builtState: schnorrBuiltState
  , solver: schnorrSolver
  , input: fixedValidSignature
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
  :: Array Vesta.ScalarField
  -> Int
  -> Vesta.ScalarField
  -> Vesta.ScalarField
computePublicEval publicInputs domainLog2 zeta =
  let
    omega = ProofFFI.domainGenerator domainLog2
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
type IPATestContext =
  { challenges :: Vector 16 Vesta.ScalarField
  , spongeState :: Sponge Pallas.ScalarField
  , combinedPolynomial :: AffinePoint Pallas.ScalarField
  , omega :: Vesta.ScalarField
  }

mkIpaTestContext :: VestaTestContext -> IPATestContext
mkIpaTestContext ctx =
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
