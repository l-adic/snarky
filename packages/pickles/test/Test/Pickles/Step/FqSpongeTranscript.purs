-- | Test the Fq-sponge absorption sequence for incrementallyVerifyProof.
-- |
-- | Replays the FqSponge transcript in pure PureScript over Fq (= Pallas.ScalarField)
-- | and compares challenges/digest against Rust Kimchi verifier oracle values.
-- |
-- | Also includes a circuit spec that proves the same computation can be
-- | expressed as a Kimchi circuit.
-- |
-- | The sponge continuity test validates that the sponge state after the
-- | transcript correctly threads into check_bulletproof by comparing
-- | against the Rust sponge checkpoint.
module Test.Pickles.Step.FqSpongeTranscript (spec) where

import Prelude

import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Pickles.Sponge (evalPureSpongeM, evalSpongeM, initialSponge, initialSpongeCircuit)
import Pickles.Verify.FqSpongeTranscript (FqSpongeInput, FqSpongeOutput, spongeTranscriptCircuit, spongeTranscriptPure)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (F(..), SizedF, coerceViaBits, toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (InductiveTestContext, StepProofContext)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

-- | For the Schnorr test, the sponge operates over Pallas.ScalarField.
type SpongeField = Pallas.ScalarField

-------------------------------------------------------------------------------
-- | F-wrapped pure reference for circuit spec.
-- | Safe because F is a newtype with identical runtime representation.
-------------------------------------------------------------------------------

spongeTranscriptF
  :: forall sgOldN chunks
   . FqSpongeInput sgOldN chunks (F SpongeField)
  -> FqSpongeOutput (F SpongeField)
spongeTranscriptF = coerce (evalPureSpongeM initialSponge <<< spongeTranscriptPure :: FqSpongeInput sgOldN chunks SpongeField -> FqSpongeOutput SpongeField)

-------------------------------------------------------------------------------
-- | For the Schnorr test circuit, t_comm has 7 chunks.
-- | This is validated at test setup time against the actual verifier index.
-------------------------------------------------------------------------------

type SchnorrTCommChunks = 7

type SchnorrFqSpongeInput = FqSpongeInput 0 SchnorrTCommChunks (F SpongeField)

-------------------------------------------------------------------------------
-- | Test spec (wrapped in Identity for mapSpec)
-------------------------------------------------------------------------------

spec :: SpecT Aff InductiveTestContext Aff Unit
spec =
  describe "Fq-sponge transcript" do
    it "produces correct digest matching Rust oracles" \{ step0 } -> do
      let ctx = buildFqSpongeTestContext step0
      liftEffect $ toBigInt ctx.result.digest `shouldEqual` toBigInt ctx.oracles.fqDigest

    it "produces correct alpha challenge matching Rust oracles" \{ step0 } -> do
      let
        ctx = buildFqSpongeTestContext step0

        psAlpha :: SizedF 128 Vesta.ScalarField
        psAlpha = coerceViaBits ctx.result.alphaChal
      liftEffect $ psAlpha `shouldEqual` ctx.oracles.alphaChal

    it "produces correct zeta challenge matching Rust oracles" \{ step0 } -> do
      let
        ctx = buildFqSpongeTestContext step0

        psZeta :: SizedF 128 Vesta.ScalarField
        psZeta = coerceViaBits ctx.result.zetaChal
      liftEffect $ psZeta `shouldEqual` ctx.oracles.zetaChal

    it "produces correct beta matching Rust oracles" \{ step0 } -> do
      let
        ctx = buildFqSpongeTestContext step0

        psBeta :: Vesta.ScalarField
        psBeta = toField (coerceViaBits ctx.result.beta :: SizedF 128 Vesta.ScalarField)
      liftEffect $ toBigInt psBeta `shouldEqual` toBigInt (toField ctx.oracles.beta)

    it "produces correct gamma matching Rust oracles" \{ step0 } -> do
      let
        ctx = buildFqSpongeTestContext step0

        psGamma :: Vesta.ScalarField
        psGamma = toField (coerceViaBits ctx.result.gamma :: SizedF 128 Vesta.ScalarField)
      liftEffect $ toBigInt psGamma `shouldEqual` toBigInt (toField ctx.oracles.gamma)

    it "circuit is satisfiable and matches pure implementation" \{ step0 } -> do
      let ctx = buildFqSpongeTestContext step0
      circuitSpecPureInputs
        { builtState: compilePure
            (Proxy @SchnorrFqSpongeInput)
            (Proxy @(FqSpongeOutput (F SpongeField)))
            (Proxy @(KimchiConstraint SpongeField))
            (\input -> evalSpongeM initialSpongeCircuit (spongeTranscriptCircuit input))
            Kimchi.initialState
        , checker: Kimchi.eval
        , solver: makeSolver (Proxy @(KimchiConstraint SpongeField)) (\input -> evalSpongeM initialSpongeCircuit (spongeTranscriptCircuit input))
        , testFunction: satisfied spongeTranscriptF
        , postCondition: Kimchi.postCondition
        }
        [ ctx.circuitInput ]

-------------------------------------------------------------------------------
-- | Test context
-------------------------------------------------------------------------------

type FqSpongeTestContext =
  { oracles ::
      { fqDigest :: Vesta.ScalarField
      , alphaChal :: SizedF 128 Vesta.ScalarField
      , zetaChal :: SizedF 128 Vesta.ScalarField
      , beta :: SizedF 128 Vesta.ScalarField
      , gamma :: SizedF 128 Vesta.ScalarField
      }
  , result :: FqSpongeOutput SpongeField
  , circuitInput :: SchnorrFqSpongeInput
  }

-- | Build the FqSponge test context from a StepProofContext.
-- | Pure computation: extracts commitments and runs the sponge transcript.
buildFqSpongeTestContext :: StepProofContext -> FqSpongeTestContext
buildFqSpongeTestContext ctx =
  let
    commitments = ProofFFI.pallasProofCommitments ctx.proof
    publicCommArray = ProofFFI.pallasPublicComm ctx.verifierIndex ctx.publicInputs

    indexDigest = ProofFFI.pallasVerifierIndexDigest ctx.verifierIndex
    publicComm = unsafePartial fromJust $ Array.head publicCommArray
    wComm = commitments.wComm
    zComm = commitments.zComm

    tComm :: Vector SchnorrTCommChunks (AffinePoint SpongeField)
    tComm = unsafePartial fromJust $ Vector.toVector commitments.tComm

    input = { indexDigest, sgOld: Vector.nil, publicComm, wComm, zComm, tComm }
    result = evalPureSpongeM initialSponge (spongeTranscriptPure input)

    circuitInput :: SchnorrFqSpongeInput
    circuitInput =
      { indexDigest: F indexDigest
      , sgOld: Vector.nil
      , publicComm: coerce publicComm
      , wComm: coerce wComm
      , zComm: coerce zComm
      , tComm: coerce tComm
      }
  in
    { oracles:
        { fqDigest: ctx.oracles.fqDigest
        , alphaChal: ctx.oracles.alphaChal
        , zetaChal: ctx.oracles.zetaChal
        , beta: ctx.oracles.beta
        , gamma: ctx.oracles.gamma
        }
    , result
    , circuitInput
    }
