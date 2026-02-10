module Test.Pickles.WrapInputBuilder
  ( buildWrapCircuitInput
  , buildWrapCircuitParams
  , buildWrapClaimedDigest
  , WrapCircuitInput
  , WrapCircuitParams
  ) where

-- | Shared helpers for constructing Wrap circuit input from a VestaTestContext.
-- |
-- | This module is separated from both E2E.purs and WrapE2E.purs to avoid
-- | circular dependencies.

import Prelude

import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.IPA as IPA
import Pickles.PlonkChecks.Permutation (permScalar)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (F(..), SizedF, coerceViaBits, toField, wrapF)
import Snarky.Circuit.Kimchi (Type1, toShifted)
import Snarky.Curves.Class (curveParams, fromBigInt, pow, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.E2E (VestaTestContext, mkIpaTestContext)
import Test.Pickles.ProofFFI as ProofFFI
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Standard Kimchi constants
zkRows :: Int
zkRows = 3

-- | The circuit input type for the Wrap circuit.
type WrapCircuitInput = IncrementallyVerifyProofInput 9 0 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))

-- | Compile-time parameters for the Wrap circuit.
type WrapCircuitParams = IncrementallyVerifyProofParams 9 Pallas.ScalarField

-------------------------------------------------------------------------------
-- | Build WrapCircuitParams from a VestaTestContext
-------------------------------------------------------------------------------

buildWrapCircuitParams :: VestaTestContext -> WrapCircuitParams
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
buildWrapClaimedDigest :: VestaTestContext -> Pallas.ScalarField
buildWrapClaimedDigest ctx = fromBigInt (toBigInt ctx.oracles.fqDigest)

-------------------------------------------------------------------------------
-- | Build WrapCircuitInput from a VestaTestContext
-------------------------------------------------------------------------------

buildWrapCircuitInput :: VestaTestContext -> WrapCircuitInput
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
