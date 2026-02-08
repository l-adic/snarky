module Test.Pickles.FtComm (spec) where

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (fold)
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Vector (Vector, toVector, zipWith)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.FtComm (ftCommCircuit)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams, fromAffine, fromBigInt, pow, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.E2E (TestContext, createTestContext)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied)
import Test.Spec (SpecT, beforeAll, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

-- | The ft_comm circuit runs on Fq (= Pallas.ScalarField = Vesta.BaseField).
-- | The chunk scalars are pre-computed in Fp (Vesta's scalar field) and coerced
-- | to Fq as circuit inputs, because computing them in Fq would give wrong results
-- | (different field arithmetic). In the real step verifier (Fp circuit), the chunk
-- | scalars can be computed in-circuit since the circuit field matches the scalar field.
type CircuitField = Pallas.ScalarField

-- | The quotient polynomial t has 7 chunks (degree up to 7 * domain_size).
type NumTCommChunks = 7

-- | Circuit input: perm_scalar and the 7 chunk scalars (pre-computed in Fp, coerced to Fq).
type FtCommInput f =
  { permScalar :: f
  , chunkScalars :: Vector NumTCommChunks f
  }

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll createTestContext $
  describe "FtComm" do
    it "circuit computes ft_comm matching Rust" ftCommTest

ftCommTest :: TestContext -> Aff Unit
ftCommTest ctx = do
  let
    -- Ground truth from Rust
    expected :: AffinePoint CircuitField
    expected = ProofFFI.pallasFtComm ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Constant bases (Fq-coordinate Vesta points)
    sigmaLast :: AffinePoint (F CircuitField)
    sigmaLast = coerce $ ProofFFI.pallasSigmaCommLast ctx.verifierIndex

    tCommChunks :: Vector NumTCommChunks (AffinePoint (F CircuitField))
    tCommChunks = unsafePartial fromJust $ toVector @NumTCommChunks $
      coerce (ProofFFI.pallasProofCommitments ctx.proof).tComm

    -- perm_scalar from Rust (independent input)
    permScalar :: Pallas.BaseField
    permScalar = ProofFFI.pallasPermScalar ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Chunk scalars: -(zeta^n - 1) * (zeta^max_poly_size)^i
    -- Computed in Fp (Vesta's scalar field), the correct field for Vesta MSM
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    zetaToDomainSize = pow ctx.oracles.zeta n
    negZetaNMinusOne = one - zetaToDomainSize
    maxPolySize = ProofFFI.pallasVerifierIndexMaxPolySize ctx.verifierIndex
    zetaToSrs = pow ctx.oracles.zeta (BigInt.fromInt maxPolySize)

    tCommChunkScalars :: Vector NumTCommChunks Vesta.ScalarField
    tCommChunkScalars = Vector.generate \i ->
      negZetaNMinusOne * pow zetaToSrs (BigInt.fromInt $ getFinite i)

    -- Coerce Fp -> Fq via BigInt (safe because Fp < Fq in Pasta)
    fpToFq :: Pallas.BaseField -> F CircuitField
    fpToFq x = F (fromBigInt (toBigInt x))

    -- All 8 scalar-base pairs for the pure check
    allScalars = Vector.cons permScalar tCommChunkScalars
    allBases = Vector.cons sigmaLast tCommChunks

  -- Sanity check
  liftEffect $ (expected.x /= zero) `shouldEqual` true

  -- Verify pure group arithmetic matches Rust
  let
    unwrapPt :: AffinePoint (F CircuitField) -> Vesta.G
    unwrapPt { x: F x', y: F y' } =
      fromAffine @Pallas.ScalarField @Vesta.G { x: x', y: y' }

    terms = zipWith (\s pt -> scalarMul s (unwrapPt pt)) allScalars allBases
    pureResult = unsafePartial fromJust $ toAffine @Pallas.ScalarField @Vesta.G $
      fold terms

  liftEffect $ pureResult `shouldEqual` expected

  -- Circuit test using ftCommCircuit with pre-computed scalars
  let
    ftCommParams =
      { sigmaLast
      , tCommChunks
      , curveParams: curveParams (Proxy @Vesta.G)
      }

    circuitInput :: FtCommInput (F CircuitField)
    circuitInput =
      { permScalar: fpToFq permScalar
      , chunkScalars: map fpToFq tCommChunkScalars
      }

    circuit
      :: forall t
       . CircuitM CircuitField (KimchiConstraint CircuitField) t Identity
      => FtCommInput (FVar CircuitField)
      -> Snarky (KimchiConstraint CircuitField) t Identity (AffinePoint (FVar CircuitField))
    circuit = ftCommCircuit ftCommParams

    testFn :: FtCommInput (F CircuitField) -> AffinePoint (F CircuitField)
    testFn _ = coerce expected

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(FtCommInput (F CircuitField)))
        (Proxy @(AffinePoint (F CircuitField)))
        (Proxy @(KimchiConstraint CircuitField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint CircuitField)) circuit
    , testFunction: satisfied testFn
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]
