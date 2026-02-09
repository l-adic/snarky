module Test.Pickles.CombinedPolyComm (spec) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (combinePolynomials)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, SizedF, Snarky, assertEq, coerceViaBits, const_)
import Snarky.Circuit.Kimchi (expandToEndoScalar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (fromAffine, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.E2E (VestaTestContext, createVestaTestContext)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied_)
import Test.Spec (SpecT, beforeAll, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

-- | The combined polynomial commitment circuit runs on Fq (= Pallas.ScalarField).
type CircuitField = Pallas.ScalarField

-- | Circuit input: the 128-bit polyscale challenge (xi).
-- | Powers of xi are computed implicitly via Horner accumulation.
type CombinedPolyCommInput f = { xi :: SizedF 128 f }

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll createVestaTestContext $
  describe "CombinedPolyComm" do
    it "circuit computes combined polynomial commitment matching Rust" combinedPolyCommTest

combinedPolyCommTest :: VestaTestContext -> Aff Unit
combinedPolyCommTest ctx = do
  let
    -- Ground truth from Rust
    expected :: AffinePoint CircuitField
    expected = ProofFFI.pallasCombinedPolynomialCommitment ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Assemble all 45 commitment bases in to_batch order

    -- 1. public_comm (1 point)
    publicComm :: AffinePoint Pallas.ScalarField
    publicComm = unsafePartial fromJust $ Array.head $
      ProofFFI.pallasPublicComm ctx.verifierIndex ctx.publicInputs

    -- 2. ft_comm (1 point)
    ftComm :: AffinePoint Pallas.ScalarField
    ftComm = ProofFFI.pallasFtComm ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- 3. z_comm and w_comm from proof commitments
    commitments = ProofFFI.pallasProofCommitments ctx.proof

    -- 4. VK column commitments (27 points: 6 index + 15 coeff + 6 sigma)
    columnCommsRaw :: Array (AffinePoint Pallas.ScalarField)
    columnCommsRaw = ProofFFI.pallasVerifierIndexColumnComms ctx.verifierIndex

    indexComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    indexComms = unsafePartial fromJust $ Vector.toVector @6 $ Array.take 6 columnCommsRaw

    coeffComms :: Vector 15 (AffinePoint Pallas.ScalarField)
    coeffComms = unsafePartial fromJust $ Vector.toVector @15 $ Array.take 15 $ Array.drop 6 columnCommsRaw

    sigmaComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    sigmaComms = unsafePartial fromJust $ Vector.toVector @6 $ Array.drop 21 columnCommsRaw

    -- Assemble in to_batch order:
    -- public(1), ft(1), z(1), index(6), w(15), coeff(15), sigma(6) = 45
    constPt :: AffinePoint CircuitField -> AffinePoint (FVar CircuitField)
    constPt { x, y } = { x: const_ x, y: const_ y }

    allBases :: Vector 45 (AffinePoint (FVar CircuitField))
    allBases = map constPt $
      (publicComm :< ftComm :< commitments.zComm :< Vector.nil)
        `Vector.append` indexComms
        `Vector.append` commitments.wComm
        `Vector.append` coeffComms
        `Vector.append` sigmaComms

    -- xi (polyscale challenge) - convert from Fp to circuit field Fq
    -- ctx.oracles.vChal :: SizedF 128 Vesta.ScalarField (= Fp)
    xiChalFq :: SizedF 128 CircuitField
    xiChalFq = coerceViaBits ctx.oracles.vChal

  -- Sanity check: expected is non-trivial
  liftEffect $ (expected.x /= zero) `shouldEqual` true

  -- Verify pure Horner accumulation matches Rust
  let
    -- Expand 128-bit challenge to full Vesta scalar via endo decomposition
    v :: Pallas.BaseField
    v = expandToEndoScalar xiChalFq

    toG :: AffinePoint CircuitField -> Vesta.G
    toG pt = fromAffine @CircuitField @Vesta.G pt

    -- Horner right-to-left: Q = C_0 + v*(C_1 + v*(C_2 + ... + v*C_{n-1}))
    -- Fold left over reversed bases: start with C_{n-1}, then acc = C_i + v*acc
    rawBases :: Vector 45 (AffinePoint CircuitField)
    rawBases =
      (publicComm :< ftComm :< commitments.zComm :< Vector.nil)
        `Vector.append` indexComms
        `Vector.append` commitments.wComm
        `Vector.append` coeffComms
        `Vector.append` sigmaComms
    reversedBases = Vector.reverse rawBases
    { head, tail } = Vector.uncons reversedBases

    pureResult = unsafePartial fromJust $ toAffine @CircuitField @Vesta.G $
      foldl (\acc base -> toG base <> scalarMul v acc) (toG head) tail

  liftEffect $ pureResult `shouldEqual` expected

  -- Circuit test
  let
    circuitInput :: CombinedPolyCommInput (F CircuitField)
    circuitInput = { xi: coerce xiChalFq }

    circuit
      :: forall t
       . CircuitM CircuitField (KimchiConstraint CircuitField) t Identity
      => CombinedPolyCommInput (FVar CircuitField)
      -> Snarky (KimchiConstraint CircuitField) t Identity Unit
    circuit { xi } = do
      result <- combinePolynomials allBases xi
      assertEq result { x: const_ expected.x, y: const_ expected.y }

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(CombinedPolyCommInput (F CircuitField)))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint CircuitField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint CircuitField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]
