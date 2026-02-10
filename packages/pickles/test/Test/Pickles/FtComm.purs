module Test.Pickles.FtComm (spec) where

import Prelude

import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Vector (Vector, toVector)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.FtComm (ftComm)
import Pickles.IPA as IPA
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, assertEq, const_)
import Snarky.Circuit.Kimchi (Type1, toShifted)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (pow)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (StepProofContext, createStepProofContext)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied_)
import Test.Spec (SpecT, beforeAll, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

-- | The ft_comm circuit runs on Fq (= Pallas.ScalarField = Vesta.BaseField).
type CircuitField = Pallas.ScalarField

-- | The quotient polynomial t has 7 chunks (degree up to 7 * domain_size).
type NumTCommChunks = 7

-- | Circuit input: the three shifted scalars from deferred values.
type FtCommInput f =
  { perm :: Type1 f
  , zetaToSrsLength :: Type1 f
  , zetaToDomainSize :: Type1 f
  }

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll createStepProofContext $
  describe "FtComm" do
    it "circuit computes ft_comm matching Rust" ftCommTest

ftCommTest :: StepProofContext -> Aff Unit
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

    -- Scalars in Fp (Vesta scalar field = Pallas base field)
    permScalar :: Pallas.BaseField
    permScalar = ProofFFI.pallasPermScalar ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    zetaToDomainSizeRaw = pow ctx.oracles.zeta n
    maxPolySize = ProofFFI.pallasVerifierIndexMaxPolySize ctx.verifierIndex
    zetaToSrsRaw = pow ctx.oracles.zeta (BigInt.fromInt maxPolySize)

    -- Build shifted circuit inputs (Fp values → Type1 in Fq circuit)
    constPt :: AffinePoint (F CircuitField) -> AffinePoint (FVar CircuitField)
    constPt { x: F x', y: F y' } = { x: const_ x', y: const_ y' }

    circuitInput :: FtCommInput (F CircuitField)
    circuitInput =
      { perm: toShifted (F permScalar)
      , zetaToSrsLength: toShifted (F zetaToSrsRaw)
      , zetaToDomainSize: toShifted (F zetaToDomainSizeRaw)
      }

    circuit
      :: forall t
       . CircuitM CircuitField (KimchiConstraint CircuitField) t Identity
      => FtCommInput (FVar CircuitField)
      -> Snarky (KimchiConstraint CircuitField) t Identity Unit
    circuit { perm, zetaToSrsLength, zetaToDomainSize } = do
      res <- ftComm
        IPA.type1ScalarOps
        { sigmaLast: constPt sigmaLast
        , tComm: map constPt tCommChunks
        , perm
        , zetaToSrsLength
        , zetaToDomainSize
        }
      assertEq (constPt $ coerce expected) res

  -- Sanity check
  liftEffect $ (expected.x /= zero) `shouldEqual` true

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(FtCommInput (F CircuitField)))
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
