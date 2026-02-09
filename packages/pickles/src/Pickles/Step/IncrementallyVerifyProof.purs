-- | Wire together the component circuits for incrementallyVerifyProof.
-- |
-- | This is the core Step verifier circuit that:
-- |   1. Computes x_hat (public input commitment)
-- |   2. Runs the Fq-sponge transcript (derives alpha/beta/gamma/zeta)
-- |   3. Asserts deferred values match sponge output
-- |   4. Computes ft_comm
-- |   5. Runs checkBulletproof
-- |
-- | Reference: mina/src/lib/pickles/step_verifier.ml:484-626
module Pickles.Step.IncrementallyVerifyProof
  ( IncrementallyVerifyProofParams
  , IncrementallyVerifyProofInput
  , IncrementallyVerifyProofOutput
  , incrementallyVerifyProof
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.FtComm (ftComm)
import Pickles.IPA (CheckBulletproofInput, IpaScalarOps, checkBulletproof)
import Pickles.PublicInputCommitment (publicInputCommitment)
import Pickles.Sponge (SpongeM, liftSnarky)
import Pickles.Step.FqSpongeTranscript (spongeTranscriptCircuit)
import Pickles.Step.Types (BulletproofChallenges, DeferredValues)
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, assertEq, assertEqual_, const_)
import Snarky.Circuit.DSL as SizedF
import Snarky.Circuit.Kimchi (GroupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Compile-time constants from verifier index / SRS.
type IncrementallyVerifyProofParams nPublic f =
  { curveParams :: CurveParams f
  , lagrangeComms :: Vector nPublic (AffinePoint (F f))
  , blindingH :: AffinePoint (F f)
  , sigmaCommLast :: AffinePoint (F f)
  , columnComms ::
      { index :: Vector 6 (AffinePoint (F f))
      , coeff :: Vector 15 (AffinePoint (F f))
      , sigma :: Vector 6 (AffinePoint (F f))
      }
  , indexDigest :: f
  }

-- | Circuit input. sgOldN is 0 or 2, nPublic is # of public inputs.
-- | `fv` is `F f` for values or `FVar f` for circuit variables.
type IncrementallyVerifyProofInput nPublic sgOldN fv sf =
  { publicInput :: Vector nPublic fv
  , sgOld :: Vector sgOldN (AffinePoint fv)
  , deferredValues :: DeferredValues fv sf
  , wComm :: Vector 15 (AffinePoint fv)
  , zComm :: AffinePoint fv
  , tComm :: Vector 7 (AffinePoint fv)
  , opening ::
      { delta :: AffinePoint fv
      , sg :: AffinePoint fv
      , lr :: Vector 16 { l :: AffinePoint fv, r :: AffinePoint fv }
      , z1 :: sf
      , z2 :: sf
      }
  }

-- | Output of incrementallyVerifyProof.
type IncrementallyVerifyProofOutput f =
  { spongeDigestBeforeEvaluations :: FVar f
  , bulletproofChallenges :: BulletproofChallenges (FVar f)
  , success :: BoolVar f
  }

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

-- | The core step verifier circuit.
-- |
-- | Wires together publicInputCommitment, spongeTranscript, ftComm, and
-- | checkBulletproof. Asserts deferred values match sponge output.
-- |
-- | Type parameters:
-- | - `nChunks`: chunks for publicInputCommitment MSM (typically 51)
-- | - `sgOldN`: number of previous proof sg points (0 for base case, 2 for recursion)
-- | - `f`: circuit field (Pallas.ScalarField = Fq for step verifier)
-- | - `f'`: scalar field of commitment curve
-- | - `g`: commitment curve group
-- | - `sf`: shifted scalar type (Type1 or Type2)
incrementallyVerifyProof
  :: forall @nChunks nPublic sgOldN f f' @g sf t m bitsUsed sDiv2Bits _l _l2
   . PrimeField f
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => PoseidonField f
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => CircuitM f (KimchiConstraint f) t m
  => Add bitsUsed _l 255
  => Add sDiv2Bits 1 255
  => Mul 5 nChunks bitsUsed
  => Reflectable sDiv2Bits Int
  => Reflectable bitsUsed Int
  => Reflectable nPublic Int
  => Add 1 _l2 7
  => IpaScalarOps f (KimchiConstraint f) t m sf
  -> GroupMapParams f
  -> IncrementallyVerifyProofParams nPublic f
  -> IncrementallyVerifyProofInput nPublic sgOldN (FVar f) sf
  -> SpongeM f (KimchiConstraint f) t m (IncrementallyVerifyProofOutput f)
incrementallyVerifyProof scalarOps groupMapParams_ params input = do
  -- 1. Compute x_hat (public input commitment)
  let
    pairs = unsafePartial fromJust $ NEA.fromFoldable $
      Vector.zipWith (\scalar base -> { scalar, base })
        input.publicInput
        params.lagrangeComms
  xHat <- liftSnarky $ publicInputCommitment @nChunks
    params.curveParams
    pairs
    params.blindingH

  -- 2. Run Fq-sponge transcript
  let
    spongeInput =
      { indexDigest: const_ params.indexDigest
      , sgOld: input.sgOld
      , publicComm: xHat
      , wComm: input.wComm
      , zComm: input.zComm
      , tComm: input.tComm
      }
  { beta, gamma, alphaChal, zetaChal, digest } <- spongeTranscriptCircuit spongeInput

  -- 3. Assert deferred values match sponge output
  liftSnarky do
    -- Beta/gamma: full field element comparison
    assertEqual_ (SizedF.toField beta) input.deferredValues.plonk.beta
    assertEqual_ (SizedF.toField gamma) input.deferredValues.plonk.gamma
    -- Alpha/zeta: raw 128-bit scalar challenge comparison
    assertEq alphaChal input.deferredValues.plonk.alpha
    assertEq zetaChal input.deferredValues.plonk.zeta

  -- 4. Compute ft_comm
  ftCommResult <- liftSnarky $ ftComm
    scalarOps
    { sigmaLast: constPt params.sigmaCommLast
    , tComm: input.tComm
    , perm: input.deferredValues.perm
    , zetaToSrsLength: input.deferredValues.zetaToSrsLength
    , zetaToDomainSize: input.deferredValues.zetaToDomainSize
    }

  -- 5. Assemble 45 commitment bases in to_batch order
  let
    allBases :: Vector 45 (AffinePoint (FVar f))
    allBases =
      (xHat :< ftCommResult :< input.zComm :< Vector.nil)
        `Vector.append` map constPt params.columnComms.index
        `Vector.append` input.wComm
        `Vector.append` map constPt params.columnComms.coeff
        `Vector.append` map constPt params.columnComms.sigma

  -- 6. Build CheckBulletproofInput and run checkBulletproof
  let
    bpInput :: CheckBulletproofInput 16 (FVar f) sf
    bpInput =
      { xi: input.deferredValues.xi
      , delta: input.opening.delta
      , sg: input.opening.sg
      , lr: input.opening.lr
      , z1: input.opening.z1
      , z2: input.opening.z2
      , combinedInnerProduct: input.deferredValues.combinedInnerProduct
      , b: input.deferredValues.b
      , blindingGenerator: constPt params.blindingH
      }

  { success, challenges } <- checkBulletproof @f @g
    scalarOps
    groupMapParams_
    allBases
    bpInput

  -- 7. Return output
  pure { spongeDigestBeforeEvaluations: digest, bulletproofChallenges: challenges, success }

  where
  constPt :: AffinePoint (F f) -> AffinePoint (FVar f)
  constPt { x: F x', y: F y' } = { x: const_ x', y: const_ y' }
