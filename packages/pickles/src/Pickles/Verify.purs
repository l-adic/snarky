-- | Wire together the component circuits for incrementallyVerifyProof.
-- |
-- | This is the core verifier circuit, shared by both Step and Wrap:
-- |   1. Computes x_hat (public input commitment)
-- |   2. Runs the Fq-sponge transcript (derives alpha/beta/gamma/zeta)
-- |   3. Asserts deferred values match sponge output
-- |   4. Computes ft_comm
-- |   5. Runs checkBulletproof
-- |
-- | Reference: mina/src/lib/pickles/step_verifier.ml:484-626
module Pickles.Verify
  ( IncrementallyVerifyProofParams
  , IncrementallyVerifyProofInput
  , IncrementallyVerifyProofOutput
  , incrementallyVerifyProof
  , verify
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.FtComm (ftComm)
import Pickles.IPA (CheckBulletproofInput, IpaScalarOps, checkBulletproof)
import Pickles.PublicInputCommit (class PublicInputCommit, publicInputCommit)
import Pickles.Sponge (SpongeM, liftSnarky)
import Pickles.Verify.FqSpongeTranscript (spongeTranscriptCircuit)
import Pickles.Verify.Types (BulletproofChallenges, DeferredValues)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, assertEq, const_, if_)
import Snarky.Circuit.Kimchi (GroupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Compile-time constants from verifier index / SRS.
type IncrementallyVerifyProofParams f =
  { curveParams :: CurveParams f
  , lagrangeComms :: Array (AffinePoint (F f))
  , blindingH :: AffinePoint (F f)
  , sigmaCommLast :: AffinePoint (F f)
  , columnComms ::
      { index :: Vector 6 (AffinePoint (F f))
      , coeff :: Vector 15 (AffinePoint (F f))
      , sigma :: Vector 6 (AffinePoint (F f))
      }
  , indexDigest :: f
  }

-- | Circuit input. sgOldN is 0 or 2.
-- | `publicInput` is the structured public input type (e.g., Vector n (FVar f) for Wrap,
-- | or a protocol-defined record for Step). Must have a PublicInputCommit instance.
-- | `d` is the number of IPA rounds
type IncrementallyVerifyProofInput publicInput sgOldN d fv sf =
  { publicInput :: publicInput
  , sgOld :: Vector sgOldN (AffinePoint fv)
  , deferredValues :: DeferredValues d fv sf
  , wComm :: Vector 15 (AffinePoint fv)
  , zComm :: AffinePoint fv
  , tComm :: Vector 7 (AffinePoint fv)
  , opening ::
      { delta :: AffinePoint fv
      , sg :: AffinePoint fv
      , lr :: Vector d { l :: AffinePoint fv, r :: AffinePoint fv }
      , z1 :: sf
      , z2 :: sf
      }
  }

-- | Output of incrementallyVerifyProof.
type IncrementallyVerifyProofOutput d f =
  { spongeDigestBeforeEvaluations :: FVar f
  , bulletproofChallenges :: BulletproofChallenges d (FVar f)
  , success :: BoolVar f
  }

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

-- | The core verifier circuit.
-- |
-- | Wires together publicInputCommit, spongeTranscript, ftComm, and
-- | checkBulletproof. Asserts deferred values match sponge output.
-- |
-- | Type parameters:
-- | - `publicInput`: structured public input type with PublicInputCommit instance
-- | - `sgOldN`: number of previous proof sg points (0 for base case, 2 for recursion)
-- | - `f`: circuit field (Pallas.ScalarField = Fq for step verifier)
-- | - `f'`: scalar field of commitment curve
-- | - `g`: commitment curve group
-- | - `sf`: shifted scalar type (Type1 or Type2)
incrementallyVerifyProof
  :: forall publicInput sgOldN d f f' @g sf t m _l2 _l3
   . PrimeField f
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => PoseidonField f
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => CircuitM f (KimchiConstraint f) t m
  => PublicInputCommit publicInput f
  => Reflectable d Int
  => Add 1 _l2 7
  => Add 1 _l3 d
  => IpaScalarOps f t m sf
  -> GroupMapParams f
  -> IncrementallyVerifyProofParams f
  -> IncrementallyVerifyProofInput publicInput sgOldN d (FVar f) sf
  -> SpongeM f (KimchiConstraint f) t m (IncrementallyVerifyProofOutput d f)
incrementallyVerifyProof scalarOps groupMapParams_ params input = do
  -- 1. Compute x_hat (public input commitment)
  xHat <- liftSnarky $ publicInputCommit
    params.curveParams
    input.publicInput
    params.lagrangeComms
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

  -- 3. Assert deferred values match sponge output (all 128-bit scalar challenges)
  liftSnarky $
    assertEq { beta, gamma, alpha: alphaChal, zeta: zetaChal } input.deferredValues.plonk

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
    bpInput :: CheckBulletproofInput d (FVar f) sf
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

-------------------------------------------------------------------------------
-- | verify (Step_verifier.verify)
-------------------------------------------------------------------------------

-- | Thin wrapper around incrementallyVerifyProof that asserts:
-- |   1. Sponge digest matches the claimed digest from the unfinalized proof
-- |   2. Bulletproof challenges match the claimed challenges (bypassed for base case)
-- |
-- | Reference: mina/src/lib/pickles/step_verifier.ml:1164-1222
verify
  :: forall publicInput sgOldN d f f' @g sf t m _l2 _l3
   . PrimeField f
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => PoseidonField f
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => CircuitM f (KimchiConstraint f) t m
  => PublicInputCommit publicInput f
  => Reflectable d Int
  => Add 1 _l2 7
  => Add 1 _l3 d
  => IpaScalarOps f t m sf
  -> GroupMapParams f
  -> IncrementallyVerifyProofParams f
  -> IncrementallyVerifyProofInput publicInput sgOldN d (FVar f) sf
  -> BoolVar f -- isBaseCase
  -> FVar f -- claimed spongeDigestBeforeEvaluations
  -> SpongeM f (KimchiConstraint f) t m (BoolVar f)
verify scalarOps groupMapParams_ params input isBaseCase claimedDigest = do
  -- 1. Call incrementallyVerifyProof
  output <- incrementallyVerifyProof @g scalarOps groupMapParams_ params input

  -- 2. Assert sponge digest matches (soft-gated for base case, line 1207)
  liftSnarky do
    digest' <- if_ isBaseCase claimedDigest output.spongeDigestBeforeEvaluations
    assertEq digest' claimedDigest

  -- 3. Assert bulletproof challenges match with base-case bypass (lines 1209-1221)
  liftSnarky $ for_ (Vector.zip input.deferredValues.bulletproofChallenges output.bulletproofChallenges)
    \(Tuple c1 c2) -> do
      c2' <- if_ isBaseCase c1 c2
      assertEq c1 c2'

  -- 4. Return bulletproof success
  pure output.success
