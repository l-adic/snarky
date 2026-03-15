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
import Pickles.IPA (CheckBulletproofInput, checkBulletproof)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode, publicInputCommit)
import Pickles.ShiftOps (IpaScalarOps)
import Pickles.Sponge (SpongeM, initialSpongeCircuit, labelM, liftSnarky)
import Pickles.Sponge as Sponge
import Pickles.Verify.FqSpongeTranscript (spongeTranscriptOptCircuit)
import Pickles.Verify.Types (BulletproofChallenges, DeferredValues, toPlonkMinimal)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import RandomOracle.Sponge (Sponge)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, assertEq, const_, if_, label)
import Snarky.Circuit.Kimchi (GroupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Compile-time constants from verifier index / SRS.
-- | Row-polymorphic so callers can pass wider records (e.g., WrapParams).
type IncrementallyVerifyProofParams :: Type -> Row Type -> Type
type IncrementallyVerifyProofParams f r =
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
  , endo :: f -- ^ EndoScalar constant for challenge expansion
  , groupMapParams :: GroupMapParams f
  , correctionMode :: CorrectionMode
  , useOptSponge :: Boolean -- ^ true for Wrap (Opt_sponge), false for Step (regular sponge)
  | r
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
  :: forall publicInput sgOldN totalBases d f f' @g sf t m _l3 _l4 r
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
  => Add 1 _l3 d
  => Add sgOldN 45 totalBases
  => Add 1 _l4 totalBases
  => IpaScalarOps f t m sf
  -> IncrementallyVerifyProofParams f r
  -> IncrementallyVerifyProofInput publicInput sgOldN d (FVar f) sf
  -> SpongeM f (KimchiConstraint f) t m (IncrementallyVerifyProofOutput d f)
incrementallyVerifyProof scalarOps params input = labelM "incrementally-verify-proof" do
  let endoParams = { endo: const_ params.endo, groupMapParams: params.groupMapParams }

  -- 1. Compute index_digest by hashing VK commitments (matches OCaml sponge_after_index)
  indexDigest <- liftSnarky $ label "ivp_index_digest" $
    Sponge.evalSpongeM (initialSpongeCircuit :: Sponge (FVar f)) do
      -- Absorption order matches OCaml's index_to_field_elements:
      -- sigma_comm (7) → coefficients_comm (15) → index comms (6)
      let
        absorbConstPt { x: F x', y: F y' } = do
          Sponge.absorb (const_ x')
          Sponge.absorb (const_ y')
      -- sigma_comm: sigma (6) + sigmaCommLast (1) = 7
      for_ params.columnComms.sigma absorbConstPt
      absorbConstPt params.sigmaCommLast
      -- coefficients_comm: 15
      for_ params.columnComms.coeff absorbConstPt
      -- index comms: generic, psm, complete_add, mul, emul, endomul_scalar = 6
      for_ params.columnComms.index absorbConstPt
      -- Squeeze digest
      Sponge.squeeze

  -- 2. Sponge transcript + x_hat
  -- Step (regular sponge): absorb index_digest + sg_old BEFORE x_hat, matching
  --   OCaml step_verifier.ml ordering. Uses regular sponge (not Opt_sponge).
  -- Wrap (OptSponge): compute x_hat first, then run spongeTranscriptOptCircuit.
  { xHat, beta, gamma, alphaChal, zetaChal, digest } <-
    if params.useOptSponge then do
      -- Wrap path: compute x_hat first, then OptSponge for all absorptions
      xHat <- liftSnarky $ label "ivp_xhat" $ publicInputCommit params input.publicInput
      let spongeInput = { indexDigest, sgOld: input.sgOld, publicComm: xHat, wComm: input.wComm, zComm: input.zComm, tComm: input.tComm }
      result <- labelM "ivp_opt_sponge" $ spongeTranscriptOptCircuit endoParams spongeInput
      pure { xHat, beta: result.beta, gamma: result.gamma, alphaChal: result.alphaChal, zetaChal: result.zetaChal, digest: result.digest }
    else do
      -- Step path: absorb index_digest + sg_old into main sponge BEFORE x_hat
      -- Matches step_verifier.ml:528-530
      Sponge.absorb indexDigest
      for_ input.sgOld Sponge.absorbPoint
      -- Compute x_hat
      xHat <- liftSnarky $ label "ivp_xhat" $ publicInputCommit params input.publicInput
      -- Continue sponge transcript: absorb x_hat, w_comm, squeeze beta/gamma, etc.
      -- step_verifier.ml:551-568
      Sponge.absorbPoint xHat
      for_ input.wComm Sponge.absorbPoint
      -- beta/gamma: squeeze_challenge (constrain_low_bits:true)
      beta <- Sponge.squeezeScalarChallenge endoParams
      gamma <- Sponge.squeezeScalarChallenge endoParams
      -- z_comm: receive
      Sponge.absorbPoint input.zComm
      -- alpha: squeeze_scalar (constrain_low_bits:false)
      alphaChal <- Sponge.squeezeScalar endoParams
      -- t_comm: receive
      for_ input.tComm Sponge.absorbPoint
      -- zeta: squeeze_scalar (constrain_low_bits:false)
      zetaChal <- Sponge.squeezeScalar endoParams
      -- Copy sponge before squeezing digest (step_verifier.ml:559)
      spongeBeforeEvals <- Sponge.getSponge
      digest <- Sponge.squeeze
      Sponge.putSponge spongeBeforeEvals
      pure { xHat, beta, gamma, alphaChal, zetaChal, digest }

  -- 3. Assert deferred values match sponge output (all 128-bit scalar challenges)
  liftSnarky $ label "ivp_assert_plonk" $
    assertEq { beta, gamma, alpha: alphaChal, zeta: zetaChal } (toPlonkMinimal input.deferredValues.plonk)

  -- 4. Compute ft_comm
  ftCommResult <- liftSnarky $ label "ivp_ftcomm" $ ftComm
    scalarOps
    { sigmaLast: constPt params.sigmaCommLast
    , tComm: input.tComm
    , perm: input.deferredValues.plonk.perm
    , zetaToSrsLength: input.deferredValues.plonk.zetaToSrsLength
    , zetaToDomainSize: input.deferredValues.plonk.zetaToDomainSize
    }

  -- 5. Assemble commitment bases: sg_old + 45 fixed bases (to_batch order)
  -- Matches OCaml: sg_old[0..1], x_hat, ft_comm, z_comm, index(6), w_comm(15), coeff(15), sigma(6)
  let
    allBases :: Vector totalBases (AffinePoint (FVar f))
    allBases =
      input.sgOld `Vector.append`
        ( (xHat :< ftCommResult :< input.zComm :< Vector.nil)
            `Vector.append` map constPt params.columnComms.index
            `Vector.append` input.wComm
            `Vector.append` map constPt params.columnComms.coeff
            `Vector.append` map constPt params.columnComms.sigma
        )

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

  { success, challenges } <- labelM "ivp_bulletproof" $ checkBulletproof @f @g
    scalarOps
    endoParams
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
  :: forall publicInput sgOldN totalBases d f f' @g sf t m _l2 _l3 _l4 r
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
  => Add sgOldN 45 totalBases
  => Add 1 _l4 totalBases
  => IpaScalarOps f t m sf
  -> IncrementallyVerifyProofParams f r
  -> IncrementallyVerifyProofInput publicInput sgOldN d (FVar f) sf
  -> BoolVar f -- isBaseCase
  -> FVar f -- claimed spongeDigestBeforeEvaluations
  -> SpongeM f (KimchiConstraint f) t m (BoolVar f)
verify scalarOps params input isBaseCase claimedDigest = labelM "verify" do
  -- 1. Call incrementallyVerifyProof
  output <- incrementallyVerifyProof @g scalarOps params input

  -- 2. Assert sponge digest matches (soft-gated for base case, line 1207)
  labelM "ivp_assert_digest" $ liftSnarky do
    digest' <- if_ isBaseCase claimedDigest output.spongeDigestBeforeEvaluations
    assertEq digest' claimedDigest

  -- 3. Assert bulletproof challenges match with base-case bypass (lines 1209-1221)
  labelM "ivp_assert_bp_challenges" $ liftSnarky $
    for_ (Vector.zip input.deferredValues.bulletproofChallenges output.bulletproofChallenges)
      \(Tuple c1 c2) -> do
        c2' <- if_ isBaseCase c1 c2
        assertEq c1 c2'

  -- 4. Return bulletproof success
  pure output.success
