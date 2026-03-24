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
  , packStatement
  , verify
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
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
import Pickles.Verify.Types (BranchData, BulletproofChallenges, DeferredValues, PlonkInCircuit, WrapDeferredValues, toPlonkMinimal)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeMkSizedF)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, assertEq, const_, if_, label)
import Snarky.Circuit.Kimchi (GroupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | SRS-derived constants (true environment, known outside the circuit).
-- | Row-polymorphic so callers can pass wider records (e.g., WrapParams).
-- |
-- | The verifier index data (columnComms, sigmaCommLast) is NOT here — in OCaml
-- | it enters the Step circuit via `exists ~request:(fun () -> Req.Wrap_index)`
-- | as circuit variables (step_main.ml:345-348). It lives in the input instead.
type IncrementallyVerifyProofParams :: Type -> Row Type -> Type
type IncrementallyVerifyProofParams f r =
  { curveParams :: CurveParams f
  , lagrangeComms :: Array (AffinePoint (F f))
  , blindingH :: AffinePoint (F f)
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
-- |
-- | The verifier index fields (columnComms, sigmaCommLast) are circuit variables,
-- | not constants. In OCaml they enter the Step circuit via
-- | `exists ~request:(fun () -> Req.Wrap_index)` (step_main.ml:345-348).
-- | In the Wrap circuit they are constants (wrap_main.ml:209 Inner_curve.constant).
-- | Either way, by the time they reach this function they are `fv` (FVar f).
type IncrementallyVerifyProofInput publicInput sgOldN d fv sf =
  { publicInput :: publicInput
  , sgOld :: Vector sgOldN (AffinePoint fv)
  , deferredValues :: DeferredValues d fv sf
  -- Verifier index (VK) data — circuit variables in Step, constants in Wrap
  , sigmaCommLast :: AffinePoint fv
  , columnComms ::
      { index :: Vector 6 (AffinePoint fv)
      , coeff :: Vector 15 (AffinePoint fv)
      , sigma :: Vector 6 (AffinePoint fv)
      }
  -- Protocol messages and opening proof
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
  -> Maybe (Sponge (FVar f)) -- ^ Pre-computed sponge_after_index. Nothing = compute internally.
  -> SpongeM f (KimchiConstraint f) t m (IncrementallyVerifyProofOutput d f)
incrementallyVerifyProof scalarOps params input mSpongeAfterIndex = labelM "incrementally-verify-proof" do
  let endoParams = { endo: const_ params.endo, groupMapParams: params.groupMapParams }

  -- 1. Compute index_digest by hashing VK commitments (matches OCaml sponge_after_index)
  -- When sponge_after_index is provided (full verify_one), just copy+squeeze.
  -- When Nothing (standalone IVP), compute from scratch.
  -- Reference: step_verifier.ml:530-536
  indexDigest <- liftSnarky $ label "ivp_index_digest" $ case mSpongeAfterIndex of
    Just spongeAfterIndex ->
      -- OCaml: let index_sponge = Sponge.copy sponge_after_index in
      --        Sponge.squeeze_field index_sponge
      Sponge.evalSpongeM spongeAfterIndex Sponge.squeeze
    Nothing ->
      Sponge.evalSpongeM (initialSpongeCircuit :: Sponge (FVar f)) do
        -- Absorption order matches OCaml's index_to_field_elements:
        -- sigma_comm (7) → coefficients_comm (15) → index comms (6)
        let
          absorbPt { x, y } = do
            Sponge.absorb x
            Sponge.absorb y
        -- sigma_comm: sigma (6) + sigmaCommLast (1) = 7
        for_ input.columnComms.sigma absorbPt
        absorbPt input.sigmaCommLast
        -- coefficients_comm: 15
        for_ input.columnComms.coeff absorbPt
        -- index comms: generic, psm, complete_add, mul, emul, endomul_scalar = 6
        for_ input.columnComms.index absorbPt
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
      labelM "ivp_absorb_index_digest" $ Sponge.absorb indexDigest
      labelM "ivp_absorb_sg_old" $ for_ input.sgOld \pt -> do
        labelM "ivp_sg_x" $ Sponge.absorb pt.x
        labelM "ivp_sg_y" $ Sponge.absorb pt.y
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
    { sigmaLast: input.sigmaCommLast
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
            `Vector.append` input.columnComms.index
            `Vector.append` input.wComm
            `Vector.append` input.columnComms.coeff
            `Vector.append` input.columnComms.sigma
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
-- | packStatement (Spec.pack + to_data for WrapStatement)
-------------------------------------------------------------------------------

-- | Convert a WrapStatement into the public input tuple expected by the IVP.
-- |
-- | This is the PureScript equivalent of OCaml's
-- |   Spec.pack (Types.Wrap.Statement.In_circuit.spec ...) (to_data statement)
-- |
-- | The result type matches the PublicInputCommit instance used by publicInputCommit.
-- |
-- | Reference: step_verifier.ml:1249-1264
packStatement
  :: forall d f sf
   . PrimeField f
  => { proofState ::
         { deferredValues :: WrapDeferredValues d (FVar f) sf (BoolVar f)
         , spongeDigestBeforeEvaluations :: FVar f
         , messagesForNextWrapProof :: FVar f
         }
     , messagesForNextStepProof :: FVar f
     }
  -> Tuple (Vector 5 sf)
       (Tuple (Vector 2 (SizedF 128 (FVar f)))
         (Tuple (Vector 3 (SizedF 128 (FVar f)))
           (Tuple (Vector 3 (FVar f))
             (Tuple (Vector d (SizedF 128 (FVar f)))
               (SizedF 10 (FVar f))))))
packStatement { proofState: ps, messagesForNextStepProof } =
  let
    dv = ps.deferredValues
    plonk = dv.plonk
    bd = dv.branchData
    -- Branch_data.pack: 4*domain_log2 + mask_0 + 2*mask_1
    m0 :: FVar f
    m0 = coerce (Vector.index bd.proofsVerifiedMask (unsafeFinite @2 0))
    m1 :: FVar f
    m1 = coerce (Vector.index bd.proofsVerifiedMask (unsafeFinite @2 1))
    packedBranchData = unsafeMkSizedF $
      CVar.add_ (CVar.scale_ (one + one + one + one) bd.domainLog2)
        (CVar.add_ m0 (CVar.scale_ (one + one) m1))
  in
    -- Vec5 sf: [cip, b, zetaToSrs, zetaToDom, perm]
    Tuple
      (dv.combinedInnerProduct :< dv.b :< plonk.zetaToSrsLength :< plonk.zetaToDomainSize :< plonk.perm :< Vector.nil)
      -- Vec2 SizedF128: [beta, gamma]
      (Tuple
        (plonk.beta :< plonk.gamma :< Vector.nil)
        -- Vec3 SizedF128: [alpha, zeta, xi]
        (Tuple
          (plonk.alpha :< plonk.zeta :< dv.xi :< Vector.nil)
          -- Vec3 f: [sponge_digest, msg_wrap, msg_step]
          (Tuple
            (ps.spongeDigestBeforeEvaluations :< ps.messagesForNextWrapProof :< messagesForNextStepProof :< Vector.nil)
            -- Vec d SizedF128: bulletproof_challenges
            (Tuple
              dv.bulletproofChallenges
              -- SizedF10: packed branch_data
              packedBranchData))))

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
  -> Maybe (Sponge (FVar f)) -- ^ Pre-computed sponge_after_index
  -> SpongeM f (KimchiConstraint f) t m (BoolVar f)
verify scalarOps params input isBaseCase claimedDigest mSpongeAfterIndex = labelM "verify" do
  -- 1. Call incrementallyVerifyProof
  output <- incrementallyVerifyProof @g scalarOps params input mSpongeAfterIndex

  -- 2. Assert sponge digest matches unconditionally (step_verifier.ml:1294)
  labelM "ivp_assert_digest" $ liftSnarky $
    assertEq claimedDigest output.spongeDigestBeforeEvaluations

  -- 3. Assert bulletproof challenges match with base-case bypass (lines 1209-1221)
  labelM "ivp_assert_bp_challenges" $ liftSnarky $
    for_ (Vector.zip input.deferredValues.bulletproofChallenges output.bulletproofChallenges)
      \(Tuple c1 c2) -> do
        c2' <- if_ isBaseCase c1 c2
        assertEq c1 c2'

  -- 4. Return bulletproof success
  pure output.success
