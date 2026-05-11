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
module Pickles.IncrementallyVerifyProof
  ( IncrementallyVerifyProofParams
  , IncrementallyVerifyProofInput
  , IncrementallyVerifyProofOutput
  , incrementallyVerifyProof
  , ivpTrace
  , packStatement
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import Partial.Unsafe (unsafePartial)
import Pickles.FtComm (ftComm)
import Pickles.IPA (CheckBulletproofInput, checkBulletproof)
import Pickles.IncrementallyVerifyProof.FqSpongeTranscript (spongeTranscriptOptCircuit)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode, LagrangeBaseLookup, publicInputCommit)
import Pickles.ShiftOps (IpaScalarOps)
import Pickles.Sponge (SpongeM, initialSpongeCircuit, labelM, liftSnarky)
import Pickles.Sponge as Sponge
import Pickles.Trace as Trace
import Pickles.Verify.Types (BulletproofChallenges, DeferredValues, WrapDeferredValues, toPlonkMinimal)
import Pickles.Wrap.Types (IvpBaseline)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, assertEq, const_, exists, label, readCVar)
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField)
import Snarky.Circuit.DSL.SizedF as SizedF
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
  , lagrangeAt :: LagrangeBaseLookup f
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
  , sgOldMask :: Vector sgOldN fv
  -- ^ actual_proofs_verified_mask (OCaml absorbs sg_old with keep flags).
  , deferredValues :: DeferredValues d fv sf
  -- Verifier index (VK) data — circuit variables in Step, constants in Wrap
  , sigmaCommLast :: AffinePoint fv
  , columnComms ::
      { index :: Vector 6 (AffinePoint fv)
      , coeff :: Vector 15 (AffinePoint fv)
      , sigma :: Vector 6 (AffinePoint fv)
      }
  -- Protocol messages and opening proof
  -- TODO(num_chunks): When num_chunks > 1, each commitment point becomes
  -- Vector numChunks (AffinePoint fv). The tComm size (currently 7) is
  -- ceil(domain_size / max_poly_size) * 7. For num_chunks = 1 this is just 7.
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
-- | DEBUG: emit a solve-time trace of a circuit variable's assigned value.
-- |
-- | Uses `exists` to allocate a throw-away variable whose witness computation
-- | runs `readCVar`. At solve time this reads the variable's assigned value
-- | and emits a `[label] VALUE` line via `unsafePerformEffect` → Trace.fieldF.
-- | The allocated var is unused and its only constraint is the no-op `check`
-- | for `FVar`, so adding these calls does NOT change the constraint system
-- | shape.
-- |
-- | `unsafePerformEffect` is used to avoid propagating a `MonadEffect m`
-- | constraint through the entire IVP/step/wrap call chain. This is
-- | purely for debugging.
ivpTrace
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => String
  -> FVar f
  -> Snarky c t m Unit
ivpTrace labelStr v = do
  _ <- exists do
    val <- readCVar v
    let _ = unsafePerformEffect (Trace.fieldF labelStr val)
    pure val
  pure unit

incrementallyVerifyProof
  :: forall publicInput sgOldN totalBases totalBasesPred d dPred f f' @g sf t m r
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
  => Reflectable sgOldN Int
  => Add 1 dPred d
  => Add sgOldN IvpBaseline totalBases
  => Add 1 totalBasesPred totalBases
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
      -- Trace the inputs to the OptSponge so we can diff them byte-for-byte
      -- against OCaml's wrap_verifier IVP. Same labels as the step path,
      -- so both runs populate the same keys (wrap run overwrites step run
      -- within the same file).
      liftSnarky $ ivpTrace "ivp.trace.wrap.index_digest" indexDigest
      xHat <- liftSnarky $ label "ivp_xhat" $ publicInputCommit params input.publicInput
      liftSnarky $ ivpTrace "ivp.trace.wrap.xhat.x" xHat.x
      liftSnarky $ ivpTrace "ivp.trace.wrap.xhat.y" xHat.y
      liftSnarky do
        forWithIndex_ input.sgOld \fi pt -> do
          let i = getFinite fi
          ivpTrace ("ivp.trace.wrap.sg_old." <> show i <> ".x") pt.x
          ivpTrace ("ivp.trace.wrap.sg_old." <> show i <> ".y") pt.y
        forWithIndex_ input.wComm \fi pt -> do
          let i = getFinite fi
          ivpTrace ("ivp.trace.wrap.w_comm." <> show i <> ".x") pt.x
          ivpTrace ("ivp.trace.wrap.w_comm." <> show i <> ".y") pt.y
      let
        spongeInput = { indexDigest, sgOld: input.sgOld, publicComm: xHat, wComm: input.wComm, zComm: input.zComm, tComm: input.tComm }
        mask = map (coerce :: FVar f -> Bool (FVar f)) input.sgOldMask
      result <- labelM "ivp_opt_sponge" $ spongeTranscriptOptCircuit endoParams mask spongeInput
      liftSnarky $ ivpTrace "ivp.trace.wrap.beta_squeezed" (SizedF.toField result.beta)
      pure { xHat, beta: result.beta, gamma: result.gamma, alphaChal: result.alphaChal, zetaChal: result.zetaChal, digest: result.digest }
    else do
      -- Step path: absorb index_digest + sg_old into main sponge BEFORE x_hat
      -- Matches step_verifier.ml:528-530
      liftSnarky $ ivpTrace "ivp.trace.index_digest" indexDigest
      labelM "ivp_absorb_index_digest" $ Sponge.absorb indexDigest
      labelM "ivp_absorb_sg_old" do
        liftSnarky $ forWithIndex_ input.sgOld \fi pt -> do
          let i = getFinite fi
          ivpTrace ("ivp.trace.sg_old." <> show i <> ".x") pt.x
          ivpTrace ("ivp.trace.sg_old." <> show i <> ".y") pt.y
        for_ input.sgOld \pt -> do
          labelM "ivp_sg_x" $ Sponge.absorb pt.x
          labelM "ivp_sg_y" $ Sponge.absorb pt.y
      -- Compute x_hat
      xHat <- liftSnarky $ label "ivp_xhat" $ publicInputCommit params input.publicInput
      liftSnarky $ ivpTrace "ivp.trace.xhat.x" xHat.x
      liftSnarky $ ivpTrace "ivp.trace.xhat.y" xHat.y
      -- Continue sponge transcript: absorb x_hat, w_comm, squeeze beta/gamma, etc.
      -- step_verifier.ml:551-568
      Sponge.absorbPoint xHat
      liftSnarky $ forWithIndex_ input.wComm \fi pt -> do
        let i = getFinite fi
        ivpTrace ("ivp.trace.w_comm." <> show i <> ".x") pt.x
        ivpTrace ("ivp.trace.w_comm." <> show i <> ".y") pt.y
      for_ input.wComm Sponge.absorbPoint
      -- beta/gamma: squeeze_challenge (constrain_low_bits:true)
      beta <- Sponge.squeezeScalarChallenge endoParams
      liftSnarky $ ivpTrace "ivp.trace.beta_squeezed" (SizedF.toField beta)
      gamma <- Sponge.squeezeScalarChallenge endoParams
      liftSnarky $ ivpTrace "ivp.trace.gamma_squeezed" (SizedF.toField gamma)
      -- z_comm: receive
      liftSnarky $ ivpTrace "ivp.trace.zcomm.x" input.zComm.x
      liftSnarky $ ivpTrace "ivp.trace.zcomm.y" input.zComm.y
      Sponge.absorbPoint input.zComm
      -- alpha: squeeze_scalar (constrain_low_bits:false)
      alphaChal <- Sponge.squeezeScalar endoParams
      liftSnarky $ ivpTrace "ivp.trace.alpha_squeezed" (SizedF.toField alphaChal)
      -- t_comm: receive
      liftSnarky $ forWithIndex_ input.tComm \fi pt -> do
        let i = getFinite fi
        ivpTrace ("ivp.trace.tcomm." <> show i <> ".x") pt.x
        ivpTrace ("ivp.trace.tcomm." <> show i <> ".y") pt.y
      for_ input.tComm Sponge.absorbPoint
      -- zeta: squeeze_scalar (constrain_low_bits:false)
      zetaChal <- Sponge.squeezeScalar endoParams
      liftSnarky $ ivpTrace "ivp.trace.zeta_squeezed" (SizedF.toField zetaChal)
      -- Copy sponge before squeezing digest (step_verifier.ml:559)
      spongeBeforeEvals <- Sponge.getSponge
      digest <- Sponge.squeeze
      liftSnarky $ ivpTrace "ivp.trace.digest" digest
      Sponge.putSponge spongeBeforeEvals
      pure { xHat, beta, gamma, alphaChal, zetaChal, digest }

  -- 3. Assert deferred values match sponge output (all 128-bit scalar challenges)
  liftSnarky do
    let expected = toPlonkMinimal input.deferredValues.plonk
    label "ivp_assert_plonk_beta" $ assertEq beta expected.beta
    label "ivp_assert_plonk_gamma" $ assertEq gamma expected.gamma
    label "ivp_assert_plonk_alpha" $ assertEq alphaChal expected.alpha
    label "ivp_assert_plonk_zeta" $ assertEq zetaChal expected.zeta

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
  -- TODO(num_chunks): With num_chunks > 1, each commitment is an array of chunk
  -- points. The allBases vector would grow by a factor of num_chunks, and
  -- totalBases = sgOldN + num_chunks * 45. The combinePolynomials fold would
  -- need inner loops over chunks (see OCaml's Pcs_batch.combine_split_commitments).
  let
    allBases =
      input.sgOld `Vector.append`
        ( (xHat :< ftCommResult :< input.zComm :< Vector.nil)
            `Vector.append` input.columnComms.index
            `Vector.append` input.wComm
            `Vector.append` input.columnComms.coeff
            `Vector.append` input.columnComms.sigma
        )

    -- Per-base masks: sg_old entries use actual_proofs_verified_mask (Maybe keep),
    -- all other bases are unconditional (Nothing). Matches OCaml's Opt.Maybe for sg_old.
    allBaseMasks =
      (map (Just <<< coerce) input.sgOldMask) `Vector.append`
        (Vector.replicate @45 Nothing)

  -- 6. Build CheckBulletproofInput and run checkBulletproof
  let
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
    allBaseMasks
    bpInput

  -- Emit `beta_used` here (AFTER checkBulletproof) so the wrap trace
  -- order matches OCaml's wrap_verifier.ml:1525 — IPA verification
  -- runs first, then the deferred-values comparison dumps `plonk.beta`.
  liftSnarky $ when params.useOptSponge $
    ivpTrace "ivp.trace.wrap.beta_used" (SizedF.toField (toPlonkMinimal input.deferredValues.plonk).beta)

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
       ( Tuple (Vector 2 (SizedF 128 (FVar f)))
           ( Tuple (Vector 3 (SizedF 128 (FVar f)))
               ( Tuple (Vector 3 (FVar f))
                   ( Tuple (Vector d (SizedF 128 (FVar f)))
                       (SizedF 10 (FVar f))
                   )
               )
           )
       )
packStatement { proofState: ps, messagesForNextStepProof } =
  let
    dv = ps.deferredValues
    plonk = dv.plonk
    bd = dv.branchData

    -- Branch_data.pack: 4*domain_log2 + mask_0 + 2*mask_1
    m0 = coerce (Vector.index bd.proofsVerifiedMask (unsafeFinite @2 0))

    m1 = coerce (Vector.index bd.proofsVerifiedMask (unsafeFinite @2 1))
    packedBranchData = unsafePartial $ unsafeFromField $
      CVar.add_ (CVar.scale_ (one + one + one + one) bd.domainLog2)
        (CVar.add_ m0 (CVar.scale_ (one + one) m1))
  in
    -- Vec5 sf: [cip, b, zetaToSrs, zetaToDom, perm]
    Tuple
      (dv.combinedInnerProduct :< dv.b :< plonk.zetaToSrsLength :< plonk.zetaToDomainSize :< plonk.perm :< Vector.nil)
      -- Vec2 SizedF128: [beta, gamma]
      ( Tuple
          (plonk.beta :< plonk.gamma :< Vector.nil)
          -- Vec3 SizedF128: [alpha, zeta, xi]
          ( Tuple
              (plonk.alpha :< plonk.zeta :< dv.xi :< Vector.nil)
              -- Vec3 f: [sponge_digest, msg_wrap, msg_step]
              ( Tuple
                  (ps.spongeDigestBeforeEvaluations :< ps.messagesForNextWrapProof :< messagesForNextStepProof :< Vector.nil)
                  -- Vec d SizedF128: bulletproof_challenges
                  ( Tuple
                      dv.bulletproofChallenges
                      -- SizedF10: packed branch_data
                      packedBranchData
                  )
              )
          )
      )

-------------------------------------------------------------------------------
