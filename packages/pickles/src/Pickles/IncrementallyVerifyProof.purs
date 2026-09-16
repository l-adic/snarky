-- | The core verifier circuit, shared by step and wrap: the public
-- | input commitment, the fq-sponge transcript and its deferred-values
-- | assertions, the ft commitment, and the bulletproof check, wired
-- | into one pass.
module Pickles.IncrementallyVerifyProof
  ( IncrementallyVerifyProofParams
  , IncrementallyVerifyProofInput
  , IncrementallyVerifyProofOutput
  , incrementallyVerifyProof
  , ftComm
  , packStatement
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (foldM, for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.DeferredValues (BulletproofChallenges, DeferredValues, toPlonkMinimal)
import Pickles.IPA (checkBulletproof)
import Pickles.IncrementallyVerifyProof.FqSpongeTranscript (assertPlonkChallenges, ivpTrace, spongeTranscriptCircuit, spongeTranscriptOptCircuit)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode, LagrangeBaseLookup, publicInputCommit)
import Pickles.ShiftOps (IpaScalarOps)
import Pickles.Sponge (SpongeM, initialSpongeCircuit, labelM, liftSnarky)
import Pickles.Sponge as Sponge
import Pickles.Types (ChunkedCommitment(..), WrapStatement)
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.DSL (Bool(..), BoolVar, F(..), FVar, Snarky, const_, label)
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (GroupMapParams)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve)
import Snarky.Data.EllipticCurve (AffinePoint(..), CurveParams)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | SRS-derived constants, known outside the circuit. Row-polymorphic
-- | so callers can pass wider records.
-- |
-- | The verifier index commitments are not here: they are circuit
-- | variables, and live in `IncrementallyVerifyProofInput`.
type IncrementallyVerifyProofParams :: Int -> Type -> Row Type -> Type
type IncrementallyVerifyProofParams stepChunks f r =
  { curveParams :: CurveParams f
  , lagrangeAt :: LagrangeBaseLookup stepChunks f
  , blindingH :: AffinePoint (F f)
  , endo :: f -- ^ the endoscalar constant for challenge expansion
  , groupMapParams :: GroupMapParams f
  , correctionMode :: CorrectionMode
  , useOptSponge :: Boolean -- ^ true for wrap, false for step
  | r
  }

-- | The circuit input. `sgOldN` is 0 or 2 and `d` is the number of IPA
-- | rounds; `publicInput` is whatever the protocol commits to — a
-- | `Vector n (FVar f)` for wrap, a record for step — and needs a
-- | `PublicInputCommit` instance.
-- |
-- | The verifier index commitments arrive as `fv` whether the caller
-- | held them as circuit variables (step) or as constants (wrap).
type IncrementallyVerifyProofInput publicInput sgOldN stepChunks tCommLen d fv sf =
  { publicInput :: publicInput
  , sgOld :: Vector sgOldN (AffinePoint fv)
  , sgOldMask :: Vector sgOldN fv
  -- ^ the actual-proofs-verified keep flags for `sgOld`
  , deferredValues :: DeferredValues d fv sf
  -- The verifier index commitments, all at the verified proof's
  -- `stepChunks`: the step VK commitments must agree with the step
  -- proof's chunk count.
  , sigmaCommLast :: ChunkedCommitment stepChunks (AffinePoint fv)
  , columnComms ::
      { index :: Vector 6 (ChunkedCommitment stepChunks (AffinePoint fv))
      , coeff :: Vector 15 (ChunkedCommitment stepChunks (AffinePoint fv))
      , sigma :: Vector 6 (ChunkedCommitment stepChunks (AffinePoint fv))
      }
  -- Protocol messages and opening proof. `wComm` and `zComm` carry
  -- `stepChunks` chunks per polynomial. `tComm` is flat, of length
  -- `tCommLen = 7 * stepChunks`: kimchi splits `t` at degree
  -- `7 * domain_size`, then each of those 7 pieces again into
  -- `stepChunks` chunks of `max_poly_size`.
  , wComm :: Vector 15 (ChunkedCommitment stepChunks (AffinePoint fv))
  , zComm :: ChunkedCommitment stepChunks (AffinePoint fv)
  , tComm :: Vector tCommLen (AffinePoint fv)
  , opening ::
      { delta :: AffinePoint fv
      , sg :: AffinePoint fv
      , lr :: Vector d { l :: AffinePoint fv, r :: AffinePoint fv }
      , z1 :: sf
      , z2 :: sf
      }
  }

type IncrementallyVerifyProofOutput d f =
  { spongeDigestBeforeEvaluations :: FVar f
  , bulletproofChallenges :: BulletproofChallenges d (FVar f)
  , success :: BoolVar f
  }

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

-- | The core verifier circuit: wires `publicInputCommit`, the sponge
-- | transcript, `ftComm` and `checkBulletproof` together, and asserts
-- | that the deferred values agree with the sponge's challenges.
incrementallyVerifyProof
  :: forall publicInput sgOldN stepChunks numChunksPred tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5 totalBases totalBasesPred d dPred f f' @g sf r cr
   . PrimeField f
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => PoseidonField f
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => PublicInputCommit publicInput f
  => Reflectable d Int
  => Reflectable sgOldN Int
  => Reflectable stepChunks Int
  => Reflectable tCommLen Int
  => Reflectable nonSgBases Int
  => Compare 0 stepChunks LT
  => Add 1 numChunksPred stepChunks
  => Add 1 dPred d
  -- `tComm` is one flat vector of `7 * stepChunks` points; `ftComm`
  -- Horner-reduces it as a single list.
  => Mul 7 stepChunks tCommLen
  => Add 1 tCommLenPred tCommLen
  -- The MSM has `sgOldN + 1 + 44*stepChunks` bases, laid out by
  -- `allBases` below. `xHat` is chunked because at two chunks the step
  -- `wrap_domain` exceeds the wrap SRS `max_poly_size`, so the
  -- public-input commitment splits into `stepChunks` pieces.
  --
  -- One `indexSigmaN` serves both index (6nc) and sigma (6nc), and one
  -- `wCoeffN` both wComm (15nc) and coeff (15nc): `Mul` is functionally
  -- determined, so separate binders would force a length-mismatch
  -- unification.
  => Mul 15 stepChunks wCoeffN
  => Mul 6 stepChunks indexSigmaN
  => Mul 44 stepChunks chunkBases
  => Add 1 chunkBases nonSgBases
  => Add sgOldN nonSgBases totalBases
  -- One `Add` per append in the non-sgOld group, spelling out the
  -- running total; the group ends at `nonSgBases`, and the outer append
  -- of `sgOld` is the `Add sgOldN nonSgBases totalBases` above.
  => Add stepChunks 1 sg1 -- xHat + ftComm = nc + 1
  => Add sg1 stepChunks sg2 -- + zComm = 1 + 2nc
  => Add sg2 indexSigmaN sg3 -- + index = 1 + 8nc
  => Add sg3 wCoeffN sg4 -- + wComm = 1 + 23nc
  => Add sg4 wCoeffN sg5 -- + coeff = 1 + 38nc
  => Add sg5 indexSigmaN nonSgBases -- + sigma = 1 + 44nc
  => Add 1 totalBasesPred totalBases
  => IpaScalarOps f cr sf
  -> IncrementallyVerifyProofParams stepChunks f r
  -> IncrementallyVerifyProofInput publicInput sgOldN stepChunks tCommLen d (FVar f) sf
  -> Maybe (Sponge (FVar f)) -- ^ a pre-computed sponge-after-index
  -> SpongeM f (KimchiConstraint f) cr (IncrementallyVerifyProofOutput d f)
incrementallyVerifyProof scalarOps params input mSpongeAfterIndex = labelM "incrementally-verify-proof" do
  let endoParams = { endo: const_ params.endo, groupMapParams: params.groupMapParams }

  -- The index digest: squeeze the caller's sponge-after-index, or hash
  -- the VK commitments from scratch when there is none.
  indexDigest <- liftSnarky $ label "ivp_index_digest" $ case mSpongeAfterIndex of
    Just spongeAfterIndex ->
      Sponge.evalSpongeM spongeAfterIndex Sponge.squeeze
    Nothing ->
      Sponge.evalSpongeM (initialSpongeCircuit :: Sponge (FVar f)) do
        -- The absorption order is fixed: sigma_comm (7), then
        -- coefficients_comm (15), then the index comms (6), each
        -- commitment's chunks in chunk order, `x` before `y`.
        let
          absorbPt (AffinePoint { x, y }) = do
            Sponge.absorb x
            Sponge.absorb y
          absorbChunks cc = for_ (unwrap cc) absorbPt
        -- sigma_comm is the 6 sigma commitments plus `sigmaCommLast`
        for_ input.columnComms.sigma absorbChunks
        absorbChunks input.sigmaCommLast
        for_ input.columnComms.coeff absorbChunks
        -- generic, psm, complete_add, mul, emul, endomul_scalar
        for_ input.columnComms.index absorbChunks
        Sponge.squeeze

  -- Step absorbs the index digest and `sgOld` before `xHat`, through a
  -- plain sponge; wrap computes `xHat` first and absorbs everything
  -- through an `OptSponge`.
  { xHat, beta, gamma, alphaChal, zetaChal, digest } <-
    if params.useOptSponge then do
      -- The trace labels are shared with the step path, so a later run
      -- overwrites an earlier one in the same file.
      liftSnarky $ ivpTrace "ivp.trace.wrap.index_digest" indexDigest
      xHat <- liftSnarky $ label "ivp_xhat" $ publicInputCommit params input.publicInput
      -- Chunk 0's trace key carries no index suffix, so a one-chunk run
      -- emits the unsuffixed key.
      liftSnarky $ forWithIndex_ xHat \fi (AffinePoint pt) -> do
        let i = getFinite fi
        if i == 0 then do
          ivpTrace "ivp.trace.wrap.xhat.x" pt.x
          ivpTrace "ivp.trace.wrap.xhat.y" pt.y
        else do
          ivpTrace ("ivp.trace.wrap.xhat." <> show i <> ".x") pt.x
          ivpTrace ("ivp.trace.wrap.xhat." <> show i <> ".y") pt.y
      liftSnarky do
        forWithIndex_ input.sgOld \fi (AffinePoint pt) -> do
          let i = getFinite fi
          ivpTrace ("ivp.trace.wrap.sg_old." <> show i <> ".x") pt.x
          ivpTrace ("ivp.trace.wrap.sg_old." <> show i <> ".y") pt.y
        forWithIndex_ input.wComm \fi cc ->
          forWithIndex_ (unwrap cc) \fj (AffinePoint pt) -> do
            let i = getFinite fi
            let j = getFinite fj
            ivpTrace ("ivp.trace.wrap.w_comm." <> show i <> "." <> show j <> ".x") pt.x
            ivpTrace ("ivp.trace.wrap.w_comm." <> show i <> "." <> show j <> ".y") pt.y
      let
        spongeInput = { indexDigest, sgOld: input.sgOld, publicComm: ChunkedCommitment xHat, wComm: input.wComm, zComm: input.zComm, tComm: input.tComm }
        mask = map (coerce :: FVar f -> Bool (FVar f)) input.sgOldMask
      result <- labelM "ivp_opt_sponge" $ spongeTranscriptOptCircuit endoParams mask spongeInput
      liftSnarky $ ivpTrace "ivp.trace.wrap.beta_squeezed" (SizedF.toField result.beta)
      pure { xHat, beta: result.beta, gamma: result.gamma, alphaChal: result.alphaChal, zetaChal: result.zetaChal, digest: result.digest }
    else do
      -- Step path: `xHat` is computed at its point in the schedule.
      result <- spongeTranscriptCircuit endoParams
        { indexDigest, sgOld: input.sgOld, wComm: input.wComm, zComm: input.zComm, tComm: input.tComm }
        (liftSnarky $ label "ivp_xhat" $ publicInputCommit params input.publicInput)
      pure { xHat: result.xHat, beta: result.beta, gamma: result.gamma, alphaChal: result.alphaChal, zetaChal: result.zetaChal, digest: result.digest }

  liftSnarky $ assertPlonkChallenges { beta, gamma, alphaChal, zetaChal, digest }
    (toPlonkMinimal input.deferredValues.plonk)

  ftCommResult <- liftSnarky $ label "ivp_ftcomm" $ ftComm
    scalarOps
    { sigmaLast: unwrap input.sigmaCommLast
    , tComm: input.tComm
    , perm: input.deferredValues.plonk.perm
    , zetaToSrsLength: input.deferredValues.plonk.zetaToSrsLength
    , zetaToDomainSize: input.deferredValues.plonk.zetaToDomainSize
    }

  -- The base layout is fixed, flat and in xi-Horner emission order,
  -- each polynomial's chunks adjacent:
  --   sgOld, xHat (stepChunks), ftComm,
  --   zComm (stepChunks),
  --   index comms (6 polys × stepChunks),
  --   wComm (15 polys × stepChunks),
  --   coeff comms (15 polys × stepChunks),
  --   sigma_comm[0..PERMUTS-2] (6 polys × stepChunks).
  -- `sigmaCommLast` is not a base here; it enters only the index-digest
  -- absorb.
  let
    wCommFlat = Vector.concat (coerce input.wComm :: Vector 15 (Vector stepChunks (AffinePoint (FVar f))))
    indexFlat = Vector.concat (coerce input.columnComms.index :: Vector 6 (Vector stepChunks (AffinePoint (FVar f))))
    coeffFlat = Vector.concat (coerce input.columnComms.coeff :: Vector 15 (Vector stepChunks (AffinePoint (FVar f))))
    sigmaFlat = Vector.concat (coerce input.columnComms.sigma :: Vector 6 (Vector stepChunks (AffinePoint (FVar f))))
    allBases =
      input.sgOld `Vector.append`
        ( xHat
            `Vector.append` (ftCommResult :< Vector.nil)
            `Vector.append` unwrap input.zComm
            `Vector.append` indexFlat
            `Vector.append` wCommFlat
            `Vector.append` coeffFlat
            `Vector.append` sigmaFlat
        )

    -- Only the `sgOld` bases are masked; every other base is
    -- unconditional.
    allBaseMasks =
      (map (Just <<< coerce) input.sgOldMask) `Vector.append`
        (Vector.replicate @nonSgBases Nothing)

  let
    bpInput =
      { xi: input.deferredValues.xi
      , deferred:
          { combinedInnerProduct: input.deferredValues.combinedInnerProduct
          , b: input.deferredValues.b
          }
      , opening: input.opening
      , blindingGenerator: constPt params.blindingH
      }

  { success, challenges } <- labelM "ivp_bulletproof" $ checkBulletproof @f @g
    scalarOps
    endoParams
    allBases
    allBaseMasks
    bpInput

  -- `beta_used` is emitted after the bulletproof check, so the wrap
  -- trace carries the IPA verification first and the deferred-values
  -- comparison after it.
  liftSnarky $ when params.useOptSponge $
    ivpTrace "ivp.trace.wrap.beta_used" (SizedF.toField (toPlonkMinimal input.deferredValues.plonk).beta)

  pure { spongeDigestBeforeEvaluations: digest, bulletproofChallenges: challenges, success }

  where
  constPt :: AffinePoint (F f) -> AffinePoint (FVar f)
  constPt (AffinePoint { x: F x', y: F y' }) = AffinePoint { x: const_ x', y: const_ y' }

-------------------------------------------------------------------------------
-- | The wrap statement as public input
-------------------------------------------------------------------------------

-- | A `WrapStatement` as the nested public-input tuple the verifier
-- | commits to; the nesting is the one `publicInputCommit`'s instance
-- | expects.
packStatement
  :: forall d f sf
   . PrimeField f
  => WrapStatement d (FVar f) sf (BoolVar f)
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
-- | The ft polynomial commitment
-------------------------------------------------------------------------------

-- | The ft polynomial commitment, one step of the verifier above:
-- |
-- |   ft_comm = scale(σ_last, perm) + reduced_t
-- |             - scale(reduced_t, zeta_to_domain)
-- |
-- | where `reduced_t` is the Horner reduction of `t_comm`'s chunks at
-- | `zeta_to_srs`.
ftComm
  :: forall stepChunks numChunksPred tCommLen tCommLenPred f r sf cr
   . PrimeField f
  => Add 1 numChunksPred stepChunks
  => Add 1 tCommLenPred tCommLen
  => { scaleByShifted :: AffinePoint (FVar f) -> sf -> Snarky f (KimchiConstraint f) cr (AffinePoint (FVar f))
     | r
     }
  -> { sigmaLast :: Vector stepChunks (AffinePoint (FVar f))
     , tComm :: Vector tCommLen (AffinePoint (FVar f))
     , perm :: sf
     , zetaToSrsLength :: sf
     , zetaToDomainSize :: sf
     }
  -> Snarky f (KimchiConstraint f) cr (AffinePoint (FVar f))
ftComm { scaleByShifted } { sigmaLast, tComm, perm, zetaToSrsLength, zetaToDomainSize } = label "ft-comm" do
  -- `sigmaLast` and `tComm` are both chunk arrays, each collapsed by
  -- `hornerReduce` before it is scaled. Emission order: the negated
  -- `zeta_to_domain` term, then `fComm + reduced_t`, then the outer
  -- add.

  reducedSigmaLast <- hornerReduce sigmaLast
  fComm <- scaleByShifted reducedSigmaLast perm
  chunkedTComm <- hornerReduce tComm
  zetaDomTerm <- scaleByShifted chunkedTComm zetaToDomainSize
  negZetaDomTerm <- Curves.negate zetaDomTerm
  { p: r1 } <- addComplete fComm chunkedTComm
  { p: result } <- addComplete r1 negZetaDomTerm
  pure result
  where
  -- res = comm[n-1]; for i = n-2 downto 0:
  --   res = comm[i] + scale res zetaToSrsLength
  hornerReduce
    :: forall k kPred
     . Add 1 kPred k
    => Vector k (AffinePoint (FVar f))
    -> Snarky f (KimchiConstraint f) cr (AffinePoint (FVar f))
  hornerReduce v =
    let
      { last, init } = Vector.unsnoc v
    in
      foldM
        ( \acc chunk -> do
            scaled <- scaleByShifted acc zetaToSrsLength
            { p } <- addComplete chunk scaled
            pure p
        )
        last
        (Vector.reverse init)

-------------------------------------------------------------------------------
