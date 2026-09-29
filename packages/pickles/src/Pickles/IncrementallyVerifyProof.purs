-- | The core verifier circuit, shared by step and wrap: the public
-- | input commitment, the fq-sponge transcript and its deferred-values
-- | assertions, the ft commitment, and the bulletproof check, wired
-- | into one pass.
module Pickles.IncrementallyVerifyProof
  ( IncrementallyVerifyProofParams
  , IncrementallyVerifyProofInput
  , IncrementallyVerifyProofOutput
  , class StepChunkLayout
  , layoutBases
  , incrementallyVerifyProof
  , ftComm
  , PackedWrapStatement
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
import Effect.Exception.Unsafe (unsafeThrow)
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
  , sgOldMask :: Maybe (Vector sgOldN fv)
  -- ^ the actual-proofs-verified keep flags for `sgOld`: `Just` on
  -- the wrap side, `Nothing` on the step side, whose `sgOld` bases are
  -- all unconditional
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
-- | Base layout
-------------------------------------------------------------------------------

-- | The bulletproof base layout of a `stepChunks`-chunk proof: `tComm`
-- | has `tCommLen = 7 * stepChunks` chunks, and the MSM has
-- | `nonSgBases = 1 + 44 * stepChunks` bases besides `sgOld`. `xHat` is
-- | chunked too: at two chunks the step domain exceeds the wrap SRS's
-- | `max_poly_size`.
class StepChunkLayout :: Int -> Int -> Int -> Constraint
class
  ( Mul 7 stepChunks tCommLen
  , Reflectable nonSgBases Int
  ) <=
  StepChunkLayout stepChunks tCommLen nonSgBases
  | stepChunks -> tCommLen nonSgBases where
  -- | The non-`sgOld` bases, flat and in xi-Horner order, each
  -- | polynomial's chunks adjacent.
  layoutBases
    :: forall a
     . { xHat :: Vector stepChunks a
       , ftComm :: a
       , zComm :: Vector stepChunks a
       , index :: Vector 6 (Vector stepChunks a)
       , wComm :: Vector 15 (Vector stepChunks a)
       , coeff :: Vector 15 (Vector stepChunks a)
       , sigma :: Vector 6 (Vector stepChunks a)
       }
    -> Vector nonSgBases a

-- One `Add` per append. `w` and `i` each size two groups: `Mul`'s
-- fundep would unify separate binders for the same product anyway.
-- `Mul 44` pins the total at `1 + 44 * stepChunks`.
instance
  ( Mul 7 n t
  , Mul 15 n w
  , Mul 6 n i
  , Mul 44 n c
  , Add 1 c s
  , Add n 1 s1
  , Add s1 n s2
  , Add s2 i s3
  , Add s3 w s4
  , Add s4 w s5
  , Add s5 i s
  , Reflectable s Int
  ) =>
  StepChunkLayout n t s where
  layoutBases r =
    r.xHat
      `Vector.append` (r.ftComm :< Vector.nil)
      `Vector.append` r.zComm
      `Vector.append` Vector.concat r.index
      `Vector.append` Vector.concat r.wComm
      `Vector.append` Vector.concat r.coeff
      `Vector.append` Vector.concat r.sigma

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

-- | The core verifier circuit: wires `publicInputCommit`, the sponge
-- | transcript, `ftComm` and `checkBulletproof` together, and asserts
-- | that the deferred values agree with the sponge's challenges.
incrementallyVerifyProof
  :: forall publicInput sgOldN stepChunks numChunksPred tCommLen tCommLenPred nonSgBases totalBases totalBasesPred d dPred f f' @g sf r cr
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
  => Compare 0 stepChunks LT
  => Add 1 numChunksPred stepChunks
  => Add 1 dPred d
  => StepChunkLayout stepChunks tCommLen nonSgBases
  => Add 1 tCommLenPred tCommLen
  => Add sgOldN nonSgBases totalBases
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
        mask = case input.sgOldMask of
          Just keeps -> map (coerce :: FVar f -> Bool (FVar f)) keeps
          Nothing -> unsafeThrow "incrementallyVerifyProof: the conditional sponge needs sgOldMask"
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

  -- `sigmaCommLast` is not a base here; it enters only the index-digest
  -- absorb.
  let
    allBases =
      input.sgOld `Vector.append` layoutBases
        { xHat
        , ftComm: ftCommResult
        , zComm: unwrap input.zComm
        , index: map unwrap input.columnComms.index
        , wComm: map unwrap input.wComm
        , coeff: map unwrap input.columnComms.coeff
        , sigma: map unwrap input.columnComms.sigma
        }

    -- Only the wrap side's `sgOld` bases are masked; every other base
    -- is unconditional.
    sgOldBaseMasks :: Vector sgOldN (Maybe (BoolVar f))
    sgOldBaseMasks = case input.sgOldMask of
      Just keeps -> map (Just <<< coerce) keeps
      Nothing -> Vector.replicate Nothing

    allBaseMasks =
      sgOldBaseMasks `Vector.append` (Vector.replicate @nonSgBases Nothing)

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

-- | A wrap statement's public input, one scalar per Lagrange base, at
-- | cell type `x` and shifted-claim type `sf`: the five claims, the two
-- | challenges, the three scalar challenges, the three digests, the `d`
-- | bulletproof challenges and the packed branch data.
type PackedWrapStatement :: Int -> Type -> Type -> Type
type PackedWrapStatement d x sf =
  Tuple (Vector 5 sf)
    ( Tuple (Vector 2 (SizedF 128 x))
        ( Tuple (Vector 3 (SizedF 128 x))
            ( Tuple (Vector 3 x)
                (Tuple (Vector d (SizedF 128 x)) (SizedF 10 x))
            )
        )
    )

-- | A `WrapStatement` as the nested public-input tuple the verifier
-- | commits to; the nesting is the one `publicInputCommit`'s instance
-- | expects.
packStatement
  :: forall d f sf
   . PrimeField f
  => WrapStatement d (FVar f) sf (BoolVar f)
  -> PackedWrapStatement d (FVar f) sf
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
