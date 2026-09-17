-- | In-circuit verification of a kimchi IPA opening proof: the
-- | challenge polynomial `bPoly` and its two-point combination, the
-- | Fiat-Shamir extraction of the round challenges, the Horner combine
-- | of the commitment bases, and the final equation
-- | `c*Q + delta = z1*(sg + b*u) + z2*H`.
module Pickles.IPA
  ( -- * Types
    LrPair
  , BPolyInput
  , ComputeBInput
  , BCorrectInput
  , BulletReduceInput
  , BulletproofDeferred
  , BulletproofOpening
  , IpaFinalCheckInput
  , IpaFinalCheckResult
  , CheckBulletproofInput
  -- * Challenge polynomial
  , bPoly
  , bPolyCircuit
  , challengePolyEvals
  , computeChallenges
  -- * Combined b evaluation
  , computeB
  , computeBCircuit
  -- * Challenge extraction
  , extractScalarChallenges
  -- * Bullet reduce
  , bulletReduceCircuit
  -- * Verification
  , bCorrectCircuit
  -- * Combined polynomial commitment
  , combinePolynomials
  -- * IPA final check
  , ipaFinalCheckCircuit
  -- * Full bulletproof check
  , checkBulletproof
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (foldM, for_, product)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import JS.BigInt as BigInt
import Pickles.ShiftOps (IpaScalarOps)
import Pickles.Sponge (SpongeM, absorb, absorbPoint, getSponge, labelM, liftSnarky, squeeze, squeezeScalar)
import Pickles.Trace as Trace
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class BasicSystem, BoolVar, F(..), FVar, SizedF, Snarky, add_, and_, const_, equals_, if_, label, scale_)
import Snarky.Circuit.DSL (exists, readCVar) as SDSL
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (GroupMapParams, addComplete, endo, endoInv, groupMapCircuit, toField)
import Snarky.Circuit.Kimchi.RangeCheck (split128Below)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve, modulus, pow, toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | The `L` and `R` commitment points of one IPA round, on the
-- | commitment curve — the other curve of the 2-cycle.
type LrPair f = { l :: AffinePoint f, r :: AffinePoint f }

type BPolyInput d f = { challenges :: Vector d f, x :: f }

-- | The `computeBCircuit` arguments, as an open row so `BCorrectInput`
-- | can extend it.
type ComputeBInput d f r =
  { challenges :: Vector d f
  , zeta :: f
  , zetaOmega :: f
  , evalscale :: f
  | r
  }

type BCorrectInput n f = ComputeBInput n f (expectedB :: f)

type BulletReduceInput n f =
  { pairs :: Vector n (LrPair f)
  , challenges :: Vector n (SizedF 128 f)
  }

-------------------------------------------------------------------------------
-- | Challenge Polynomial (b_poly)
-------------------------------------------------------------------------------

-- | The IPA challenge polynomial
-- | `b_poly(chals, x) = ∏_{i<k} (1 + chals[i] * x^{2^{k-1-i}})`, step 8
-- | of appendix A.2 of https://eprint.iacr.org/2020/499.
-- |
-- | `d` is the number of IPA rounds, the domain log2.
bPoly :: forall d f. Reflectable d Int => PrimeField f => Vector d f -> f -> f
bPoly chals x =
  let
    -- powTwos[i] = x^{2^i}
    powTwos = Vector.generate \i ->
      pow x (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt (getFinite i)))

    -- reversed to [x^{2^{d-1}}, …, x², x], then paired with chals
    terms = Vector.zipWith (\c p -> one + c * p) chals (Vector.reverse powTwos)
  in
    product terms

-- | The in-circuit `bPoly`, in two phases: `k-1` squarings building
-- | `[pt, pt², pt⁴, …, pt^(2^(k-1))]`, then `k-1` accumulations of
-- | `∏ (1 + chals[i] * powTwoPows[k-1-i])`. The split and its order fix
-- | the constraint sequence.
bPolyCircuit
  :: forall d dPred f c r
   . Add 1 dPred d
  => Reflectable d Int
  => PrimeField f
  => BasicSystem f c
  => BPolyInput d (FVar f)
  -> Snarky f c r (FVar f)
bPolyCircuit { challenges: chals, x: pt } = label "b-poly" do
  let { tail: chalsTail } = Vector.uncons chals
  Tuple squaredPowers _ <- mapAccumM
    ( \prev _ -> do
        sq <- pure prev * pure prev
        pure (Tuple sq sq)
    )
    pt
    chalsTail
  let powTwoPows = Vector.append (pt :< Vector.nil) squaredPowers

  let
    paired = Vector.zipWith Tuple chals (Vector.reverse powTwoPows)
    { head: Tuple c0 pw0, tail: rest } = Vector.uncons paired
  cp0 <- pure c0 * pure pw0
  let initProd = add_ (const_ one) cp0
  foldM
    ( \acc (Tuple c pw) -> do
        cp <- pure c * pure pw
        let term = add_ (const_ one) cp
        pure term * pure acc
    )
    initProd
    rest

-- | The previous proofs' challenge polynomials at one point:
-- | `bPolyCircuit` per challenge vector. The last vector's polynomial
-- | is emitted first; the result is in vector order.
challengePolyEvals
  :: forall n d dPred f c r
   . Add 1 dPred d
  => Reflectable d Int
  => PrimeField f
  => BasicSystem f c
  => Vector n (Vector d (FVar f))
  -> FVar f
  -> Snarky f c r (Vector n (FVar f))
challengePolyEvals prevChallenges pt = do
  rev <- for (Vector.reverse prevChallenges) \chals ->
    bPolyCircuit { challenges: chals, x: pt }
  pure (Vector.reverse rev)

-- | The bulletproof challenges expanded through the endomorphism:
-- | `toField` on each 128-bit challenge. The last challenge is expanded
-- | first; the result is in vector order.
computeChallenges
  :: forall d n f r
   . FieldSizeInBits f n
  => Compare 128 n LT
  => PrimeField f
  => Vector d (SizedF 128 (FVar f))
  -> FVar f
  -> Snarky f (KimchiConstraint f) r (Vector d (FVar f))
computeChallenges chals endoVar = do
  expandedRev <- for (Vector.reverse chals) \c -> toField @8 c endoVar
  pure (Vector.reverse expandedRev)

-------------------------------------------------------------------------------
-- | Combined b evaluation
-------------------------------------------------------------------------------

-- | `bPoly(chals, zeta) + evalscale * bPoly(chals, zetaOmega)`.
computeB
  :: forall d f
   . Reflectable d Int
  => PrimeField f
  => Vector d f
  -> { zeta :: f, zetaOmega :: f, evalscale :: f }
  -> f
computeB chals { zeta, zetaOmega, evalscale } =
  bPoly chals zeta + evalscale * bPoly chals zetaOmega

-- | The in-circuit `computeB`. The `zetaOmega` evaluation is emitted
-- | first, then its scaling, then the `zeta` evaluation.
computeBCircuit
  :: forall d dPred f c r cr
   . Add 1 dPred d
  => Reflectable d Int
  => PrimeField f
  => BasicSystem f c
  => ComputeBInput d (FVar f) r
  -> Snarky f c cr (FVar f)
computeBCircuit { challenges, zeta, zetaOmega, evalscale } = label "compute-b" do
  bZetaOmega <- bPolyCircuit { challenges, x: zetaOmega }
  scaledB <- pure evalscale * pure bZetaOmega
  bZeta <- bPolyCircuit { challenges, x: zeta }
  pure $ add_ bZeta scaledB

-------------------------------------------------------------------------------
-- | Challenge Extraction (In-Circuit)
-------------------------------------------------------------------------------

-- | The 128-bit scalar challenge of each IPA round, in order. The endo
-- | expansion to full field elements happens separately, in
-- | `computeChallenges`.
extractScalarChallenges
  :: forall n f r cr
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => { endo :: FVar f | r }
  -> Vector n (LrPair (FVar f))
  -> SpongeM f (KimchiConstraint f) cr (Vector n (SizedF 128 (FVar f)))
extractScalarChallenges params pairs = for pairs \{ l, r } -> do
  absorbPoint l
  absorbPoint r
  -- `squeezeScalar` leaves the low 128 bits unconstrained.
  squeezeScalar params

-------------------------------------------------------------------------------
-- | Verification
-------------------------------------------------------------------------------

-- | Whether `computeBCircuit` agrees with the statement's `expectedB`.
bCorrectCircuit
  :: forall n nPred f c r
   . Add 1 nPred n
  => Reflectable n Int
  => PrimeField f
  => BasicSystem f c
  => BCorrectInput n (FVar f)
  -> Snarky f c r (BoolVar f)
bCorrectCircuit input@{ expectedB } = label "b-correct" do
  computedB <- computeBCircuit input
  expectedB `equals_` computedB

-------------------------------------------------------------------------------
-- | Bullet Reduce (lr_prod computation)
-------------------------------------------------------------------------------

-- | `lr_prod = Σ_i (endoInv(L_i, u_i) + endo(R_i, u_i))`, over the
-- | round challenges `u_i`.
bulletReduceCircuit
  :: forall n nPred @f f' @g r
   . Reflectable n Int
  => Add 1 nPred n
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => HasEndo f f'
  => FrModule f' g
  => WeierstrassCurve f g
  => PrimeField f
  => BulletReduceInput n (FVar f)
  -> Snarky f (KimchiConstraint f) r { p :: AffinePoint (FVar f), isInfinity :: BoolVar f }
bulletReduceCircuit { pairs, challenges } = label "bullet-reduce" do
  -- Emission order: endoInv(L), then endo(R), then the add.
  terms <- for (Vector.zip pairs challenges) \(Tuple { l, r } u) -> do
    lScaled <- endoInv @f @f' @g l u
    rScaled <- endo @128 @32 r u
    addComplete lScaled rScaled
  let
    { head, tail } = Vector.uncons terms
  -- `addComplete` assumes finite inputs, so every term's `isInfinity`
  -- is the constant `false_` rather than a witness. Folding the points
  -- alone therefore loses nothing.
  result <- foldM
    (\acc q -> _.p <$> addComplete acc q.p)
    head.p
    tail
  pure { p: result, isInfinity: head.isInfinity }

-------------------------------------------------------------------------------
-- | IPA Final Check Circuit
-------------------------------------------------------------------------------

-- | The two deferred scalars of the opening check: used in the Schnorr
-- | equation here, certified by the next circuit's
-- | `finalizeOtherProof`.
-- |
-- | Not named "advice": in snarky that word is the prover-side handler
-- | mechanism, and these are public input of the previous proof.
type BulletproofDeferred sf =
  { combinedInnerProduct :: sf
  , b :: sf
  }

-- | The opening proof as the circuit reads it — the same fields as
-- | `WrapProofOpening` in `Pickles.Types`, as a plain record — checked
-- | in the Schnorr equation here. Only `sg` is looked at again, one
-- | proof later, as `sg_old`.
type BulletproofOpening n f sf =
  { lr :: Vector n (LrPair f)
  , z1 :: sf
  , z2 :: sf
  , delta :: AffinePoint f
  , sg :: AffinePoint f -- ^ the challenge-polynomial commitment
  }

type IpaFinalCheckInput n f sf =
  { -- `groupMap(squeeze(sponge))`, derived by the caller
    u :: AffinePoint f
  -- from the verifier index and `xi`
  , combinedPolynomial :: AffinePoint f
  , deferred :: BulletproofDeferred sf
  , opening :: BulletproofOpening n f sf
  -- the SRS blinding generator `H`, a constant
  , blindingGenerator :: AffinePoint f
  }

-- | The check's verdict and the round challenges it extracted.
type IpaFinalCheckResult n f =
  { success :: BoolVar f
  , challenges :: Vector n (SizedF 128 (FVar f))
  }

-- | The IPA verification equation
-- | `c*Q + delta = z1*(sg + b*u) + z2*H`, with the round challenges and
-- | `c` derived from the sponge.
-- |
-- | Stays in `SpongeM` so the caller owns the sponge lifecycle; the
-- | sponge must be ready to squeeze for `u`, that is, just after
-- | absorbing the combined inner product.
-- |
-- | The circuit field `f` is the commitment curve's base field: a
-- | Pallas circuit (Fp) commits on Vesta and takes `Type1` for `sf`, a
-- | Vesta circuit (Fq) commits on Pallas and takes `Type2`.
ipaFinalCheckCircuit
  :: forall n nPred @f f' @g sf r cr
   . Reflectable n Int
  => Add 1 nPred n
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => PoseidonField f
  => PrimeField f
  => IpaScalarOps f cr sf
  -> { endo :: FVar f, groupMapParams :: GroupMapParams f | r }
  -> IpaFinalCheckInput n (FVar f) sf
  -> SpongeM f (KimchiConstraint f) cr (IpaFinalCheckResult n f)
ipaFinalCheckCircuit scalarOps params input = do
  let
    -- A local copy of the `ivpTrace` in
    -- `Pickles.IncrementallyVerifyProof.FqSpongeTranscript`.
    ivpTrace labelStr v = do
      _ <- SDSL.exists do
        val <- SDSL.readCVar v
        let _ = unsafePerformEffect (Trace.fieldF labelStr val)
        pure val
      pure unit
  liftSnarky do
    ivpTrace "ipa.dbg.sg.x" (unwrap input.opening.sg).x
    ivpTrace "ipa.dbg.sg.y" (unwrap input.opening.sg).y
    ivpTrace "ipa.dbg.delta.x" (unwrap input.opening.delta).x
    ivpTrace "ipa.dbg.delta.y" (unwrap input.opening.delta).y
    ivpTrace "ipa.dbg.cp.x" (unwrap input.combinedPolynomial).x
    ivpTrace "ipa.dbg.cp.y" (unwrap input.combinedPolynomial).y
    ivpTrace "ipa.dbg.u.x" (unwrap input.u).x
    ivpTrace "ipa.dbg.u.y" (unwrap input.u).y

  scalarChallenges <- labelM "ipa_extract_challenges" $
    extractScalarChallenges params input.opening.lr

  -- Every L/R absorption above precedes any curve operation here.
  lrProd <- liftSnarky $ label "ipa_bullet_reduce" $ do
    { p } <- bulletReduceCircuit @f @g
      { pairs: input.opening.lr
      , challenges: scalarChallenges
      }
    pure p

  -- The scaling of `u` is emitted before the add.
  pPrime <- liftSnarky $ label "ipa_scale_cip" do
    cipU <- label "ipa_scale_cip_scale" $ scalarOps.scaleByShifted input.u input.deferred.combinedInnerProduct
    { p } <- label "ipa_scale_cip_add" $ addComplete input.combinedPolynomial cipU
    pure p

  q <- liftSnarky $ label "ipa_q" do
    { p } <- addComplete pPrime lrProd
    pure p

  -- `delta` is absorbed only after the bullet reduce and `q`.
  c <- labelM "ipa_squeeze_c" $ do
    absorbPoint input.opening.delta
    squeezeScalar params

  liftSnarky do
    ivpTrace "ipa.dbg.(unwrap q).x" (unwrap q).x
    ivpTrace "ipa.dbg.(unwrap q).y" (unwrap q).y
    ivpTrace "ipa.dbg.c" (SizedF.toField c)

  success <- liftSnarky $ label "ipa_final_eq" $ do
    -- LHS: c*Q + delta
    cQ <- label "ipa_endo_q" $ endo @128 @32 q c
    { p: lhs } <- label "ipa_lhs_add" $ addComplete cQ input.opening.delta

    -- RHS: z1*(sg + b*u) + z2*H, where `b` is an input here and
    -- `bCorrectCircuit` certifies it.
    bU <- label "ipa_scale_b" $ scalarOps.scaleByShifted input.u input.deferred.b
    { p: sgPlusBU } <- label "ipa_sg_add" $ addComplete input.opening.sg bU
    z1Term <- label "ipa_scale_z1" $ scalarOps.scaleByShifted sgPlusBU input.opening.z1
    z2Term <- label "ipa_scale_z2" $ scalarOps.scaleByShifted input.blindingGenerator input.opening.z2
    { p: rhs } <- label "ipa_rhs_add" $ addComplete z1Term z2Term

    ivpTrace "ipa.dbg.(unwrap lhs).x" (unwrap lhs).x
    ivpTrace "ipa.dbg.(unwrap lhs).y" (unwrap lhs).y
    ivpTrace "ipa.dbg.(unwrap rhs).x" (unwrap rhs).x
    ivpTrace "ipa.dbg.(unwrap rhs).y" (unwrap rhs).y

    xEqual <- equals_ (unwrap lhs).x (unwrap rhs).x
    yEqual <- equals_ (unwrap lhs).y (unwrap rhs).y
    xEqual `and_` yEqual

  pure { success, challenges: scalarChallenges }

-------------------------------------------------------------------------------
-- | Combined Polynomial Commitment
-------------------------------------------------------------------------------

-- | The Horner combine of the commitment bases under the 128-bit
-- | polyscale `xi`: `Q = C_0 + xi*(C_1 + xi*(… + xi*C_{n-1}))`.
-- |
-- | A `Just keep` mask makes that base conditional — the accumulator
-- | passes through where the bit is false, as the proofs-verified mask
-- | needs for `sg_old`; `Nothing` is unconditional.
combinePolynomials
  :: forall n nPred f f' r
   . Add 1 nPred n
  => FieldSizeInBits f 255
  => HasEndo f f'
  => PrimeField f
  => Vector n (AffinePoint (FVar f))
  -> Vector n (Maybe (BoolVar f)) -- ^ per-base keep mask
  -> SizedF 128 (FVar f)
  -> Snarky f (KimchiConstraint f) r (AffinePoint (FVar f))
combinePolynomials bases masks xi = label "combine-polynomials" do
  let
    paired = Vector.zip bases masks
    reversed = Vector.reverse paired
    { head: Tuple h _, tail: t } = Vector.uncons reversed
  foldM
    ( \acc (Tuple base mKeep) -> do
        xiAcc <- endo @128 @32 acc xi
        { p } <- addComplete base xiAcc
        case mKeep of
          Nothing -> pure p
          Just keep -> if_ keep p acc
    )
    h
    t

-------------------------------------------------------------------------------
-- | Full Bulletproof Check
-------------------------------------------------------------------------------

-- | The proof data `checkBulletproof` reads, after the fq-sponge
-- | transcript.
type CheckBulletproofInput n f sf =
  { -- the 128-bit polyscale, a deferred value from the fr-sponge
    xi :: SizedF 128 f
  , deferred :: BulletproofDeferred sf
  , opening :: BulletproofOpening n f sf
  -- the SRS blinding generator, a constant
  , blindingGenerator :: AffinePoint f
  }

-- | The full opening check: absorb the combined inner product, derive
-- | `u`, combine the commitment bases, then run `ipaFinalCheckCircuit`.
-- |
-- | The sponge must be in its before-evaluations state. The commitment
-- | bases are constants from the verifier index and the proof, so they
-- | are passed separately from the circuit input.
checkBulletproof
  :: forall numBases numBasesPred n nPred @f f' @g sf r cr
   . Reflectable n Int
  => Add 1 nPred n
  => Add 1 numBasesPred numBases
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => PoseidonField f
  => PrimeField f
  => IpaScalarOps f cr sf
  -> { endo :: FVar f, groupMapParams :: GroupMapParams f | r }
  -> Vector numBases (AffinePoint (FVar f))
  -> Vector numBases (Maybe (BoolVar f)) -- ^ per-base keep mask
  -> CheckBulletproofInput n (FVar f) sf
  -> SpongeM f (KimchiConstraint f) cr (IpaFinalCheckResult n f)
checkBulletproof scalarOps params commitmentBases baseMasks input = do
  let
    ivpTrace' labelStr v = do
      _ <- SDSL.exists do
        val <- SDSL.readCVar v
        let _ = unsafePerformEffect (Trace.fieldF labelStr val)
        pure val
      pure unit
  pre <- getSponge
  liftSnarky do
    ivpTrace' "ipa.dbg.wrap_sponge_pre.s0" (Vector.index pre.state (unsafeFinite @3 0))
    ivpTrace' "ipa.dbg.wrap_sponge_pre.s1" (Vector.index pre.state (unsafeFinite @3 1))
    ivpTrace' "ipa.dbg.wrap_sponge_pre.s2" (Vector.index pre.state (unsafeFinite @3 2))

  labelM "bp_absorb_cip" $ do
    let cipFields = scalarOps.shiftedToAbsorbFields input.deferred.combinedInnerProduct
    for_ cipFields absorb

  post <- getSponge
  liftSnarky do
    ivpTrace' "ipa.dbg.wrap_sponge_post.s0" (Vector.index post.state (unsafeFinite @3 0))
    ivpTrace' "ipa.dbg.wrap_sponge_post.s1" (Vector.index post.state (unsafeFinite @3 1))
    ivpTrace' "ipa.dbg.wrap_sponge_post.s2" (Vector.index post.state (unsafeFinite @3 2))

  -- `u` is squeezed before the bases are combined.
  u <- labelM "ipa_group_map" $ do
    t <- squeeze
    liftSnarky do
      u' <- groupMapCircuit params.groupMapParams t
      label "ipa_lower_half" $ lowerHalfPoint params.endo u'

  combinedPolynomial <- labelM "bp_combine_poly" $ liftSnarky $
    combinePolynomials commitmentBases baseMasks input.xi

  labelM "bp_ipa_check" $ ipaFinalCheckCircuit @f @g scalarOps params
    { u
    , combinedPolynomial
    , deferred: input.deferred
    , opening: input.opening
    , blindingGenerator: input.blindingGenerator
    }

-- | The IPA base with its ordinate in the lower half: `(x, y')` with
-- | `y' = ±y` and `y'` at most `(p - 1)/2`. The group map leaves the
-- | square root's sign to the prover; the native prover and verifier
-- | take the lower-half root too.
lowerHalfPoint
  :: forall f r
   . PrimeField f
  => FieldSizeInBits f 255
  => FVar f
  -> AffinePoint (FVar f)
  -> Snarky f (KimchiConstraint f) r (AffinePoint (FVar f))
lowerHalfPoint endoScalar (AffinePoint { x, y }) = do
  isUpper :: BoolVar f <- SDSL.exists do
    F yVal <- SDSL.readCVar y
    pure $ toBigInt yVal >= half
  y' <- if_ isUpper (scale_ (negate one) y) y
  void $ split128Below true endoScalar half y'
  pure $ AffinePoint { x, y: y' }
  where
  half = (modulus @f + BigInt.fromInt 1) / BigInt.fromInt 2

