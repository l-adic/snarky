-- | Finalize another proof's deferred values in the Wrap circuit.
-- |
-- | The Wrap circuit verifies a previous Step proof. Unlike the Step FOP which
-- | has domain masking and conditional challenge absorption, the Wrap FOP:
-- | - Uses a constant domain generator (no masking, zetaw = scale_(gen, zeta))
-- | - Computes omega powers as pure constants (no in-circuit inv/mul)
-- | - Uses a plain sponge for challenge digest (no OptSponge)
-- | - Has no proofs-verified mask (all sg_evals are EvalJust)
-- | - Uses Type2 shift for deferred values (x + 2^(n-1))
-- | - Uses squeeze_scalar (constrain_low_bits:false) for xi
-- | - Seals beta, gamma, and all shifted values (matching map_plonk_to_field)
-- |
-- | Reference: wrap_verifier.ml:1511-1783 `finalize_other_proof`
module Pickles.Wrap.FinalizeOtherProof
  ( WrapFinalizeOtherProofInput
  , wrapFinalizeOtherProofCircuit
  , pow2PowMul
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (foldM)
import Data.Int (pow) as Int
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for, traverse, traverse_)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, zipWith, (!!))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (bCorrectCircuit, bPolyCircuit)
import Pickles.Linearization.Env (EnvM, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (runLinearizationPoly)
import Pickles.PlonkChecks (absorbPointEval, extractEvalFields)
import Pickles.PlonkChecks.CombinedInnerProduct (buildEvalListUnmasked, hornerCombine)
import Pickles.PlonkChecks.GateConstraints (buildEvalPoint)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Sponge (absorb, evalSpongeM, initialSpongeCircuit, labelM, liftSnarky, squeeze, squeezeScalar, squeezeScalarChallenge)
import Pickles.Step.Domain (pow2PowSquare)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofOutput, FinalizeOtherProofParams)
import Pickles.Verify (ivpTrace)
import Pickles.Verify.Types (UnfinalizedProof, toPlonkMinimal)
import Pickles.Wrap.OtherField as WrapOtherField
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import RandomOracle.Sponge (Sponge)
import Snarky.Circuit.CVar (negate_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, add_, all_, const_, div_, equals_, inv_, label, mul_, pow_, seal, sub_)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (Type2, toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Input for the Wrap circuit's FinalizeOtherProof.
-- |
-- | Unlike the Step FOP input, this has:
-- | - No `mask`: all previous proofs are always present
-- | - No `domainLog2Var`: domain is fixed at compile time
-- |
-- | Reference: wrap_verifier.ml:1511-1520
type WrapFinalizeOtherProofInput n d fv b =
  { unfinalized :: UnfinalizedProof d fv (Type2 fv) b
  , witness :: ProofWitness fv
  , prevChallenges :: Vector n (Vector d fv)
  }

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

-- | Maximum alpha power needed by permutation and constant_term.
maxAlphaPower :: Int
maxAlphaPower = 70

-- | Finalize another proof's deferred values in the Wrap circuit.
-- |
-- | Reference: wrap_verifier.ml:1511-1783
wrapFinalizeOtherProofCircuit
  :: forall _d d _n n f f' g t m r2
   . Add 1 _d d
  => Add 1 _n n
  => PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => LinearizationFFI f g
  => Reflectable d Int
  => FinalizeOtherProofParams f r2
  -> (FVar f -> Snarky (KimchiConstraint f) t m (FVar f))
  -> WrapFinalizeOtherProofInput n d (FVar f) (BoolVar f)
  -> Snarky (KimchiConstraint f) t m (FinalizeOtherProofOutput d f)
wrapFinalizeOtherProofCircuit params vanishingPolynomial { unfinalized, witness, prevChallenges } = label "wrap-finalize-other-proof" do
  let
    ops = WrapOtherField.fopShiftOps @f @m
    deferred = unfinalized.deferredValues
    endoVar = const_ params.endo
    allEvals = witness.allEvals

  ---------------------------------------------------------------------------
  -- Step 1: map_plonk_to_field
  -- OCaml: map_challenges ~f:seal ~scalar:scalar_to_field
  -- Right-to-left record field evaluation: zeta, gamma, beta, alpha
  ---------------------------------------------------------------------------
  let plonkMin = toPlonkMinimal deferred.plonk
  zeta <- label "step1_zeta" $ toField @8 plonkMin.zeta endoVar
  gamma <- label "step1_gamma" $ seal (SizedF.toField plonkMin.gamma)
  beta <- label "step1_beta" $ seal (SizedF.toField plonkMin.beta)
  alpha <- label "step1_alpha" $ toField @8 plonkMin.alpha endoVar

  -- map_fields ~f:(Shifted_value.Type2.map ~f:seal)
  -- Right-to-left: perm, zetaToDomainSize, zetaToSrsLength
  sealedPlonk <- label "step1_seal_shifted" do
    perm <- ops.sealInner deferred.plonk.perm
    zetaToDomainSize <- ops.sealInner deferred.plonk.zetaToDomainSize
    zetaToSrsLength <- ops.sealInner deferred.plonk.zetaToSrsLength
    pure { perm, zetaToDomainSize, zetaToSrsLength }

  ---------------------------------------------------------------------------
  -- Step 2: Compute zetaw
  -- OCaml: zetaw = Field.mul domain#generator plonk.zeta
  -- Generator is Field.constant → scale_ produces no R1CS
  ---------------------------------------------------------------------------
  zetaw <- mul_ params.domain.generator zeta

  ---------------------------------------------------------------------------
  -- Step 3: Compute challenge polynomial evaluations (sg_evals)
  -- OCaml right-to-left: zetaw tuple element first, then zeta.
  -- Within each: right-to-left Vector.map (last element first).
  ---------------------------------------------------------------------------
  sgZetawRev <- label "step3_sgZetaw" $ for (Vector.reverse prevChallenges) \chals ->
    bPolyCircuit { challenges: chals, x: zetaw }
  let sgZetaw = Vector.reverse sgZetawRev

  sgZetaRev <- label "step3_sgZeta" $ for (Vector.reverse prevChallenges) \chals ->
    bPolyCircuit { challenges: chals, x: zeta }
  let sgZeta = Vector.reverse sgZetaRev

  ---------------------------------------------------------------------------
  -- Step 4: Sponge operations
  -- Plain sponge for challenge_digest (absorb all unconditionally).
  -- squeeze_scalar for xi (constrain_low_bits:false).
  -- squeeze_challenge for r (constrain_low_bits:true).
  ---------------------------------------------------------------------------
  { xi, r, xiCorrect, xiRaw, rRaw } <- label "step4_sponge" $ evalSpongeM initialSpongeCircuit do
    labelM "abs_sd" $ absorb unfinalized.spongeDigestBeforeEvaluations
    -- Challenge digest: separate plain sponge over all prev challenges
    challengeDigest <- liftSnarky $ label "step4_challengeDigest" $ evalSpongeM (initialSpongeCircuit :: Sponge (FVar f)) do
      traverse_ (traverse_ absorb) prevChallenges
      squeeze
    labelM "abs_cd" $ absorb challengeDigest
    labelM "abs_fte" $ absorb allEvals.ftEval1
    labelM "abs_pe_z" $ absorb allEvals.publicEvals.zeta
    labelM "abs_pe_zw" $ absorb allEvals.publicEvals.omegaTimesZeta
    labelM "abs_ze_z" $ absorb allEvals.zEvals.zeta
    labelM "abs_ze_zw" $ absorb allEvals.zEvals.omegaTimesZeta
    _ <- traverse (\(Tuple i pe) -> labelM ("abs_ie_" <> show (getFinite i)) $ absorbPointEval pe)
      (Vector.zip (Vector.generate @6 identity) allEvals.indexEvals)
    _ <- traverse (\(Tuple i pe) -> labelM ("abs_we_" <> show (getFinite i)) $ absorbPointEval pe)
      (Vector.zip (Vector.generate @15 identity) allEvals.witnessEvals)
    _ <- traverse (\(Tuple i pe) -> labelM ("abs_ce_" <> show (getFinite i)) $ absorbPointEval pe)
      (Vector.zip (Vector.generate @15 identity) allEvals.coeffEvals)
    _ <- traverse (\(Tuple i pe) -> labelM ("abs_se_" <> show (getFinite i)) $ absorbPointEval pe)
      (Vector.zip (Vector.generate @6 identity) allEvals.sigmaEvals)
    -- xi: squeeze_scalar (constrain_low_bits:false)
    xiActual <- labelM "sq_xi" $ squeezeScalar { endo: endoVar }
    -- r: squeeze_challenge (constrain_low_bits:true)
    rActual <- labelM "sq_r" $ squeezeScalarChallenge { endo: endoVar }
    liftSnarky $ label "step4_expand" do
      xiCorr <- equals_ (SizedF.toField xiActual) (SizedF.toField deferred.xi)
      xi' <- toField @8 deferred.xi endoVar
      r' <- toField @8 rActual endoVar
      pure { xi: xi', r: r', xiCorrect: xiCorr, xiRaw: SizedF.toField xiActual, rRaw: SizedF.toField rActual }

  ---------------------------------------------------------------------------
  -- Step 5: pow2_pows
  -- OCaml computes zeta_n and zetaw_n for combined_evals (both generate
  -- Square constraints even for single-chunk evals where result isn't used).
  ---------------------------------------------------------------------------
  label "step5_pow2pows" do
    void $ pow2PowSquare zeta params.domainLog2
    void $ pow2PowSquare zetaw params.domainLog2

  ---------------------------------------------------------------------------
  -- Steps 6+7: PlonK env + ft_eval0
  -- Omega powers are pure constants (generator is constant).
  -- zetaToNMinus1 is zeta^n - 1 (no domain masking).
  ---------------------------------------------------------------------------
  let
    pEval0 = allEvals.publicEvals.zeta

    evalPoint = buildEvalPoint
      { witnessEvals: allEvals.witnessEvals
      , coeffEvals: map _.zeta allEvals.coeffEvals
      , indexEvals: allEvals.indexEvals
      , defaultVal: const_ zero
      }

    w0 :: Vector 15 (FVar f)
    w0 = map _.zeta allEvals.witnessEvals

    s0 :: Vector 6 (FVar f)
    s0 = map _.zeta allEvals.sigmaEvals

    zZeta = allEvals.zEvals.zeta
    zOmegaTimesZeta = allEvals.zEvals.omegaTimesZeta

    shifts = params.domain.shifts

  -- Precompute alpha^0..alpha^70 (shared between ft_eval0 and perm_scalar)
  -- Must come before omega power usage to match OCaml constraint order.
  alphaPowers <- label "step6_alphaPowers" $ precomputeAlphaPowers maxAlphaPower alpha

  ---------------------------------------------------------------------------
  -- Step 6: Omega powers from domain#generator (plonk_checks.ml:248-265)
  -- When generator is Const, inv_/mul_/square_ short-circuit to constants.
  -- When generator is non-constant (wrap_main dynamic domain), these generate R1CS.
  ---------------------------------------------------------------------------
  let gen = params.domain.generator
  omegaM1 <- inv_ gen -- omega^-1 = one / gen
  omegaM2 <- mul_ omegaM1 omegaM1 -- omega^-2 (OCaml: let square x = x * x in plonk_checks)
  let omegaZkP1 = omegaM2 -- zk_rows == zk_rows_by_default → empty loop
  omegaZk <- mul_ omegaZkP1 omegaM1 -- omega^-3

  -- zkPoly = (zeta - omega^-1)(zeta - omega^-2)(zeta - omega^-3)
  zkPoly <- label "step7_zkPoly" do
    t1 <- mul_ (zeta `sub_` omegaM1) (zeta `sub_` omegaZkP1)
    mul_ t1 (zeta `sub_` omegaZk)

  -- zetaToNMinus1: zeta^n - 1 (no domain masking, just pow2pow and subtract)
  -- Uses mul_ (R1CS) not square_ because this comes from plonk_checks.pow2pow
  -- which uses F.(acc * acc), unlike wrap_verifier.pow2pow which uses Field.square.
  zetaToNMinus1 <- label "step7_zetaToNMinus1" $
    vanishingPolynomial zeta

  let
    alphaPow n = unsafePartial $ fromJust $ Array.index alphaPowers n
    a21 = alphaPow 21
    a22 = alphaPow 22
    a23 = alphaPow 23

  -- ft_eval0: term1 - p_eval0 - term2 + boundary - constant_term
  let w6 = w0 !! unsafeFinite @15 6
  term1Init <- label "step7_ft_term1init" $ mul_ (add_ w6 gamma) zOmegaTimesZeta >>= \t -> mul_ t a21 >>= \t' -> mul_ t' zkPoly
  let wSigma = zipWith Tuple (Vector.take @6 w0) s0
  term1 <- label "step7_ft_term1" $ foldM
    ( \acc (Tuple wi si) -> do
        betaSi <- mul_ beta si
        mul_ (add_ (add_ betaSi wi) gamma) acc
    )
    term1Init
    wSigma

  let term1MinusP = sub_ term1 pEval0

  term2Init <- label "step7_ft_term2init" $ mul_ a21 zkPoly >>= \t -> mul_ t zZeta
  let wShifts = zipWith Tuple (Vector.take @7 w0) shifts
  term2 <- label "step7_ft_term2" $ foldM
    ( \acc (Tuple wi si) -> do
        betaZetaSi <- mul_ beta zeta >>= \t -> mul_ t si
        mul_ acc (add_ (add_ gamma betaZetaSi) wi)
    )
    term2Init
    wShifts

  let
    -- omega_to_zk is a constant in Wrap (unlike Step where it's a circuit var)
    zetaMinusOmegaZk = sub_ zeta omegaZk
    zetaMinus1 = sub_ zeta (const_ one)

  boundary <- label "step7_ft_boundary" do
    term23 <- mul_ zetaToNMinus1 a23 >>= \t -> mul_ t zetaMinus1
    term22 <- mul_ zetaToNMinus1 a22 >>= \t -> mul_ t zetaMinusOmegaZk
    let oneMinusZ = sub_ (const_ one) zZeta
    nominator <- mul_ (add_ term22 term23) oneMinusZ
    denominator <- mul_ zetaMinusOmegaZk zetaMinus1
    div_ nominator denominator

  let permResult = add_ (sub_ term1MinusP term2) boundary

  -- omegaForLagrange: matches OCaml plonk_checks.ml:311-328 unnormalized_lagrange_basis
  -- Returns the omega power for a given lagrange basis position.
  -- Uses circuit-computed omega values (constant when domain is constant).
  let
    omegaForLagrange { zkRows: zk, offset } =
      if not zk && offset == 0 then const_ one
      else if not zk && offset == 1 then gen
      else if not zk && offset == (-1) then omegaM1
      else if not zk && offset == (-2) then omegaZkP1
      else if not zk && offset == (-3) then omegaZk
      else if zk && offset == 0 then omegaZk
      -- (true, -1) is lazy in OCaml; not used by constant_term tokens
      else const_ one

    vanishesOnZk = const_ one

    baseEnv :: EnvM f (Snarky (KimchiConstraint f) t m)
    baseEnv = buildCircuitEnvM
      alphaPowers
      zeta
      params.domainLog2
      omegaForLagrange
      evalPoint
      vanishesOnZk
      beta
      gamma
      (const_ one) -- jointCombiner (None → 1)
    env = baseEnv { computeZetaToNMinus1 = pure zetaToNMinus1 }

  constantTerm <- label "step7_ft_constantTerm" $ evaluateM (runLinearizationPoly params.linearizationPoly) env

  let ftEval0 = sub_ permResult constantTerm

  ---------------------------------------------------------------------------
  -- Step 8: Combined inner product
  -- OCaml right-to-left for `+`: zetaw combine computed first.
  -- No mask: all sg_evals are EvalJust.
  ---------------------------------------------------------------------------
  combineZetaw <- label "step8_combineZetaw" $ hornerCombine xi $ buildEvalListUnmasked
    { sgEvals: sgZetaw
    , publicInput: allEvals.publicEvals.omegaTimesZeta
    , ftEval: allEvals.ftEval1
    , evals: extractEvalFields _.omegaTimesZeta allEvals
    }

  rTimesZetaw <- label "step8_rTimesZetaw" $ mul_ r combineZetaw

  combineZeta <- label "step8_combineZeta" $ hornerCombine xi $ buildEvalListUnmasked
    { sgEvals: sgZeta
    , publicInput: allEvals.publicEvals.zeta
    , ftEval: ftEval0
    , evals: extractEvalFields _.zeta allEvals
    }

  let actualCip = add_ combineZeta rTimesZetaw
  let expectedCip = ops.unshift deferred.combinedInnerProduct
  cipCorrect <- label "step8_cipCorrect" $ equals_ expectedCip actualCip

  ---------------------------------------------------------------------------
  -- Step 9: b_correct
  -- Expand 16 bulletproof challenges via endo (reverse order matching
  -- OCaml's right-to-left Vector.map evaluation).
  ---------------------------------------------------------------------------
  expandedRev <- label "step9_expandChallenges" $ for (Vector.reverse deferred.bulletproofChallenges) \c -> toField @8 c endoVar
  let expandedChallenges = Vector.reverse expandedRev

  bCorrect <- label "step9_bCorrect" $ bCorrectCircuit
    { challenges: expandedChallenges
    , zeta
    , zetaOmega: zetaw
    , evalscale: r
    , expectedB: ops.unshift deferred.b
    }

  ---------------------------------------------------------------------------
  -- Step 10: perm_correct
  -- Inline perm scalar using shared alpha powers (a21, zkPoly).
  -- perm = -(z_omega * beta * alpha^21 * zkp * prod(gamma + beta*s_i + w_i))
  ---------------------------------------------------------------------------
  actualPerm <- label "step10_perm" do
    init' <- mul_ zOmegaTimesZeta beta >>= \t -> mul_ t a21 >>= \t' -> mul_ t' zkPoly
    let wSigmaPerm = zipWith Tuple (Vector.take @6 w0) s0
    result <- foldM
      ( \acc (Tuple wi si) -> do
          betaSigma <- mul_ beta si
          let term = add_ (add_ gamma betaSigma) wi
          mul_ acc term
      )
      init'
      wSigmaPerm
    pure (negate_ result)

  -- zeta_to_srs_length computation (generates constraints even though result is voided)
  label "step10_zetaToSrs" $ void $ pow_ zeta (Int.pow 2 params.srsLengthLog2)

  plonkOk <- label "step10_plonkOk" $ ops.shiftedEqual sealedPlonk.perm actualPerm

  ---------------------------------------------------------------------------
  -- Step 11: Combine all checks
  ---------------------------------------------------------------------------
  finalized <- label "step11_finalized" $ all_ [ xiCorrect, bCorrect, cipCorrect, plonkOk ]

  -- DIAG: dump key field values for wrap FOP so we can identify which
  -- FOP component (cip/b/perm/xi/r) mismatches vs its claim.
  ivpTrace "wrap.fop.dbg.xi_expanded" xi
  ivpTrace "wrap.fop.dbg.xi_claim_raw" (SizedF.toField deferred.xi)
  ivpTrace "wrap.fop.dbg.xi_sponge_raw" xiRaw
  ivpTrace "wrap.fop.dbg.r_sponge" r
  ivpTrace "wrap.fop.dbg.r_sponge_raw" rRaw
  ivpTrace "wrap.fop.dbg.cip_actual" actualCip
  ivpTrace "wrap.fop.dbg.cip_expected" expectedCip
  ivpTrace "wrap.fop.dbg.combineZeta" combineZeta
  ivpTrace "wrap.fop.dbg.combineZetaw" combineZetaw
  ivpTrace "wrap.fop.dbg.perm_actual" actualPerm
  ivpTrace "wrap.fop.dbg.zeta" zeta
  ivpTrace "wrap.fop.dbg.zetaw" zetaw
  ivpTrace "wrap.fop.dbg.ftEval0" ftEval0
  ivpTrace "wrap.fop.dbg.ftEval1_used" allEvals.ftEval1

  let challenges = deferred.bulletproofChallenges

  pure { finalized, xiCorrect, bCorrect, cipCorrect, plonkOk, challenges, expandedChallenges }

-- | Compute x^(2^n) using R1CS (mul) constraints.
-- |
-- | Matches OCaml's plonk_checks.pow2pow which uses F.(acc * acc).
-- | Generates R1CS constraints (co=1, cm=-1), unlike pow2PowSquare which
-- | generates Square constraints (co=-1, cm=1).
pow2PowMul
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Int
  -> Snarky c t m (FVar f)
pow2PowMul x n = go x n
  where
  go acc i
    | i <= 0 = pure acc
    | otherwise = do
        sq <- mul_ acc acc
        go sq (i - 1)
