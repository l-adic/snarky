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
  ( Input
  , wrapFinalizeOtherProofCircuit
  , pow2PowMul
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Int (pow) as Int
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.FinalizeOtherProof (Output, Params)
import Pickles.IPA (bCorrectCircuit, challengePolyEvals, computeChallenges)
import Pickles.IncrementallyVerifyProof (ivpTrace)
import Pickles.Linearization.Env (AlphaPowersLen, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (runLinearizationPoly)
import Pickles.PlonkChecks (challengeDigest, extractEvalFields, squeezeXiR)
import Pickles.PlonkChecks.CombinedInnerProduct (buildEvalListUnmasked, combinedInnerProduct)
import Pickles.PlonkChecks.Domain (omegaPowers, zkPolynomial)
import Pickles.PlonkChecks.GateConstraints (buildEvalPoint)
import Pickles.PlonkChecks.Permutation as Permutation
import Pickles.ProofWitness (ProofWitness)
import Pickles.Util.Pow2 (pow2PowSquare)
import Pickles.Verify.Types (UnfinalizedProof, toPlonkMinimal)
import Pickles.Wrap.OtherField as WrapOtherField
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class BasicSystem, BoolVar, FVar, Snarky, all_, const_, equals_, label, mul_, pow_, seal, sub_)
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
type Input n d fv b =
  { unfinalized :: UnfinalizedProof d fv (Type2 fv) b
  , witness :: ProofWitness fv
  , prevChallenges :: Vector n (Vector d fv)
  }

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

-- | Finalize another proof's deferred values in the Wrap circuit.
-- |
-- | Reference: wrap_verifier.ml:1511-1783
wrapFinalizeOtherProofCircuit
  :: forall d dPred n nPred nd ndPred f f' r r2
   . Add 1 dPred d
  => Add 1 nPred n
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable nd Int
  => PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => LinearizationFFI f
  => Reflectable d Int
  => Params nd f r2
  -> (FVar f -> Snarky f (KimchiConstraint f) r (FVar f))
  -> Input n d (FVar f) (BoolVar f)
  -> Snarky f (KimchiConstraint f) r (Output d f)
wrapFinalizeOtherProofCircuit params vanishingPolynomial { unfinalized, witness, prevChallenges } = label "wrap-finalize-other-proof" do
  -- Wrap is currently single-domain; access via Vector.head. Multi-
  -- domain wrap dispatch (if ever needed) would mirror Step's
  -- Pseudo.toDomain pattern in Commit C.
  let
    ops = WrapOtherField.fopShiftOps @f
    deferred = unfinalized.deferredValues
    endoVar = const_ params.endo
    allEvals = witness.allEvals
    headDomain = Vector.head params.domains
    domain = { generator: headDomain.generator, shifts: params.shifts }
    domainLog2 = headDomain.log2

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
  zetaw <- mul_ domain.generator zeta

  ---------------------------------------------------------------------------
  -- Step 3: Compute challenge polynomial evaluations (sg_evals)
  -- OCaml right-to-left: zetaw tuple element first, then zeta.
  -- Within each: right-to-left Vector.map (last element first).
  ---------------------------------------------------------------------------
  sgZetaw <- label "step3_sgZetaw" $ challengePolyEvals prevChallenges zetaw
  sgZeta <- label "step3_sgZeta" $ challengePolyEvals prevChallenges zeta

  ---------------------------------------------------------------------------
  -- Step 4: Sponge operations
  -- Plain sponge for challenge_digest (absorb all unconditionally).
  -- squeeze_scalar for xi (constrain_low_bits:false).
  -- squeeze_challenge for r (constrain_low_bits:true).
  ---------------------------------------------------------------------------
  { xi: xiActual, r: rActual } <- label "step4_sponge" $ squeezeXiR
    { spongeDigestBeforeEvaluations: unfinalized.spongeDigestBeforeEvaluations
    , challengeDigest: challengeDigest prevChallenges
    , allEvals
    , endo: endoVar
    , xiConstrainLowBits: false
    }
  xiCorrect <- label "step4_xiCorrect" $ equals_ (SizedF.toField xiActual) (SizedF.toField deferred.xi)
  xi <- label "step4_xi" $ toField @8 deferred.xi endoVar
  r <- label "step4_r" $ toField @8 rActual endoVar
  let
    xiRaw = SizedF.toField xiActual
    rRaw = SizedF.toField rActual

  ---------------------------------------------------------------------------
  -- Step 5: pow2_pows
  -- OCaml computes zeta_n and zetaw_n for combined_evals (both generate
  -- Square constraints even for single-chunk evals where result isn't used).
  ---------------------------------------------------------------------------
  label "step5_pow2pows" do
    void $ pow2PowSquare zeta domainLog2
    void $ pow2PowSquare zetaw domainLog2

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

    w0 = map _.zeta allEvals.witnessEvals

    s0 = map _.zeta allEvals.sigmaEvals

    zZeta = allEvals.zEvals.zeta
    zOmegaTimesZeta = allEvals.zEvals.omegaTimesZeta

    shifts = domain.shifts

  -- Precompute alpha^0..alpha^70 (shared between ft_eval0 and perm_scalar)
  -- Must come before omega power usage to match OCaml constraint order.
  alphaPowers <- label "step6_alphaPowers" $ precomputeAlphaPowers alpha

  ---------------------------------------------------------------------------
  -- Step 6: Omega powers from domain#generator (plonk_checks.ml:248-265)
  -- When generator is Const, inv_/mul_/square_ short-circuit to constants.
  -- When generator is non-constant (wrap_main dynamic domain), these generate R1CS.
  ---------------------------------------------------------------------------
  let gen = domain.generator
  omegas@{ omegaToMinus1: omegaM1, omegaToZkPlus1: omegaZkP1, omegaToZk: omegaZk } <-
    omegaPowers { generator: gen, zkRows: params.zkRows }
  zkPoly <- label "step7_zkPoly" $ zkPolynomial zeta omegas

  -- zetaToNMinus1: zeta^n - 1 (no domain masking, just pow2pow and subtract)
  -- Uses mul_ (R1CS) not square_ because this comes from plonk_checks.pow2pow
  -- which uses F.(acc * acc), unlike wrap_verifier.pow2pow which uses Field.square.
  zetaToNMinus1 <- label "step7_zetaToNMinus1" $
    vanishingPolynomial zeta

  let
    alphaPow n = Vector.index alphaPowers (unsafeFinite @AlphaPowersLen n)
    a21 = alphaPow 21
    a22 = alphaPow 22
    a23 = alphaPow 23

  -- ft_eval0: term1 - p_eval0 - term2 + boundary - constant_term. The
  -- permutation half is `Permutation.permContributionCircuit`, shared with
  -- the step verifier. omega_to_zk is a constant in Wrap (unlike Step where
  -- it's a circuit var) when the domain is; the gadget is agnostic.
  permResult <- Permutation.permContributionCircuit
    { w: Vector.take @7 w0
    , sigma: s0
    , z: { zeta: zZeta, omegaTimesZeta: zOmegaTimesZeta }
    , shifts
    , alpha
    , beta
    , gamma
    , zkPolynomial: zkPoly
    , zetaToNMinus1
    , omegaToMinusZkRows: omegaZk
    , zeta
    }
    { pEval0, alphaPow21: a21, alphaPow22: a22, alphaPow23: a23 }

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

    baseEnv = buildCircuitEnvM
      alphaPowers
      zeta
      domainLog2
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
  actualCip <- combinedInnerProduct
    { xi
    , r
    , evalsZeta: buildEvalListUnmasked
        { sgEvals: sgZeta
        , publicInput: allEvals.publicEvals.zeta
        , ftEval: ftEval0
        , evals: extractEvalFields _.zeta allEvals
        }
    , evalsZetaw: buildEvalListUnmasked
        { sgEvals: sgZetaw
        , publicInput: allEvals.publicEvals.omegaTimesZeta
        , ftEval: allEvals.ftEval1
        , evals: extractEvalFields _.omegaTimesZeta allEvals
        }
    }
  let expectedCip = ops.unshift deferred.combinedInnerProduct
  cipCorrect <- equals_ expectedCip actualCip

  ---------------------------------------------------------------------------
  -- Step 9: b_correct
  -- Expand 16 bulletproof challenges via endo (reverse order matching
  -- OCaml's right-to-left Vector.map evaluation).
  ---------------------------------------------------------------------------
  expandedChallenges <- label "step9_expandChallenges" $
    computeChallenges deferred.bulletproofChallenges endoVar

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
  actualPerm <- label "step10_perm" $ Permutation.permScalarCircuit
    { w: Vector.take @6 w0
    , sigma: s0
    , zOmega: zOmegaTimesZeta
    , beta
    , gamma
    , zkPolynomial: zkPoly
    , alphaPow21: a21
    }

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
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Int
  -> Snarky f c r (FVar f)
pow2PowMul x n = go x n
  where
  go acc i
    | i <= 0 = pure acc
    | otherwise = do
        sq <- mul_ acc acc
        go sq (i - 1)
