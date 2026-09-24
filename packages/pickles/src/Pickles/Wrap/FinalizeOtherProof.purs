-- | The wrap circuit's half of finalize-other-proof: recheck the
-- | deferred values the step proof it verifies left behind.
-- |
-- | The step-side counterpart is `Pickles.Step.FinalizeOtherProof`. The
-- | shared gadgets live in `Pickles.FinalizeOtherProof` and
-- | `Pickles.PlonkChecks`.
module Pickles.Wrap.FinalizeOtherProof
  ( Input
  , wrapFinalizeOtherProofCircuit
  , pow2PowMul
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Fin (unsafeFinite)
import Data.Int (pow) as Int
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.DeferredValues (UnfinalizedProof, toPlonkMinimal)
import Pickles.FinalizeOtherProof (Output, Params, pow2PowSquare)
import Pickles.IPA (bCorrectCircuit, challengePolyEvals, computeChallenges)
import Pickles.IncrementallyVerifyProof.FqSpongeTranscript (ivpTrace)
import Pickles.Linearization.Env (AlphaPowersLen, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (runLinearizationPoly)
import Pickles.PlonkChecks (buildEvalListUnmasked, buildEvalPoint, challengeDigest, combinedInnerProduct, extractEvalFields, omegaPowers, permContributionCircuit, permScalarCircuit, squeezeXiR, zkPolynomial)
import Pickles.Types (Evals)
import Pickles.Wrap.OtherField as WrapOtherField
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class BasicSystem, BoolVar, FVar, Snarky, add_, all_, const_, equals_, label, mul_, pow_, seal, sub_)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (Type2, toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField)

-- | What `wrapFinalizeOtherProofCircuit` reads: the step proof's
-- | unfinalized deferred values, its evaluations, and the `n` previous
-- | bullet-proof challenge stacks. Every slot is always present, so
-- | there is no mask.
type Input n d fv b =
  { unfinalized :: UnfinalizedProof d fv (Type2 fv) b
  , allEvals :: Evals fv
  , prevChallenges :: Vector n (Vector d fv)
  }

-- | Recompute the step proof's deferred values and report whether each
-- | matches the claim in its statement, together with the expanded
-- | bullet-proof challenges.
wrapFinalizeOtherProofCircuit
  :: forall d dPred n nPred f f' r r2
   . Add 1 dPred d
  => Add 1 nPred n
  => PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => LinearizationFFI f
  => Reflectable d Int
  => Params f r2
  -> (FVar f -> Snarky f (KimchiConstraint f) r (FVar f))
  -> Input n d (FVar f) (BoolVar f)
  -> Snarky f (KimchiConstraint f) r (Output d f)
wrapFinalizeOtherProofCircuit params vanishingPolynomial { unfinalized, allEvals, prevChallenges } = label "wrap-finalize-other-proof" do
  -- `params.domains` is a singleton: the caller has already resolved
  -- which domain this slot uses.
  let
    ops = WrapOtherField.fopShiftOps @f
    deferred = unfinalized.deferredValues
    endoVar = const_ params.endo
    headDomain = NEA.head params.domains
    domain = { generator: headDomain.generator, shifts: params.shifts }
    domainLog2 = headDomain.log2

  -- The order of these four is fixed by the constraint layout: zeta,
  -- gamma, beta, alpha.
  let plonkMin = toPlonkMinimal deferred.plonk
  zeta <- label "step1_zeta" $ toField @8 plonkMin.zeta endoVar
  gamma <- label "step1_gamma" $ seal (SizedF.toField plonkMin.gamma)
  beta <- label "step1_beta" $ seal (SizedF.toField plonkMin.beta)
  alpha <- label "step1_alpha" $ toField @8 plonkMin.alpha endoVar

  -- Likewise fixed: perm, zetaToDomainSize, zetaToSrsLength.
  sealedPlonk <- label "step1_seal_shifted" do
    perm <- ops.sealInner deferred.plonk.perm
    zetaToDomainSize <- ops.sealInner deferred.plonk.zetaToDomainSize
    zetaToSrsLength <- ops.sealInner deferred.plonk.zetaToSrsLength
    pure { perm, zetaToDomainSize, zetaToSrsLength }

  zetaw <- mul_ domain.generator zeta

  -- Challenge-polynomial evaluations, in fixed order: zetaw before
  -- zeta, and within each, the last challenge first.
  sgZetaw <- label "step3_sgZetaw" $ challengePolyEvals prevChallenges zetaw
  sgZeta <- label "step3_sgZeta" $ challengePolyEvals prevChallenges zeta

  -- A plain sponge, absorbing every challenge unconditionally. `xi` is
  -- squeezed without the low-bit constraint, `r` with it.
  { xi: xiActual, r: rActual } <- label "step4_sponge" $ squeezeXiR
    { spongeDigestBeforeEvaluations: unfinalized.spongeDigestBeforeEvaluations
    , challengeDigest: challengeDigest prevChallenges
    , allEvals
    , endo: endoVar
    }
  xiCorrect <- label "step4_xiCorrect" $ equals_ (SizedF.toField xiActual) (SizedF.toField deferred.xi)
  xi <- label "step4_xi" $ toField @8 deferred.xi endoVar
  r <- label "step4_r" $ toField @8 rActual endoVar
  let
    xiRaw = SizedF.toField xiActual
    rRaw = SizedF.toField rActual

  -- Recombining chunked evaluations is a Horner fold in
  -- `zeta^(2^srsLengthLog2)`, the chunk size, which is why the reference
  -- computes both powers at this point. This port collapses the
  -- evaluations out of circuit, in `Pickles.Prove.Pure.Wrap`, so nothing
  -- here reads the results — but the Square constraints are part of the
  -- circuit, so the calls stay.
  label "step5_pow2pows" do
    void $ pow2PowSquare zeta params.srsLengthLog2
    void $ pow2PowSquare zetaw params.srsLengthLog2

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

  -- `alpha^0 .. alpha^70`, shared by `ft_eval0` and the perm scalar.
  -- Emitted before any omega power, because the order is fixed.
  alphaPowers <- label "step6_alphaPowers" $ precomputeAlphaPowers alpha

  -- A constant generator folds these to constants; the dynamic wrap
  -- domain makes them emit R1CS.
  let gen = domain.generator
  omegas@{ omegaToMinus1: omegaM1, omegaToZkPlus1: omegaZkP1, omegaToZk: omegaZk } <-
    omegaPowers { generator: gen, zkRows: params.zkRows }
  zkPoly <- label "step7_zkPoly" $ zkPolynomial zeta omegas

  -- `zeta^n - 1`, with no domain masking.
  zetaToNMinus1 <- label "step7_zetaToNMinus1" $
    vanishingPolynomial zeta

  let
    alphaPow n = Vector.index alphaPowers (unsafeFinite @AlphaPowersLen n)
    a21 = alphaPow 21
    a22 = alphaPow 22
    a23 = alphaPow 23

  -- The permutation half of `ft_eval0`; the constant term is
  -- subtracted below.
  permResult <- permContributionCircuit
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

  -- The omega power for one unnormalized lagrange basis position.
  let
    omegaForLagrange { zkRows: zk, offset } =
      if not zk && offset == 0 then const_ one
      else if not zk && offset == 1 then gen
      else if not zk && offset == (-1) then omegaM1
      else if not zk && offset == (-2) then omegaZkP1
      else if not zk && offset == (-3) then omegaZk
      else if zk && offset == 0 then omegaZk
      -- `(true, -1)` is never requested by the constant-term tokens.
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

  -- Endo-expanded last challenge first; the order is fixed.
  expandedChallenges <- label "step9_expandChallenges" $
    computeChallenges deferred.bulletproofChallenges endoVar

  bCorrect <- label "step9_bCorrect" $ bCorrectCircuit
    { challenges: expandedChallenges
    , zeta
    , zetaOmega: zetaw
    , evalscale: r
    , expectedB: ops.unshift deferred.b
    }

  actualPerm <- label "step10_perm" $ permScalarCircuit
    { w: Vector.take @6 w0
    , sigma: s0
    , zOmega: zOmegaTimesZeta
    , beta
    , gamma
    , zkPolynomial: zkPoly
    , alphaPow21: a21
    }

  actualZetaToSrs <- label "step10_zetaToSrs" $ pow_ zeta (Int.pow 2 params.srsLengthLog2)

  -- The three scalars `ft_comm` scales by, each against its claim
  -- (`Plonk_checks.checked`): `perm`, `zeta^(2^srsLengthLog2)`, `zeta^n`.
  permOk <- label "step10_permOk" $ ops.shiftedEqual sealedPlonk.perm actualPerm
  zetaToSrsOk <- label "step10_zetaToSrsOk" $
    ops.shiftedEqual sealedPlonk.zetaToSrsLength actualZetaToSrs
  zetaToDomainOk <- label "step10_zetaToDomainOk" $
    ops.shiftedEqual sealedPlonk.zetaToDomainSize (zetaToNMinus1 `add_` const_ one)
  plonkOk <- label "step10_plonkOk" $ all_ [ permOk, zetaToSrsOk, zetaToDomainOk ]

  finalized <- label "step11_finalized" $ all_ [ xiCorrect, bCorrect, cipCorrect, plonkOk ]

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

-- | `x^(2^n)`, built from multiplication constraints. `pow2PowSquare`
-- | computes the same value from Square constraints, so the two emit
-- | different circuits and are not interchangeable.
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
