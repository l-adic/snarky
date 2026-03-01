-- | Finalize another proof's deferred values in the Step circuit.
-- |
-- | When the Step circuit verifies a previous Wrap proof, it calls this
-- | function to verify all the deferred values. This includes:
-- | - xi_correct (scalar challenge matches squeezed value)
-- | - b_correct (challenge polynomial evaluation)
-- | - combined_inner_product_correct
-- | - plonk_checks_passed (permutation check)
-- |
-- | Domain values (omega powers, zkPolynomial, zetaToNMinus1) are computed
-- | in-circuit from the masked domain generator, matching OCaml's constraint
-- | structure exactly. The domain generator is masked by `domainWhich`
-- | (a boolean comparing runtime domain_log2 against compile-time value).
-- |
-- | Reference: step_verifier.ml:823-1165 `finalize_other_proof`
module Pickles.Step.FinalizeOtherProof
  ( -- * Types
    FinalizeOtherProofParams
  , FinalizeOtherProofInput
  , FinalizeOtherProofOutput
  -- * Circuit
  , finalizeOtherProofCircuit
  -- * Component Circuits (exported for testing)
  , module PlonkChecks
  , module ChallengeDigest
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (unsafeFinite)
import Data.Foldable (foldM)
import Data.Int (pow) as Int
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, zipWith, (!!))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (bCorrectCircuit, bPolyCircuit)
import Pickles.Linearization.Env (EnvM, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI, domainGenerator, domainShifts)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (LinearizationPoly, runLinearizationPoly)
import Pickles.OptSponge as OptSponge
import Pickles.PlonkChecks (absorbAllEvals)
import Pickles.PlonkChecks (absorbAllEvals) as PlonkChecks
import Pickles.PlonkChecks.CombinedInnerProduct (buildEvalList, hornerCombine)
import Pickles.PlonkChecks.GateConstraints (buildEvalPoint, parseHex)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Sponge (absorb, evalSpongeM, initialSpongeCircuit, liftSnarky, squeezeScalarChallenge)
import Pickles.Step.ChallengeDigest (ChallengeDigestInput, challengeDigestCircuit) as ChallengeDigest
import Pickles.Step.Domain (domainVanishingPoly, pow2PowSquare)
import Pickles.Verify.Types (BulletproofChallenges, UnfinalizedProof, toPlonkMinimal)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (negate_, scale_)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, add_, all_, const_, div_, equals_, inv_, mul_, pow_, sub_)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField, fromInt)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Compile-time parameters for finalizing another proof.
-- |
-- | These come from the verification key / are known at circuit compile time.
-- |
-- | - `domain`: Domain generator and shift values
-- | - `domainLog2`: Log2 of domain size (e.g. 16)
-- | - `srsLengthLog2`: Log2 of SRS length (e.g. 16)
-- | - `endo`: Endomorphism coefficient for scalar challenge conversion
-- | - `linearizationPoly`: The linearization polynomial for gate constraints
-- |
-- | Reference: step_verifier.ml:823 `finalize_other_proof` parameters
type FinalizeOtherProofParams :: Type -> Row Type -> Type
type FinalizeOtherProofParams f r =
  { domain :: { generator :: f, shifts :: Vector 7 f }
  , domainLog2 :: Int
  , srsLengthLog2 :: Int
  , endo :: f -- ^ EndoScalar coefficient (= Wrap_inner_curve.scalar = Vesta.endo_scalar for Step)
  , linearizationPoly :: LinearizationPoly f
  | r
  }

-- | Input for finalizing another proof.
-- |
-- | This combines:
-- | - `unfinalized`: The deferred values from the proof's public input
-- | - `witness`: Private witness data (polynomial evaluations)
-- | - `mask`: Proofs-verified mask (which previous proofs are "real")
-- | - `prevChallenges`: Old bulletproof challenges from all previous proofs
-- |     (already expanded to full field, used for CIP sg_evals and challenge_digest)
-- | - `domainLog2Var`: Runtime domain_log2 variable from public input
type FinalizeOtherProofInput n d f sf b =
  { -- | Unfinalized proof from public input
    unfinalized :: UnfinalizedProof d f sf b
  -- | Private witness data (polynomial evaluations)
  , witness :: ProofWitness f
  -- | Proofs-verified mask (for CIP and challenge_digest)
  , mask :: Vector n b
  -- | Old bulletproof challenges from all previous proofs
  , prevChallenges :: Vector n (Vector d f)
  -- | Runtime domain_log2 variable from public input
  , domainLog2Var :: f
  }

-- | Output from finalizing another proof.
-- |
-- | Returns:
-- | - `finalized`: Boolean indicating whether all checks passed
-- | - `challenges`: The raw bulletproof challenges (128-bit scalar challenges)
-- | - `expandedChallenges`: The expanded bulletproof challenges (full field via endo)
type FinalizeOtherProofOutput d f =
  { finalized :: BoolVar f
  , xiCorrect :: BoolVar f
  , bCorrect :: BoolVar f
  , cipCorrect :: BoolVar f
  , plonkOk :: BoolVar f
  , challenges :: BulletproofChallenges d (FVar f)
  , expandedChallenges :: Vector d (FVar f)
  }

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

-- | Maximum alpha power needed by either permutation or constant_term.
maxAlphaPower :: Int
maxAlphaPower = 70

-- | Finalize another proof's deferred values.
-- |
-- | This circuit verifies all the deferred values from a Wrap proof,
-- | matching OCaml's step_verifier.ml constraint structure exactly:
-- |
-- | 1. **Expand plonk minimal**: Convert raw 128-bit alpha/zeta to full field
-- |    (zeta expanded before alpha, matching OCaml right-to-left)
-- |
-- | 2. **Domain masking**: maskedGen = scale_(generator, domainWhich),
-- |    then zetaw = mul_ maskedGen zeta (non-constant, generates R1CS)
-- |
-- | 3. **Challenge polynomial evals**: bPoly for all prev_challenges at zetaw
-- |    then zeta (reverse order matching OCaml's right-to-left Vector.map2)
-- |
-- | 4. **Fr-sponge**: challenge_digest via OptSponge, absorb evaluations,
-- |    derive xi and r
-- |
-- | 5. **pow2_pows**: Compute zeta^(2^n) and zetaw^(2^n) via Square constraints
-- |
-- | 6. **Omega powers in-circuit**: inv_(maskedGen) → omega^-1, square → omega^-2,
-- |    multiply → omega^-3 (matching OCaml's non-constant domain generator)
-- |
-- | 7. **ft_eval0**: Inlined computation using shared alpha powers and
-- |    buildCircuitEnvM for constant_term evaluation
-- |
-- | 8. **CIP**: Horner fold matching Pcs_batch.combine_split_evaluations
-- |
-- | 9. **b_correct**: Challenge polynomial evaluation check
-- |
-- | 10. **perm_correct**: Permutation scalar using shared alpha powers
-- |
-- | 11. **Combine**: all_ [xiCorrect, bCorrect, cipCorrect, plonkOk]
-- |
-- | Reference: step_verifier.ml:823-1165
finalizeOtherProofCircuit
  :: forall _d d n f f' g t m sf r1 r2
   . Add 1 _d d
  => PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => LinearizationFFI f g
  => Reflectable d Int
  => { unshift :: sf -> FVar f
     , shiftedEqual :: sf -> FVar f -> Snarky (KimchiConstraint f) t m (BoolVar f)
     | r1
     }
  -> FinalizeOtherProofParams f r2
  -> FinalizeOtherProofInput n d (FVar f) sf (BoolVar f)
  -> Snarky (KimchiConstraint f) t m (FinalizeOtherProofOutput d f)
finalizeOtherProofCircuit ops params { unfinalized, witness, mask, prevChallenges, domainLog2Var } = do
  let
    deferred = unfinalized.deferredValues
    endoVar = const_ params.endo
    allEvals = witness.allEvals

  ---------------------------------------------------------------------------
  -- Step 2: Expand alpha and zeta via endo
  -- OCaml's map_challenges evaluates record fields right-to-left:
  --   zeta = scalar t.zeta is computed before alpha = scalar t.alpha
  ---------------------------------------------------------------------------
  let plonkMin = toPlonkMinimal deferred.plonk
  zeta <- toField @8 plonkMin.zeta endoVar
  alpha <- toField @8 plonkMin.alpha endoVar
  let beta = SizedF.toField plonkMin.beta
  let gamma = SizedF.toField plonkMin.gamma

  ---------------------------------------------------------------------------
  -- Step 3: Domain masking and zetaw
  -- OCaml: gen = mask [which_bit] [gen_constant] = Scale(gen_const, which_bit)
  -- Then: zetaw = mul gen zeta → R1CS because gen is non-constant
  ---------------------------------------------------------------------------
  domainWhich <- equals_ (const_ (fromInt params.domainLog2)) domainLog2Var
  let maskedGen = scale_ params.domain.generator (coerce domainWhich :: FVar f)
  zetaw <- mul_ maskedGen zeta

  ---------------------------------------------------------------------------
  -- Step 4: Compute challenge polynomial evaluations (sg_evals)
  -- OCaml right-to-left Vector.map2: index (n-1) evaluated before index 0.
  -- Within each, zetaw evaluated before zeta (right-to-left pair construction).
  ---------------------------------------------------------------------------
  sgZetawRev <- for (Vector.reverse prevChallenges) \chals ->
    bPolyCircuit { challenges: chals, x: zetaw }
  let sgZetaw = Vector.reverse sgZetawRev

  sgZetaRev <- for (Vector.reverse prevChallenges) \chals ->
    bPolyCircuit { challenges: chals, x: zeta }
  let sgZeta = Vector.reverse sgZetaRev

  ---------------------------------------------------------------------------
  -- Steps 5-8: Sponge operations
  -- challenge_digest via OptSponge, absorb sponge_digest + challenge_digest +
  -- all evaluations, squeeze xi and r.
  ---------------------------------------------------------------------------
  let
    pending :: Array (Tuple (BoolVar f) (FVar f))
    pending = Array.concat $ Vector.toUnfoldable $
      Vector.zipWith
        ( \keep chals ->
            map (Tuple keep) (Vector.toUnfoldable chals :: Array _)
        )
        mask
        prevChallenges

  { xi, r, xiCorrect } <- evalSpongeM initialSpongeCircuit do
    absorb unfinalized.spongeDigestBeforeEvaluations
    challengeDigest <- liftSnarky $
      OptSponge.squeeze (OptSponge.create :: OptSponge.OptSponge f) pending
    absorb challengeDigest
    absorbAllEvals allEvals
    xiActual <- squeezeScalarChallenge { endo: endoVar }
    rActual <- squeezeScalarChallenge { endo: endoVar }
    liftSnarky do
      xiCorr <- equals_ (SizedF.toField xiActual) (SizedF.toField deferred.xi)
      xi' <- toField @8 deferred.xi endoVar
      r' <- toField @8 rActual endoVar
      pure { xi: xi', r: r', xiCorrect: xiCorr }

  ---------------------------------------------------------------------------
  -- Step 9: pow2_pows via Field.square
  -- OCaml computes pow2_pows eagerly for zeta and zetaw (generates Square
  -- constraints even though the values may not all be used directly).
  ---------------------------------------------------------------------------
  void $ pow2PowSquare zeta params.domainLog2
  void $ pow2PowSquare zetaw params.domainLog2

  ---------------------------------------------------------------------------
  -- Step 10: Omega powers in-circuit
  -- OCaml computes omega powers from maskedGen (non-constant), so each
  -- produces R1CS constraints. zk_rows == zk_rows_by_default (3) → empty loop.
  --   omega_to_minus_1 = one / gen
  --   omega_to_minus_2 = square omega_to_minus_1
  --   omega_to_zk_plus_1 = omega_to_minus_2 (empty loop for zk_rows=3)
  --   omega_to_zk = omega_to_zk_plus_1 * omega_to_minus_1
  ---------------------------------------------------------------------------
  omegaM1 <- inv_ maskedGen
  omegaM2 <- mul_ omegaM1 omegaM1 -- OCaml: square x = x * x (R1CS, not Square)
  let omegaZkP1 = omegaM2 -- zk_rows == zk_rows_by_default → empty loop
  omegaZk <- mul_ omegaZkP1 omegaM1

  -- zkPoly = (zeta - omega^-1)(zeta - omega^-2)(zeta - omega^-3)
  -- Note: omegaM1 = omega^-1, omegaZkP1 = omega^-2, omegaZk = omega^-3
  zkPoly <- do
    t1 <- mul_ (zeta `sub_` omegaM1) (zeta `sub_` omegaZkP1)
    mul_ t1 (zeta `sub_` omegaZk)

  -- zetaToNMinus1 via domainVanishingPoly (mask * zeta^n - 1, sealed)
  zetaToNMinus1 <- domainVanishingPoly domainWhich zeta params.domainLog2

  ---------------------------------------------------------------------------
  -- Steps 10+11a: PlonK env + ft_eval0
  -- Inlined permutation contribution + boundary quotient + constant_term.
  -- Uses shared alpha powers between ft_eval0 and perm_scalar.
  ---------------------------------------------------------------------------
  let
    pEval0 = allEvals.publicEvals.zeta

    evalPoint = buildEvalPoint
      { witnessEvals: allEvals.witnessEvals
      , coeffEvals: map _.zeta allEvals.coeffEvals
      , indexEvals: allEvals.indexEvals
      , defaultVal: const_ zero
      }

    gen = domainGenerator @f params.domainLog2
    omegaToMinus1 = recip gen
    omegaToMinus2 = omegaToMinus1 * omegaToMinus1
    omegaToMinus3 = omegaToMinus1 * omegaToMinus1 * omegaToMinus1
    omegaToMinus4 = omegaToMinus1 * omegaToMinus1 * omegaToMinus1 * omegaToMinus1

    omegaForLagrange { zkRows: zk, offset } =
      if not zk && offset == 0 then one
      else if zk && offset == (-1) then omegaToMinus4
      else if not zk && offset == 1 then gen
      else if not zk && offset == (-1) then omegaToMinus1
      else if not zk && offset == (-2) then omegaToMinus2
      else if zk && offset == 0 then omegaToMinus3
      else one

    w0 :: Vector 15 (FVar f)
    w0 = map _.zeta allEvals.witnessEvals

    s0 :: Vector 6 (FVar f)
    s0 = map _.zeta allEvals.sigmaEvals

    zZeta = allEvals.zEvals.zeta
    zOmegaTimesZeta = allEvals.zEvals.omegaTimesZeta

    shifts :: Vector 7 f
    shifts = domainShifts @f params.domainLog2

  -- Precompute alpha^0..alpha^70 (shared between ft_eval0 and perm_scalar)
  alphaPowers <- precomputeAlphaPowers maxAlphaPower alpha

  let
    alphaPow n = unsafePartial $ fromJust $ Array.index alphaPowers n
    a21 = alphaPow 21
    a22 = alphaPow 22
    a23 = alphaPow 23

  -- ft_eval0: term1 - p_eval0 - term2 + boundary - constant_term
  let w6 = w0 !! unsafeFinite 6
  term1Init <- mul_ (add_ w6 gamma) zOmegaTimesZeta >>= \t -> mul_ t a21 >>= \t' -> mul_ t' zkPoly
  let wSigma = zipWith Tuple (Vector.take @6 w0) s0
  term1 <- foldM
    ( \acc (Tuple wi si) -> do
        betaSi <- mul_ beta si
        mul_ (add_ (add_ betaSi wi) gamma) acc
    )
    term1Init
    wSigma

  let term1MinusP = sub_ term1 pEval0

  term2Init <- mul_ a21 zkPoly >>= \t -> mul_ t zZeta
  let wShifts = zipWith Tuple (Vector.take @7 w0) (map (const_ :: f -> FVar f) shifts)
  term2 <- foldM
    ( \acc (Tuple wi si) -> do
        betaZetaSi <- mul_ beta zeta >>= \t -> mul_ t si
        mul_ acc (add_ (add_ gamma betaZetaSi) wi)
    )
    term2Init
    wShifts

  let
    -- OCaml: omega_to_minus_zk_rows = omega_to_zk (circuit var, not constant)
    zetaMinusOmegaZk = sub_ zeta omegaZk
    zetaMinus1 = sub_ zeta (const_ one)

  boundary <- do
    term23 <- mul_ zetaToNMinus1 a23 >>= \t -> mul_ t zetaMinus1
    term22 <- mul_ zetaToNMinus1 a22 >>= \t -> mul_ t zetaMinusOmegaZk
    let oneMinusZ = sub_ (const_ one) zZeta
    nominator <- mul_ (add_ term22 term23) oneMinusZ
    denominator <- mul_ zetaMinusOmegaZk zetaMinus1
    div_ nominator denominator

  let permResult = add_ (sub_ term1MinusP term2) boundary

  let
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
      parseHex
    env = baseEnv { computeZetaToNMinus1 = pure zetaToNMinus1 }

  constantTerm <- evaluateM (runLinearizationPoly params.linearizationPoly) env

  let ftEval0 = sub_ permResult constantTerm

  ---------------------------------------------------------------------------
  -- Steps 11b-c: Combined inner product
  -- OCaml right-to-left for `+`: zetaw combine computed first.
  ---------------------------------------------------------------------------
  let
    evalsZeta = [ zZeta ]
      <> (Array.fromFoldable $ map _.zeta allEvals.indexEvals)
      <> (Array.fromFoldable $ map _.zeta allEvals.witnessEvals)
      <> (Array.fromFoldable $ map _.zeta allEvals.coeffEvals)
      <> (Array.fromFoldable $ map _.zeta allEvals.sigmaEvals)

    evalsZetaw = [ allEvals.zEvals.omegaTimesZeta ]
      <> (Array.fromFoldable $ map _.omegaTimesZeta allEvals.indexEvals)
      <> (Array.fromFoldable $ map _.omegaTimesZeta allEvals.witnessEvals)
      <> (Array.fromFoldable $ map _.omegaTimesZeta allEvals.coeffEvals)
      <> (Array.fromFoldable $ map _.omegaTimesZeta allEvals.sigmaEvals)

    sgEvalsZetaw = Array.fromFoldable $
      Vector.zipWith (\m s -> Tuple m s) mask sgZetaw
    sgEvalsZeta = Array.fromFoldable $
      Vector.zipWith (\m s -> Tuple m s) mask sgZeta

  combineZetaw <- hornerCombine xi $ buildEvalList
    sgEvalsZetaw
    allEvals.publicEvals.omegaTimesZeta
    allEvals.ftEval1
    evalsZetaw

  rTimesZetaw <- mul_ r combineZetaw

  combineZeta <- hornerCombine xi $ buildEvalList
    sgEvalsZeta
    allEvals.publicEvals.zeta
    ftEval0
    evalsZeta

  let actualCip = add_ combineZeta rTimesZetaw
  let expectedCip = ops.unshift deferred.combinedInnerProduct
  cipCorrect <- equals_ expectedCip actualCip

  ---------------------------------------------------------------------------
  -- Step 12: b_correct
  -- Expand 16 bulletproof challenges via endo (reverse order matching
  -- OCaml's right-to-left Vector.map evaluation).
  ---------------------------------------------------------------------------
  expandedRev <- for (Vector.reverse deferred.bulletproofChallenges) \c -> toField @8 c endoVar
  let expandedChallenges = Vector.reverse expandedRev

  bCorrect <- bCorrectCircuit
    { challenges: expandedChallenges
    , zeta
    , zetaOmega: zetaw
    , evalscale: r
    , expectedB: ops.unshift deferred.b
    }

  ---------------------------------------------------------------------------
  -- Step 13: perm_correct
  -- Inline perm scalar using shared alpha powers (a21, zkPoly).
  -- perm = -(z_omega * beta * alpha^21 * zkp * prod(gamma + beta*s_i + w_i))
  ---------------------------------------------------------------------------
  actualPerm <- do
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
  void $ pow_ zeta (Int.pow 2 params.srsLengthLog2)

  plonkOk <- ops.shiftedEqual deferred.plonk.perm actualPerm

  ---------------------------------------------------------------------------
  -- Step 14: Combine all checks
  ---------------------------------------------------------------------------
  finalized <- all_ [ xiCorrect, bCorrect, cipCorrect, plonkOk ]

  let challenges = deferred.bulletproofChallenges

  pure { finalized, xiCorrect, bCorrect, cipCorrect, plonkOk, challenges, expandedChallenges }
