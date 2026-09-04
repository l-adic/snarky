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
    Input
  -- * Circuit
  , finalizeOtherProofCircuit
  -- * Helpers (exported for use by Pickles.Step.Main's side-loaded slot dispatch)
  , mkSideLoadedOnesPrefixMask
  ) where

import Prelude

import Data.Fin (Finite, getFinite, unsafeFinite)
import Data.Foldable (foldM)
import Data.Int (pow) as Int
import Data.Reflectable (class Reflectable)
import Data.Semigroup.Foldable as Foldable1
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.FinalizeOtherProof (DomainMode(..), Output, Params)
import Pickles.IPA (bCorrectCircuit, challengePolyEvals, computeChallenges)
import Pickles.Linearization.Env (AlphaPowersLen, EnvM, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI, domainGenerator)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (runLinearizationPoly)
import Pickles.PlonkChecks (extractEvalFields, maskedChallengeDigest, squeezeXiR)
import Pickles.PlonkChecks.CombinedInnerProduct (buildEvalList, combinedInnerProduct)
import Pickles.PlonkChecks.Domain (knownDomainVanishingPolynomial, knownDomainWhiches, omegaPowers, zkPolynomial)
import Pickles.PlonkChecks.GateConstraints (buildEvalPoint)
import Pickles.PlonkChecks.Permutation as Permutation
import Pickles.ProofWitness (ProofWitness)
import Pickles.Pseudo as Pseudo
import Pickles.Util.Pow2 (pow2PowSquare)
import Pickles.Verify.Types (UnfinalizedProof, toPlonkMinimal)
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (BoolVar, FVar, Snarky, all_, and_, assertAny_, const_, equals_, if_, label, mul_, not_, pow_, square_, sub_, true_)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (toField)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField, fromInt)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Side-loaded domain universe size: 17 covers log2s [0..16] (= the
-- | `max_domains.h` upper bound from
-- | `Side_loaded_verification_key`).
type SideLoadedDomainCount = 17

-- | Maximum log2 in the side-loaded universe (= 16).
sideLoadedDomainLog2Max :: Int
sideLoadedDomainLog2Max = 16

-- | The side-loaded candidate log2s `[0..16]` (OCaml `side_loaded_domain`'s
-- | `Vector.init (S max_n) ~f:Fn.id`, `step_verifier.ml:817-840`).
sideLoadedLog2s :: Vector SideLoadedDomainCount Int
sideLoadedLog2s = Vector.generate getFinite

-- | The generator of each side-loaded candidate domain, as constants.
sideLoadedGenerators :: forall f. LinearizationFFI f => Vector SideLoadedDomainCount (FVar f)
sideLoadedGenerators = map (const_ <<< domainGenerator) sideLoadedLog2s

-- | The domain-mode dispatch, resolved once: what `maskedGen` and the
-- | vanishing polynomial each select on. `KnownDomainsMode` carries the
-- | which bit of each compile-time domain; `SideLoadedMode` carries the
-- | ones-prefix mask (`Utils.ones_vector`) for the iterative vanishing
-- | polynomial and the one-hot which bits over the `[0..16]` universe
-- | (`O.of_index`), in OCaml's emission order.
data DomainSel nd f
  = Known (Vector nd (BoolVar f))
  | SideLoaded
      { onesPrefix :: Vector 16 (BoolVar f)
      , whiches :: Vector SideLoadedDomainCount (BoolVar f)
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
type Input n d f sf b =
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

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

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
-- | 6. **Omega powers in-circuit**: `omegaPowers` from the non-constant
-- |    maskedGen, generic in the prev proof's `zkRows`
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
  :: forall d dPred nd ndPred n f f' r sf r1 r2
   . Add 1 dPred d
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable nd Int
  => PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => LinearizationFFI f
  => Reflectable d Int
  => { unshift :: sf -> FVar f
     , shiftedEqual :: sf -> FVar f -> Snarky f (KimchiConstraint f) r (BoolVar f)
     | r1
     }
  -> Params nd f r2
  -> Input n d (FVar f) sf (BoolVar f)
  -> Snarky f (KimchiConstraint f) r (Output d f)
finalizeOtherProofCircuit ops params { unfinalized, witness, mask, prevChallenges, domainLog2Var } = label "finalize-other-proof" do
  -- Multi-domain compile-time dispatch via Pseudo (mirrors OCaml
  -- `Pseudo.Domain.to_domain`, `pseudo.ml:103-128`). For nd=1
  -- callers (single-rule), the Vector 1 of mask bits + values
  -- collapses to identical gate emission as the pre-multi-domain
  -- single-domain path.
  --
  -- For nd>1 (multi-rule callers, e.g. TwoPhaseChain b1's Self
  -- prev), each per-branch domain contributes one extra
  -- `Field.equal` (mask construction) and one extra `Field.mul` in
  -- the vanishing-poly mask, matching OCaml's per-branch
  -- `Pseudo.mask` constraint emission.
  let
    -- Maximum log2 across all possible domains, used to size pow2_pows
    -- in the vanishing polynomial. For KnownDomainsMode this is the
    -- maximum across `params.domains` (Vector nd is `Foldable1` for
    -- nd ≥ 1 via the `Add 1 _nd nd` constraint, so this is total).
    -- For SideLoadedMode the universe is fixed at [0..16] per
    -- `Side_loaded_verification_key.max_domains.h`, so `maxLog2 = 16`
    -- regardless of `params.domains` — mirrors OCaml
    -- `step_verifier.ml:840` `domain ~max:(Domain.log2_size max_domains.h)`.
    maxLog2 = case params.domainMode of
      KnownDomainsMode -> Foldable1.maximum (map _.log2 params.domains)
      SideLoadedMode -> sideLoadedDomainLog2Max
    -- For non-FOP-domain code paths (`buildCircuitEnvM`) that need
    -- a single Int domain log2 — use maxLog2 (matches OCaml's
    -- `domain#log2_size` which returns the max log2 for compiled
    -- circuits via `Pseudo.Domain.to_domain`'s `max_log2`).
    domainLog2 = maxLog2
    -- shifts are constant across all unique_domains (OCaml's
    -- `Pseudo.Domain.shifts` `disabled_not_the_same` assertion)
    domain = { shifts: params.shifts }
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
  -- Step 3: Domain selection, masking and zetaw
  -- OCaml: gen = mask which (Vector.map domains domain_generator)
  --        zetaw = Field.mul gen plonk.zeta
  -- For nd=1: mask = b₀, gen = (b₀:>t) * gen₀_const = Scale (no Generic).
  -- For nd>1: gen = sum (b_i * gen_i_const), each Scale (no Generic), sum is linear.
  -- In both cases gen is non-constant, so `mul_ gen zeta` emits one
  -- R1CS Generic gate.
  ---------------------------------------------------------------------------
  domainSel <- case params.domainMode of
    -- `knownDomainWhiches` is OCaml `step_verifier.ml:880-893`'s
    -- `Vector.map unique_domains ~f:(equals branch_data.domain_log2)`,
    -- emitted right-to-left as OCaml does (for domains [9, 14] the
    -- `equals 14` gate precedes `equals 9`).
    KnownDomainsMode -> Known <$> knownDomainWhiches domainLog2Var params.domains
    -- OCaml `side_loaded_domain` (`step_verifier.ml:817-840`) computes
    -- the `Utils.ones_vector` mask FIRST (16 equals + 16 `&&`), then
    -- `O.of_index` over the `[0..16]` universe: 17 `equals_` gates over
    -- [16, 15, …, 0] plus a `Boolean.Assert.any` (the one-hot constraint
    -- at `one_hot_vector.ml:23`). No compile-time domain data enters.
    SideLoadedMode -> do
      onesPrefix <- mkSideLoadedOnesPrefixMask domainLog2Var
      whiches <- knownDomainWhiches domainLog2Var (map { log2: _ } sideLoadedLog2s)
      assertAny_ (Vector.toUnfoldable whiches)
      pure (SideLoaded { onesPrefix, whiches })

  maskedGen <- case domainSel of
    Known whiches -> Pseudo.mask whiches (map _.generator params.domains)
    SideLoaded { whiches } -> Pseudo.mask whiches sideLoadedGenerators
  zetaw <- mul_ maskedGen zeta

  ---------------------------------------------------------------------------
  -- Step 4: Compute challenge polynomial evaluations (sg_evals)
  -- OCaml right-to-left Vector.map2: index (n-1) evaluated before index 0.
  -- Within each, zetaw evaluated before zeta (right-to-left pair construction).
  ---------------------------------------------------------------------------
  sgZetaw <- challengePolyEvals prevChallenges zetaw
  sgZeta <- challengePolyEvals prevChallenges zeta

  ---------------------------------------------------------------------------
  -- Steps 5-8: Sponge operations
  -- challenge_digest via OptSponge, absorb sponge_digest + challenge_digest +
  -- all evaluations, squeeze xi and r.
  ---------------------------------------------------------------------------
  { xi: xiActual, r: rActual } <- squeezeXiR
    { spongeDigestBeforeEvaluations: unfinalized.spongeDigestBeforeEvaluations
    , challengeDigest: maskedChallengeDigest mask prevChallenges
    , allEvals
    , endo: endoVar
    , xiConstrainLowBits: true
    }
  xiCorrect <- equals_ (SizedF.toField xiActual) (SizedF.toField deferred.xi)
  xi <- toField @8 deferred.xi endoVar
  r <- toField @8 rActual endoVar

  ---------------------------------------------------------------------------
  -- Step 9: pow2_pows via Field.square
  -- OCaml computes pow2_pows eagerly for zeta and zetaw (generates Square
  -- constraints even though the values may not all be used directly).
  -- Uses srsLengthLog2 (= Common.Max_degree.step_log2 = StepIPARounds = 16),
  -- not domainLog2: matches OCaml `let n = Int.ceil_log2 Max_degree.step in
  -- pow2_pow plonk.zeta n` in step_verifier.ml.
  -- TODO -- even if this is a no-op, void is not the right answer here
  ---------------------------------------------------------------------------
  void $ pow2PowSquare zeta params.srsLengthLog2
  void $ pow2PowSquare zetaw params.srsLengthLog2

  ---------------------------------------------------------------------------
  -- Steps 10+11a: PlonK env + ft_eval0
  -- Inlined permutation contribution + boundary quotient + constant_term.
  -- Uses shared alpha powers between ft_eval0 and perm_scalar.
  --
  -- OCaml constraint order: precomputeAlphaPowers first, then omega powers
  -- in-circuit, then zkPoly, then zetaToNMinus1, then the actual terms.
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

    shifts = domain.shifts

  -- Precompute alpha^0..alpha^70 (shared between ft_eval0 and perm_scalar)
  -- Must come before omega powers to match OCaml constraint order.
  alphaPowers <- precomputeAlphaPowers alpha

  ---------------------------------------------------------------------------
  -- Step 10: Omega powers in-circuit
  -- OCaml computes omega powers from maskedGen (non-constant), so each
  -- produces R1CS constraints (`omegaPowers`, generic in `zkRows`), then
  -- the permutation vanishing polynomial at zeta.
  ---------------------------------------------------------------------------
  omegas@{ omegaToMinus1: omegaM1, omegaToZkPlus1: omegaZkP1, omegaToZk: omegaZk } <-
    omegaPowers { generator: maskedGen, zkRows: params.zkRows }
  zkPoly <- zkPolynomial zeta omegas

  -- zetaToNMinus1 via multi-domain vanishing polynomial.
  -- Mirrors OCaml `Pseudo.Domain.to_domain.vanishing_polynomial` (`pseudo.ml:118-127`):
  --   pow2_pows[0..maxLog2] = [zeta, zeta^2, ..., zeta^(2^maxLog2)]
  --   masked = mask whichBits (Vector.map domains pow2_pows[d.log2])
  --   result = seal (masked - 1)
  -- For nd=1 emits same gate count as the previous single-domain
  -- `domainVanishingPoly`. For nd>1 emits one extra Generic per
  -- additional domain (mask multiplication).
  zetaToNMinus1 <- label "domain-vanishing-poly" case domainSel of
    Known whiches -> knownDomainVanishingPolynomial whiches params.domains zeta
    SideLoaded { onesPrefix } -> do
      -- Iterative side-loaded vanishing polynomial. Mirrors OCaml
      -- `step_verifier.ml:796-810` (`vanishing_polynomial mask`):
      --   mask = ones_vector ~first_zero:domainLog2Var (length 16)
      --   acc = x ;  for i = 0..15:
      --     acc = if mask[i] then square(acc) else acc
      --   result = Field.sub (go x 0) Field.one      -- NO seal
      -- The OCaml side-loaded path returns the result UNSEALED (just a
      -- Cvar Add of `acc - 1`); the seal happens via downstream `mul_`s
      -- materializing as needed. Matching this saves one Generic gate
      -- and keeps the Generic-pair queue parity in sync with OCaml at
      -- the start of `ft_eval0`.
      acc <- foldM
        ( \accV bit -> do
            sq <- square_ accV
            if_ bit sq accV
        )
        zeta
        onesPrefix
      pure (acc `sub_` const_ one)

  let
    alphaPow n = Vector.index alphaPowers (unsafeFinite @AlphaPowersLen n)
    a21 = alphaPow 21
    a22 = alphaPow 22
    a23 = alphaPow 23

  -- ft_eval0: term1 - p_eval0 - term2 + boundary - constant_term.
  -- OCaml `step_verifier.ml` calls `Plonk_checks.ft_eval0` which is
  -- labelled `ft_eval0 / Field.Checked.mul` (~375 R1CS Generic gates
  -- for the big perm-scalar sum + boundary). The permutation half is
  -- `Permutation.permContributionCircuit`, shared with the wrap verifier.
  -- OCaml: omega_to_minus_zk_rows = omega_to_zk (circuit var, not constant).
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

  let
    omegaForLagrange { zkRows: zk, offset } =
      if not zk && offset == 0 then const_ one
      else if not zk && offset == 1 then maskedGen
      else if not zk && offset == (-1) then omegaM1
      else if not zk && offset == (-2) then omegaZkP1
      else if not zk && offset == (-3) then omegaZk
      else if zk && offset == 0 then omegaZk
      -- (true, -1) is lazy in OCaml; not used by constant_term tokens
      else const_ one

    vanishesOnZk = const_ one

    baseEnv :: EnvM f (Snarky f (KimchiConstraint f) r)
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

  -- OCaml `Plonk_checks.scalars_env` evaluation labelled
  -- `scalars_env / Field.Checked.mul / if_ / div`. PS routes the
  -- linearization poly through `evaluateM` which performs the same
  -- arithmetic + lookups; wrap in `scalars_env` so the diff can
  -- localize.
  constantTerm <- label "scalars_env" $
    evaluateM (runLinearizationPoly params.linearizationPoly) env

  let ftEval0 = sub_ permResult constantTerm

  ---------------------------------------------------------------------------
  -- Steps 11b-c: Combined inner product
  -- OCaml right-to-left for `+`: zetaw combine computed first.
  -- OCaml labels: `combine / Field.Checked.mul`. PS wraps the two
  -- horner-fold evaluations in `combine` so per-label totals align.
  ---------------------------------------------------------------------------
  actualCip <- combinedInnerProduct
    { xi
    , r
    , evalsZeta: buildEvalList
        { sgEvals: Vector.zipWith Tuple mask sgZeta
        , publicInput: allEvals.publicEvals.zeta
        , ftEval: ftEval0
        , evals: extractEvalFields _.zeta allEvals
        }
    , evalsZetaw: buildEvalList
        { sgEvals: Vector.zipWith Tuple mask sgZetaw
        , publicInput: allEvals.publicEvals.omegaTimesZeta
        , ftEval: allEvals.ftEval1
        , evals: extractEvalFields _.omegaTimesZeta allEvals
        }
    }
  let expectedCip = ops.unshift deferred.combinedInnerProduct
  cipCorrect <- equals_ expectedCip actualCip

  ---------------------------------------------------------------------------
  -- Step 12: b_correct
  -- Expand 16 bulletproof challenges via endo (reverse order matching
  -- OCaml's right-to-left Vector.map evaluation).
  ---------------------------------------------------------------------------
  expandedChallenges <- computeChallenges deferred.bulletproofChallenges endoVar

  -- OCaml labels: `b_correct / Field.Checked.mul` — wrap the
  -- bCorrectCircuit body so the per-label diff aligns with OCaml.
  bCorrect <- label "b_correct" $ bCorrectCircuit
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
  actualPerm <- label "perm_actual" $ Permutation.permScalarCircuit
    { w: Vector.take @6 w0
    , sigma: s0
    , zOmega: zOmegaTimesZeta
    , beta
    , gamma
    , zkPolynomial: zkPoly
    , alphaPow21: a21
    }

  -- zeta_to_srs_length computation (generates constraints even though result is voided)
  label "perm_pow_zeta_srs" $ void $ pow_ zeta (Int.pow 2 params.srsLengthLog2)

  plonkOk <- label "perm_shifted_equal"
    $ ops.shiftedEqual deferred.plonk.perm actualPerm

  ---------------------------------------------------------------------------
  -- Step 14: Combine all checks
  ---------------------------------------------------------------------------
  finalized <- all_ [ xiCorrect, bCorrect, cipCorrect, plonkOk ]

  let challenges = deferred.bulletproofChallenges

  pure { finalized, xiCorrect, bCorrect, cipCorrect, plonkOk, challenges, expandedChallenges }

-------------------------------------------------------------------------------
-- | Side-loaded helpers
-------------------------------------------------------------------------------

-- | Build the runtime ones-prefix mask for side-loaded vanishing
-- | polynomial. Mirrors OCaml `util.ml:51-66`'s
-- | `Utils.ones_vector ~first_zero:domainLog2Var (length 16)`:
-- |
-- |   value := true
-- |   for i = 0..15:
-- |     value := value && not (Field.equal first_zero (Field.of_int i))
-- |     emit value
-- |
-- | Result: a length-16 vector of `BoolVar` where bit `i` is true iff
-- | `first_zero > i` (i.e. positions strictly below the runtime
-- | `domainLog2Var`). Each iteration emits one `equals_` and one
-- | `and_` constraint ⇒ 32 R1CS gates total.
-- |
-- | Used by `finalizeOtherProofCircuit`'s `SideLoadedMode` branch
-- | for the iterative `if_(mask[i], square, …)` vanishing polynomial
-- | (`step_verifier.ml:796-810`).
mkSideLoadedOnesPrefixMask
  :: forall f r
   . PrimeField f
  => FVar f
  -> Snarky f (KimchiConstraint f) r (Vector 16 (BoolVar f))
mkSideLoadedOnesPrefixMask first_zero = label "ones_prefix_mask" do
  -- Iterate i = 0..15 threading the running AND as a `mapAccumM`
  -- accumulator: each step computes `newAcc = prev ∧ (first_zero ≠ i)`
  -- and emits it as the visited value, collecting the per-index values
  -- into the result `Vector 16`.
  let
    indices :: Vector 16 (Finite 16)
    indices = Vector.generate identity
  map fst $ mapAccumM
    ( \prev fi -> do
        let i = getFinite fi
        eq <- equals_ first_zero (const_ (fromInt i))
        newAcc <- (and_ prev) (not_ eq)
        pure (Tuple newAcc newAcc)
    )
    true_
    indices
