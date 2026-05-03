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
  , DomainMode(..)
  -- * Circuit
  , finalizeOtherProofCircuit
  -- * Helpers (exported for use by Pickles.Step.Main's side-loaded slot dispatch)
  , mkSideLoadedOnesPrefixMask
  -- * Component Circuits (exported for testing)
  , module PlonkChecks
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (unsafeFinite)
import Data.Foldable (foldM)
import Data.Int (pow) as Int
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Semigroup.Foldable as Foldable1
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, zipWith, (!!))
import Data.Vector as Vector
import Pickles.IPA (bCorrectCircuit, bPolyCircuit)
import Pickles.Linearization.Env (AlphaPowersLen, EnvM, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (LinearizationPoly, runLinearizationPoly)
import Pickles.OptSponge as OptSponge
import Pickles.PlonkChecks (absorbAllEvals) as PlonkChecks
import Pickles.PlonkChecks (absorbAllEvals, extractEvalFields)
import Pickles.PlonkChecks.CombinedInnerProduct (buildEvalList, hornerCombine)
import Pickles.PlonkChecks.GateConstraints (buildEvalPoint)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Pseudo as Pseudo
import Pickles.Sponge (absorb, evalSpongeM, initialSpongeCircuit, liftSnarky, squeezeScalarChallenge)
import Pickles.Step.Domain (buildPow2PowsArray, pow2PowSquare)
import Pickles.Verify.Types (BulletproofChallenges, UnfinalizedProof, toPlonkMinimal)
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.CVar (negate_)
import Effect.Exception.Unsafe (unsafeThrow)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, add_, all_, and_, assertAny_, const_, div_, equals_, if_, inv_, label, mul_, not_, pow_, seal, square_, sub_, true_)
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
-- | - `domains`: Per-branch `{ generator, log2 }` over the `nd` possible
-- |   step-domain sizes the prev proof could have. For single-rule
-- |   callers `nd = 1`. Multi-rule (e.g. TwoPhaseChain Self prev)
-- |   passes the deduped Vector of all possible per-branch step domains.
-- |   Mirrors OCaml `domain_for_compiled`'s `unique_domains`.
-- | - `shifts`: kimchi permutation argument shifts. Single Vector
-- |   because OCaml's `Pseudo.Domain.shifts` asserts shifts are
-- |   identical across all unique domains
-- |   (`disabled_not_the_same`).
-- | - `srsLengthLog2`: Log2 of SRS length (e.g. 16)
-- | - `endo`: Endomorphism coefficient for scalar challenge conversion
-- | - `linearizationPoly`: The linearization polynomial for gate constraints
-- |
-- | Reference: step_verifier.ml:823 `finalize_other_proof` parameters,
-- |            pseudo.ml `Pseudo.Domain.to_domain`
-- | Domain-resolution mode for `finalize_other_proof`.
-- |
-- | * `KnownDomainsMode` — compiled-rule path. `params.domains` is the
-- |   compile-time `unique_domains` Vector (typically `Vector 1` for
-- |   single-rule, larger for multi-branch self prevs). Vanishing
-- |   polynomial uses pow2_pows + `Pseudo.mask` (compiled
-- |   `Pseudo.Domain.to_domain.vanishing_polynomial`,
-- |   `pseudo.ml:103-128`).
-- | * `SideLoadedMode` — side-loaded prev. `params.domains` is the
-- |   universe `Vector 17` of all candidate log2s ∈ [0..16]
-- |   (= `Side_loaded_verification_key.max_domains.h`'s log2). FOP
-- |   body builds the runtime ones-prefix mask internally from
-- |   `input.domainLog2Var` (`Utils.ones_vector
-- |   ~first_zero:domainLog2Var`) and uses the iterative
-- |   `if_(mask[i], square, …)` pattern for the vanishing polynomial
-- |   (OCaml `step_verifier.ml:796-810` + `:817-840`). FOP body also
-- |   emits `Boolean.Assert.any` over the one-hot bits to mirror
-- |   `O.of_index`'s constraint (`one_hot_vector.ml:23`).
data DomainMode
  = KnownDomainsMode
  | SideLoadedMode

type FinalizeOtherProofParams :: Int -> Type -> Row Type -> Type
type FinalizeOtherProofParams nd f r =
  { domains :: Vector nd { generator :: FVar f, log2 :: Int }
  , shifts :: Vector 7 (FVar f)
  , srsLengthLog2 :: Int
  , endo :: f -- ^ EndoScalar coefficient (= Wrap_inner_curve.scalar = Vesta.endo_scalar for Step)
  , linearizationPoly :: LinearizationPoly f
  , domainMode :: DomainMode
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
  :: forall d dPred nd ndPred n f f' g t m sf r1 r2
   . Add 1 dPred d
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable nd Int
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
  -> FinalizeOtherProofParams nd f r2
  -> FinalizeOtherProofInput n d (FVar f) sf (BoolVar f)
  -> Snarky (KimchiConstraint f) t m (FinalizeOtherProofOutput d f)
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
    -- in the vanishing polynomial. For nd=1 this equals the only
    -- domain's log2 (no extra Square gates vs single-domain code).
    -- Max log2 across the slot's possible domains. `Vector nd` is
    -- `Foldable1` for nd ≥ 1 (witnessed by the `Add 1 _nd nd`
    -- constraint), so this is total.
    maxLog2 = Foldable1.maximum (map _.log2 params.domains)
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
  -- Step 3: Domain masking and zetaw
  -- OCaml: gen = mask which (Vector.map domains domain_generator)
  --        zetaw = Field.mul gen plonk.zeta
  -- For nd=1: mask = b₀, gen = (b₀:>t) * gen₀_const = Scale (no Generic).
  -- For nd>1: gen = sum (b_i * gen_i_const), each Scale (no Generic), sum is linear.
  -- In both cases gen is non-constant, so `mul_ gen zeta` emits one
  -- R1CS Generic gate.
  ---------------------------------------------------------------------------
  -- OCaml `side_loaded_domain` (`step_verifier.ml:817-840`) computes
  -- the `Utils.ones_vector` mask FIRST (16 equals + 16 `&&`), then
  -- calls `O.of_index` (17 equals + 1 assert_any). PS mirrors that
  -- order: ones-prefix mask first, then the domain-which traversal.
  -- The precomputed mask is threaded down to the vanishing polynomial
  -- via `Maybe (Vector 16 (BoolVar f))` (Just for SideLoadedMode,
  -- Nothing for KnownDomainsMode where the compiled-path
  -- vanishing_polynomial uses pow2_pows + Pseudo.mask instead).
  precomputedOnesPrefix <- case params.domainMode of
    SideLoadedMode -> Just <$> mkSideLoadedOnesPrefixMask domainLog2Var
    KnownDomainsMode -> pure Nothing

  -- OCaml `step_verifier.ml:880-893` does `Vector.map unique_domains
  -- ~f:(equals branch_data.domain_log2)` — Vector.map evaluates
  -- right-to-left, so for domains [9, 14] OCaml emits the `equals 14`
  -- gate (constant 14 in coeffs[4]) BEFORE the `equals 9` gate. PS's
  -- `traverse` is left-to-right, so we mirror OCaml by reversing the
  -- input, traversing, and reversing the output back. Without this,
  -- the resulting CS has the constants swapped relative to OCaml.
  domainWhichesRev <- traverse
    (\d -> equals_ (const_ (fromInt d.log2)) domainLog2Var)
    (Vector.reverse params.domains)
  let domainWhiches = Vector.reverse domainWhichesRev
  -- Side-loaded path mirrors OCaml's `O.of_index` which calls
  -- `Boolean.Assert.any` over its 17 one-hot bits
  -- (`one_hot_vector.ml:23`). Compiled `Pseudo.Domain.to_domain`
  -- doesn't enforce one-hot — caller wiring constrains the
  -- runtime `domainLog2Var` upstream.
  case params.domainMode of
    SideLoadedMode -> assertAny_ (Vector.toUnfoldable domainWhiches)
    KnownDomainsMode -> pure unit
  maskedGen <- Pseudo.mask domainWhiches (map _.generator params.domains)
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

  -- zetaToNMinus1 via multi-domain vanishing polynomial.
  -- Mirrors OCaml `Pseudo.Domain.to_domain.vanishing_polynomial` (`pseudo.ml:118-127`):
  --   pow2_pows[0..maxLog2] = [zeta, zeta^2, ..., zeta^(2^maxLog2)]
  --   masked = mask whichBits (Vector.map domains pow2_pows[d.log2])
  --   result = seal (masked - 1)
  -- For nd=1 emits same gate count as the previous single-domain
  -- `domainVanishingPoly`. For nd>1 emits one extra Generic per
  -- additional domain (mask multiplication).
  zetaToNMinus1 <- label "domain-vanishing-poly" case params.domainMode of
    KnownDomainsMode -> do
      pow2PowsArr <- buildPow2PowsArray zeta maxLog2
      let
        pow2AtLog2 :: Vector nd (FVar f)
        pow2AtLog2 = map
          ( \d -> case Array.index pow2PowsArr d.log2 of
              Just v -> v
              Nothing -> const_ zero -- unreachable: log2 ≤ maxLog2 by construction
          )
          params.domains
      masked <- Pseudo.mask domainWhiches pow2AtLog2
      label "seal_domain_vanishing" $ seal (masked `sub_` const_ one)
    SideLoadedMode -> do
      -- Iterative side-loaded vanishing polynomial. Mirrors OCaml
      -- `step_verifier.ml:796-810` + `:817-840`
      -- (`side_loaded_domain.vanishing_polynomial mask`):
      --   mask = ones_vector ~first_zero:domainLog2Var (length 16)
      --   acc = x ;  for i = 0..15:
      --     acc = if mask[i] then square(acc) else acc
      --   result = seal (acc - 1)
      -- Mask was already computed at FOP entry (matching OCaml's
      -- `Utils.ones_vector` call site INSIDE `side_loaded_domain`,
      -- which runs BEFORE the `O.of_index` traversal). We just
      -- consume the precomputed result here.
      onesPrefix <- case precomputedOnesPrefix of
        Just v -> pure v
        Nothing -> unsafeThrow
          "Pickles.Step.FinalizeOtherProof: SideLoadedMode reached \
          \vanishing-poly without a precomputed ones-prefix mask — \
          \bug in the SideLoadedMode dispatch above."
      acc <- foldM
        ( \accV bit -> do
            sq <- square_ accV
            if_ bit sq accV
        )
        zeta
        onesPrefix
      label "seal_domain_vanishing" $ seal (acc `sub_` const_ one)

  let
    alphaPow n = Vector.index alphaPowers (unsafeFinite @AlphaPowersLen n)
    a21 = alphaPow 21
    a22 = alphaPow 22
    a23 = alphaPow 23

  -- ft_eval0: term1 - p_eval0 - term2 + boundary - constant_term.
  -- OCaml `step_verifier.ml` calls `Plonk_checks.ft_eval0` which is
  -- labelled `ft_eval0 / Field.Checked.mul` (~375 R1CS Generic gates
  -- for the big perm-scalar sum + boundary). PS performs the same
  -- arithmetic; the `ft_eval0_perm` label scopes the big mul chain so
  -- the diff can localize any structural drift from the side-loaded
  -- path in this region.
  permResult <- label "ft_eval0_perm" do
    let w6 = w0 !! unsafeFinite @15 6
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
    let wShifts = zipWith Tuple (Vector.take @7 w0) shifts
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

    pure $ add_ (sub_ term1MinusP term2) boundary

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

    baseEnv :: EnvM f (Snarky (KimchiConstraint f) t m)
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
  cipCorrect <- label "combine" do
    combineZetaw <- hornerCombine xi $ buildEvalList
      { sgEvals: Vector.zipWith Tuple mask sgZetaw
      , publicInput: allEvals.publicEvals.omegaTimesZeta
      , ftEval: allEvals.ftEval1
      , evals: extractEvalFields _.omegaTimesZeta allEvals
      }

    rTimesZetaw <- mul_ r combineZetaw

    combineZeta <- hornerCombine xi $ buildEvalList
      { sgEvals: Vector.zipWith Tuple mask sgZeta
      , publicInput: allEvals.publicEvals.zeta
      , ftEval: ftEval0
      , evals: extractEvalFields _.zeta allEvals
      }

    let actualCip = add_ combineZeta rTimesZetaw
    let expectedCip = ops.unshift deferred.combinedInnerProduct
    equals_ expectedCip actualCip

  ---------------------------------------------------------------------------
  -- Step 12: b_correct
  -- Expand 16 bulletproof challenges via endo (reverse order matching
  -- OCaml's right-to-left Vector.map evaluation).
  ---------------------------------------------------------------------------
  expandedRev <- for (Vector.reverse deferred.bulletproofChallenges) \c -> toField @8 c endoVar
  let expandedChallenges = Vector.reverse expandedRev

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
  :: forall f t m
   . PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => FVar f
  -> Snarky (KimchiConstraint f) t m (Vector 16 (BoolVar f))
mkSideLoadedOnesPrefixMask first_zero = label "ones_prefix_mask" do
  -- Iterate i = 0..15, threading the running `value` and collecting
  -- it after each AND. The collected bits land in left-to-right
  -- order; convert to Vector 16 via `unsafePartial fromJust`
  -- (length is statically 16 by construction).
  let
    step :: { acc :: BoolVar f, masks :: Array (BoolVar f) } -> Int
      -> Snarky (KimchiConstraint f) t m
           { acc :: BoolVar f, masks :: Array (BoolVar f) }
    step st i = do
      eq <- equals_ first_zero (const_ (fromInt i))
      newAcc <- (and_ st.acc) (not_ eq)
      pure { acc: newAcc, masks: st.masks <> [ newAcc ] }
  result <- foldM step { acc: true_, masks: [] } (Array.range 0 15)
  case Vector.toVector result.masks of
    Just v -> pure v
    Nothing -> unsafeThrow
      "Pickles.Step.FinalizeOtherProof.mkSideLoadedOnesPrefixMask: \
      \expected exactly 16 mask bits — bug in helper construction."
