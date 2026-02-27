-- | Circuit JSON comparison tests for FinalizeOtherProof sub-circuits.
-- |
-- | Each sub-circuit matches a specific step of OCaml's
-- | `Step_verifier.finalize_other_proof` (step_verifier.ml:828-1165).
-- | The corresponding OCaml dumps are in dump_circuit_impl.ml.
module Test.Pickles.CircuitJson (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (foldM, foldl, intercalate)
import Data.Int (pow) as Int
import Data.Map as Map
import Data.Maybe (fromJust)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, zipWith, (!!))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Effect.Exception (throw)
import Foreign (MultipleErrors)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Partial.Unsafe (unsafePartial)
import Pickles.IPA as IPA
import Pickles.Linearization.Env (EnvM, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Linearization.FFI as LinFFI
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.OptSponge as OptSponge
import Pickles.PlonkChecks (AllEvals, absorbAllEvals)
import Pickles.PlonkChecks.GateConstraints (buildEvalPoint, parseHex)
import Pickles.PlonkChecks.Permutation (PermutationInput, permScalarCircuit)
import Pickles.Sponge (absorb, evalSpongeM, initialSpongeCircuit, liftSnarky, squeezeScalarChallenge)
import Pickles.Types (StepField)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Backend.Kimchi.CircuitJson (CircuitData, CircuitGateData, circuitToJson, diffCircuits, formatGate, readCircuitJson)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F, FVar, SizedF, Snarky, add_, div_, equals_, if_, mul_, pow_, sub_)
import Snarky.Circuit.Kimchi (Type1(..), fromShiftedType1Circuit, shiftedEqualType1, toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Snarky.Curves.Vesta as Vesta
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- | Constants
-------------------------------------------------------------------------------

-- | Domain log2 for the Step circuit (matches OCaml: Pow_2_roots_of_unity 16)
domainLog2 :: Int
domainLog2 = 16

-- | Domain generator for the step domain
domainGenerator :: StepField
domainGenerator = LinFFI.domainGenerator domainLog2

-- | Endo coefficient for scalar challenge expansion (= Wrap_inner_curve.scalar)
stepEndo :: StepField
stepEndo = let EndoScalar e = endoScalar @Vesta.BaseField @StepField in e

-------------------------------------------------------------------------------
-- | Input parsing helpers
-------------------------------------------------------------------------------

-- | Unsafe array index into a Vector (for compile-time circuit building only)
unsafeIdx :: forall n f. Vector n f -> Int -> f
unsafeIdx v i =
  let
    arr = Vector.toUnfoldable v :: Array f
  in
    unsafePartial $ Array.unsafeIndex arr i

-- | Treat a field variable as a 128-bit scalar challenge (for circuit compilation)
asSizedF128 :: forall f. FVar f -> SizedF 128 (FVar f)
asSizedF128 = unsafeCoerce

-------------------------------------------------------------------------------
-- | Sub-circuit 1: expand_plonk (Steps 2+4)
-- |
-- | Expands scalar challenges alpha, zeta via endo.
-- | Computes zetaw = domain#generator * zeta.
-- |
-- | OCaml reference: step_verifier.ml:867-889
-- |   let scalar = SC.to_field_checked ~endo:Endo.Wrap_inner_curve.scalar in
-- |   let plonk = map_challenges ~f:Fn.id ~scalar plonk in
-- |   let zetaw = Field.mul domain#generator plonk.zeta in
-- |
-- | Input layout (4 fields):
-- |   0: alpha (scalar_challenge inner)
-- |   1: beta (plain field, passed through)
-- |   2: gamma (plain field, passed through)
-- |   3: zeta (scalar_challenge inner)
-------------------------------------------------------------------------------

expandPlonkCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 4 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
expandPlonkCircuit inputs = do
  let
    endoVar = const_ stepEndo
    rawAlpha = asSizedF128 $ unsafeIdx inputs 0
    rawZeta = asSizedF128 $ unsafeIdx inputs 3

  -- Step 2: scalar challenge expansion (only alpha and zeta go through endo)
  _alpha <- toField @8 rawAlpha endoVar
  zeta <- toField @8 rawZeta endoVar

  -- Step 4: zetaw = generator * zeta
  void $ mul_ (const_ domainGenerator) zeta

-------------------------------------------------------------------------------
-- | Sub-circuit 2: challenge_digest (Step 7a)
-- |
-- | Computes challenge digest from prev_challenges using opt_sponge.
-- |
-- | OCaml reference: step_verifier.ml:923-933
-- |   let opt_sponge = Opt_sponge.create sponge_params in
-- |   Vector.iter2 actual_width_mask prev_challenges
-- |     ~f:(fun keep chals ->
-- |       Vector.iter chals ~f:(fun chal ->
-- |         Opt_sponge.absorb opt_sponge (keep, chal))) ;
-- |   Opt_sponge.squeeze opt_sponge
-- |
-- | Input layout (34 fields):
-- |   0-1:   mask (2 booleans)
-- |   2-17:  prev_challenges[0] (16 fields)
-- |   18-33: prev_challenges[1] (16 fields)
-------------------------------------------------------------------------------

challengeDigestStandaloneCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 34 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
challengeDigestStandaloneCircuit inputs = do
  let
    -- Inputs 0-1 are mask booleans (coerce FVar to BoolVar)
    mask :: Vector 2 (BoolVar StepField)
    mask = Vector.generate \j -> coerce $ unsafeIdx inputs (getFinite j)

    -- Inputs 2-33 are prev_challenges (2 proofs × 16 challenges)
    prevChallenges :: Vector 2 (Vector 16 (FVar StepField))
    prevChallenges = Vector.generate \j ->
      Vector.generate \k ->
        unsafeIdx inputs (2 + 16 * getFinite j + getFinite k)

    -- Build pending absorptions: for each proof, for each challenge, (keep, chal)
    pending :: Array (Tuple (BoolVar StepField) (FVar StepField))
    pending = Array.concat $ Vector.toUnfoldable $
      Vector.zipWith
        ( \keep chals ->
            map (Tuple keep) (Vector.toUnfoldable chals :: Array _)
        )
        mask
        prevChallenges

  void $ OptSponge.squeeze (OptSponge.create :: OptSponge.OptSponge StepField) pending

-------------------------------------------------------------------------------
-- | Sub-circuit 3: b_correct (Step 12)
-- |
-- | Expands 16 bulletproof challenges via endo, builds challenge polynomial,
-- | evaluates at zeta and zetaw, checks b = b(zeta) + r * b(zetaw).
-- |
-- | OCaml reference: step_verifier.ml:1126-1141
-- |   let bulletproof_challenges = compute_challenges ~scalar bulletproof_challenges in
-- |   let challenge_poly = unstage (challenge_polynomial (...)) in
-- |   let b_actual = challenge_poly zeta + (r * challenge_poly zetaw) in
-- |   let b_used = Shifted_value.Type1.to_field ~shift:shift1 b in
-- |   equal b_used b_actual
-- |
-- | Input layout (20 fields):
-- |   0-15:  bulletproof_challenges (16 scalar_challenge inners)
-- |   16:    zeta (already expanded)
-- |   17:    zetaw (already expanded)
-- |   18:    r (already expanded)
-- |   19:    claimed_b (Type1 shifted value)
-------------------------------------------------------------------------------

bCorrectStandaloneCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 20 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
bCorrectStandaloneCircuit inputs = do
  let
    endoVar = const_ stepEndo

    -- Parse 16 scalar challenge inners
    rawChallenges :: Vector 16 (SizedF 128 (FVar StepField))
    rawChallenges = Vector.generate \j ->
      asSizedF128 $ unsafeIdx inputs (getFinite j)

    zeta = unsafeIdx inputs 16
    zetaw = unsafeIdx inputs 17
    r = unsafeIdx inputs 18
    claimedB = unsafeIdx inputs 19

  -- OCaml's Vector.map evaluates side effects in reverse order (right-to-left
  -- :: evaluation), so toField constraints for challenge[15] are emitted first.
  -- We reverse before expanding, then reverse back, to match constraint order
  -- while preserving the correct mathematical ordering for bPoly.
  expandedChallengesRev <- for (Vector.reverse rawChallenges) \c -> toField @8 c endoVar
  let expandedChallenges = Vector.reverse expandedChallengesRev

  void $ IPA.bCorrectCircuit
    { challenges: expandedChallenges
    , zeta
    , zetaOmega: zetaw
    , evalscale: r
    , expectedB: fromShiftedType1Circuit (Type1 claimedB)
    }

-------------------------------------------------------------------------------
-- | Sub-circuit 4: plonk_checks_passed (Step 13)
-- |
-- | Verifies that the claimed perm scalar matches the computed value.
-- | This isolates the Plonk_checks.checked / derive_plonk logic.
-- |
-- | OCaml reference: plonk_checks.ml:450-476
-- |   derive_plonk: perm = -(z_omega * beta * alpha^21 * zkp * prod(gamma + beta*s_i + w_i))
-- |   checked: Shifted_value.equal Field.equal (perm plonk) (perm actual)
-- |
-- | Input layout (18 fields):
-- |   0:     alpha (expanded to full field)
-- |   1:     beta
-- |   2:     gamma
-- |   3:     zkPolynomial
-- |   4:     z_omega (z eval at omega*zeta)
-- |   5-10:  sigma[0..5] (sigma evals at zeta)
-- |   11-16: w[0..5] (witness evals at zeta)
-- |   17:    claimed_perm (Shifted_value.Type1 inner)
-------------------------------------------------------------------------------

plonkChecksPassedCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 18 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
plonkChecksPassedCircuit inputs = do
  let
    -- Build PermutationInput from flat array.
    -- permScalarCircuit only uses first 6 w values, z.omegaTimesZeta,
    -- alpha, beta, gamma, sigma, and zkPolynomial.
    -- Other fields get dummy constants (never accessed).
    permInput :: PermutationInput (FVar StepField)
    permInput =
      { w: Vector.generate \j ->
          let
            i = getFinite j
          in
            if i < 6 then unsafeIdx inputs (11 + i) else const_ zero
      , sigma: Vector.generate \j -> unsafeIdx inputs (5 + getFinite j)
      , z: { zeta: const_ zero, omegaTimesZeta: unsafeIdx inputs 4 }
      , shifts: Vector.generate \_ -> const_ zero
      , alpha: unsafeIdx inputs 0
      , beta: unsafeIdx inputs 1
      , gamma: unsafeIdx inputs 2
      , zkPolynomial: unsafeIdx inputs 3
      , zetaToNMinus1: const_ zero
      , omegaToMinusZkRows: const_ zero
      , zeta: const_ zero
      }

  -- Compute actual perm scalar
  actualPerm <- permScalarCircuit permInput

  -- Compare using shiftedEqualType1 (matches OCaml's Shifted_value.equal)
  void $ shiftedEqualType1 (Type1 $ unsafeIdx inputs 17) actualPerm

-------------------------------------------------------------------------------
-- | Sub-circuit 5: ft_eval0 (Step 11a)
-- |
-- | Computes the ft polynomial evaluation at zeta.
-- | This combines permutation terms and gate constraint constant_term,
-- | sharing the same env (alpha powers, zkPoly, etc.) between both.
-- |
-- | OCaml reference: plonk_checks.ml:350-400
-- |   ft_eval0 = term1 - p_eval0 - term2 + (nominator / denominator) - constant_term
-- |
-- | Input layout (91 fields = linearization layout + p_eval0):
-- |   0-29:  w (15 pairs)
-- |   30-59: coefficients (15 pairs)
-- |   60-61: z (pair)
-- |   62-73: s (6 pairs)
-- |   74-85: selectors (6 pairs)
-- |   86:    alpha
-- |   87:    beta
-- |   88:    gamma
-- |   89:    zeta
-- |   90:    p_eval0
-------------------------------------------------------------------------------

-- | Maximum alpha power needed by either permutation or constant_term
maxAlphaPower :: Int
maxAlphaPower = 70

ftEval0StandaloneCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 91 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m (FVar StepField)
ftEval0StandaloneCircuit inputs = do
  let
    at i = inputs !! unsafeFinite i

    -- Parse inputs matching OCaml layout
    alpha = at 86
    beta = at 87
    gamma = at 88
    zeta = at 89
    pEval0 = at 90

    -- Build eval point for constant_term evaluation
    evalPoint = buildEvalPoint
      { witnessEvals: (Vector.generate \j -> { zeta: at (2 * getFinite j), omegaTimesZeta: at (2 * getFinite j + 1) }) :: Vector 15 (PointEval (FVar StepField))
      , coeffEvals: (Vector.generate \j -> at (30 + 2 * getFinite j)) :: Vector 15 (FVar StepField)
      , indexEvals: (Vector.generate \j -> { zeta: at (74 + 2 * getFinite j), omegaTimesZeta: at (74 + 2 * getFinite j + 1) }) :: Vector 6 (PointEval (FVar StepField))
      , defaultVal: const_ zero
      }

    -- Domain constants
    gen = LinFFI.domainGenerator @StepField domainLog2
    omegaToMinus1 = recip gen
    omegaToMinus2 = omegaToMinus1 * omegaToMinus1
    omegaToMinus3 = omegaToMinus1 * omegaToMinus1 * omegaToMinus1
    omegaToMinus4 = omegaToMinus1 * omegaToMinus1 * omegaToMinus1 * omegaToMinus1

    -- omega_to_minus_zk_rows = omega^(-3) for zk_rows=3
    omegaToMinusZkRows = omegaToMinus3

    -- Omega constant for lagrange basis (matches buildCircuitEnvM/linearizationCircuitM)
    omegaForLagrange { zkRows: zk, offset } =
      if not zk && offset == 0 then one
      else if zk && offset == (-1) then omegaToMinus4
      else if not zk && offset == 1 then gen
      else if not zk && offset == (-1) then omegaToMinus1
      else if not zk && offset == (-2) then omegaToMinus2
      else if zk && offset == 0 then omegaToMinus3
      else one

    -- w0 = first column of each witness pair (zeta evaluation)
    w0 :: Vector 15 (FVar StepField)
    w0 = Vector.generate \j -> at (2 * getFinite j)

    -- s0 = first column of each sigma pair (zeta evaluation)
    s0 :: Vector 6 (FVar StepField)
    s0 = Vector.generate \j -> at (62 + 2 * getFinite j)

    -- z evaluations
    zZeta = at 60
    zOmegaTimesZeta = at 61

    -- Domain shifts (7 values)
    shifts :: Vector 7 StepField
    shifts = LinFFI.domainShifts domainLog2

  -- 1. Precompute alpha powers (shared between permutation and constant_term)
  alphaPowers <- precomputeAlphaPowers maxAlphaPower alpha

  let
    alphaPow n = unsafePartial $ fromJust $ Array.index alphaPowers n
    a21 = alphaPow 21
    a22 = alphaPow 22
    a23 = alphaPow 23

  -- 2. Eager zk_polynomial = (zeta - ω⁻¹)(zeta - ω⁻²)(zeta - ω⁻³)
  zkPoly <- do
    t1 <- mul_ (zeta `sub_` const_ omegaToMinus1) (zeta `sub_` const_ omegaToMinus2)
    mul_ t1 (zeta `sub_` const_ omegaToMinus3)

  -- 3. Eager zeta_to_n_minus_1 = zeta^(2^domainLog2) - 1
  -- (This is computed separately from the env's lazy version;
  --  the env will also compute it when evaluating constant_term)
  _eagerZetaToNMinus1 <- do
    zetaToN <- pow_ zeta (Int.pow 2 domainLog2)
    pure (zetaToN `sub_` const_ one)

  -- 4. Term 1: product with sigma evaluations
  -- OCaml: let init = (w_n + gamma) * e1_z * alpha^21 * zkp in
  --        Vector.foldi e0_s ~init ~f:(fun i acc s -> ((beta * s) + w0.(i) + gamma) * acc)
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

  -- 5. term1 - p_eval0
  let term1MinusP = sub_ term1 pEval0

  -- 6. Term 2: product with shifts
  -- OCaml: init = alpha^21 * zkp * e0_z
  --        Array.foldi shifts ~init ~f:(fun i acc s -> acc * (gamma + beta*zeta*s + w0[i]))
  term2Init <- mul_ a21 zkPoly >>= \t -> mul_ t zZeta
  let wShifts = zipWith Tuple (Vector.take @7 w0) (map (const_ :: StepField -> FVar StepField) shifts)
  term2 <- foldM
    ( \acc (Tuple wi si) -> do
        betaZetaSi <- mul_ beta zeta >>= \t -> mul_ t si
        mul_ acc (add_ (add_ gamma betaZetaSi) wi)
    )
    term2Init
    wShifts

  -- 7. Boundary quotient
  let
    zetaMinusOmega = sub_ zeta (const_ omegaToMinusZkRows)
    zetaMinus1 = sub_ zeta (const_ one)

  -- nominator = (zeta1m1 * alpha^22 * (zeta - omega^-3) + zeta1m1 * alpha^23 * (zeta - 1)) * (1 - z(zeta))
  -- OCaml evaluates right side of `+` first (right-to-left), so alpha^23 term is computed before alpha^22 term
  term23 <- mul_ _eagerZetaToNMinus1 a23 >>= \t -> mul_ t zetaMinus1
  term22 <- mul_ _eagerZetaToNMinus1 a22 >>= \t -> mul_ t zetaMinusOmega
  let oneMinusZ = sub_ (const_ one) zZeta
  nominator <- mul_ (add_ term22 term23) oneMinusZ

  -- denominator = (zeta - omega^-3) * (zeta - 1)
  denominator <- mul_ zetaMinusOmega zetaMinus1

  -- boundary = nominator / denominator
  boundary <- div_ nominator denominator

  -- 8. Combine permutation terms: term1 - p_eval0 - term2 + boundary
  let permResult = add_ (sub_ term1MinusP term2) boundary

  -- 9. Compute constant_term using the same env (shared alpha powers)
  let
    vanishesOnZk = const_ one -- joint_combiner is None

    env :: EnvM StepField (Snarky (KimchiConstraint StepField) t m)
    env = buildCircuitEnvM
      alphaPowers
      zeta
      domainLog2
      omegaForLagrange
      evalPoint
      vanishesOnZk
      beta
      gamma
      (const_ one) -- jointCombiner (None → 1)
      parseHex

  constantTerm <- evaluateM PallasTokens.constantTermTokens env

  -- 10. ft_eval0 = permResult - constant_term
  pure $ sub_ permResult constantTerm

-------------------------------------------------------------------------------
-- | Sub-circuit 6: sponge_and_challenges (Steps 7+8)
-- |
-- | Reconstructs the Fiat-Shamir sponge state by absorbing all evaluation
-- | data, then squeezes xi and r challenges and expands them via endo.
-- |
-- | OCaml reference: step_verifier.ml:920-999
-- |   challenge_digest via opt_sponge
-- |   absorb sponge_digest, challenge_digest, ft_eval1, public_input, all evals
-- |   squeeze_challenge twice → xi, r
-- |   scalar xi, scalar r → expand to full field
-- |
-- | Input layout (124 fields):
-- |   0-1:     mask (2 booleans)
-- |   2-17:    prev_challenges[0] (16 fields)
-- |   18-33:   prev_challenges[1] (16 fields)
-- |   34:      sponge_digest_before_evaluations
-- |   35:      ft_eval1
-- |   36-37:   public_input (zeta, zetaw)
-- |   38-67:   w[0..14] pairs = 30 fields
-- |   68-97:   coefficients[0..14] pairs = 30 fields
-- |   98-99:   z pair = 2 fields
-- |   100-111: s[0..5] pairs = 12 fields
-- |   112-123: selectors[0..5] pairs = 12 fields
-------------------------------------------------------------------------------

spongeAndChallengesStandaloneCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 124 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
spongeAndChallengesStandaloneCircuit inputs = do
  let
    endoVar = const_ stepEndo

    -- Inputs 0-1 are mask booleans (coerce FVar to BoolVar)
    mask :: Vector 2 (BoolVar StepField)
    mask = Vector.generate \j -> coerce $ unsafeIdx inputs (getFinite j)

    -- Inputs 2-33 are prev_challenges (2 proofs × 16 challenges)
    prevChallenges :: Vector 2 (Vector 16 (FVar StepField))
    prevChallenges = Vector.generate \j ->
      Vector.generate \k ->
        unsafeIdx inputs (2 + 16 * getFinite j + getFinite k)

    -- Build pending absorptions: for each proof, for each challenge, (keep, chal)
    pending :: Array (Tuple (BoolVar StepField) (FVar StepField))
    pending = Array.concat $ Vector.toUnfoldable $
      Vector.zipWith
        ( \keep chals ->
            map (Tuple keep) (Vector.toUnfoldable chals :: Array _)
        )
        mask
        prevChallenges

    spongeDigest = unsafeIdx inputs 34

    -- Build AllEvals from flat input array
    allEvals :: AllEvals (FVar StepField)
    allEvals =
      { ftEval1: unsafeIdx inputs 35
      , publicEvals:
          { zeta: unsafeIdx inputs 36
          , omegaTimesZeta: unsafeIdx inputs 37
          }
      , zEvals:
          { zeta: unsafeIdx inputs 98
          , omegaTimesZeta: unsafeIdx inputs 99
          }
      , indexEvals: Vector.generate \j ->
          { zeta: unsafeIdx inputs (112 + 2 * getFinite j)
          , omegaTimesZeta: unsafeIdx inputs (112 + 2 * getFinite j + 1)
          }
      , witnessEvals: Vector.generate \j ->
          { zeta: unsafeIdx inputs (38 + 2 * getFinite j)
          , omegaTimesZeta: unsafeIdx inputs (38 + 2 * getFinite j + 1)
          }
      , coeffEvals: Vector.generate \j ->
          { zeta: unsafeIdx inputs (68 + 2 * getFinite j)
          , omegaTimesZeta: unsafeIdx inputs (68 + 2 * getFinite j + 1)
          }
      , sigmaEvals: Vector.generate \j ->
          { zeta: unsafeIdx inputs (100 + 2 * getFinite j)
          , omegaTimesZeta: unsafeIdx inputs (100 + 2 * getFinite j + 1)
          }
      }

  -- 1. Challenge digest via OptSponge
  challengeDigest <- OptSponge.squeeze (OptSponge.create :: OptSponge.OptSponge StepField) pending

  -- 2-8. Main sponge: absorb, squeeze, expand
  evalSpongeM initialSpongeCircuit do
    -- Absorb sponge_digest (pre-initialization)
    absorb spongeDigest
    -- Absorb challenge_digest
    absorb challengeDigest
    -- Absorb ft_eval1, public_input, z, selectors, witness, coeff, sigma
    absorbAllEvals allEvals
    -- Squeeze xi and r (128-bit range-checked via EndoScalar)
    xi <- squeezeScalarChallenge { endo: endoVar }
    r <- squeezeScalarChallenge { endo: endoVar }
    -- Expand xi and r to full field via endo
    liftSnarky do
      void $ toField @8 xi endoVar
      void $ toField @8 r endoVar

-------------------------------------------------------------------------------
-- | Sub-circuit 7: combined_inner_product (Step 11)
-- |
-- | Computes the combined inner product used in bulletproof verification:
-- |   CIP = sum_j xi^j f_j(zeta) + r * sum_j xi^j f_j(zetaw)
-- | where f_j includes sg_evals (challenge polynomial evaluations), public input,
-- | ft_eval, and all polynomial evaluations.
-- |
-- | The Horner scheme: flat list of evaluations is reversed, then fold_left
-- | with mul_and_add: Just fx → fx + xi * acc, Maybe (b, fx) → if b then (fx + xi*acc) else acc.
-- |
-- | OCaml reference: step_verifier.ml:1060-1121
-- |   let combine ~ft ~sg_evals x_hat e = Common.combined_evaluation ~xi v
-- |   combine_zeta + r * combine_zetaw
-- |
-- | Input layout (129 fields):
-- |   0-1:     mask (2 booleans)
-- |   2-17:    prev_challenges[0] (16 fields)
-- |   18-33:   prev_challenges[1] (16 fields)
-- |   34:      zeta
-- |   35:      zetaw
-- |   36:      xi (already expanded to full field)
-- |   37:      r (already expanded to full field)
-- |   38:      ft_eval0 (precomputed from PlonK relation)
-- |   39:      ft_eval1
-- |   40:      public_input at zeta
-- |   41:      public_input at zetaw
-- |   42-84:   evals at zeta (43 fields: z, 6 selectors, 15 w, 15 coeff, 6 s)
-- |   85-127:  evals at zetaw (43 fields: same structure)
-- |   128:     claimed_cip (Type1 shifted value inner)
-------------------------------------------------------------------------------

-- | Evaluation in the Horner fold: either always present (Just) or masked (Maybe).
data EvalOpt f
  = EvalJust (FVar f)
  | EvalMaybe (BoolVar f) (FVar f)

-- | Horner fold matching OCaml's Pcs_batch.combine_split_evaluations.
-- | Takes reversed flat evaluation list, initializes from head, folds with mul_and_add.
hornerCombine
  :: forall f c t m
   . CircuitM f c t m
  => FVar f -> Array (EvalOpt f) -> Snarky c t m (FVar f)
hornerCombine xi evals = do
  let
    reversed = Array.reverse evals
    initVal = unsafePartial $ fromJust $ Array.head reversed
    rest = unsafePartial $ fromJust $ Array.tail reversed
    initResult = case initVal of
      EvalJust x -> x
      EvalMaybe _ _ -> unsafeCoerce unit -- unreachable: init is always Just in our case
  foldM
    ( \acc opt -> case opt of
        EvalJust fx -> do
          xiAcc <- pure xi * pure acc
          pure (add_ fx xiAcc)
        EvalMaybe b fx -> do
          xiAcc <- pure xi * pure acc
          let then_ = add_ fx xiAcc
          if_ b then_ acc
    )
    initResult
    rest

-- | Build the flat evaluation list matching OCaml's combine function.
-- | Order: sg_evals, public_input, ft_eval, z, 6 selectors, 15 w, 15 coeff, 6 s
-- | This matches Evals.In_circuit.to_list order for always-present fields.
buildEvalList
  :: forall f
   . Array (Tuple (BoolVar f) (FVar f)) -- sg_evals [(keep, eval)]
  -> FVar f                              -- public_input
  -> FVar f                              -- ft_eval
  -> Array (FVar f)                      -- always-present evals (43: z, 6 sel, 15 w, 15 coeff, 6 s)
  -> Array (EvalOpt f)
buildEvalList sgEvals pub ft evals =
  map (\(Tuple keep eval) -> EvalMaybe keep eval) sgEvals
    <> [ EvalJust pub, EvalJust ft ]
    <> map EvalJust evals

cipStandaloneCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 129 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
cipStandaloneCircuit inputs = do
  let
    -- Inputs 2-33 are prev_challenges (2 proofs × 16 challenges)
    prevChallenges :: Vector 2 (Vector 16 (FVar StepField))
    prevChallenges = Vector.generate \j ->
      Vector.generate \k ->
        unsafeIdx inputs (2 + 16 * getFinite j + getFinite k)

    zeta = unsafeIdx inputs 34
    zetaw = unsafeIdx inputs 35
    xi = unsafeIdx inputs 36
    r = unsafeIdx inputs 37
    ftEval0 = unsafeIdx inputs 38
    ftEval1 = unsafeIdx inputs 39
    pubZeta = unsafeIdx inputs 40
    pubZetaw = unsafeIdx inputs 41
    claimedCip = unsafeIdx inputs 128

    -- Parse evals at a given base offset.
    -- to_list order: z, gen_sel, pos_sel, comp_add_sel, mul_sel, emul_sel,
    -- endo_scal_sel, w0..w14, coeff0..coeff14, s0..s5
    evalsAt :: Int -> Array (FVar StepField)
    evalsAt base = map (unsafeIdx inputs)
      ( [ base ]                                             -- z
          <> map (\j -> base + 1 + j) (Array.range 0 5)     -- 6 selectors
          <> map (\j -> base + 7 + j) (Array.range 0 14)    -- 15 w
          <> map (\j -> base + 22 + j) (Array.range 0 14)   -- 15 coeff
          <> map (\j -> base + 37 + j) (Array.range 0 5)    -- 6 s
      )

    evalsZeta = evalsAt 42
    evalsZetaw = evalsAt 85

    -- Mask elements
    mask0 :: BoolVar StepField
    mask0 = coerce $ unsafeIdx inputs 0

    mask1 :: BoolVar StepField
    mask1 = coerce $ unsafeIdx inputs 1

    prevChals0 = Vector.index prevChallenges (unsafeFinite 0)
    prevChals1 = Vector.index prevChallenges (unsafeFinite 1)

  -- Compute challenge polynomial evaluations.
  -- OCaml right-to-left Vector.map2: index 1 evaluated before index 0.
  sg1_z <- IPA.bPolyCircuit { challenges: prevChals1, x: zeta }
  sg0_z <- IPA.bPolyCircuit { challenges: prevChals0, x: zeta }
  sg1_w <- IPA.bPolyCircuit { challenges: prevChals1, x: zetaw }
  sg0_w <- IPA.bPolyCircuit { challenges: prevChals0, x: zetaw }

  -- Compute CIP: combine_zeta + r * combine_zetaw.
  -- OCaml right-to-left for infix `+`: zetaw combine computed first.
  combineZetaw <- hornerCombine xi $ buildEvalList
    [ Tuple mask0 sg0_w, Tuple mask1 sg1_w ]
    pubZetaw ftEval1 evalsZetaw

  rTimesZetaw <- pure r * pure combineZetaw

  combineZeta <- hornerCombine xi $ buildEvalList
    [ Tuple mask0 sg0_z, Tuple mask1 sg1_z ]
    pubZeta ftEval0 evalsZeta

  let actualCip = add_ combineZeta rTimesZetaw

  -- Compare with claimed CIP via Type1.to_field then equal
  let expected = fromShiftedType1Circuit (Type1 claimedCip)
  void $ equals_ expected actualCip

-------------------------------------------------------------------------------
-- | Full FinalizeOtherProof wrapper circuit (for reference)
-------------------------------------------------------------------------------

-- finalizeOtherProofWrapperCircuit
--   :: forall t m
--    . CircuitM StepField (KimchiConstraint StepField) t m
--   => Vector 151 (FVar StepField)
--   -> Snarky (KimchiConstraint StepField) t m Unit
-- finalizeOtherProofWrapperCircuit inputs = do
--   let
--     endoVar = const_ stepEndo
--     rawAlpha = asSizedF128 $ unsafeIdx inputs 0
--     rawBeta = asSizedF128 $ unsafeIdx inputs 1
--     rawGamma = asSizedF128 $ unsafeIdx inputs 2
--     rawZeta = asSizedF128 $ unsafeIdx inputs 3
--     claimedPerm = Type1 $ unsafeIdx inputs 6
--     claimedCIP = Type1 $ unsafeIdx inputs 7
--     claimedB = Type1 $ unsafeIdx inputs 8
--     rawXi = asSizedF128 $ unsafeIdx inputs 9
--
--     bulletproofChallenges :: Vector 16 (SizedF 128 (FVar StepField))
--     bulletproofChallenges = Vector.generate \j ->
--       asSizedF128 $ unsafeIdx inputs (10 + getFinite j)
--
--     mask :: Vector 2 (BoolVar StepField)
--     mask = Vector.generate \j -> asBool $ unsafeIdx inputs (26 + getFinite j)
--
--     allEvals = parseAllEvals inputs
--
--     prevChallenges :: Vector 2 (Vector 16 (SizedF 128 (FVar StepField)))
--     prevChallenges = Vector.generate \j ->
--       Vector.generate \k ->
--         asSizedF128 $ unsafeIdx inputs (118 + 16 * getFinite j + getFinite k)
--
--     spongeDigest = unsafeIdx inputs 150
--
--   plonk <- expandPlonkMinimalCircuit endoVar
--     { alpha: rawAlpha, beta: rawBeta, gamma: rawGamma, zeta: rawZeta }
--
--   evalSpongeM initialSpongeCircuit do
--     absorb spongeDigest
--     challengeDigest <- challengeDigestCircuit { mask, oldChallenges: prevChallenges }
--     absorb challengeDigest
--     absorbAllEvals allEvals
--     squeezedXi <- squeezeScalarChallenge
--     xiCorrect <- liftSnarky $ isEqual squeezedXi rawXi
--     rawR <- squeezeScalarChallenge
--     polyscale <- liftSnarky $ toField squeezedXi endoVar
--     evalscale <- liftSnarky $ toField rawR endoVar
--     zetaOmega <- liftSnarky $ mul_ plonk.zeta (const_ domainGenerator)
--
--     let
--       permInput :: PermutationInput (FVar StepField)
--       permInput =
--         { w: map _.zeta (Vector.take @7 allEvals.witnessEvals)
--         , sigma: map _.zeta allEvals.sigmaEvals
--         , z: allEvals.zEvals
--         , shifts: map const_ domainShifts
--         , alpha: plonk.alpha
--         , beta: plonk.beta
--         , gamma: plonk.gamma
--         , zkPolynomial: const_ zero
--         , zetaToNMinus1: const_ zero
--         , omegaToMinusZkRows: const_ zero
--         , zeta: plonk.zeta
--         }
--
--       gateInput :: GateConstraintInput (FVar StepField)
--       gateInput =
--         { witnessEvals: allEvals.witnessEvals
--         , coeffEvals: map _.zeta allEvals.coeffEvals
--         , indexEvals: allEvals.indexEvals
--         , alpha: plonk.alpha
--         , beta: plonk.beta
--         , gamma: plonk.gamma
--         , jointCombiner: const_ zero
--         , vanishesOnZk: const_ zero
--         , lagrangeFalse0: const_ zero
--         , lagrangeTrue1: const_ zero
--         }
--
--     computedCIP <- liftSnarky $
--       combinedInnerProductCheckCircuit Linearization.pallas domainLog2 plonk.zeta
--         { polyscale, evalscale }
--         { permInput
--         , gateInput
--         , publicEvalForFt: const_ zero
--         , publicPointEval: allEvals.publicEvals
--         , ftEval1: allEvals.ftEval1
--         , zEvals: allEvals.zEvals
--         , indexEvals: allEvals.indexEvals
--         , witnessEvals: allEvals.witnessEvals
--         , coeffEvals: allEvals.coeffEvals
--         , sigmaEvals: allEvals.sigmaEvals
--         }
--     cipCorrect <- liftSnarky $
--       equals_ (fromShiftedType1Circuit claimedCIP) computedCIP
--
--     expandedChallenges <- liftSnarky $
--       for bulletproofChallenges \c -> toField c endoVar
--     bOk <- liftSnarky $ IPA.bCorrectCircuit
--       { challenges: expandedChallenges
--       , zeta: plonk.zeta
--       , zetaOmega
--       , evalscale
--       , expectedB: fromShiftedType1Circuit claimedB
--       }
--
--     permOk <- liftSnarky $ plonkArithmeticCheckCircuit { unshift: fromShiftedType1Circuit }
--       { claimedPerm, permInput }
--
--     liftSnarky do
--       a <- and_ xiCorrect cipCorrect
--       b <- and_ bOk permOk
--       void $ and_ a b

-------------------------------------------------------------------------------
-- | Test infrastructure
-------------------------------------------------------------------------------

fixtureDir :: String
fixtureDir = "packages/snarky-kimchi/test/fixtures/"

-- | Count gates by kind
gateTypeSummary :: forall f. Array (CircuitGateData f) -> String
gateTypeSummary gates =
  let
    counts = foldl (\m g -> Map.insertWith (+) (show g.kind) 1 m) Map.empty gates
    lines = map (\(Tuple k v) -> "  " <> k <> ": " <> show v)
      (Map.toUnfoldable counts :: Array (Tuple String Int))
  in
    intercalate "\n" lines

-- | Generic comparison test: compile PS circuit, load OCaml fixture, compare.
compareCircuit
  :: String -- fixture name (without .json)
  -> String -- compiled PS circuit JSON
  -> Either MultipleErrors (CircuitData StepField)
  -> Aff Unit
compareCircuit name psJson ocamlResult = do
  let
    psCircuit :: Either MultipleErrors (CircuitData StepField)
    psCircuit = readCircuitJson psJson
  case ocamlResult, psCircuit of
    Right ocaml, Right ps -> do
      let
        ocamlLen = Array.length ocaml.gates
        psLen = Array.length ps.gates
      log $ name <> " OCaml: pi=" <> show ocaml.publicInputSize <> ", gates=" <> show ocamlLen
      log $ name <> " PS:    pi=" <> show ps.publicInputSize <> ", gates=" <> show psLen
      log $ "OCaml gate types:\n" <> gateTypeSummary ocaml.gates
      log $ "PS gate types:\n" <> gateTypeSummary ps.gates
      ps.publicInputSize `shouldEqual` ocaml.publicInputSize
      -- Check gate count match first — don't silently drop gates
      if ocamlLen /= psLen then
        log $ "Gate count mismatch: OCaml=" <> show ocamlLen <> " PS=" <> show psLen
      else pure unit
      -- Compare gates that exist in both, report first divergence
      let diffs = diffCircuits ocaml ps
      log $ "Differing gate indices: " <> intercalate ", "
        (map (\d -> show d.index <> "(" <> show d.ocaml.kind <> ")") diffs)
      if Array.length diffs > 0 then do
        let
          first = unsafePartial $ Array.unsafeIndex diffs 0
          msg = "First divergence at gate " <> show first.index <> ":\n"
            <> "  OCaml: "
            <> formatGate first.index first.ocaml
            <> "\n"
            <> "  PS:    "
            <> formatGate first.index first.ps
            <> "\n"
            <> "Total differences: "
            <> show (Array.length diffs)
            <> " / "
            <> show (max ocamlLen psLen)
        liftEffect $ throw msg
      else pure unit
      -- If all zipped gates match but lengths differ, that's still a failure
      if ocamlLen /= psLen then
        liftEffect $ throw $ "Gate count mismatch: OCaml=" <> show ocamlLen <> " PS=" <> show psLen
          <> ". All "
          <> show (min ocamlLen psLen)
          <> " shared gates match."
      else pure unit
    Left e, _ -> liftEffect $ throw $ "Failed to parse OCaml JSON: " <> show e
    _, Left e -> liftEffect $ throw $ "Failed to parse PureScript JSON: " <> show e

loadFixture :: String -> Aff (Either MultipleErrors (CircuitData StepField))
loadFixture name = liftEffect do
  buf <- FS.readFile (fixtureDir <> name <> ".json")
  json <- Buffer.toString UTF8 buf
  pure (readCircuitJson json :: Either _ (CircuitData StepField))

-------------------------------------------------------------------------------
-- | Compiled circuits
-------------------------------------------------------------------------------

type V4 = Vector 4 (F StepField)
type V18 = Vector 18 (F StepField)
type V20 = Vector 20 (F StepField)
type V34 = Vector 34 (F StepField)
type V91 = Vector 91 (F StepField)
type V124 = Vector 124 (F StepField)
type V129 = Vector 129 (F StepField)
type V151 = Vector 151 (F StepField)

compileExpandPlonk :: String
compileExpandPlonk = circuitToJson @StepField $
  compilePure (Proxy @V4) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    expandPlonkCircuit
    Kimchi.initialState

compileChallengeDigest :: String
compileChallengeDigest = circuitToJson @StepField $
  compilePure (Proxy @V34) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    challengeDigestStandaloneCircuit
    Kimchi.initialState

compileBCorrect :: String
compileBCorrect = circuitToJson @StepField $
  compilePure (Proxy @V20) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    bCorrectStandaloneCircuit
    Kimchi.initialState

compilePlonkChecksPassed :: String
compilePlonkChecksPassed = circuitToJson @StepField $
  compilePure (Proxy @V18) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    plonkChecksPassedCircuit
    Kimchi.initialState

compileFtEval0 :: String
compileFtEval0 = circuitToJson @StepField $
  compilePure (Proxy @V91) (Proxy @(F StepField)) (Proxy @(KimchiConstraint StepField))
    ftEval0StandaloneCircuit
    Kimchi.initialState

compileSpongeAndChallenges :: String
compileSpongeAndChallenges = circuitToJson @StepField $
  compilePure (Proxy @V124) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    spongeAndChallengesStandaloneCircuit
    Kimchi.initialState

compileCip :: String
compileCip = circuitToJson @StepField $
  compilePure (Proxy @V129) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    cipStandaloneCircuit
    Kimchi.initialState

-- compileFopStep :: String
-- compileFopStep = circuitToJson @StepField $
--   compilePure (Proxy @V151) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
--     finalizeOtherProofWrapperCircuit
--     Kimchi.initialState

-------------------------------------------------------------------------------
-- | Spec
-------------------------------------------------------------------------------

spec :: Spec Unit
spec =
  describe "FinalizeOtherProof CircuitJson" do
    it "Sub-circuit 1: expand_plonk (Steps 2+4)" do
      ocaml <- loadFixture "expand_plonk_circuit"
      compareCircuit "expand_plonk" compileExpandPlonk ocaml

    it "Sub-circuit 2: challenge_digest (Step 7a)" do
      ocaml <- loadFixture "challenge_digest_circuit"
      compareCircuit "challenge_digest" compileChallengeDigest ocaml

    it "Sub-circuit 3: b_correct (Step 12)" do
      ocaml <- loadFixture "b_correct_circuit"
      compareCircuit "b_correct" compileBCorrect ocaml

    it "Sub-circuit 4: plonk_checks_passed (Step 13)" do
      ocaml <- loadFixture "plonk_checks_passed_circuit"
      compareCircuit "plonk_checks_passed" compilePlonkChecksPassed ocaml

    it "Sub-circuit 5: ft_eval0 (Step 11a)" do
      ocaml <- loadFixture "ft_eval0_circuit"
      compareCircuit "ft_eval0" compileFtEval0 ocaml

    it "Sub-circuit 6: sponge_and_challenges (Steps 7+8)" do
      ocaml <- loadFixture "sponge_and_challenges_circuit"
      compareCircuit "sponge_and_challenges" compileSpongeAndChallenges ocaml

    it "Sub-circuit 7: combined_inner_product (Step 11)" do
      ocaml <- loadFixture "cip_circuit"
      compareCircuit "cip" compileCip ocaml

-- it "Full: Step (Tick/Fp) circuit structure comparison" do
--   ocaml <- loadFixture "finalize_other_proof_circuit"
--   compareCircuit "full_fop" compileFopStep ocaml
