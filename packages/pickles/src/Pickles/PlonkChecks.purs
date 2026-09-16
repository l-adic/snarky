-- | The scalar side of the kimchi verifier, as pickles defers it.
-- |
-- | This is the PureScript counterpart of OCaml
-- | `mina/src/lib/crypto/pickles/plonk_checks/plonk_checks.ml`, and it keeps
-- | that file's shape: the evaluation records, chunk recombination
-- | (`actual_evaluation` / `evals_of_split_evals`), the domain scalars of
-- | `scalars_env`, the gate-constraint environment the linearization
-- | interpreter reads, the permutation argument (`perm_scalar`, the
-- | permutation half of `ft_eval0`), the combined inner product
-- | (`Pcs_batch.combine_split_evaluations`), and the fr-sponge schedule that
-- | derives `xi` and `r`.
-- |
-- | Both `finalize_other_proof`s are built out of these pieces:
-- | `Pickles.Step.FinalizeOtherProof` (step_verifier.ml) and
-- | `Pickles.Wrap.FinalizeOtherProof` (wrap_verifier.ml). The pure reference
-- | prover (`Pickles.Prove.Pure.*`) and the out-of-circuit verifier
-- | (`Pickles.Verify`) consume the same records.
module Pickles.PlonkChecks
  ( -- * Evaluation records
    --
    -- `AllEvalsRow` is here only because `AllEvals` is defined over it and
    -- PureScript requires a synonym's referents to be exported alongside it.
    -- Nothing outside names the row; the type to write is `AllEvals`.
    AllEvals
  , AllEvalsRow
  , ChunkedAllEvals
  , extractEvalFields
  , absorbAllEvals
  -- * Chunk recombination
  , collapsePointEval
  , collapseChunkedAllEvals
  -- * Domain scalars
  , omegaPowers
  , zkPolynomial
  , knownDomainWhiches
  , knownDomainVanishingPolynomial
  -- * The gate-constraint environment
  , buildEvalPoint
  , buildChallenges
  -- * The permutation argument
  , permScalar
  , permContribution
  , permContributionCircuit
  , permScalarCircuit
  -- * The combined inner product
  -- |
  -- | `EvalOpt` is abstract: `buildEvalList`/`buildEvalListUnmasked` produce
  -- | the list and `combinedInnerProduct` consumes it, so the constructors
  -- | stay in here.
  , EvalOpt
  , buildEvalList
  , buildEvalListUnmasked
  , combinedInnerProduct
  -- * The fr-sponge schedule
  , challengeDigest
  , maskedChallengeDigest
  , squeezeXiR
  , FrSpongeInput
  , frSpongeChallengesPure
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Fin (Finite, unsafeFinite)
import Data.Foldable (foldM, foldl, foldr, traverse_)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, zipWith, (!!), (:<))
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Unsafe (unsafePerformEffect)
import JS.BigInt as BigInt
import Pickles.Constants (zkRowsByDefault)
import Pickles.Linearization.Env (EvalPoint)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Linearization.Types (CurrOrNext(..), GateType(..))
import Pickles.OptSponge as OptSponge
import Pickles.Pseudo as Pseudo
import Pickles.Sponge (class MonadSponge, PureSpongeM, absorb, evalPureSpongeM, evalSpongeM, initialSponge, initialSpongeCircuit, liftSnarky, squeeze, squeezeScalar', squeezeScalarChallenge, squeezeScalarChallengePure)
import Pickles.Trace as Trace
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Snarky.Circuit.CVar (negate_)
import Snarky.Circuit.DSL (class BasicSystem, BoolVar, FVar, SizedF, Snarky, add_, coerceViaBits, const_, div_, equals_, if_, inv_, label, mul_, seal, square_, sub_)
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromInt, pow)

-------------------------------------------------------------------------------
-- | Evaluation records
-------------------------------------------------------------------------------

-- | All polynomial evaluations at zeta and zeta*omega.
-- |
-- | These are the witness values needed for PLONK verification.
-- | The sizes match Kimchi's configuration:
-- | - ft polynomial (only at zeta*omega, ftEval0 is computed)
-- | - 6 selector (index) polynomials
-- | - 15 witness columns
-- | - 15 coefficient columns
-- | - 6 sigma polynomials (PERMUTS - 1)
-- |
-- | Each `PointEval` here is the COLLAPSED (single-chunk) form produced by
-- | `collapsePointEval` — chunks recombined via Horner at `pt^(2^rounds)`.
-- | Used by ftEval0, derivePlonk, and any other code path that consumes a
-- | polynomial's value at zeta / zetaw.
-- |
-- | For the COMBINED INNER PRODUCT specifically, the original CHUNKED
-- | evals must be xi-batched (`Pcs_batch.combine_split_evaluations`);
-- | see `ChunkedAllEvals` below.
-- |
-- | Reference: Plonk_types.All_evals in composition_types.ml
type AllEvals f = Record (AllEvalsRow f ())

-- | `AllEvals` as an open row, so a record that carries the evaluations
-- | alongside other fields (`FrSpongeInput`) states the containment instead
-- | of repeating the seven fields.
type AllEvalsRow :: Type -> Row Type -> Row Type
type AllEvalsRow f r =
  ( ftEval1 :: f -- ft polynomial eval at zeta*omega (ftEval0 is computed)
  , publicEvals :: PointEval f
  , zEvals :: PointEval f
  , indexEvals :: Vector 6 (PointEval f)
  , witnessEvals :: Vector 15 (PointEval f)
  , coeffEvals :: Vector 15 (PointEval f)
  , sigmaEvals :: Vector 6 (PointEval f)
  | r
  )

-- | The CHUNKED form of `AllEvals`: each polynomial's evaluation at zeta
-- | / zeta·omega is a `NonEmptyArray (PointEval f)` with one entry per
-- | chunk. For an inner proof at num_chunks=1 each array has length 1
-- | (and the chunked combine collapses to the same result as the legacy
-- | single-eval one); for chunks2 (step num_chunks=2) each polynomial
-- | contributes 2 chunks.
-- |
-- | OCaml stores these as `(f array * f array)` per polynomial inside
-- | `Plonk_types.Evals.t` (`wrap.ml:25-26`). The xi-batching
-- | `Pcs_batch.combine_split_evaluations` flattens the chunk arrays and
-- | folds right-to-left with `acc' = chunk + xi * acc`.
type ChunkedAllEvals f =
  { ftEval1 :: f
  , publicEvals :: NonEmptyArray (PointEval f)
  , zEvals :: NonEmptyArray (PointEval f)
  , indexEvals :: Vector 6 (NonEmptyArray (PointEval f))
  , witnessEvals :: Vector 15 (NonEmptyArray (PointEval f))
  , coeffEvals :: Vector 15 (NonEmptyArray (PointEval f))
  , sigmaEvals :: Vector 6 (NonEmptyArray (PointEval f))
  }

-- | Extract the 43 always-present evaluation fields in CIP order:
-- | z(1), index(6), witness(15), coeff(15), sigma(6).
extractEvalFields :: forall f. (PointEval f -> f) -> AllEvals f -> Vector 43 f
extractEvalFields proj evals =
  proj evals.zEvals :<
    map proj evals.indexEvals
      `Vector.append` map proj evals.witnessEvals
      `Vector.append` map proj evals.coeffEvals
      `Vector.append` map proj evals.sigmaEvals

-- | Absorb all polynomial evaluations into the sponge.
-- |
-- | Follows Kimchi's absorption order:
-- | ftEval1, public, z, index (6), witness (15), coeff (15), sigma (6)
absorbAllEvals
  :: forall f m
   . MonadSponge f m
  => AllEvals f
  -> m Unit
absorbAllEvals evals = do
  absorb evals.ftEval1
  absorbPointEval evals.publicEvals
  absorbPointEval evals.zEvals
  traverse_ absorbPointEval evals.indexEvals
  traverse_ absorbPointEval evals.witnessEvals
  traverse_ absorbPointEval evals.coeffEvals
  traverse_ absorbPointEval evals.sigmaEvals

-- | Absorb a `PointEval`: zeta then zeta*omega.
absorbPointEval
  :: forall f m
   . MonadSponge f m
  => PointEval f
  -> m Unit
absorbPointEval pe = do
  absorb pe.zeta
  absorb pe.omegaTimesZeta

-------------------------------------------------------------------------------
-- | Chunk recombination
-------------------------------------------------------------------------------
--
-- When a polynomial doesn't fit in a single SRS-sized slice, the prover
-- commits to chunks `e[0], e[1], ..., e[n-1]` representing
--   P(x) = e[0] + e[1] * x^N + e[2] * x^(2N) + ... + e[n-1] * x^((n-1)*N)
-- where `N = 2^rounds` is the SRS-poly size. These recombine the chunks at
-- evaluation point `pt` into the single scalar `P(pt)` via Horner's method
-- (`plonk_checks.ml:90-100`, `actual_evaluation`).
--
-- Validation strategy: no in-isolation golden tests. Correctness is
-- exercised end-to-end via Checkpoint 4's chunks2 witness-byte-equality
-- (any error in this Horner combine cascades to combined_inner_product
-- divergence at the byte level vs OCaml). See `docs/chunking.md` and
-- `docs/chunking-ffi-audit.md`.

-- | Horner combine for `n` chunked evaluations at point `pt^(2^rounds)`.
-- |
-- | Returns `e[0] + ptN * (e[1] + ptN * (... + ptN * e[n-1]))`
-- | where `ptN = pt^(2^rounds)`. Algebraically:
-- |   Σ_{i=0..n-1} e[i] * ptN^i
-- |
-- | At `n=1` returns `e[0]` unchanged (identity).
-- |
-- | The implementation mirrors the OCaml 6-liner exactly:
-- |   1. Compute `ptN` via `rounds` rounds of squaring `pt`.
-- |   2. Reverse the input array.
-- |   3. Fold from the new head with accumulator update `acc' = fx + ptN * acc`.
actualEvaluationArr
  :: forall f
   . Semiring f
  => Array f
  -> f
  -> Int
  -> f
actualEvaluationArr xs pt rounds =
  let
    ptN = squareN rounds pt
    xsRev = Array.reverse xs
  in
    case Array.uncons xsRev of
      Just { head, tail } -> foldl (\acc fx -> fx + ptN * acc) head tail
      Nothing -> zero

-- | `squareN n x = x^(2^n)`. n=0 → x, n=1 → x*x, n=2 → (x*x)^2 = x^4, etc.
squareN :: forall f. Semiring f => Int -> f -> f
squareN n x = go n x
  where
  go 0 acc = acc
  go i acc = go (i - 1) (acc * acc)

-- | Collapse a chunked PointEval (one {zeta, omegaTimesZeta} per chunk)
-- | into a scalar PointEval by Horner-combining each component at its
-- | respective evaluation point.
-- |
-- | At `num_chunks = 1` returns the only chunk's value verbatim
-- | (Horner-of-1 = identity). At `n > 1` produces the polynomial's
-- | combined evaluation `Σ_{i=0..n-1} chunk[i] * pt^(2^rounds * i)`.
-- |
-- | This is the host-side analog of OCaml's `evals_of_split_evals`
-- | (`plonk_checks.ml:102`).
collapsePointEval
  :: forall f
   . Semiring f
  => { rounds :: Int, zeta :: f, zetaOmega :: f }
  -> NonEmptyArray { zeta :: f, omegaTimesZeta :: f }
  -> { zeta :: f, omegaTimesZeta :: f }
collapsePointEval { rounds, zeta, zetaOmega } chunks =
  let
    arr = NEA.toArray chunks
  in
    { zeta: actualEvaluationArr (map _.zeta arr) zeta rounds
    , omegaTimesZeta: actualEvaluationArr (map _.omegaTimesZeta arr) zetaOmega rounds
    }

-- | Collapse every `NonEmptyArray (PointEval f)` in a `ChunkedAllEvals f`
-- | into a single `PointEval f` via `collapsePointEval`. Mirrors OCaml
-- | `Plonk_checks.evals_of_split_evals` applied to a whole `Evals.t`.
-- |
-- | The result feeds `ftEval0`, `derivePlonk`, and any other downstream
-- | code that wants a single value per polynomial. CIP itself does NOT
-- | go through here — it consumes the chunked form directly (= OCaml
-- | `Pcs_batch.combine_split_evaluations`).
collapseChunkedAllEvals
  :: forall f
   . Semiring f
  => { rounds :: Int, zeta :: f, zetaOmega :: f }
  -> ChunkedAllEvals f
  -> AllEvals f
collapseChunkedAllEvals ctx chunked =
  let
    collapse = collapsePointEval ctx
  in
    { ftEval1: chunked.ftEval1
    , publicEvals: collapse chunked.publicEvals
    , zEvals: collapse chunked.zEvals
    , indexEvals: map collapse chunked.indexEvals
    , witnessEvals: map collapse chunked.witnessEvals
    , coeffEvals: map collapse chunked.coeffEvals
    , sigmaEvals: map collapse chunked.sigmaEvals
    }

-------------------------------------------------------------------------------
-- | Domain scalars
-------------------------------------------------------------------------------
--
-- The domain-dependent scalars of `finalize_other_proof`, shared by the step
-- and wrap verifiers: the negative powers of the domain generator and the
-- permutation vanishing polynomial (`plonk_checks.ml` `scalars_env`), and the
-- step side's known-domain selection and vanishing polynomial
-- (`step_verifier.ml` `finalize_other_proof` and `pseudo.ml`
-- `Pseudo.Domain.to_domain`).

-- | `ω⁻¹`, `ω^{-(zkRows-1)}` and `ω^{-zkRows}` for the domain generator `ω`.
type OmegaPowers f =
  { omegaToMinus1 :: FVar f
  , omegaToZkPlus1 :: FVar f
  , omegaToZk :: FVar f
  }

-- | The negative generator powers (plonk_checks.ml:248-264): `ω⁻¹ = 1/gen`,
-- | `ω⁻² = ω⁻¹ · ω⁻¹` (OCaml's `square x = x * x`, an R1CS row), then
-- | `zkRows − 3` further multiplications by `ω⁻¹` (none at the default
-- | `zkRows = 3`) reaching `ω^{-(zkRows-1)}`, and one more for `ω^{-zkRows}`.
-- |
-- | Requires `zkRows ≥ 3` (kimchi's minimum, `zkRowsByDefault`); a smaller
-- | value has no `ω^{-(zkRows-1)}` distinct from the two rows above and is
-- | rejected, as OCaml's `Array.init` at a negative length raises.
omegaPowers
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => { generator :: FVar f, zkRows :: Int }
  -> Snarky f c r (OmegaPowers f)
omegaPowers { generator, zkRows }
  | zkRows < zkRowsByDefault = unsafeThrow $
      "Pickles.PlonkChecks.omegaPowers: zkRows = " <> show zkRows
        <> " is below kimchi's minimum "
        <> show zkRowsByDefault
  | otherwise =
      do
        omegaToMinus1 <- inv_ generator
        omegaToMinus2 <- mul_ omegaToMinus1 omegaToMinus1
        omegaToZkPlus1 <- go omegaToMinus1 omegaToMinus2 (zkRows - zkRowsByDefault)
        omegaToZk <- mul_ omegaToZkPlus1 omegaToMinus1
        pure { omegaToMinus1, omegaToZkPlus1, omegaToZk }
      where
      go omegaToMinus1 term i
        | i <= 0 = pure term
        | otherwise = do
            next <- mul_ term omegaToMinus1
            go omegaToMinus1 next (i - 1)

-- | The permutation vanishing polynomial at `ζ`,
-- | `(ζ − ω⁻¹)(ζ − ω^{-(zkRows-1)})(ζ − ω^{-zkRows})` (plonk_checks.ml:273-279):
-- | two rows.
zkPolynomial
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> OmegaPowers f
  -> Snarky f c r (FVar f)
zkPolynomial zeta { omegaToMinus1, omegaToZkPlus1, omegaToZk } = do
  t1 <- mul_ (zeta `sub_` omegaToMinus1) (zeta `sub_` omegaToZkPlus1)
  mul_ t1 (zeta `sub_` omegaToZk)

-- | Which known domain is the prev proof's: one `equals_` of the runtime
-- | `domain_log2` against each domain's, emitted last-to-first (OCaml's
-- | right-to-left `Vector.map`, step_verifier.ml:880-893), in domain order.
knownDomainWhiches
  :: forall nd f c r rd
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Vector nd { log2 :: Int | rd }
  -> Snarky f c r (Vector nd (BoolVar f))
knownDomainWhiches domainLog2Var domains = do
  rev <- traverse (\d -> equals_ (const_ (fromInt d.log2)) domainLog2Var) (Vector.reverse domains)
  pure (Vector.reverse rev)

-- | `ζⁿ − 1` for the selected known domain (`Pseudo.Domain.to_domain`'s
-- | `vanishing_polynomial`, pseudo.ml:118-127): the table `ζ^{2^i}` for
-- | `i` up to the largest domain's log2 by squaring, the entry at each
-- | domain's log2 selected by the which bits, minus one, sealed.
knownDomainVanishingPolynomial
  :: forall nd f r rd
   . PrimeField f
  => Reflectable nd Int
  => Vector nd (BoolVar f)
  -> Vector nd { log2 :: Int | rd }
  -> FVar f
  -> Snarky f (KimchiConstraint f) r (FVar f)
knownDomainVanishingPolynomial whiches domains zeta = do
  let maxLog2 = foldr max 0 (map _.log2 domains)
  pow2Pows <- buildPow2PowsArray zeta maxLog2
  -- every `log2 ≤ maxLog2`, so the index is always in range
  let pow2AtLog2 = map (\d -> fromMaybe (const_ zero) (Array.index pow2Pows d.log2)) domains
  masked <- Pseudo.mask whiches pow2AtLog2
  label "seal_domain_vanishing" $ seal (masked `sub_` const_ one)

-- | `[x, x², x⁴, …, x^(2^maxLog2)]` by `maxLog2` Square rows (`pseudo.ml:119-123`).
buildPow2PowsArray
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Int
  -> Snarky f c r (Array (FVar f))
buildPow2PowsArray x maxLog2 = go [ x ] maxLog2
  where
  go acc i
    | i <= 0 = pure acc
    | otherwise = case Array.last acc of
        Nothing -> pure acc -- unreachable: acc is non-empty
        Just lastV -> do
          sq <- square_ lastV
          go (Array.snoc acc sq) (i - 1)

-------------------------------------------------------------------------------
-- | The gate-constraint environment
-------------------------------------------------------------------------------
--
-- The linearization interpreter reads the constraint polynomial off an
-- `EvalPoint` and a challenge record; these two build them from the proof's
-- evaluations. The constraint polynomial combines witness evaluations
-- (15 columns × 2 rows), coefficient evaluations (15 columns), gate selector
-- evaluations (Poseidon, Generic, VarBaseMul, …), the protocol challenges
-- (alpha, beta, gamma, jointCombiner) and the domain-dependent values
-- (Lagrange basis, vanishing polynomial).

-- | Build EvalPoint from input vectors.
-- | Maps column lookups to the appropriate vector elements.
buildEvalPoint
  :: forall a
   . { witnessEvals :: Vector 15 (PointEval a)
     , coeffEvals :: Vector 15 a
     , indexEvals :: Vector 6 (PointEval a)
     , defaultVal :: a
     }
  -> EvalPoint a
buildEvalPoint { witnessEvals, coeffEvals, indexEvals, defaultVal } =
  let
    pointEvalAt :: forall n. Reflectable n Int => Vector n (PointEval a) -> Finite n -> CurrOrNext -> a
    pointEvalAt v col row =
      let
        a = v !! col
      in
        case row of
          Curr -> a.zeta
          Next -> a.omegaTimesZeta
  in
    { witness: \row col -> pointEvalAt witnessEvals col row
    , coefficient: \col -> coeffEvals !! col
    , index: \row gt ->
        let
          idx = unsafeFinite @6
          -- Gate order matches Kimchi verifier's column ordering:
          -- Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul, EndoMulScalar
          -- See kimchi/src/verifier.rs lines 485-490
          -- Only these 6 gate types are supported; others require additional FFI support.
          gateIdx = case gt of
            Generic -> idx 0
            Poseidon -> idx 1
            CompleteAdd -> idx 2
            VarBaseMul -> idx 3
            EndoMul -> idx 4
            EndoMulScalar -> idx 5
            _ -> unsafeThrow $ "buildEvalPoint: unsupported gate type " <> show gt
        in
          pointEvalAt indexEvals gateIdx row
    , lookupAggreg: \_ -> defaultVal
    , lookupSorted: \_ _ -> defaultVal
    , lookupTable: \_ -> defaultVal
    , lookupRuntimeTable: \_ -> defaultVal
    , lookupRuntimeSelector: \_ -> defaultVal
    , lookupKindIndex: \_ -> defaultVal
    }

-- | Build Challenges from input values.
-- | The UnnormalizedLagrangeBasis calls in the linearization are:
-- |   { zkRows: false, offset: 0 }
-- |   { zkRows: true, offset: -1 }
buildChallenges
  :: forall a r
   . { alpha :: a
     , beta :: a
     , gamma :: a
     , jointCombiner :: a
     , vanishesOnZk :: a
     , lagrangeFalse0 :: a
     , lagrangeTrue1 :: a
     | r
     }
  -> { alpha :: a
     , beta :: a
     , gamma :: a
     , jointCombiner :: a
     , vanishesOnZeroKnowledgeAndPreviousRows :: a
     , unnormalizedLagrangeBasis :: { zkRows :: Boolean, offset :: Int } -> a
     }
buildChallenges { alpha, beta, gamma, jointCombiner, vanishesOnZk, lagrangeFalse0, lagrangeTrue1 } =
  { alpha
  , beta
  , gamma
  , jointCombiner
  , vanishesOnZeroKnowledgeAndPreviousRows: vanishesOnZk
  , unnormalizedLagrangeBasis: \{ zkRows: zk, offset } ->
      if not zk && offset == 0 then lagrangeFalse0
      else if zk && offset == (-1) then lagrangeTrue1
      else lagrangeFalse0
  }

-------------------------------------------------------------------------------
-- | The permutation argument
-------------------------------------------------------------------------------
--
-- The permutation contribution to the linearization check. The full
-- verification equation is
--   ft_eval0 = perm_contribution - constant_term + boundary_quotient = 0
-- where the gate-constraint environment above supplies `constant_term` and
-- these supply the permutation terms.
--
-- See: https://o1-labs.github.io/mina-book/crypto/plonk/maller_15.html

-- | The offset of alpha powers for the permutation argument.
-- | See: https://github.com/o1-labs/proof-systems/blob/516b16fc9b0fdcab5c608cd1aea07c0c66b6675d/kimchi/src/index.rs#L190
permAlpha0 :: Int
permAlpha0 = 21

-- | Input record for permutation argument verification.
-- | Kimchi uses 7 permutation columns (PERMUTS = 7), with 6 sigma
-- | polynomial evaluations included in the proof (PERMUTS - 1 = 6).
-- |
-- | Use as `PermutationInput f` for field values or
-- | `PermutationInput (FVar f)` for circuit variables.
type PermutationInput a =
  { -- First 7 witness column evaluations at zeta
    w :: Vector 7 a
  , -- Sigma polynomial evaluations at zeta (6 columns, PERMUTS-1)
    sigma :: Vector 6 a
  , -- Permutation polynomial z evaluations at zeta and zeta*omega
    z :: PointEval a
  , -- Domain shift values (7 values, one per permutation column)
    shifts :: Vector 7 a
  , -- Protocol challenges
    alpha :: a
  , beta :: a
  , gamma :: a
  , -- Zero-knowledge polynomial evaluated at zeta:
    -- zkp = (zeta - omega^{n-1}) * (zeta - omega^{n-2}) * (zeta - omega^{n-3})
    zkPolynomial :: a
  , -- zeta^n - 1 (domain vanishing polynomial at zeta)
    zetaToNMinus1 :: a
  , -- omega^{-zkRows} (domain generator raised to minus zk_rows)
    omegaToMinusZkRows :: a
  , -- The evaluation point itself
    zeta :: a
  }

-- | Compute the perm scalar at the field level.
-- | This is the coefficient of z(x) in the full linearization polynomial.
-- |
-- | perm = -(z(zeta*omega) * beta * alpha^21 * zkp * ∏_{i=0}^{5}(gamma + beta*sigma_i + w_i))
-- |
-- | Reference: derive_plonk in plonk_checks.ml
permScalar :: forall f. PrimeField f => PermutationInput f -> f
permScalar input =
  let
    alphaPow21 = pow input.alpha (BigInt.fromInt permAlpha0)
    init = input.z.omegaTimesZeta * input.beta * alphaPow21 * input.zkPolynomial
    -- Zip first 6 witness columns with sigma, fold the product
    wSigma = zipWith Tuple (Vector.take @6 input.w) input.sigma
    product = foldl
      (\acc (Tuple wi si) -> acc * (input.gamma + input.beta * si + wi))
      init
      wSigma
  in
    negate product

-- | Compute the permutation contribution to ft_eval0 at the field level.
-- | This includes both product terms and the boundary quotient. The
-- | in-circuit twin is `permContributionCircuit` below (the division is a
-- | witnessed inverse there).
-- |
-- | Reference: ft_eval0 in plonk_checks.ml
permContribution :: forall f. PrimeField f => PermutationInput f -> f
permContribution input =
  let
    alphaPow21 = pow input.alpha (BigInt.fromInt permAlpha0)
    alphaPow22 = alphaPow21 * input.alpha
    alphaPow23 = alphaPow22 * input.alpha

    w6 = input.w !! unsafeFinite @7 6
    term1Init = (w6 + input.gamma) * input.z.omegaTimesZeta * alphaPow21 * input.zkPolynomial
    wSigma = zipWith Tuple (Vector.take @6 input.w) input.sigma

    -- Trace per-iteration accumulator. Final value = same as `term1`
    -- computed via `foldl` below; we use the array version so we can
    -- capture intermediates.
    term1Stages :: Array f
    term1Stages = Array.scanl
      (\acc (Tuple wi si) -> (input.beta * si + wi + input.gamma) * acc)
      term1Init
      (Array.fromFoldable (Vector.toUnfoldable wSigma :: Array _))
    term1 = case Array.last term1Stages of
      Just v -> v
      Nothing -> term1Init

    term2Init = alphaPow21 * input.zkPolynomial * input.z.zeta
    wShifts = zipWith Tuple input.w input.shifts

    term2Stages :: Array f
    term2Stages = Array.scanl
      (\acc (Tuple wi si) -> acc * (input.gamma + input.beta * input.zeta * si + wi))
      term2Init
      (Array.fromFoldable (Vector.toUnfoldable wShifts :: Array _))
    term2 = case Array.last term2Stages of
      Just v -> v
      Nothing -> term2Init

    zetaMinusOmega = input.zeta - input.omegaToMinusZkRows
    zetaMinus1 = input.zeta - one
    nominator =
      ( input.zetaToNMinus1 * alphaPow22 * zetaMinusOmega
          + input.zetaToNMinus1 * alphaPow23 * zetaMinus1
      )
        * (one - input.z.zeta)
    denominator = zetaMinusOmega * zetaMinus1
    boundary = nominator / denominator

    result = term1 - term2 + boundary

    -- ===== DIAGNOSTIC TRACE (chunks2 nc=2 byte-diff) =====
    traceArr lbl arr = Array.foldM
      (\i v -> Trace.field (lbl <> show i) v *> pure (i + 1))
      (0 :: Int)
      arr
    _ = unsafePerformEffect $ do
      Trace.field "perm.alpha_pow21" alphaPow21
      Trace.field "perm.alpha_pow22" alphaPow22
      Trace.field "perm.alpha_pow23" alphaPow23
      Trace.field "perm.term1.init" term1Init
      _ <- traceArr "perm.term1.after_i" term1Stages
      Trace.field "perm.term1.final" term1
      Trace.field "perm.term2.init" term2Init
      _ <- traceArr "perm.term2.after_i" term2Stages
      Trace.field "perm.term2.final" term2
      Trace.field "perm.zeta_minus_omega" zetaMinusOmega
      Trace.field "perm.zeta_minus_1" zetaMinus1
      Trace.field "perm.boundary.nominator" nominator
      Trace.field "perm.boundary.denominator" denominator
      Trace.field "perm.boundary" boundary
      Trace.field "perm.result" result
  in
    result

-- | The in-circuit twin of `permContribution`, with the public-input evaluation
-- | subtracted between the two products as OCaml's `ft_eval0` does:
-- |
-- |   term1 - p_eval0 - term2 + boundary
-- |
-- | Op for op the `ft_eval0` of `plonk_checks.ml` (`Plonk_checks.ft_eval0`,
-- | labelled `ft_eval0 / Field.Checked.mul`): `mul_` chains in OCaml's
-- | evaluation order, `beta * zeta` recomputed per shift step, the boundary
-- | quotient's `alpha^23` term before its `alpha^22` term (OCaml evaluates
-- | `a + b` right to left). The alpha powers come from the caller's
-- | precomputed table (`precomputeAlphaPowers`), which OCaml's `scalars_env`
-- | builds once and shares with the perm scalar. The caller subtracts the
-- | constant term. The labels scope the big mul chain so the circuit diff can
-- | localize structural drift in this region.
-- |
-- | `input.alpha` is unused here: the circuit reads the table, not `alpha`.
permContributionCircuit
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => PermutationInput (FVar f)
  -> { pEval0 :: FVar f, alphaPow21 :: FVar f, alphaPow22 :: FVar f, alphaPow23 :: FVar f }
  -> Snarky f c r (FVar f)
permContributionCircuit input { pEval0, alphaPow21: a21, alphaPow22: a22, alphaPow23: a23 } =
  label "ft_eval0_perm" do
    let
      w0 = input.w
      w6 = w0 !! unsafeFinite @7 6
      beta = input.beta
      gamma = input.gamma
      zeta = input.zeta
      zZeta = input.z.zeta
      zOmegaTimesZeta = input.z.omegaTimesZeta
      zkPoly = input.zkPolynomial
    term1Init <- label "term1_init" $
      mul_ (add_ w6 gamma) zOmegaTimesZeta >>= \t -> mul_ t a21 >>= \t' -> mul_ t' zkPoly
    let wSigma = zipWith Tuple (Vector.take @6 w0) input.sigma
    term1 <- label "term1_fold" $ foldM
      ( \acc (Tuple wi si) -> do
          betaSi <- mul_ beta si
          mul_ (add_ (add_ betaSi wi) gamma) acc
      )
      term1Init
      wSigma

    let term1MinusP = sub_ term1 pEval0

    term2Init <- label "term2_init" $
      mul_ a21 zkPoly >>= \t -> mul_ t zZeta
    let wShifts = zipWith Tuple w0 input.shifts
    term2 <- label "term2_fold" $ foldM
      ( \acc (Tuple wi si) -> do
          betaZetaSi <- mul_ beta zeta >>= \t -> mul_ t si
          mul_ acc (add_ (add_ gamma betaZetaSi) wi)
      )
      term2Init
      wShifts

    let
      zetaMinusOmegaZk = sub_ zeta input.omegaToMinusZkRows
      zetaMinus1 = sub_ zeta (const_ one)

    boundary <- label "boundary" do
      term23 <- mul_ input.zetaToNMinus1 a23 >>= \t -> mul_ t zetaMinus1
      term22 <- mul_ input.zetaToNMinus1 a22 >>= \t -> mul_ t zetaMinusOmegaZk
      let oneMinusZ = sub_ (const_ one) zZeta
      nominator <- mul_ (add_ term22 term23) oneMinusZ
      denominator <- mul_ zetaMinusOmegaZk zetaMinus1
      div_ nominator denominator

    pure $ add_ (sub_ term1MinusP term2) boundary

-- | The in-circuit twin of `permScalar` (OCaml `derive_plonk`'s `perm`):
-- |
-- |   -(z(zeta*omega) * beta * alpha^21 * zkp * ∏_{i<6} (gamma + beta*sigma_i + w_i))
-- |
-- | `mul_` chains in OCaml's evaluation order; `alpha^21` comes from the
-- | caller's table.
permScalarCircuit
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => { w :: Vector 6 (FVar f)
     , sigma :: Vector 6 (FVar f)
     , zOmega :: FVar f
     , beta :: FVar f
     , gamma :: FVar f
     , zkPolynomial :: FVar f
     , alphaPow21 :: FVar f
     }
  -> Snarky f c r (FVar f)
permScalarCircuit { w, sigma, zOmega, beta, gamma, zkPolynomial: zkPoly, alphaPow21 } = do
  init' <- mul_ zOmega beta >>= \t -> mul_ t alphaPow21 >>= \t' -> mul_ t' zkPoly
  result <- foldM
    ( \acc (Tuple wi si) -> do
        betaSigma <- mul_ beta si
        mul_ acc (add_ (add_ gamma betaSigma) wi)
    )
    init'
    (zipWith Tuple w sigma)
  pure (negate_ result)

-------------------------------------------------------------------------------
-- | The combined inner product
-------------------------------------------------------------------------------

-- | Evaluation in the Horner fold: either always present (Just) or masked (Maybe).
-- |
-- | Matches OCaml's `Pcs_batch.combine_split_evaluations` which uses
-- | `Shifted_value.of_cvar` for always-present and `if_` for masked evaluations.
data EvalOpt f
  = EvalJust (FVar f)
  | EvalMaybe (BoolVar f) (FVar f)

-- | Horner fold matching OCaml's `Pcs_batch.combine_split_evaluations`.
-- |
-- | Takes the polynomial batching scalar (xi) and a flat evaluation list.
-- | Reverses the list, initializes from head, folds with mul_and_add:
-- |   Just fx → fx + xi * acc
-- |   Maybe (b, fx) → if b then (fx + xi * acc) else acc
-- |
-- | Reference: step_verifier.ml:1060-1121 (combine ~ft ~sg_evals)
hornerCombine
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> NonEmptyArray (EvalOpt f)
  -> Snarky f c r (FVar f)
hornerCombine xi evals = label "horner-combine" do
  let
    reversed = NEA.reverse evals
    { head: initVal, tail: rest } = NEA.uncons reversed
    initResult = case initVal of
      EvalJust x -> x
      EvalMaybe _ x -> x -- unreachable in practice: init is always Just
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
-- |
-- | Order: sg_evals(n), public_input, ft_eval, z+index+witness+coeff+sigma (43).
-- | This matches `Evals.In_circuit.to_list` order for always-present fields.
buildEvalList
  :: forall n f
   . { sgEvals :: Vector n (Tuple (BoolVar f) (FVar f))
     , publicInput :: FVar f
     , ftEval :: FVar f
     , evals :: Vector 43 (FVar f)
     }
  -> NonEmptyArray (EvalOpt f)
buildEvalList x =
  let
    sgEvals = map (\(Tuple keep eval) -> EvalMaybe keep eval) x.sgEvals
    others = NEA.cons' (EvalJust x.publicInput) [ EvalJust x.ftEval ]
    evals = map EvalJust $ NEA.fromFoldable1 x.evals
  in
    NEA.prependArray (Vector.toUnfoldable sgEvals)
      $ NEA.concat
      $
        NEA.cons' others [ evals ]

-- | Build evaluation list with all sg_evals unmasked (EvalJust).
-- |
-- | Used by the Wrap FOP where all previous proofs are always present
-- | (no proofs-verified mask).
buildEvalListUnmasked
  :: forall n nPred f
   . Add 1 nPred n
  => { sgEvals :: Vector n (FVar f)
     , publicInput :: FVar f
     , ftEval :: FVar f
     , evals :: Vector 43 (FVar f)
     }
  -> NonEmptyArray (EvalOpt f)
buildEvalListUnmasked x =
  let
    sgEvals = map EvalJust $ NEA.fromFoldable1 x.sgEvals
    others = NEA.cons' (EvalJust x.publicInput) [ EvalJust x.ftEval ]
    evals = map EvalJust $ NEA.fromFoldable1 x.evals
  in
    NEA.concat $ NEA.cons' sgEvals [ others, evals ]

-- | The combined inner product `combine(zeta) + r * combine(zetaw)`, the
-- | zetaw fold first.
-- |
-- | Reference: `combined_inner_product_correct` in step_verifier.ml
combinedInnerProduct
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => { xi :: FVar f
     , r :: FVar f
     , evalsZeta :: NonEmptyArray (EvalOpt f)
     , evalsZetaw :: NonEmptyArray (EvalOpt f)
     }
  -> Snarky f c r (FVar f)
combinedInnerProduct { xi, r, evalsZeta, evalsZetaw } = label "combine" do
  combineZetaw <- hornerCombine xi evalsZetaw
  rTimesZetaw <- mul_ r combineZetaw
  combineZeta <- hornerCombine xi evalsZeta
  pure (add_ combineZeta rTimesZetaw)

-------------------------------------------------------------------------------
-- | The fr-sponge schedule of finalize_other_proof
-------------------------------------------------------------------------------

-- | The digest of the previous proofs' bulletproof challenges (OCaml
-- | `challenge_digest` in wrap_verifier.ml): a fresh sponge absorbing every
-- | challenge, squeezed once.
challengeDigest
  :: forall n d f r
   . PoseidonField f
  => PrimeField f
  => Vector n (Vector d (FVar f))
  -> Snarky f (KimchiConstraint f) r (FVar f)
challengeDigest prevChallenges = evalSpongeM initialSpongeCircuit do
  traverse_ (traverse_ absorb) prevChallenges
  squeeze

-- | The digest of the previous proofs' bulletproof challenges under the
-- | proofs-verified mask (OCaml `challenge_digest` in step_verifier.ml): an
-- | `OptSponge` absorbing each challenge only where its proof's slot is real.
maskedChallengeDigest
  :: forall n d f r
   . PoseidonField f
  => PrimeField f
  => Vector n (BoolVar f)
  -> Vector n (Vector d (FVar f))
  -> Snarky f (KimchiConstraint f) r (FVar f)
maskedChallengeDigest mask prevChallenges =
  OptSponge.squeeze OptSponge.create $ Array.concat $ Vector.toUnfoldable $
    Vector.zipWith (\keep chals -> map (Tuple keep) (Vector.toUnfoldable chals))
      mask
      prevChallenges

-- | The fr-sponge schedule (OCaml step_verifier.ml step 7, wrap_verifier.ml
-- | step 4): absorb the sponge digest before evaluations, then the challenge
-- | digest (computed here, between the two absorbs), then every evaluation;
-- | squeeze xi and r as 128-bit scalar challenges. `xiConstrainLowBits` is
-- | OCaml's `squeeze_challenge` (true, step) versus `squeeze_scalar` (false,
-- | wrap) for xi; r is always `squeeze_challenge`.
squeezeXiR
  :: forall f cr
   . PoseidonField f
  => PrimeField f
  => FieldSizeInBits f 255
  => { spongeDigestBeforeEvaluations :: FVar f
     , challengeDigest :: Snarky f (KimchiConstraint f) cr (FVar f)
     , allEvals :: AllEvals (FVar f)
     , endo :: FVar f
     , xiConstrainLowBits :: Boolean
     }
  -> Snarky f (KimchiConstraint f) cr { xi :: SizedF 128 (FVar f), r :: SizedF 128 (FVar f) }
squeezeXiR p = evalSpongeM initialSpongeCircuit do
  absorb p.spongeDigestBeforeEvaluations
  digest <- liftSnarky p.challengeDigest
  absorb digest
  absorbAllEvals p.allEvals
  xi <- squeezeScalar' p.xiConstrainLowBits { endo: p.endo }
  r <- squeezeScalarChallenge { endo: p.endo }
  pure { xi, r }

-- | Input for the out-of-circuit fr-sponge, whose absorption order matches
-- | Kimchi's protocol exactly: fq_digest, prev_challenge_digest, ft_eval1,
-- | public_evals, then all poly evals in the order z, selectors (6),
-- | witness (15), coefficients (15), sigma (6).
-- |
-- | Reference: mina/src/lib/pickles/step_verifier.ml (lines 946-954)
type FrSpongeInput f = Record
  ( AllEvalsRow f
      ( fqDigest :: f -- Fq-sponge digest before Fr-sponge
      , prevChallengeDigest :: f -- digest of previous recursion challenges (zero for base case)
      , endo :: f -- EndoScalar coefficient (= G::endos().1 = endo_r)
      )
  )

-- | Result of Fr-sponge challenge derivation.
-- | Contains both raw 128-bit scalar challenges and endo-expanded full field values.
-- | Raw values are used for xi_correct/r_correct verification (comparing 128-bit challenges).
-- | Expanded values are used for CIP computation.
type FrSpongeChallenges f =
  { rawXi :: SizedF 128 f -- raw 128-bit xi challenge (for verification)
  , xi :: f -- endo-expanded polyscale (for CIP)
  , rawR :: SizedF 128 f -- raw 128-bit r challenge (for verification)
  , evalscale :: f -- endo-expanded evalscale (for CIP)
  }

-- | The out-of-circuit twin of `squeezeXiR`: replay the fr-sponge and return
-- | both the raw 128-bit challenges and their endo expansions.
frSpongeChallengesPure
  :: forall f
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => FrSpongeInput f
  -> FrSpongeChallenges f
frSpongeChallengesPure input =
  evalPureSpongeM initialSponge do
    -- 1. Absorb fq_digest and prev_challenge_digest
    absorb input.fqDigest
    absorb input.prevChallengeDigest

    -- 2. Absorb ft_eval1
    absorb input.ftEval1

    -- 3. Absorb public evals
    absorb input.publicEvals.zeta
    absorb input.publicEvals.omegaTimesZeta

    -- 4. Absorb all polynomial evaluations
    absorbEvaluationsPure input

    -- 5. Squeeze scalar challenge for xi (raw 128-bit)
    rawXi <- squeezeScalarChallengePure

    -- 6. Squeeze scalar challenge for r (raw 128-bit)
    rawR <- squeezeScalarChallengePure

    -- 7. Expand to full field via endo for CIP use
    let
      xi = toFieldPure (coerceViaBits rawXi) input.endo
      evalscale = toFieldPure (coerceViaBits rawR) input.endo

    pure { rawXi, xi, rawR, evalscale }

-- | Absorb the z, selector, witness, coefficient and sigma evaluations, in
-- | Kimchi's order. Unlike `absorbAllEvals` this skips `ftEval1` and the
-- | public evals, which `frSpongeChallengesPure` absorbs earlier.
absorbEvaluationsPure
  :: forall f r
   . PoseidonField f
  => { zEvals :: PointEval f
     , indexEvals :: Vector 6 (PointEval f)
     , witnessEvals :: Vector 15 (PointEval f)
     , coeffEvals :: Vector 15 (PointEval f)
     , sigmaEvals :: Vector 6 (PointEval f)
     | r
     }
  -> PureSpongeM f Unit
absorbEvaluationsPure input = do
  absorbPointEval input.zEvals
  traverse_ absorbPointEval input.indexEvals
  traverse_ absorbPointEval input.witnessEvals
  traverse_ absorbPointEval input.coeffEvals
  traverse_ absorbPointEval input.sigmaEvals
