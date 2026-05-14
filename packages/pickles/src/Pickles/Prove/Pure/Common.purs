-- | Field-polymorphic pure helpers shared by the step and wrap
-- | provers.
-- |
-- | This module consolidates what used to live in six separate
-- | `Pickles.Prove.Pure.*` modules:
-- |
-- | * `EvalsOfSplit` → `actualEvaluation`, `evalsOfSplitPoint`
-- | * `BulletproofB` → `computeBpChalsAndB`
-- | * `CombinedInnerProductBatch` → `combinedInnerProductBatch`
-- | * `DerivePlonkType1` / `DerivePlonkType2` → `derivePlonk`
-- | * `FtEval0Type1` / `FtEval0Type2` → `ftEval0`
-- |
-- | The Type1/Type2 split in the last four was pure duplication —
-- | OCaml shares the same `derive_plonk` / `ft_eval0` body under the
-- | `Plonk_checks.Make (Shifted_value.Type1) ...` vs
-- | `Plonk_checks.Make (Shifted_value.Type2) ...` functor
-- | instantiations. In PS we recover the same sharing via a
-- | `Shifted (F f) sf` constraint: the caller picks the output
-- | shifted-value type (via return-type annotation) and the same body
-- | services both Type1 and Type2 callers.
-- |
-- | All helpers are pure (no FFI, no circuit monad). They are consumed
-- | by `Pickles.Prove.Pure.Step` (and eventually `Pickles.Prove.Pure.Wrap`).
module Pickles.Prove.Pure.Common
  ( -- * Evaluation recombination
    actualEvaluation
  -- * Bulletproof
  , BulletproofBInput
  , BulletproofBOutput
  , computeBpChalsAndB
  -- * Combined inner product
  , CombinedInnerProductBatchInput
  , combinedInnerProductBatch
  , CombinedInnerProductBatchChunkedInput
  , combinedInnerProductBatchChunked
  -- * Scalar derivations (unified Type1+Type2)
  , DerivePlonkInput
  , derivePlonk
  , FtEval0Input
  , ftEval0
  -- * Cross-field reinterpretation
  , crossFieldDigest
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, foldr)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Pickles.IPA (bPoly)
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Types (LinearizationPoly, runLinearizationPoly)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Pickles.PlonkChecks (AllEvals, ChunkedAllEvals)
import Pickles.PlonkChecks.GateConstraints (buildEvalPoint)
import Pickles.PlonkChecks.Permutation (permContribution, permScalar)
import Pickles.Verify.Types (PlonkInCircuit, PlonkMinimal, expandPlonkMinimal)
import Poseidon (class PoseidonField)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField, fromBigInt, pow, toBigInt)
import Snarky.Types.Shifted (class Shifted, toShifted)

--------------------------------------------------------------------------------
-- Evaluation recombination — `actualEvaluation` / `evalsOfSplitPoint`
--------------------------------------------------------------------------------

-- | `pow2Pow n x = x^(2^n)`, computed by repeated squaring.
-- |
-- | Matches the local `pt_n` computation in OCaml's `actual_evaluation`
-- | (plonk_checks.ml:92-94).
pow2Pow :: forall f. Semiring f => Int -> f -> f
pow2Pow n x
  | n <= 0 = x
  | otherwise = pow2Pow (n - 1) (x * x)

-- | Combine a chunked evaluation `e` at a point `pt`, with chunk base
-- | `pt^(2^rounds)`. Given `e = [a0, a1, ..., a_{n-1}]` and
-- | `ptN = pt^(2^rounds)`, returns
-- |
-- |   `a0 + ptN · a1 + ptN^2 · a2 + ... + ptN^(n-1) · a_{n-1}`
-- |
-- | Computed via Horner's rule, mirroring OCaml's `actual_evaluation`
-- | (`plonk_checks.ml:90-100`). For an empty input, returns `zero`.
actualEvaluation
  :: forall f
   . Semiring f
  => Int
  -> f
  -> Array f
  -> f
actualEvaluation rounds pt e =
  let
    ptN = pow2Pow rounds pt
  in
    foldr (\fx acc -> fx + ptN * acc) zero e

type BulletproofBInput d f =
  { rawPrechallenges :: Vector d (SizedF 128 f)
  , endo :: f
  , zeta :: f
  , zetaw :: f
  , r :: f
  }

-- | Output of `computeBpChalsAndB`.
-- |
-- | * `chals` — endo-expanded field-level bulletproof challenges.
-- | * `b` — `b_poly(zeta) + r · b_poly(zetaw)`, the opening target.
type BulletproofBOutput d f =
  { chals :: Vector d f
  , b :: f
  }

-- | Pure PS port of the "new bulletproof challenges + b" computation
-- | at OCaml `step.ml:359-379`. Expands the raw prechallenges via
-- | `toFieldPure`, builds the challenge polynomial via `bPoly`, and
-- | evaluates `b_poly(zeta) + r·b_poly(zetaw)` — the combined IPA
-- | opening target.
computeBpChalsAndB
  :: forall d f n
   . Reflectable d Int
  => PrimeField f
  => FieldSizeInBits f n
  => Compare 128 n LT
  => BulletproofBInput d f
  -> BulletproofBOutput d f
computeBpChalsAndB input =
  let
    chals = map (\chal -> toFieldPure chal input.endo) input.rawPrechallenges

    bAtZeta = bPoly chals input.zeta
    bAtZetaw = bPoly chals input.zetaw

    b = bAtZeta + input.r * bAtZetaw
  in
    { chals, b }

--------------------------------------------------------------------------------
-- Combined inner product — `combinedInnerProductBatch`
--------------------------------------------------------------------------------

-- | Input to `combinedInnerProductBatch`.
-- |
-- | Type parameters:
-- |
-- | * `n` — number of previous proofs whose bp challenges feed one
-- |   `b_poly` each into the batch.
-- | * `d` — length of each prev-proof bp challenge vector (= IPA
-- |   rounds).
-- | * `f` — the field in which the CIP is computed. Step-field side
-- |   uses `StepField`; wrap-field side uses `WrapField`.
type CombinedInnerProductBatchInput n d f =
  { allEvals :: AllEvals f
  , publicEvals :: PointEval f
  , ftEval0 :: f
  , ftEval1 :: f
  , oldBulletproofChallenges :: Vector n (Vector d f)
  , xi :: f
  , r :: f
  , zeta :: f
  , zetaw :: f
  }

-- | Field-polymorphic pure PS port of kimchi's batched
-- | `combined_inner_product`. Used on both sides of the recursion:
-- |
-- | * **step-field** — `Pickles.Wrap.combined_inner_product` in OCaml
-- |   `wrap.ml:22-62` (called from `expand_deferred`). Caller
-- |   instantiates `f = StepField`.
-- | * **wrap-field** — the inline block at OCaml
-- |   `step.ml:464-496`. Caller instantiates `f = WrapField`.
-- |
-- | Batching order (matching `wrap.ml:50-54` / `step.ml:472-485`):
-- | `b_polys (n)`, `public_input (1)`, `ft (1)`, `z (1)`,
-- | `index (6)`, `witness (15)`, `coefficient (15)`, `sigma (6)`.
-- |
-- | Implements the Horner fold
-- |
-- |   `sum_i xi^i · (eval_i.zeta + r · eval_i.omegaTimesZeta)`
-- |
-- | which factors as `combine Fst zeta + r · combine Snd zetaw`, the
-- | form OCaml uses.
-- |
-- | Non-chunked assumption: single chunk per polynomial. Caller must
-- | recombine via `evalsOfSplitPoint` upstream.
combinedInnerProductBatch
  :: forall n d f
   . Reflectable d Int
  => PrimeField f
  => CombinedInnerProductBatchInput n d f
  -> f
combinedInnerProductBatch input =
  let
    bPolyEvals = map
      ( \chals ->
          { zeta: bPoly chals input.zeta
          , omegaTimesZeta: bPoly chals input.zetaw
          }
      )
      (Array.fromFoldable input.oldBulletproofChallenges)

    ftPointEval = { zeta: input.ftEval0, omegaTimesZeta: input.ftEval1 }

    all = input.allEvals

    orderedEvals =
      bPolyEvals
        <> [ input.publicEvals, ftPointEval, all.zEvals ]
        <> Array.fromFoldable all.indexEvals
        <> Array.fromFoldable all.witnessEvals
        <> Array.fromFoldable all.coeffEvals
        <> Array.fromFoldable all.sigmaEvals

    step { result, scale } eval =
      let
        term = eval.zeta + input.r * eval.omegaTimesZeta
      in
        { result: result + scale * term
        , scale: scale * input.xi
        }
  in
    (foldl step { result: zero, scale: one } orderedEvals).result

-- | Input to `combinedInnerProductBatchChunked` — the chunk-aware CIP.
-- |
-- | Identical to `CombinedInnerProductBatchInput` except `allEvals` and
-- | `publicEvals` carry `NonEmptyArray (PointEval f)` per polynomial
-- | (= one PointEval per chunk). `ftEval0`, `ftEval1`, and the bp
-- | challenge polynomials remain single-valued (they have no chunked
-- | structure in OCaml either).
type CombinedInnerProductBatchChunkedInput n d f =
  { allEvals :: ChunkedAllEvals f
  , publicEvals :: NonEmptyArray (PointEval f)
  , ftEval0 :: f
  , ftEval1 :: f
  , oldBulletproofChallenges :: Vector n (Vector d f)
  , xi :: f
  , r :: f
  , zeta :: f
  , zetaw :: f
  }

-- | Chunk-aware CIP. Mirrors OCaml `wrap.ml:22-62 combined_inner_product`
-- | which uses `Pcs_batch.combine_split_evaluations` to flatten chunked
-- | evaluations across all polynomials and xi-fold right-to-left:
-- |
-- |   `combine pt = sum_i xi^i * flat[i]`
-- |
-- |   where `flat = [bp_polys at pt] ++ public_input_chunks ++ [ft]
-- |              ++ z_chunks ++ index_chunks ++ witness_chunks
-- |              ++ coeff_chunks ++ sigma_chunks`
-- |
-- | The total CIP is `combine zeta + r * combine zetaw`.
-- |
-- | For inner proofs at num_chunks=1 each NonEmptyArray has length 1 and
-- | this collapses to the legacy single-eval `combinedInnerProductBatch`
-- | (byte-identical output). For chunks2 (step num_chunks=2) the extra
-- | chunks contribute additional xi-weighted terms.
-- |
-- | Reference: `Pcs_batch.combine_split_evaluations`
-- | (`pcs_batch.ml:42-51`).
combinedInnerProductBatchChunked
  :: forall n d f
   . Reflectable d Int
  => PrimeField f
  => CombinedInnerProductBatchChunkedInput n d f
  -> f
combinedInnerProductBatchChunked input =
  let
    -- bp polynomials evaluated at zeta and zetaw — single-valued (no chunking).
    -- Each contributes one element to the flat list per `pt`.
    bPolyZeta = map (\chals -> bPoly chals input.zeta)
      (Array.fromFoldable input.oldBulletproofChallenges)
    bPolyZetaw = map (\chals -> bPoly chals input.zetaw)
      (Array.fromFoldable input.oldBulletproofChallenges)

    all = input.allEvals

    -- Flatten all chunked PointEvals projecting `proj` (either `_.zeta`
    -- or `_.omegaTimesZeta`) across the polynomial list. Each polynomial
    -- contributes its full chunk array (length `num_chunks`).
    extractChunks
      :: (PointEval f -> f) -> NonEmptyArray (PointEval f) -> Array f
    extractChunks proj nea = map proj (NEA.toArray nea)

    -- Build the flat list for one evaluation point. Matches OCaml's
    -- ordering at `wrap.ml:46-54`:
    --   bp_polys (singletons) ++ public_input chunks ++ [ft]
    --   ++ z chunks ++ index chunks ++ witness chunks ++ coeff chunks
    --   ++ sigma chunks
    flatAt :: (PointEval f -> f) -> f -> Array f -> Array f
    flatAt proj ftValue bpValues =
      bpValues
        <> extractChunks proj input.publicEvals
        <> [ ftValue ]
        <> extractChunks proj all.zEvals
        <> Array.concatMap (extractChunks proj) (Vector.toUnfoldable all.indexEvals)
        <> Array.concatMap (extractChunks proj) (Vector.toUnfoldable all.witnessEvals)
        <> Array.concatMap (extractChunks proj) (Vector.toUnfoldable all.coeffEvals)
        <> Array.concatMap (extractChunks proj) (Vector.toUnfoldable all.sigmaEvals)

    -- Pcs_batch.combine_split_evaluations: reverse and xi-fold with
    --   acc' = fx + xi * acc
    -- (= horner with xi). For empty input returns zero.
    combine :: Array f -> f
    combine flat =
      case Array.uncons (Array.reverse flat) of
        Just { head, tail } -> foldl (\acc fx -> fx + input.xi * acc) head tail
        Nothing -> zero
  in
    combine (flatAt _.zeta input.ftEval0 bPolyZeta)
      + input.r * combine (flatAt _.omegaTimesZeta input.ftEval1 bPolyZetaw)

--------------------------------------------------------------------------------
-- Scalar derivations — `derivePlonk` / `ftEval0` (Type1+Type2 unified)
--------------------------------------------------------------------------------

-- | Input to `derivePlonk`.
-- |
-- | Matches the OCaml step.ml / wrap.ml variable names:
-- |
-- | * `plonkMinimal` — raw 128-bit challenges, carried forward
-- |   unchanged into the output.
-- | * `w`, `sigma`, `zZeta`, `zOmegaTimesZeta` — recombined polynomial
-- |   evaluations at (zeta, zeta·omega).
-- | * `shifts` — the 7 permutation shift constants from the domain.
-- | * `generator` — the circuit's domain generator omega.
-- | * `domainLog2` — log2 of the domain size.
-- | * `zkRows` — zero-knowledge row count (standard kimchi: 3).
-- | * `srsLengthLog2` — log2 of the SRS length, for `zeta_to_srs_length`.
-- | * `endo` — scalar endo coefficient for challenge expansion.
type DerivePlonkInput f =
  { plonkMinimal :: PlonkMinimal (F f)
  , w :: Vector 7 f
  , sigma :: Vector 6 f
  , zZeta :: f
  , zOmegaTimesZeta :: f
  , shifts :: Vector 7 f
  , generator :: f
  , domainLog2 :: Int
  , zkRows :: Int
  , srsLengthLog2 :: Int
  , endo :: f
  }

-- | Unified pure port of OCaml's `Plonk_checks.derive_plonk`
-- | (`plonk_checks.ml:403-441`), field-polymorphic over both
-- | instantiations:
-- |
-- | * `Make (Shifted_value.Type1) (Scalars_tokens_interpreter.Tick)`
-- |   (called from `wrap.ml` and `wrap_deferred_values.expand_deferred`)
-- | * `Make (Shifted_value.Type2) (Scalars_tokens_interpreter.Tock)`
-- |   (called from `step.ml:498-511`)
-- |
-- | The `Shifted (F f) sf` constraint picks which shifted-value
-- | representation the output uses. The body is identical across both
-- | instantiations; OCaml achieves the same sharing via functor
-- | application.
-- |
-- | Callers disambiguate via return-type annotation:
-- |
-- | @
-- |   let p :: PlonkInCircuit (F StepField) (Type1 (F StepField))
-- |       p = derivePlonk stepInput
-- |
-- |   let p :: PlonkInCircuit (F WrapField) (Type2 (F WrapField))
-- |       p = derivePlonk wrapInput
-- | @
derivePlonk
  :: forall f sf
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => Shifted (F f) sf
  => DerivePlonkInput f
  -> PlonkInCircuit (F f) sf
derivePlonk input =
  let
    expanded = expandPlonkMinimal input.endo input.plonkMinimal

    omegaToMinus1 = one / input.generator
    omegaToMinusZkRows = pow omegaToMinus1 (BigInt.fromInt input.zkRows)

    zkPolynomial =
      let
        omegaToZkPlus1 = pow omegaToMinus1 (BigInt.fromInt (input.zkRows - 1))
      in
        (expanded.zeta - omegaToMinus1)
          * (expanded.zeta - omegaToZkPlus1)
          * (expanded.zeta - omegaToMinusZkRows)

    zetaToNMinus1 =
      pow expanded.zeta
        (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt input.domainLog2))
        - one

    zetaToSrsLength =
      pow expanded.zeta
        (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt input.srsLengthLog2))

    permInput =
      { w: input.w
      , sigma: input.sigma
      , z: { zeta: input.zZeta, omegaTimesZeta: input.zOmegaTimesZeta }
      , shifts: input.shifts
      , alpha: expanded.alpha
      , beta: expanded.beta
      , gamma: expanded.gamma
      , zkPolynomial
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: expanded.zeta
      }
    permRaw = permScalar permInput
  in
    { alpha: input.plonkMinimal.alpha
    , beta: input.plonkMinimal.beta
    , gamma: input.plonkMinimal.gamma
    , zeta: input.plonkMinimal.zeta
    , perm: toShifted (F permRaw)
    , zetaToDomainSize: toShifted (F (zetaToNMinus1 + one))
    , zetaToSrsLength: toShifted (F zetaToSrsLength)
    }

-- | Input to `ftEval0`.
-- |
-- | Field-polymorphic version that unifies `FtEval0Type1Input` and
-- | `FtEval0Type2Input`. Callers pass the linearization token stream
-- | appropriate for their field:
-- |
-- | * step field → `Pickles.Linearization.pallas`
-- | * wrap field → `Pickles.Linearization.vesta`
-- |
-- | See `DerivePlonkInput` for the common fields. The additional
-- | fields are:
-- |
-- | * `allEvals` — all recombined polynomial evals at (zeta, zeta·omega).
-- | * `pEval0Chunks` — public-input poly evaluation chunks at zeta.
-- | * `vanishesOnZk` — precomputed
-- |   `vanishes_on_zero_knowledge_and_previous_rows`.
-- | * `omegaForLagrange` — maps `{ zkRows, offset }` to the
-- |   appropriate omega power for `unnormalized_lagrange_basis` lookups.
-- | * `linearizationPoly` — the Polish-notation token stream for the
-- |   target circuit.
type FtEval0Input f =
  { plonkMinimal :: PlonkMinimal (F f)
  , allEvals :: AllEvals f
  , pEval0Chunks :: Array f
  , shifts :: Vector 7 f
  , generator :: f
  , domainLog2 :: Int
  , zkRows :: Int
  , srsLengthLog2 :: Int
  , endo :: f
  , vanishesOnZk :: f
  , omegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> f
  , linearizationPoly :: LinearizationPoly f
  }

-- | Unified pure port of OCaml's `Plonk_checks.ft_eval0`
-- | (`plonk_checks.ml:350-400`), field-polymorphic over both Type1 and
-- | Type2 instantiations. OCaml shares the body across
-- |
-- | * `Make (Shifted_value.Type1) ...` — called from
-- |   `wrap.ml::combined_inner_product` (the wrap prover, operating
-- |   in the step field, which is `Tick.Field`);
-- | * `Make (Shifted_value.Type2) ...` — called from step.ml:488 (the
-- |   step prover, operating in the wrap field, which is `Tock.Field`).
-- |
-- | Result:
-- |
-- |   `ft_eval0 = permContribution - pEval0Folded - constantTerm`
-- |
-- | where
-- |
-- | * `permContribution` = `term1 - term2 + boundary` from
-- |   `Pickles.PlonkChecks.Permutation.permContribution`;
-- | * `pEval0Folded` = Horner fold of `pEval0Chunks` at
-- |   `zeta^(2^srsLengthLog2)`;
-- | * `constantTerm` = `evaluate linearizationPoly (fieldEnv ...)`.
ftEval0
  :: forall f f'
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => HasEndo f f'
  => FtEval0Input f
  -> f
ftEval0 input =
  let
    expanded = expandPlonkMinimal input.endo input.plonkMinimal

    omegaToMinus1 = one / input.generator
    omegaToMinusZkRows = pow omegaToMinus1 (BigInt.fromInt input.zkRows)
    omegaToZkPlus1 = pow omegaToMinus1 (BigInt.fromInt (input.zkRows - 1))

    zkPolynomial =
      (expanded.zeta - omegaToMinus1)
        * (expanded.zeta - omegaToZkPlus1)
        * (expanded.zeta - omegaToMinusZkRows)

    zetaToNMinus1 =
      pow expanded.zeta
        (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt input.domainLog2))
        - one

    pEval0Folded =
      actualEvaluation input.srsLengthLog2 expanded.zeta input.pEval0Chunks

    permInputRec =
      { w: map _.zeta (Vector.take @7 input.allEvals.witnessEvals)
      , sigma: map _.zeta input.allEvals.sigmaEvals
      , z: input.allEvals.zEvals
      , shifts: input.shifts
      , alpha: expanded.alpha
      , beta: expanded.beta
      , gamma: expanded.gamma
      , zkPolynomial
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: expanded.zeta
      }
    permRaw = permContribution permInputRec

    evalPoint = buildEvalPoint
      { witnessEvals: input.allEvals.witnessEvals
      , coeffEvals: map _.zeta input.allEvals.coeffEvals
      , indexEvals: input.allEvals.indexEvals
      , defaultVal: zero
      }

    challenges =
      { alpha: expanded.alpha
      , beta: expanded.beta
      , gamma: expanded.gamma
      , jointCombiner: one
      , vanishesOnZeroKnowledgeAndPreviousRows: input.vanishesOnZk
      , unnormalizedLagrangeBasis: \args ->
          zetaToNMinus1 / (expanded.zeta - input.omegaForLagrange args)
      }

    env = fieldEnv evalPoint challenges
    constantTerm = evaluate (runLinearizationPoly input.linearizationPoly) env
  in
    permRaw - pEval0Folded - constantTerm

--------------------------------------------------------------------------------
-- Cross-field reinterpretation
--------------------------------------------------------------------------------

-- | Reinterpret a field element's integer representation in another
-- | field. Used for hash digests and packed-limb values that must
-- | appear bit-identically in both curves of the Pasta cycle.
-- |
-- | Safe when the source value's big-int representation fits within
-- | the target field's modulus — true for digests (hashes are bounded
-- | by the sponge output width < both Pallas/Vesta scalar moduli) and
-- | for limb-packed values (each limb < 2^64).
crossFieldDigest :: forall f f'. PrimeField f => PrimeField f' => f -> f'
crossFieldDigest = fromBigInt <<< toBigInt
