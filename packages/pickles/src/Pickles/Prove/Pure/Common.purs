-- | Field-polymorphic scalar helpers shared by the step and wrap
-- | provers: evaluation recombination, the batched combined inner
-- | product, and the `derivePlonk` / `ftEval0` derivations. Pure —
-- | no FFI and no circuit monad.
module Pickles.Prove.Pure.Common
  (
    actualEvaluation
  , BulletproofBInput
  , BulletproofBOutput
  , computeBpChalsAndB
  , CombinedInnerProductBatchInput
  , combinedInnerProductBatch
  , CombinedInnerProductBatchChunkedInput
  , combinedInnerProductBatchChunked
  , DerivePlonkInput
  , derivePlonk
  , FtEval0Input
  , ftEval0
  , crossFieldDigest
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Foldable (foldl, foldr)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import JS.BigInt as BigInt
import Pickles.DeferredValues (PlonkInCircuit, PlonkMinimal, expandPlonkMinimal)
import Pickles.IPA (bPoly)
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Types (LinearizationPoly, runLinearizationPoly)
import Pickles.PlonkChecks (buildEvalPoint, permContribution, permScalar)
import Pickles.Trace as Trace
import Pickles.Types (ChunkedEvals, Evals)
import Poseidon (class PoseidonField)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField, fromBigInt, pow, toBigInt)
import Snarky.Types.Shifted (class Shifted, toShifted)

--------------------------------------------------------------------------------
-- Evaluation recombination
--------------------------------------------------------------------------------

-- | `pow2Pow n x = x^(2^n)`, by repeated squaring.
pow2Pow :: forall f. Semiring f => Int -> f -> f
pow2Pow n x
  | n <= 0 = x
  | otherwise = pow2Pow (n - 1) (x * x)

-- | Combine a chunked evaluation `e = [a0, …, a_{n-1}]` at a point
-- | `pt`, with chunk base `ptN = pt^(2^rounds)`:
-- |
-- |   `a0 + ptN · a1 + ptN^2 · a2 + … + ptN^(n-1) · a_{n-1}`
-- |
-- | Zero for an empty input.
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

type BulletproofBOutput d f =
  { chals :: Vector d f
  , b :: f
  }

-- | The endo-expanded bulletproof challenges and the combined IPA
-- | opening target `b_poly(zeta) + r · b_poly(zetaw)` over them.
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
-- Combined inner product
--------------------------------------------------------------------------------

-- | Input to `combinedInnerProductBatch`: `n` previous proofs
-- | contributing one `b_poly` each, `d` IPA rounds, in the field `f`.
type CombinedInnerProductBatchInput n d f =
  { allEvals :: Evals f
  , publicEvals :: PointEval f
  , ftEval0 :: f
  , ftEval1 :: f
  , oldBulletproofChallenges :: Vector n (Vector d f)
  , xi :: f
  , r :: f
  , zeta :: f
  , zetaw :: f
  }

-- | The batched combined inner product, the Horner fold
-- |
-- |   `sum_i xi^i · (eval_i.zeta + r · eval_i.omegaTimesZeta)`
-- |
-- | Batching order is fixed by the verifier: `b_polys (n)`,
-- | `public_input (1)`, `ft (1)`, `z (1)`, `index (6)`,
-- | `witness (15)`, `coefficient (15)`, `sigma (6)`.
-- |
-- | One chunk per polynomial; chunked callers use
-- | `combinedInnerProductBatchChunked`.
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

-- | Input to `combinedInnerProductBatchChunked`. As
-- | `CombinedInnerProductBatchInput`, except that `allEvals` and
-- | `publicEvals` carry one `PointEval` per chunk; `ftEval0`,
-- | `ftEval1` and the bp challenge polynomials are never chunked.
type CombinedInnerProductBatchChunkedInput n d f =
  { allEvals :: ChunkedEvals f
  , publicEvals :: NonEmptyArray (PointEval f)
  , ftEval0 :: f
  , ftEval1 :: f
  , oldBulletproofChallenges :: Vector n (Vector d f)
  , xi :: f
  , r :: f
  , zeta :: f
  , zetaw :: f
  }

-- | The chunk-aware combined inner product: every polynomial's chunks
-- | are flattened into one list per evaluation point, each list is
-- | xi-folded, and the result is `combine zeta + r · combine zetaw`.
-- |
-- | At `num_chunks = 1` each chunk array is a singleton and this
-- | agrees with `combinedInnerProductBatch`; above that the extra
-- | chunks contribute further xi-weighted terms.
combinedInnerProductBatchChunked
  :: forall n d f
   . Reflectable d Int
  => PrimeField f
  => CombinedInnerProductBatchChunkedInput n d f
  -> f
combinedInnerProductBatchChunked input =
  let
    -- bp polynomials are never chunked: one flat-list element each.
    bPolyZeta = map (\chals -> bPoly chals input.zeta)
      (Array.fromFoldable input.oldBulletproofChallenges)
    bPolyZetaw = map (\chals -> bPoly chals input.zetaw)
      (Array.fromFoldable input.oldBulletproofChallenges)

    all = input.allEvals

    extractChunks
      :: (PointEval f -> f) -> NonEmptyArray (PointEval f) -> Array f
    extractChunks proj nea = map proj (NEA.toArray nea)

    -- The flat list for one evaluation point. Its order is fixed by
    -- the verifier's batching: bp_polys, public_input chunks, ft, z
    -- chunks, index chunks, witness chunks, coeff chunks, sigma
    -- chunks.
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

    -- Horner in xi, right to left; zero for an empty list.
    combine :: Array f -> f
    combine flat =
      case Array.uncons (Array.reverse flat) of
        Just { head, tail } -> foldl (\acc fx -> fx + input.xi * acc) head tail
        Nothing -> zero

  in
    combine (flatAt _.zeta input.ftEval0 bPolyZeta)
      + input.r * combine (flatAt _.omegaTimesZeta input.ftEval1 bPolyZetaw)

--------------------------------------------------------------------------------
-- Scalar derivations
--------------------------------------------------------------------------------

-- | Input to `derivePlonk`.
-- |
-- | * `plonkMinimal` — raw 128-bit challenges, carried forward
-- |   unchanged into the output.
-- | * `w`, `sigma`, `zZeta`, `zOmegaTimesZeta` — recombined
-- |   polynomial evaluations at `(zeta, zeta·omega)`.
-- | * `shifts` — the 7 permutation shift constants of the domain.
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

-- | The derived Plonk scalars — `perm`, `zetaToDomainSize`,
-- | `zetaToSrsLength` — in the caller's shifted-value
-- | representation, with `plonkMinimal`'s raw challenges passed
-- | through.
-- |
-- | One body serves both the Type1 and the Type2 callers: the
-- | `Shifted (F f) sf` constraint resolves against the return-type
-- | annotation at the call site, and that is what picks the output
-- | representation.
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

-- | Input to `ftEval0`. Beyond the `DerivePlonkInput` fields:
-- |
-- | * `pEval0Chunks` — public-input polynomial evaluation chunks at
-- |   `zeta`.
-- | * `vanishesOnZk` — precomputed
-- |   `vanishes_on_zero_knowledge_and_previous_rows`.
-- | * `omegaForLagrange` — the omega power an
-- |   `unnormalized_lagrange_basis` lookup at `{ zkRows, offset }`
-- |   needs.
-- | * `linearizationPoly` — the token stream for the target circuit:
-- |   `Pickles.Linearization.pallas` in the step field,
-- |   `Pickles.Linearization.vesta` in the wrap field.
type FtEval0Input f =
  { plonkMinimal :: PlonkMinimal (F f)
  , allEvals :: Evals f
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

-- | `ft_eval0 = permContribution - pEval0Folded - constantTerm`,
-- | where `pEval0Folded` is the Horner fold of `pEval0Chunks` at
-- | `zeta^(2^srsLengthLog2)` and `constantTerm` is
-- | `linearizationPoly` evaluated in the scalar environment.
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

    result = permRaw - pEval0Folded - constantTerm

    -- Diagnostic trace. The labels pair with the ones the OCaml side
    -- emits; both write to `PICKLES_TRACE_FILE`.
    traceArr lbl arr = Array.foldM
      (\i v -> Trace.field (lbl <> show i) v *> pure (i + 1))
      (0 :: Int)
      arr
    _ = unsafePerformEffect $ do
      Trace.field "ft_eval0.input.alpha" expanded.alpha
      Trace.field "ft_eval0.input.beta" expanded.beta
      Trace.field "ft_eval0.input.gamma" expanded.gamma
      Trace.field "ft_eval0.input.zeta" expanded.zeta
      Trace.field "ft_eval0.input.generator" input.generator
      Trace.field "ft_eval0.input.endo" input.endo
      Trace.field "ft_eval0.env.omega_to_minus_1" omegaToMinus1
      Trace.field "ft_eval0.env.omega_to_zk_plus_1" omegaToZkPlus1
      Trace.field "ft_eval0.env.omega_to_minus_zk_rows" omegaToMinusZkRows
      Trace.field "ft_eval0.env.zk_polynomial" zkPolynomial
      Trace.field "ft_eval0.env.zeta_to_n_minus_1" zetaToNMinus1
      _ <- traceArr "ft_eval0.input.w." (Vector.toUnfoldable (map _.zeta input.allEvals.witnessEvals))
      _ <- traceArr "ft_eval0.input.w_omega." (Vector.toUnfoldable (map _.omegaTimesZeta input.allEvals.witnessEvals))
      _ <- traceArr "ft_eval0.input.sigma." (Vector.toUnfoldable (map _.zeta input.allEvals.sigmaEvals))
      _ <- traceArr "ft_eval0.input.coeff." (Vector.toUnfoldable (map _.zeta input.allEvals.coeffEvals))
      _ <- traceArr "ft_eval0.input.index." (Vector.toUnfoldable (map _.zeta input.allEvals.indexEvals))
      Trace.field "ft_eval0.input.z.zeta" input.allEvals.zEvals.zeta
      Trace.field "ft_eval0.input.z.omegaTimesZeta" input.allEvals.zEvals.omegaTimesZeta
      _ <- traceArr "ft_eval0.input.shifts." (Vector.toUnfoldable input.shifts)
      _ <- traceArr "ft_eval0.peval0_chunks." input.pEval0Chunks
      Trace.field "ft_eval0.peval0_folded" pEval0Folded
      Trace.field "ft_eval0.perm.raw" permRaw
      Trace.field "ft_eval0.constant_term" constantTerm
      Trace.field "ft_eval0.result" result
  in
    result

--------------------------------------------------------------------------------
-- Cross-field reinterpretation
--------------------------------------------------------------------------------

-- | Reinterpret a field element's integer representation in the other
-- | field of the Pasta cycle, for digests and packed limbs that must
-- | appear bit-identically on both. Safe while that integer stays
-- | below the target modulus — true of sponge digests, and of limbs,
-- | each `< 2^64`.
crossFieldDigest :: forall f f'. PrimeField f => PrimeField f' => f -> f'
crossFieldDigest = fromBigInt <<< toBigInt
