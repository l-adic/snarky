-- | The scalar side of the kimchi verifier, as pickles defers it: the
-- | evaluation records and their chunk recombination, the domain
-- | scalars, the gate-constraint environment the linearization
-- | interpreter reads, the permutation argument, the combined inner
-- | product, and the fr-sponge schedule deriving `xi` and `r`.
-- |
-- | Both finalize-other-proof circuits are built from these pieces:
-- | `Pickles.Step.FinalizeOtherProof` and
-- | `Pickles.Wrap.FinalizeOtherProof`. The pure reference prover
-- | (`Pickles.Prove.Pure.*`) and the out-of-circuit verifier
-- | (`Pickles.Verify`) consume the same records.
module Pickles.PlonkChecks
  ( -- * Evaluation records
    --
    -- The records themselves are `Pickles.Types.Evals` and
    -- `Pickles.Types.ChunkedEvals`; these operate on them.
    extractEvalFields
  , extractChunkedEvalFields
  , absorbEvals
  , absorbChunkedEvals
  -- * Chunk recombination
  , collapsePointEval
  , collapseChunkedEvals
  , CollapsedColumns
  , collapseChunkedEvalsCircuit
  , hornerChunks
  , singleChunkEvals
  , padChunkedEvals
  , mapChunkedEvals
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
  --
  -- `EvalOpt` is exported without its constructors:
  -- `buildEvalList`/`buildEvalListUnmasked` produce the list and
  -- `combinedInnerProduct` consumes it.
  , EvalOpt
  , buildEvalList
  , buildEvalListChunked
  , buildEvalListUnmasked
  , combinedInnerProduct
  -- * The fr-sponge schedule
  , challengeDigest
  , maskedChallengeDigest
  , squeezeXiR
  , squeezeXiRChunked
  , frSpongeChallengesPureChunked
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
import Pickles.Sponge (class MonadSponge, PureSpongeM, absorb, evalPureSpongeM, evalSpongeM, initialSponge, initialSpongeCircuit, liftSnarky, squeeze, squeezeScalarChallenge, squeezeScalarChallengePure)
import Pickles.Trace as Trace
import Pickles.Types (ChunkedEvals, Evals)
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

-- | Extract the 43 always-present evaluation fields in CIP order:
-- | z(1), index(6), witness(15), coeff(15), sigma(6).
extractEvalFields :: forall f. (PointEval f -> f) -> Evals f -> Vector 43 f
extractEvalFields proj evals =
  proj evals.zEvals :<
    map proj evals.indexEvals
      `Vector.append` map proj evals.witnessEvals
      `Vector.append` map proj evals.coeffEvals
      `Vector.append` map proj evals.sigmaEvals

-- | Absorb all polynomial evaluations into the sponge.
-- |
-- | The order is fixed by the verifier's transcript: `ftEval1`, public,
-- | `z`, index (6), witness (15), coeff (15), sigma (6).
absorbEvals
  :: forall f m
   . MonadSponge f m
  => Evals f
  -> m Unit
absorbEvals evals = do
  absorb evals.ftEval1
  absorbPointEval evals.publicEvals
  absorbPointEval evals.zEvals
  traverse_ absorbPointEval evals.indexEvals
  traverse_ absorbPointEval evals.witnessEvals
  traverse_ absorbPointEval evals.coeffEvals
  traverse_ absorbPointEval evals.sigmaEvals

-- | `absorbEvals` over chunked evaluations: the same columns in the
-- | same order, each column's `zeta` chunks and then its
-- | `omegaTimesZeta` chunks.
absorbChunkedEvals
  :: forall f m
   . MonadSponge f m
  => ChunkedEvals f
  -> m Unit
absorbChunkedEvals evals = do
  absorb evals.ftEval1
  absorbChunkedPointEval evals.publicEvals
  absorbChunkedPointEval evals.zEvals
  traverse_ absorbChunkedPointEval evals.indexEvals
  traverse_ absorbChunkedPointEval evals.witnessEvals
  traverse_ absorbChunkedPointEval evals.coeffEvals
  traverse_ absorbChunkedPointEval evals.sigmaEvals
  where
  absorbChunkedPointEval chunks = do
    traverse_ (absorb <<< _.zeta) chunks
    traverse_ (absorb <<< _.omegaTimesZeta) chunks

-- | Absorb a `PointEval`: `zeta` then `omegaTimesZeta`.
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
-- A polynomial too large for one SRS-sized slice is committed as chunks
-- `e[0], …, e[n-1]` with
--   P(x) = e[0] + e[1]·x^N + … + e[n-1]·x^((n-1)·N)
-- for `N = 2^rounds` the SRS-poly size. These recombine the chunks at
-- an evaluation point `pt` into the single scalar `P(pt)`. Background:
-- `docs/chunking.md`.

-- | Horner combine of `n` chunked evaluations: `Σ_{i<n} e[i] * ptN^i`,
-- | where `ptN = pt^(2^rounds)`. At `n = 1` the identity.
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

-- | `x^(2^n)`, by `n` squarings.
squareN :: forall f. Semiring f => Int -> f -> f
squareN n x = go n x
  where
  go 0 acc = acc
  go i acc = go (i - 1) (acc * acc)

-- | Collapse a chunked `PointEval` — one `{ zeta, omegaTimesZeta }` per
-- | chunk — into a single one, Horner-combining each component at its
-- | own evaluation point.
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

-- | Map over every evaluation of a `ChunkedEvals`.
mapChunkedEvals :: forall a b. (a -> b) -> ChunkedEvals a -> ChunkedEvals b
mapChunkedEvals f e =
  { ftEval1: f e.ftEval1
  , publicEvals: map pe e.publicEvals
  , zEvals: map pe e.zEvals
  , indexEvals: map (map pe) e.indexEvals
  , witnessEvals: map (map pe) e.witnessEvals
  , coeffEvals: map (map pe) e.coeffEvals
  , sigmaEvals: map (map pe) e.sigmaEvals
  }
  where
  pe p = { zeta: f p.zeta, omegaTimesZeta: f p.omegaTimesZeta }

-- | One-chunk `ChunkedEvals`: each evaluation as its own single
-- | chunk. `collapseChunkedEvals` inverts it at any point.
singleChunkEvals :: forall f. Evals f -> ChunkedEvals f
singleChunkEvals e =
  { ftEval1: e.ftEval1
  , publicEvals: NEA.singleton e.publicEvals
  , zEvals: NEA.singleton e.zEvals
  , indexEvals: map NEA.singleton e.indexEvals
  , witnessEvals: map NEA.singleton e.witnessEvals
  , coeffEvals: map NEA.singleton e.coeffEvals
  , sigmaEvals: map NEA.singleton e.sigmaEvals
  }

-- | `ChunkedEvals` padded with zero chunks to `numChunks` per column.
padChunkedEvals :: forall f. Semiring f => Int -> ChunkedEvals f -> ChunkedEvals f
padChunkedEvals numChunks e =
  { ftEval1: e.ftEval1
  , publicEvals: pad e.publicEvals
  , zEvals: pad e.zEvals
  , indexEvals: map pad e.indexEvals
  , witnessEvals: map pad e.witnessEvals
  , coeffEvals: map pad e.coeffEvals
  , sigmaEvals: map pad e.sigmaEvals
  }
  where
  pad chunks =
    NEA.appendArray chunks
      (Array.replicate (numChunks - NEA.length chunks) { zeta: zero, omegaTimesZeta: zero })

-- | Collapse every chunked evaluation of a `ChunkedEvals` via
-- | `collapsePointEval`, giving one value per polynomial.
-- |
-- | The combined inner product does not go through here: it xi-batches
-- | the chunked form directly.
collapseChunkedEvals
  :: forall f
   . Semiring f
  => { rounds :: Int, zeta :: f, zetaOmega :: f }
  -> ChunkedEvals f
  -> Evals f
collapseChunkedEvals ctx chunked =
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
-- The domain-dependent scalars of finalize-other-proof, shared by the
-- step and wrap verifiers: the negative powers of the domain generator
-- and the permutation vanishing polynomial, plus the step side's
-- known-domain selection and vanishing polynomial.

-- | `ω⁻¹`, `ω^{-(zkRows-1)}` and `ω^{-zkRows}` for a domain generator
-- | `ω`.
type OmegaPowers f =
  { omegaToMinus1 :: FVar f
  , omegaToZkPlus1 :: FVar f
  , omegaToZk :: FVar f
  }

-- | The `OmegaPowers` of a domain generator: one inverse, one squaring,
-- | then `zkRows − 3` further multiplications by `ω⁻¹` — none at the
-- | default `zkRows = 3` — reaching `ω^{-(zkRows-1)}`, and one more for
-- | `ω^{-zkRows}`. The row sequence is part of the circuit's shape.
-- |
-- | `zkRows ≥ 3`, kimchi's minimum (`zkRowsByDefault`), is required:
-- | below it `ω^{-(zkRows-1)}` is not distinct from the other two.
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
-- | `(ζ − ω⁻¹)(ζ − ω^{-(zkRows-1)})(ζ − ω^{-zkRows})`, in two rows.
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

-- | Which known domain is the previous proof's: one `equals_` of the
-- | runtime `domain_log2` against each domain's. The rows are emitted
-- | last-to-first; the result is in domain order.
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

-- | `ζⁿ − 1` for the selected known domain: the table `ζ^{2^i}` for `i`
-- | up to the largest domain's log2 by squaring, the entry at each
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

-- | `[x, x², x⁴, …, x^(2^maxLog2)]`, by `maxLog2` Square rows.
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
-- `EvalPoint` and a challenge record; these two build them from the
-- proof's evaluations.

-- | The `EvalPoint` the linearization interpreter reads: witness,
-- | coefficient and gate-selector lookups resolved against the proof's
-- | evaluation vectors. Every lookup-argument column returns
-- | `defaultVal`.
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
          -- The index column order is fixed by the kimchi verifier:
          -- Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul,
          -- EndoMulScalar. No other gate type is supported.
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

-- | The challenge record the linearization interpreter reads.
-- |
-- | The linearization only ever asks for two unnormalized Lagrange
-- | bases, `{ zkRows: false, offset: 0 }` and
-- | `{ zkRows: true, offset: -1 }`; anything else falls back to the
-- | first.
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
-- The permutation contribution to the linearization check
--  ft_eval0 = perm_contribution − constant_term + boundary_quotient = 0
-- where the gate-constraint environment above supplies `constant_term`.
--
-- See: https://o1-labs.github.io/mina-book/crypto/plonk/maller_15.html

-- | The offset of the alpha powers reserved for the permutation
-- | argument, fixed by kimchi:
-- | https://github.com/o1-labs/proof-systems/blob/516b16fc9b0fdcab5c608cd1aea07c0c66b6675d/kimchi/src/index.rs#L190
permAlpha0 :: Int
permAlpha0 = 21

-- | The inputs to the permutation argument, at `a = f` out of circuit
-- | and `a = FVar f` in circuit. Kimchi has 7 permutation columns, and
-- | the proof carries `PERMUTS - 1 = 6` sigma evaluations.
type PermutationInput a =
  { -- the first 7 witness evaluations at `zeta`
    w :: Vector 7 a
  , -- sigma evaluations at `zeta`
    sigma :: Vector 6 a
  , -- the permutation polynomial
    z :: PointEval a
  , -- one domain shift per permutation column
    shifts :: Vector 7 a
  , -- protocol challenges
    alpha :: a
  , beta :: a
  , gamma :: a
  , -- `zkPolynomial` above, at `zeta`
    zkPolynomial :: a
  , -- `zeta^n - 1`, the domain vanishing polynomial at `zeta`
    zetaToNMinus1 :: a
  , -- `omega^{-zkRows}`
    omegaToMinusZkRows :: a
  , -- the evaluation point
    zeta :: a
  }

-- | The coefficient of `z(x)` in the linearization polynomial, out of
-- | circuit:
-- |
-- |   -(z(ζω) · β · α²¹ · zkp · ∏_{i<6} (γ + β·σ_i + w_i))
permScalar :: forall f. PrimeField f => PermutationInput f -> f
permScalar input =
  let
    alphaPow21 = pow input.alpha (BigInt.fromInt permAlpha0)
    init = input.z.omegaTimesZeta * input.beta * alphaPow21 * input.zkPolynomial
    wSigma = zipWith Tuple (Vector.take @6 input.w) input.sigma
    product = foldl
      (\acc (Tuple wi si) -> acc * (input.gamma + input.beta * si + wi))
      init
      wSigma
  in
    negate product

-- | The permutation contribution to `ft_eval0`, out of circuit: both
-- | product terms and the boundary quotient. The in-circuit twin is
-- | `permContributionCircuit`, where the division is a witnessed
-- | inverse.
permContribution :: forall f. PrimeField f => PermutationInput f -> f
permContribution input =
  let
    alphaPow21 = pow input.alpha (BigInt.fromInt permAlpha0)
    alphaPow22 = alphaPow21 * input.alpha
    alphaPow23 = alphaPow22 * input.alpha

    w6 = input.w !! unsafeFinite @7 6
    term1Init = (w6 + input.gamma) * input.z.omegaTimesZeta * alphaPow21 * input.zkPolynomial
    wSigma = zipWith Tuple (Vector.take @6 input.w) input.sigma

    -- `scanl`, not `foldl`: the trace below wants the intermediates.
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

    -- Trace points for the transcript diff; see `Pickles.Trace`.
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

-- | The in-circuit twin of `permContribution`, with the public-input
-- | evaluation subtracted between the two products as `ft_eval0` does:
-- |
-- |   term1 - pEval0 - term2 + boundary
-- |
-- | The multiplication order is part of the circuit's shape: `β·ζ` is
-- | recomputed at each shift step, and the boundary quotient emits its
-- | `α²³` term before its `α²²` term. The alpha powers come from the
-- | caller's table (`precomputeAlphaPowers`), leaving `input.alpha`
-- | unused, and the caller subtracts the constant term. The labels
-- | scope the mul chain for the circuit diff.
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

-- | The in-circuit twin of `permScalar`:
-- |
-- |   -(z(ζω) · β · α²¹ · zkp · ∏_{i<6} (γ + β·σ_i + w_i))
-- |
-- | The multiplication order is part of the circuit's shape; `α²¹`
-- | comes from the caller's table.
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

-- | An entry of the Horner fold: always present (`EvalJust`) or folded
-- | in only when a bit is set (`EvalMaybe`).
data EvalOpt f
  = EvalJust (FVar f)
  | EvalMaybe (BoolVar f) (FVar f)

-- | Horner fold of a flat evaluation list under the batching scalar
-- | `xi`, from the last entry back: `acc' = fx + xi * acc`. A masked
-- | entry leaves `acc` untouched when its bit is false.
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

-- | The flat evaluation list for `combinedInnerProduct`. The order is
-- | fixed by the batching: `sgEvals` (n), public input, `ftEval`, then
-- | the 43 fields of `extractEvalFields`.
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

-- | `buildEvalList` with every `sgEval` always present: the wrap
-- | verifier has no proofs-verified mask.
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

-- | `buildEvalList` over chunked evaluations: each column contributes
-- | all its chunks, in chunk order, where `buildEvalList` has its one
-- | value.
buildEvalListChunked
  :: forall n f
   . { sgEvals :: Vector n (Tuple (BoolVar f) (FVar f))
     , publicInput :: NonEmptyArray (FVar f)
     , ftEval :: FVar f
     , evals :: Vector 43 (NonEmptyArray (FVar f))
     }
  -> NonEmptyArray (EvalOpt f)
buildEvalListChunked x =
  let
    sgEvals = map (\(Tuple keep eval) -> EvalMaybe keep eval) x.sgEvals
    others = NEA.snoc (map EvalJust x.publicInput) (EvalJust x.ftEval)
    evals = map EvalJust $ NEA.concat $ NEA.fromFoldable1 x.evals
  in
    NEA.prependArray (Vector.toUnfoldable sgEvals)
      $ NEA.concat
      $
        NEA.cons' others [ evals ]

-- | `extractEvalFields` over chunked evaluations: the same 43 columns,
-- | each as its chunks at one evaluation point.
extractChunkedEvalFields
  :: forall f
   . (PointEval f -> f)
  -> ChunkedEvals f
  -> Vector 43 (NonEmptyArray f)
extractChunkedEvalFields proj evals =
  map proj evals.zEvals :<
    map (map proj) evals.indexEvals
      `Vector.append` map (map proj) evals.witnessEvals
      `Vector.append` map (map proj) evals.coeffEvals
      `Vector.append` map (map proj) evals.sigmaEvals

-- | The 43 non-public columns of a `ChunkedEvals`, each recombined to
-- | one evaluation per point.
type CollapsedColumns f =
  { witnessEvals :: Vector 15 (PointEval f)
  , coeffEvals :: Vector 15 (PointEval f)
  , zEvals :: PointEval f
  , sigmaEvals :: Vector 6 (PointEval f)
  , indexEvals :: Vector 6 (PointEval f)
  }

-- | `collapseChunkedEvals` in circuit, for the 43 non-public columns:
-- | each column's chunks recombined by Horner at `zetaPow` and
-- | `zetaOmegaPow`, the two evaluation points raised to the SRS length.
-- | A one-chunk column costs nothing; each further chunk costs one
-- | multiplication.
-- |
-- | The emission order is fixed: index, sigma, `z`, coefficients,
-- | witness, each vector from its last column to its first, and within
-- | a column `omegaTimesZeta` before `zeta`.
collapseChunkedEvalsCircuit
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => { zetaPow :: FVar f, zetaOmegaPow :: FVar f }
  -> ChunkedEvals (FVar f)
  -> Snarky f c r (CollapsedColumns (FVar f))
collapseChunkedEvalsCircuit { zetaPow, zetaOmegaPow } chunked = do
  indexEvals <- traverseRev chunked.indexEvals
  sigmaEvals <- traverseRev chunked.sigmaEvals
  zEvals <- collapse chunked.zEvals
  coeffEvals <- traverseRev chunked.coeffEvals
  witnessEvals <- traverseRev chunked.witnessEvals
  pure { witnessEvals, coeffEvals, zEvals, sigmaEvals, indexEvals }
  where
  collapse chunks = do
    omegaTimesZeta <- hornerChunks zetaOmegaPow (map _.omegaTimesZeta chunks)
    zeta <- hornerChunks zetaPow (map _.zeta chunks)
    pure { zeta, omegaTimesZeta }

  traverseRev
    :: forall n
     . Vector n (NonEmptyArray (PointEval (FVar f)))
    -> Snarky f c r (Vector n (PointEval (FVar f)))
  traverseRev v = Vector.reverse <$> traverse collapse (Vector.reverse v)

-- | `∑ chunks[i] · pt^i`, by Horner from the last chunk down.
hornerChunks
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> NonEmptyArray (FVar f)
  -> Snarky f c r (FVar f)
hornerChunks pt chunks =
  let
    { init, last } = NEA.unsnoc chunks
  in
    foldM
      ( \acc fx -> do
          ptAcc <- mul_ pt acc
          pure (add_ fx ptAcc)
      )
      last
      (Array.reverse init)

-- | The combined inner product `combine(zeta) + r * combine(zetaw)`.
-- | The zetaw fold is emitted first.
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
-- | The fr-sponge schedule of finalize-other-proof
-------------------------------------------------------------------------------

-- | The digest of the previous proofs' bulletproof challenges: a fresh
-- | sponge absorbing every challenge, squeezed once.
challengeDigest
  :: forall n d f r
   . PoseidonField f
  => PrimeField f
  => Vector n (Vector d (FVar f))
  -> Snarky f (KimchiConstraint f) r (FVar f)
challengeDigest prevChallenges = evalSpongeM initialSpongeCircuit do
  traverse_ (traverse_ absorb) prevChallenges
  squeeze

-- | `challengeDigest` under the proofs-verified mask: an `OptSponge`
-- | absorbing each challenge only where its proof's slot is real.
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

-- | The fr-sponge schedule: absorb the sponge digest before
-- | evaluations, then the challenge digest — computed here, between the
-- | two absorbs — then every evaluation; squeeze `xi` and `r` as
-- | 128-bit scalar challenges.
-- |
-- | Both are squeezed with their low 128 bits range-checked, on
-- | either side, so the comparison of `xi` with its claim is exact.
squeezeXiR
  :: forall f cr
   . PoseidonField f
  => PrimeField f
  => FieldSizeInBits f 255
  => { spongeDigestBeforeEvaluations :: FVar f
     , challengeDigest :: Snarky f (KimchiConstraint f) cr (FVar f)
     , allEvals :: Evals (FVar f)
     , endo :: FVar f
     }
  -> Snarky f (KimchiConstraint f) cr { xi :: SizedF 128 (FVar f), r :: SizedF 128 (FVar f) }
squeezeXiR p = squeezeXiRChunked
  { spongeDigestBeforeEvaluations: p.spongeDigestBeforeEvaluations
  , challengeDigest: p.challengeDigest
  , chunkedEvals: singleChunkEvals p.allEvals
  , endo: p.endo
  }

-- | `squeezeXiR` over evaluations of any chunk count: every chunk is
-- | absorbed, as the verifier's transcript absorbs them.
squeezeXiRChunked
  :: forall f cr
   . PoseidonField f
  => PrimeField f
  => FieldSizeInBits f 255
  => { spongeDigestBeforeEvaluations :: FVar f
     , challengeDigest :: Snarky f (KimchiConstraint f) cr (FVar f)
     , chunkedEvals :: ChunkedEvals (FVar f)
     , endo :: FVar f
     }
  -> Snarky f (KimchiConstraint f) cr { xi :: SizedF 128 (FVar f), r :: SizedF 128 (FVar f) }
squeezeXiRChunked p = evalSpongeM initialSpongeCircuit do
  absorb p.spongeDigestBeforeEvaluations
  digest <- liftSnarky p.challengeDigest
  absorb digest
  absorbChunkedEvals p.chunkedEvals
  xi <- squeezeScalarChallenge { endo: p.endo }
  r <- squeezeScalarChallenge { endo: p.endo }
  pure { xi, r }

-- | Input for the out-of-circuit fr-sponge. The absorption order is
-- | fixed by the protocol: `fqDigest`, `prevChallengeDigest`,
-- | `ftEval1`, the public evals, then the polynomial evals as `z`,
-- | selectors (6), witness (15), coefficients (15), sigma (6).
type FrSpongeInput f =
  { evals :: Evals f
  , fqDigest :: f -- ^ the fq-sponge digest before the fr-sponge
  , prevChallengeDigest :: f -- ^ zero in the base case
  , endo :: f -- ^ the endoscalar coefficient `endo_r`
  }

-- | The fr-sponge challenges in both forms: the raw 128-bit challenges,
-- | which the deferred-values checks compare, and their endo
-- | expansions, which the combined inner product uses.
type FrSpongeChallenges f =
  { rawXi :: SizedF 128 f
  , xi :: f -- ^ the endo-expanded polyscale
  , rawR :: SizedF 128 f
  , evalscale :: f -- ^ the endo-expanded evalscale
  }

-- | The out-of-circuit twin of `squeezeXiR`: replay the fr-sponge and
-- | return both the raw 128-bit challenges and their endo expansions.
frSpongeChallengesPure
  :: forall f
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => FrSpongeInput f
  -> FrSpongeChallenges f
frSpongeChallengesPure input =
  evalPureSpongeM initialSponge do
    absorb input.fqDigest
    absorb input.prevChallengeDigest

    absorb input.evals.ftEval1

    absorbPointEval input.evals.publicEvals

    absorbEvaluationsPure input.evals

    rawXi <- squeezeScalarChallengePure

    rawR <- squeezeScalarChallengePure

    let
      xi = toFieldPure (coerceViaBits rawXi) input.endo
      evalscale = toFieldPure (coerceViaBits rawR) input.endo

    pure { rawXi, xi, rawR, evalscale }

-- | `frSpongeChallengesPure` over evaluations of any chunk count: every
-- | chunk is absorbed, as the verifier's transcript absorbs them.
frSpongeChallengesPureChunked
  :: forall f
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => { evals :: ChunkedEvals f, fqDigest :: f, prevChallengeDigest :: f, endo :: f }
  -> FrSpongeChallenges f
frSpongeChallengesPureChunked input =
  evalPureSpongeM initialSponge do
    absorb input.fqDigest
    absorb input.prevChallengeDigest
    absorbChunkedEvals input.evals
    rawXi <- squeezeScalarChallengePure
    rawR <- squeezeScalarChallengePure
    let
      xi = toFieldPure (coerceViaBits rawXi) input.endo
      evalscale = toFieldPure (coerceViaBits rawR) input.endo
    pure { rawXi, xi, rawR, evalscale }

-- | Absorb the `z`, selector, witness, coefficient and sigma
-- | evaluations in transcript order. Unlike `absorbEvals` this skips
-- | `ftEval1` and the public evals, absorbed earlier by
-- | `frSpongeChallengesPure`.
absorbEvaluationsPure
  :: forall f
   . PoseidonField f
  => Evals f
  -> PureSpongeM f Unit
absorbEvaluationsPure input = do
  absorbPointEval input.zEvals
  traverse_ absorbPointEval input.indexEvals
  traverse_ absorbPointEval input.witnessEvals
  traverse_ absorbPointEval input.coeffEvals
  traverse_ absorbPointEval input.sigmaEvals
