-- | In-circuit permutation argument verification for Kimchi/PLONK proofs.
-- |
-- | This module computes the permutation argument contribution to the
-- | linearization check. The full verification equation is:
-- |   ft_eval0 = perm_contribution - constant_term + boundary_quotient = 0
-- |
-- | The gate-constraint module handles `constant_term`; this module
-- | handles the permutation terms.
-- |
-- | Reference: mina/src/lib/pickles/plonk_checks/plonk_checks.ml
-- | See: https://o1-labs.github.io/mina-book/crypto/plonk/maller_15.html
module Pickles.PlonkChecks.Permutation
  ( PermutationInput
  , permScalar
  , permContribution
  , permContributionCircuit
  , permScalarCircuit
  , permAlpha0
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (unsafeFinite)
import Data.Foldable (foldM, foldl)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, zipWith, (!!))
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import JS.BigInt (fromInt)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Trace as Trace
import Snarky.Circuit.CVar (negate_)
import Snarky.Circuit.DSL (class BasicSystem, FVar, Snarky, add_, const_, div_, label, mul_, sub_)
import Snarky.Curves.Class (class PrimeField, pow)

-------------------------------------------------------------------------------
-- | Constants
-------------------------------------------------------------------------------

-- | The offset of alpha powers for the permutation argument.
-- | See: https://github.com/o1-labs/proof-systems/blob/516b16fc9b0fdcab5c608cd1aea07c0c66b6675d/kimchi/src/index.rs#L190
permAlpha0 :: Int
permAlpha0 = 21

-------------------------------------------------------------------------------
-- | Input Types
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- | Field-level (pure) computations
-------------------------------------------------------------------------------

-- | Compute the perm scalar at the field level.
-- | This is the coefficient of z(x) in the full linearization polynomial.
-- |
-- | perm = -(z(zeta*omega) * beta * alpha^21 * zkp * ∏_{i=0}^{5}(gamma + beta*sigma_i + w_i))
-- |
-- | Reference: derive_plonk in plonk_checks.ml
permScalar :: forall f. PrimeField f => PermutationInput f -> f
permScalar input =
  let
    alphaPow21 = pow input.alpha (fromInt permAlpha0)
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
    alphaPow21 = pow input.alpha (fromInt permAlpha0)
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

-------------------------------------------------------------------------------
-- | In-circuit computation
-------------------------------------------------------------------------------

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
permScalarCircuit { w, sigma, zOmega, beta, gamma, zkPolynomial, alphaPow21 } = do
  init' <- mul_ zOmega beta >>= \t -> mul_ t alphaPow21 >>= \t' -> mul_ t' zkPolynomial
  result <- foldM
    ( \acc (Tuple wi si) -> do
        betaSigma <- mul_ beta si
        mul_ acc (add_ (add_ gamma betaSigma) wi)
    )
    init'
    (zipWith Tuple w sigma)
  pure (negate_ result)
