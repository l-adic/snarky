-- | In-circuit permutation argument verification for Kimchi/PLONK proofs.
-- |
-- | This module computes the permutation argument contribution to the
-- | linearization check. The full verification equation is:
-- |   ft_eval0 = perm_contribution - constant_term + boundary_quotient = 0
-- |
-- | The gate constraint module (Phase 2.1) handles `constant_term`.
-- | This module handles the permutation terms.
-- |
-- | Reference: mina/src/lib/pickles/plonk_checks/plonk_checks.ml
-- | See: https://o1-labs.github.io/mina-book/crypto/plonk/maller_15.html
module Pickles.PlonkChecks.Permutation
  ( PermutationInput
  , permScalar
  , permScalarCircuit
  , permContribution
  , permAlpha0
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Foldable (foldM, foldl)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, zipWith, (!!))
import Data.Vector as Vector
import JS.BigInt (fromInt)
import Pickles.Linearization.FFI (PointEval)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky)
import Snarky.Circuit.DSL.Field (pow_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
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

-- | Compute the permutation contribution to ft_eval0 (field-level only).
-- | This includes both product terms and the boundary quotient.
-- | Note: uses division, so this cannot be directly computed in-circuit
-- | without additional witness variables.
-- |
-- | Reference: ft_eval0 in plonk_checks.ml
permContribution :: forall f. PrimeField f => PermutationInput f -> f
permContribution input =
  let
    alphaPow21 = pow input.alpha (fromInt permAlpha0)
    alphaPow22 = alphaPow21 * input.alpha
    alphaPow23 = alphaPow22 * input.alpha

    -- Term 1: product with sigma evaluations
    -- init = (w[6] + gamma) * z(zeta*omega) * alpha^21 * zkp
    -- fold: ∏_{i=0}^{5}(beta*sigma_i + w_i + gamma) * init
    w6 = input.w !! unsafeFinite 6
    term1Init = (w6 + input.gamma) * input.z.omegaTimesZeta * alphaPow21 * input.zkPolynomial
    wSigma = zipWith Tuple (Vector.take @6 input.w) input.sigma
    term1 = foldl
      (\acc (Tuple wi si) -> (input.beta * si + wi + input.gamma) * acc)
      term1Init
      wSigma

    -- Term 2: product with shifts (subtracted)
    -- init = alpha^21 * zkp * z(zeta)
    -- fold: ∏_{i=0}^{6}(gamma + beta*zeta*shift_i + w_i) * init
    term2Init = alphaPow21 * input.zkPolynomial * input.z.zeta
    wShifts = zipWith Tuple input.w input.shifts
    term2 = foldl
      (\acc (Tuple wi si) -> acc * (input.gamma + input.beta * input.zeta * si + wi))
      term2Init
      wShifts

    -- Boundary quotient:
    -- nominator = ((zeta^n-1) * alpha^22 * (zeta - omega^{-zkRows})
    --           + (zeta^n-1) * alpha^23 * (zeta - 1)) * (1 - z(zeta))
    -- denominator = (zeta - omega^{-zkRows}) * (zeta - 1)
    zetaMinusOmega = input.zeta - input.omegaToMinusZkRows
    zetaMinus1 = input.zeta - one
    nominator =
      ( input.zetaToNMinus1 * alphaPow22 * zetaMinusOmega
          + input.zetaToNMinus1 * alphaPow23 * zetaMinus1
      )
        * (one - input.z.zeta)
    denominator = zetaMinusOmega * zetaMinus1
    boundary = nominator / denominator
  in
    term1 - term2 + boundary

-------------------------------------------------------------------------------
-- | Circuit-level computation
-------------------------------------------------------------------------------

-- | Compute the perm scalar in-circuit.
-- | Uses the Semiring/Ring instances for `Snarky c t m (FVar f)` to express
-- | the arithmetic naturally.
-- |
-- | perm = -(z(zeta*omega) * beta * alpha^21 * zkp * ∏_{i=0}^{5}(gamma + beta*sigma_i + w_i))
permScalarCircuit
  :: forall f t m
   . PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => PermutationInput (FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
permScalarCircuit input = do
  -- alpha^21
  alphaPow21 <- pow_ input.alpha permAlpha0

  -- init = z.omegaTimesZeta * beta * alpha^21 * zkp
  init' <- pure input.z.omegaTimesZeta * pure input.beta
    * pure alphaPow21
    * pure input.zkPolynomial

  -- Fold: acc * (gamma + beta * sigma_i + w_i) for i = 0..5
  let wSigma = zipWith Tuple (Vector.take @6 input.w) input.sigma
  result <- foldM
    ( \acc (Tuple wi si) -> do
        -- beta * sigma_i requires a multiplication constraint
        betaSigma <- pure input.beta * pure si
        let term = CVar.add_ (CVar.add_ input.gamma betaSigma) wi
        pure acc * pure term
    )
    init'
    wSigma

  -- Negate
  pure (CVar.negate_ result)

