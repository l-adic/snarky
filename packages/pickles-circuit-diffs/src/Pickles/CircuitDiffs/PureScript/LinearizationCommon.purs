module Pickles.CircuitDiffs.PureScript.LinearizationCommon
  ( linearizationCircuitM
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Int (pow) as Int
import Data.Vector (Vector, (!!))
import Pickles.Linearization.Env (CurrOrNext(..), GateType(..)) as Env
import Pickles.Linearization.Env (EnvM, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI, domainGenerator)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (PolishToken)
import Poseidon (class PoseidonField)
import Snarky.Circuit.CVar (CVar(..), const_)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, mul_, pow_, sub_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class HasEndo, class PrimeField)

-- | Circuit that evaluates the linearization polynomial using the monadic
-- | interpreter with compact Store/Load token stream:
-- | - 90 input fields (matching OCaml dump_circuit_impl.ml layout)
-- | - Precomputed alpha powers via successive multiplication
-- | - Domain values computed from zeta (omega constants for lagrange basis)
-- | - Monadic interpreter (evaluateM) with peephole alpha optimization
linearizationCircuitM
  :: forall f f' g t m
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => LinearizationFFI f g
  => Int -- ^ domainLog2
  -> Array PolishToken
  -> Vector 90 (FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
linearizationCircuitM domLog2 tokens inputs = do
  let
    -- Unpack 90 inputs matching OCaml layout:
    -- 0-29: witness evals (15 pairs of (zeta, zetaw))
    -- 30-59: coefficient evals (15 pairs of (zeta, zetaw))
    -- 60-61: z eval (unused in constant_term)
    -- 62-73: s evals (6 pairs, unused in constant_term)
    -- 74-85: selector evals (6 pairs: generic, poseidon, completeadd, vbm, emul, emulscalar)
    -- 86: alpha, 87: beta, 88: gamma, 89: zeta
    at i = inputs !! unsafeFinite i

    -- Witness evals: 15 pairs at indices 0-29
    witnessEval row col =
      let
        base = 2 * getFinite col
      in
        case row of
          Env.Curr -> at base
          Env.Next -> at (base + 1)

    -- Coefficient evals: 15 pairs at indices 30-59
    -- OCaml treats coefficients as pairs (zeta, zetaw) but we only use zeta
    coeffEval col = at (30 + 2 * getFinite col)

    -- Selector evals: 6 pairs at indices 74-85
    -- Order: Generic=0, Poseidon=1, CompleteAdd=2, VarBaseMul=3, EndoMul=4, EndoMulScalar=5
    selectorEval row gt =
      let
        idx = case gt of
          Env.Generic -> 0
          Env.Poseidon -> 1
          Env.CompleteAdd -> 2
          Env.VarBaseMul -> 3
          Env.EndoMul -> 4
          Env.EndoMulScalar -> 5
          _ -> 0 -- Unsupported gates default to generic
        base = 74 + 2 * idx
      in
        case row of
          Env.Curr -> at base
          Env.Next -> at (base + 1)

    alpha = at 86
    beta = at 87
    gamma = at 88
    zeta = at 89

    -- Build eval point using direct lookups
    evalPoint =
      { witness: \row col -> witnessEval row col
      , coefficient: \col -> coeffEval col
      , index: \row gt -> selectorEval row gt
      , lookupAggreg: \_ -> Const zero
      , lookupSorted: \_ _ -> Const zero
      , lookupTable: \_ -> Const zero
      , lookupRuntimeTable: \_ -> Const zero
      , lookupRuntimeSelector: \_ -> Const zero
      , lookupKindIndex: \_ -> Const zero
      }

    -- Domain generator is a constant (from FFI)
    gen = domainGenerator @f domLog2

    -- All omega values are constants (no circuit constraints)
    -- omega^(-1) = 1/gen (constant fold)
    omegaToMinus1 = recip gen
    -- omega^(n - zk_rows - 1) = omega^(n-4) = omega^(-4) since omega^n = 1
    -- = (omega^(-1))^4
    omegaToMinus4 = omegaToMinus1 * omegaToMinus1 * omegaToMinus1 * omegaToMinus1
    -- omega^(n - zk_rows) = omega^(-3)
    omegaToMinus3 = omegaToMinus1 * omegaToMinus1 * omegaToMinus1
    -- omega^(n - zk_rows + 1) = omega^(-2)
    omegaToMinus2 = omegaToMinus1 * omegaToMinus1

    -- Omega constant lookup for unnormalized lagrange basis
    -- Matches OCaml's unnormalized_lagrange_basis omega resolution
    omegaForLagrange { zkRows: zk, offset } =
      if not zk && offset == 0 then const_ one
      else if zk && offset == (-1) then const_ omegaToMinus4
      else if not zk && offset == 1 then const_ gen
      else if not zk && offset == (-1) then const_ omegaToMinus1
      else if not zk && offset == (-2) then const_ omegaToMinus2
      else if zk && offset == 0 then const_ omegaToMinus3
      else const_ one

  -- 1. Precompute alpha powers (69 R1CS constraints for successive multiplication)
  alphaPowers <- precomputeAlphaPowers alpha

  -- 2. Eager zk_polynomial = (zeta - ω⁻¹)(zeta - ω⁻²)(zeta - ω⁻³)
  -- Matches OCaml plonk_checks.ml:272-279
  _zkPoly <- do
    t1 <- mul_ (zeta `sub_` const_ omegaToMinus1) (zeta `sub_` const_ omegaToMinus2)
    mul_ t1 (zeta `sub_` const_ omegaToMinus3)

  -- 3. Eager zeta_to_n_minus_1 = zeta^(2^domainLog2) - 1
  -- Matches OCaml plonk_checks.ml:294 (separate from the lazy binding at :281)
  _eagerZetaToNMinus1 <- do
    zetaToN <- pow_ zeta (Int.pow 2 domLog2)
    pure (zetaToN `sub_` const_ one)

  -- 4. vanishes_on_zero_knowledge_and_previous_rows = 1 (joint_combiner is None)
  let vanishesOnZk = const_ one

  -- 5. Build monadic env
  -- Note: zeta^n-1 is ALSO computed lazily inside the env (computeZetaToNMinus1),
  -- matching OCaml's lazy binding (plonk_checks.ml:281) forced inside
  -- unnormalized_lagrange_basis.
  let
    env :: EnvM f (Snarky (KimchiConstraint f) t m)
    env = buildCircuitEnvM
      alphaPowers
      zeta
      domLog2
      omegaForLagrange
      evalPoint
      vanishesOnZk
      beta
      gamma
      (const_ one) -- jointCombiner (None → 1)

  -- 6. Evaluate tokens using monadic interpreter
  evaluateM tokens env
