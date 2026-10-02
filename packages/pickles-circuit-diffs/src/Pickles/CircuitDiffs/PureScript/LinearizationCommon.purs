module Pickles.CircuitDiffs.PureScript.LinearizationCommon
  ( LinearizationInput(..)
  , evalPointOf
  , linearizationCircuitM
  ) where

import Prelude

import Data.Fin (reflectFinite)
import Data.Int (pow) as Int
import Data.Tuple.Nested (Tuple2, Tuple9, tuple9, uncurry9)
import Data.Vector (Vector, (!!))
import Pickles.Linearization.Env (CurrOrNext(..), GateType(..)) as Env
import Pickles.Linearization.Env (EnvM, EvalPoint, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI, PointEval, domainGenerator)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (PolishToken)
import Pickles.PlonkChecks (zkPolynomial)
import Pickles.Types (evalPair, pairEval)
import Poseidon (class PoseidonField)
import Snarky.Circuit.CVar (CVar(..), const_)
import Snarky.Circuit.DSL (class CircuitType, FVar, Snarky, UnChecked(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, pow_, sub_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class HasEndo, class PrimeField)
import Type.Proxy (Proxy(..))

-- | The input the linearization and `ft_eval0` dumps share (OCaml `dump_circuit_impl.ml`).
-- | The selectors (`indexEvals`) are generic, poseidon, complete-add, var-base-mul,
-- | endo-mul, endo-mul-scalar.
newtype LinearizationInput f = LinearizationInput
  { witnessEvals :: Vector 15 (PointEval f)
  , coeffEvals :: Vector 15 (PointEval f)
  , zEvals :: PointEval f
  , sigmaEvals :: Vector 6 (PointEval f)
  , indexEvals :: Vector 6 (PointEval f)
  , alpha :: f
  , beta :: f
  , gamma :: f
  , zeta :: f
  }

-- | The wire order, each evaluation as its `(zeta, zetaw)` pair.
type LinearizationTuple f =
  Tuple9 (Vector 15 (Tuple2 f f)) (Vector 15 (Tuple2 f f)) (Tuple2 f f) (Vector 6 (Tuple2 f f))
    (Vector 6 (Tuple2 f f))
    f
    f
    f
    f

toTuple :: forall f. LinearizationInput f -> LinearizationTuple f
toTuple (LinearizationInput i) =
  tuple9 (map evalPair i.witnessEvals) (map evalPair i.coeffEvals) (evalPair i.zEvals)
    (map evalPair i.sigmaEvals)
    (map evalPair i.indexEvals)
    i.alpha
    i.beta
    i.gamma
    i.zeta

fromTuple :: forall f. LinearizationTuple f -> LinearizationInput f
fromTuple = uncurry9 \witnessEvals coeffEvals zEvals sigmaEvals indexEvals alpha beta gamma zeta ->
  LinearizationInput
    { witnessEvals: map pairEval witnessEvals
    , coeffEvals: map pairEval coeffEvals
    , zEvals: pairEval zEvals
    , sigmaEvals: map pairEval sigmaEvals
    , indexEvals: map pairEval indexEvals
    , alpha
    , beta
    , gamma
    , zeta
    }

instance CircuitType f fa fv => CircuitType f (LinearizationInput fa) (LinearizationInput fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(LinearizationTuple fa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(LinearizationTuple fa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(LinearizationTuple fa)

-- | The interpreter's evaluation point over the input's evaluations: the coefficients'
-- | `zeta` halves only, no lookups, and an unsupported gate's selector read as generic's.
evalPointOf :: forall f. PrimeField f => LinearizationInput (FVar f) -> EvalPoint (FVar f)
evalPointOf (LinearizationInput i) =
  { witness: \row col -> at row (i.witnessEvals !! col)
  , coefficient: \col -> (i.coeffEvals !! col).zeta
  , index: \row gt -> at row case gt of
      Env.Generic -> i.indexEvals !! reflectFinite @0
      Env.Poseidon -> i.indexEvals !! reflectFinite @1
      Env.CompleteAdd -> i.indexEvals !! reflectFinite @2
      Env.VarBaseMul -> i.indexEvals !! reflectFinite @3
      Env.EndoMul -> i.indexEvals !! reflectFinite @4
      Env.EndoMulScalar -> i.indexEvals !! reflectFinite @5
      _ -> i.indexEvals !! reflectFinite @0
  , lookupAggreg: \_ -> Const zero
  , lookupSorted: \_ _ -> Const zero
  , lookupTable: \_ -> Const zero
  , lookupRuntimeTable: \_ -> Const zero
  , lookupRuntimeSelector: \_ -> Const zero
  , lookupKindIndex: \_ -> Const zero
  }
  where
  at = case _ of
    Env.Curr -> _.zeta
    Env.Next -> _.omegaTimesZeta

-- | Circuit that evaluates the linearization polynomial using the monadic
-- | interpreter with compact Store/Load token stream:
-- | - Precomputed alpha powers via successive multiplication
-- | - Domain values computed from zeta (omega constants for lagrange basis)
-- | - Monadic interpreter (evaluateM) with peephole alpha optimization
linearizationCircuitM
  :: forall f f' r
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => LinearizationFFI f
  => Int -- ^ domainLog2
  -> Array PolishToken
  -> UnChecked (LinearizationInput (FVar f))
  -> Snarky f (KimchiConstraint f) r (FVar f)
linearizationCircuitM domLog2 tokens (UnChecked input@(LinearizationInput i)) = do
  let
    { alpha, beta, gamma, zeta } = i
    evalPoint = evalPointOf input

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
  _zkPoly <- zkPolynomial zeta
    { omegaToMinus1: const_ omegaToMinus1
    , omegaToZkPlus1: const_ omegaToMinus2
    , omegaToZk: const_ omegaToMinus3
    }

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
    env :: EnvM f (Snarky f (KimchiConstraint f) r)
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
