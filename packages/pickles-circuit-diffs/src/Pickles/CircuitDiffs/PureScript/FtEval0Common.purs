module Pickles.CircuitDiffs.PureScript.FtEval0Common
  ( ftEval0CircuitM
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Int (pow) as Int
import Data.Vector (Vector, (!!))
import Data.Vector as Vector
import Pickles.Linearization.Env (AlphaPowersLen, EnvM, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.Env (CurrOrNext(..), GateType(..)) as Env
import Pickles.Linearization.FFI (class LinearizationFFI, domainGenerator, domainShifts)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (PolishToken)
import Pickles.PlonkChecks.Permutation (permContributionCircuit)
import Poseidon (class PoseidonField)
import Snarky.Circuit.CVar (CVar(..), const_)
import Snarky.Circuit.DSL (FVar, Snarky, label, mul_, pow_, sub_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class HasEndo, class PrimeField)

-- | Circuit computing `ft_eval0`, mirroring OCaml `dump_circuit_impl.ml`'s
-- | `ft_eval0_circuit` (`Plonk_checks.ft_eval0` over a `scalars_env` built
-- | at a CONSTANT domain — generator and shifts are constants, so no omega
-- | rows are emitted, unlike the in-circuit omega powers of
-- | `Pickles.Step.FinalizeOtherProof`):
-- | - 91 input fields: the linearization layout (see `LinearizationCommon`)
-- |   plus `p_eval0` at index 90
-- | - Precomputed alpha powers, eager `zk_polynomial` and eager `zeta^n - 1`
-- |   (the `scalars_env` prelude, in OCaml's emission order)
-- | - The permutation recurrence + boundary quotient via the library gadget
-- |   `Pickles.PlonkChecks.Permutation.permContributionCircuit`, as both
-- |   verifiers compute it
-- | - The constant term via the monadic interpreter, subtracted last
ftEval0CircuitM
  :: forall f f' r
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => LinearizationFFI f
  => Int -- ^ domainLog2
  -> Array PolishToken
  -> Vector 91 (FVar f)
  -> Snarky f (KimchiConstraint f) r (FVar f)
ftEval0CircuitM domLog2 tokens inputs = do
  let
    at i = inputs !! unsafeFinite i

    witnessEval row col =
      let
        base = 2 * getFinite col
      in
        case row of
          Env.Curr -> at base
          Env.Next -> at (base + 1)

    coeffEval col = at (30 + 2 * getFinite col)

    selectorEval row gt =
      let
        idx = case gt of
          Env.Generic -> 0
          Env.Poseidon -> 1
          Env.CompleteAdd -> 2
          Env.VarBaseMul -> 3
          Env.EndoMul -> 4
          Env.EndoMulScalar -> 5
          _ -> 0
        base = 74 + 2 * idx
      in
        case row of
          Env.Curr -> at base
          Env.Next -> at (base + 1)

    -- w(zeta), 15 entries; s(zeta), 6 entries; z(zeta), z(zeta omega)
    w0 :: Vector 15 (FVar f)
    w0 = Vector.generate \i -> at (2 * getFinite i)

    s0 :: Vector 6 (FVar f)
    s0 = Vector.generate \i -> at (62 + 2 * getFinite i)

    zZeta = at 60
    zOmegaTimesZeta = at 61

    alpha = at 86
    beta = at 87
    gamma = at 88
    zeta = at 89
    pEval0 = at 90

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

    -- The constant domain: generator and coset shifts from the FFI, omega
    -- powers folded as constants (no circuit constraints).
    gen = domainGenerator @f domLog2
    shifts = map const_ (domainShifts @f domLog2)
    omegaToMinus1 = recip gen
    omegaToMinus2 = omegaToMinus1 * omegaToMinus1
    omegaToMinus3 = omegaToMinus2 * omegaToMinus1
    omegaToMinus4 = omegaToMinus3 * omegaToMinus1

    omegaForLagrange { zkRows: zk, offset } =
      if not zk && offset == 0 then const_ one
      else if zk && offset == (-1) then const_ omegaToMinus4
      else if not zk && offset == 1 then const_ gen
      else if not zk && offset == (-1) then const_ omegaToMinus1
      else if not zk && offset == (-2) then const_ omegaToMinus2
      else if zk && offset == 0 then const_ omegaToMinus3
      else const_ one

  -- scalars_env prelude: alpha powers, eager zk_polynomial, eager zeta^n - 1
  alphaPowers <- precomputeAlphaPowers alpha

  zkPoly <- do
    t1 <- mul_ (zeta `sub_` const_ omegaToMinus1) (zeta `sub_` const_ omegaToMinus2)
    mul_ t1 (zeta `sub_` const_ omegaToMinus3)

  zetaToNMinus1 <- do
    zetaToN <- pow_ zeta (Int.pow 2 domLog2)
    pure (zetaToN `sub_` const_ one)

  let
    vanishesOnZk = const_ one

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
      (const_ one)

    alphaPow n = Vector.index alphaPowers (unsafeFinite @AlphaPowersLen n)
    a21 = alphaPow 21
    a22 = alphaPow 22
    a23 = alphaPow 23

  -- ft_eval0: term1 - p_eval0 - term2 + boundary - constant_term; the
  -- permutation half is the library gadget the verifiers use
  permResult <- permContributionCircuit
    { w: Vector.take @7 w0
    , sigma: s0
    , z: { zeta: zZeta, omegaTimesZeta: zOmegaTimesZeta }
    , shifts
    , alpha
    , beta
    , gamma
    , zkPolynomial: zkPoly
    , zetaToNMinus1
    , omegaToMinusZkRows: const_ omegaToMinus3
    , zeta
    }
    { pEval0, alphaPow21: a21, alphaPow22: a22, alphaPow23: a23 }

  constantTerm <- label "scalars_env" $ evaluateM tokens env

  pure (sub_ permResult constantTerm)
