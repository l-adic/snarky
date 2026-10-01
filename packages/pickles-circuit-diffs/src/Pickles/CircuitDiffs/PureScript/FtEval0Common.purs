module Pickles.CircuitDiffs.PureScript.FtEval0Common
  ( FtEval0Input
  , ftEval0CircuitM
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Int (pow) as Int
import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.LinearizationCommon (LinearizationInput(..), evalPointOf)
import Pickles.Linearization.Env (AlphaPowersLen, EnvM, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI, domainGenerator, domainShifts)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (PolishToken)
import Pickles.PlonkChecks (permContributionCircuit, zkPolynomial)
import Poseidon (class PoseidonField)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitType, FVar, Snarky, UnChecked(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, label, pow_, sub_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class HasEndo, class PrimeField)
import Type.Proxy (Proxy(..))

-- | `ft_eval0_step_circuit`'s input (OCaml `dump_circuit_impl.ml`): the linearization input
-- | and the public-input polynomial at zeta.
newtype FtEval0Input f = FtEval0Input
  { linearization :: LinearizationInput f
  , pEval0 :: f
  }

-- | The wire order.
type FtEval0Tuple f = Tuple2 (LinearizationInput f) f

toTuple :: forall f. FtEval0Input f -> FtEval0Tuple f
toTuple (FtEval0Input i) = tuple2 i.linearization i.pEval0

fromTuple :: forall f. FtEval0Tuple f -> FtEval0Input f
fromTuple = uncurry2 \linearization pEval0 -> FtEval0Input { linearization, pEval0 }

instance CircuitType f fa fv => CircuitType f (FtEval0Input fa) (FtEval0Input fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(FtEval0Tuple fa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(FtEval0Tuple fa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(FtEval0Tuple fa)

-- | Circuit computing `ft_eval0`, mirroring OCaml `dump_circuit_impl.ml`'s
-- | `ft_eval0_circuit` (`Plonk_checks.ft_eval0` over a `scalars_env` built
-- | at a CONSTANT domain — generator and shifts are constants, so no omega
-- | rows are emitted, unlike the in-circuit omega powers of
-- | `Pickles.Step.FinalizeOtherProof`):
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
  -> UnChecked (FtEval0Input (FVar f))
  -> Snarky f (KimchiConstraint f) r (FVar f)
ftEval0CircuitM domLog2 tokens (UnChecked (FtEval0Input input)) = do
  let
    LinearizationInput i = input.linearization
    { alpha, beta, gamma, zeta } = i
    pEval0 = input.pEval0
    evalPoint = evalPointOf input.linearization

    -- w(zeta), 15 entries; s(zeta), 6 entries; z(zeta), z(zeta omega)
    w0 = map _.zeta i.witnessEvals
    s0 = map _.zeta i.sigmaEvals
    zZeta = i.zEvals.zeta
    zOmegaTimesZeta = i.zEvals.omegaTimesZeta

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

  -- the library gadget at constant powers (its two rows; the dump's constant domain)
  zkPoly <- zkPolynomial zeta
    { omegaToMinus1: const_ omegaToMinus1
    , omegaToZkPlus1: const_ omegaToMinus2
    , omegaToZk: const_ omegaToMinus3
    }

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
