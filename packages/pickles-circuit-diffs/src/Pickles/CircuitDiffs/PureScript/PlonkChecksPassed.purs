module Pickles.CircuitDiffs.PureScript.PlonkChecksPassed
  ( compilePlonkChecksPassedStep
  , compilePlonkChecksPassedWrap
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.Field (StepField, WrapField)
import Pickles.PlonkChecks.Permutation (permScalarCircuit)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, Snarky, pow_)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..), shiftedEqualType1, shiftedEqualType2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

-- | `plonk_checks_passed_{step,wrap}_circuit` (OCaml `dump_circuit_impl.ml`): alpha at
-- | 0, beta 1, gamma 2, zkPolynomial 3, z(zeta*omega) 4, sigma[0..5] at 5-10,
-- | w[0..5] at 11-16, and the claimed perm at 17 as a Type1 (step) or Type2 (wrap)
-- | shifted value. `alpha^21` is computed by `pow_` as the dump does, then the perm
-- | scalar is compared with the claim through the shifted equality.
-- |
-- | Layout only: the rows are the DSL's `pow_`, the library's `permScalarCircuit`
-- | (the verifiers' perm scalar) and the library's `shiftedEqualType1`/`Type2`.
type PermInputs f =
  { alpha :: FVar f
  , beta :: FVar f
  , gamma :: FVar f
  , zkPolynomial :: FVar f
  , zOmega :: FVar f
  , sigma :: Vector 6 (FVar f)
  , w :: Vector 6 (FVar f)
  , claimed :: FVar f
  }

parsePermInputs :: forall f. Vector 18 (FVar f) -> PermInputs f
parsePermInputs inputs =
  let
    at = unsafeIdx inputs
  in
    { alpha: at 0
    , beta: at 1
    , gamma: at 2
    , zkPolynomial: at 3
    , zOmega: at 4
    , sigma: Vector.generate \j -> at (5 + getFinite j)
    , w: Vector.generate \j -> at (11 + getFinite j)
    , claimed: at 17
    }

permScalarOf
  :: forall f r
   . PrimeField f
  => PermInputs f
  -> Snarky f (KimchiConstraint f) r (FVar f)
permScalarOf i = do
  alphaPow21 <- pow_ i.alpha 21
  permScalarCircuit
    { w: i.w
    , sigma: i.sigma
    , zOmega: i.zOmega
    , beta: i.beta
    , gamma: i.gamma
    , zkPolynomial: i.zkPolynomial
    , alphaPow21
    }

plonkChecksPassedStepCircuit
  :: forall r
   . Vector 18 (FVar StepField)
  -> Snarky StepField (KimchiConstraint StepField) r Unit
plonkChecksPassedStepCircuit inputs = do
  let i = parsePermInputs inputs
  actual <- permScalarOf i
  void $ shiftedEqualType1 (Type1 i.claimed) actual

plonkChecksPassedWrapCircuit
  :: forall r
   . Vector 18 (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
plonkChecksPassedWrapCircuit inputs = do
  let i = parsePermInputs inputs
  actual <- permScalarOf i
  void $ shiftedEqualType2 (Type2 i.claimed) actual

compilePlonkChecksPassedStep :: Effect (CompiledCircuit StepField)
compilePlonkChecksPassedStep =
  compile noAdvice (Proxy @(Vector 18 (F StepField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    plonkChecksPassedStepCircuit

compilePlonkChecksPassedWrap :: Effect (CompiledCircuit WrapField)
compilePlonkChecksPassedWrap =
  compile noAdvice (Proxy @(Vector 18 (F WrapField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    plonkChecksPassedWrapCircuit
