module Pickles.CircuitDiffs.PureScript.StepMainSimpleChain
  ( compileStepMainSimpleChain
  , StepMainSimpleChainParams
  , class SimpleChainAdvice
  , getSimpleChainPrev
  ) where

-- | step_main circuit for the Simple_Chain inductive rule (N1, 1 previous proof).
-- | Delegates to the generic Pickles.Step.Main.stepMain2.
-- |
-- | Reference: mina/src/lib/crypto/pickles/dump_circuit_impl.ml (step_main_simple_chain)

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Maybe (Maybe(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Unsafe (unsafePerformEffect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyWrapSg)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (RuleOutput, stepMain2)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StepField)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertAny_, const_, equals_, exists, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type StepMainSimpleChainParams =
  { lagrangeAt :: LagrangeBaseLookup StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | Application-specific advice for the Simple_Chain N1 rule.
-- |
-- | The rule allocates one previous-proof app_state field. In OCaml this is
-- | done via `exists Field.typ ~compute:(fun () -> Field.Constant.zero)`.
-- | In PureScript we route it through this typeclass so the SAME rule
-- | definition can be used for both compilation (Effect throws) and
-- | proving (a ReaderT-based instance returns the real previous proof's
-- | app_state).
class Monad m <= SimpleChainAdvice m where
  getSimpleChainPrev :: Unit -> m (F StepField)

-- | Compilation instance: throws if evaluated. `exists` in CircuitBuilderT
-- | discards the AsProverT entirely so the throw never fires.
instance SimpleChainAdvice Effect where
  getSimpleChainPrev _ = throw "SimpleChainAdvice.getSimpleChainPrev: not available during compilation"

-- | Simple_Chain N1 rule: self_correct = (1 + prev == self)
-- | Reference: dump_circuit_impl.ml:4390-4413
simpleChainRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => SimpleChainAdvice m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 1 (FVar StepField) Unit)
simpleChainRule appState = do
  prev <- exists $ lift $ getSimpleChainPrev unit
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
    , publicOutput: unit
    }

compileStepMainSimpleChain :: StepMainSimpleChainParams -> CompiledCircuit StepField
compileStepMainSimpleChain params = unsafePerformEffect $
  compile (Proxy @Unit) (Proxy @(Vector 34 (F StepField))) (Proxy @(KimchiConstraint StepField))
    -- Step domain log2 = 14: matches OCaml's production `Fix_domains.domains`
    -- output for the Simple_chain N1 inductive rule (small circuit; ceil_log2
    -- of the constraint row count). The earlier value of 16 was a synthetic
    -- mismatch that didn't validate the production compile path. Both this
    -- helper and `dump_circuit_impl.ml` now use 14 so the JSON fixture
    -- exercises the same compile config Pickles.compile_promise produces.
    ( \_ -> stepMain2 @(PrevsSpecCons 1 PrevsSpecNil) @34 @(F StepField) @(FVar StepField) @Unit @Unit @(F StepField) @(FVar StepField) simpleChainRule
        { perSlotLagrangeAt: params.lagrangeAt :< Vector.nil
        , blindingH: params.blindingH
        , perSlotFopDomainLog2: 14 :< Vector.nil
        , perSlotKnownWrapKeys: Nothing :< Vector.nil
        }
        dummyWrapSg
    )
    Kimchi.initialState
