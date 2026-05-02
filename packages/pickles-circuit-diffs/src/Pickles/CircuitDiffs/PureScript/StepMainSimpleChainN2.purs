module Pickles.CircuitDiffs.PureScript.StepMainSimpleChainN2
  ( compileStepMainSimpleChainN2
  , StepMainSimpleChainN2Params
  , class SimpleChainN2Advice
  , getSimpleChainN2Prev1
  , getSimpleChainN2Prev2
  ) where

-- | step_main circuit for the Simple_Chain N2 rule (2 previous proofs).
-- | Delegates to the generic Pickles.Step.Main.stepMain.
-- |
-- | Reference: mina/src/lib/crypto/pickles/dump_circuit_impl.ml (step_main_simple_chain_n2)

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Partial.Unsafe (unsafeCrashWith)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyWrapSg)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (RuleOutput, SlotVkSource(..), stepMain)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StatementIO, StepField)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertAny_, const_, equals_, exists, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type StepMainSimpleChainN2Params =
  { lagrangeAt :: LagrangeBaseLookup StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | Application-specific advice for the Simple_Chain N2 rule.
-- |
-- | The rule allocates two previous-proof app_state fields. In OCaml each
-- | is `exists Field.typ ~compute:(fun () -> Field.Constant.zero)`. We
-- | route them through this typeclass so the SAME rule definition serves
-- | both compilation (Effect throws) and proving.
class Monad m <= SimpleChainN2Advice m where
  getSimpleChainN2Prev1 :: Unit -> m (F StepField)
  getSimpleChainN2Prev2 :: Unit -> m (F StepField)

-- | Compilation instance: throws if evaluated. `exists` in CircuitBuilderT
-- | discards the AsProverT entirely so the throw never fires.
instance SimpleChainN2Advice Effect where
  getSimpleChainN2Prev1 _ = throw "SimpleChainN2Advice.getSimpleChainN2Prev1: not available during compilation"
  getSimpleChainN2Prev2 _ = throw "SimpleChainN2Advice.getSimpleChainN2Prev2: not available during compilation"

-- | Simple_Chain N2 rule: self_correct = (1 + prev1 + prev2 == self)
-- | Both proofs have the same proof_must_verify = not is_base_case.
-- | Reference: dump_circuit_impl.ml:4533-4566
simpleChainN2Rule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => SimpleChainN2Advice m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 2 (FVar StepField) Unit)
simpleChainN2Rule appState = do
  prev1 <- exists $ lift $ getSimpleChainN2Prev1 unit
  prev2 <- exists $ lift $ getSimpleChainN2Prev2 unit
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (CVar.add_ (const_ one) prev1) prev2) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev1 :< prev2 :< Vector.nil
    , proofMustVerify: proofMustVerify :< proofMustVerify :< Vector.nil
    , publicOutput: unit
    }

compileStepMainSimpleChainN2
  :: StepMainSimpleChainN2Params -> Effect (CompiledCircuit StepField)
compileStepMainSimpleChainN2 params =
  compile (Proxy @Unit) (Proxy @(Vector 67 (F StepField))) (Proxy @(KimchiConstraint StepField))
    -- Step domain log2 = 16 (OCaml: dump_circuit_impl.ml
    -- `step_domains = Pow_2_roots_of_unity 16` in step_main_simple_chain_n2).
    -- Single-rule: mpvMax = len = 2, mpvPad = 0.
    ( \_ -> stepMain
        @( PrevsSpecCons 2 (StatementIO (F StepField) Unit)
            (PrevsSpecCons 2 (StatementIO (F StepField) Unit) PrevsSpecNil)
        )
        @67
        @(F StepField)
        @(FVar StepField)
        @Unit
        @Unit
        @(F StepField)
        @(FVar StepField)
        @( Tuple (StatementIO (F StepField) Unit)
            (Tuple (StatementIO (F StepField) Unit) Unit)
        )
        @2
        @0
        simpleChainN2Rule
        { perSlotLagrangeAt: params.lagrangeAt :< params.lagrangeAt :< Vector.nil
        , blindingH: params.blindingH
        , perSlotFopDomainLog2s:
            (16 :< Vector.nil) :< (16 :< Vector.nil) :< Vector.nil
        , perSlotVkSources: SharedExistsVk :< SharedExistsVk :< Vector.nil
        -- Phase 2b.31a: thunks for mpvMax-padding dummies. Single-rule
        -- callers have mpvPad=0 so `mpvFrontPad` short-circuits and the
        -- thunks never fire — `unsafeCrashWith` is fine.
        , dummyUnfp: \_ -> unsafeCrashWith "dummyUnfp: unused at mpvPad=0"
        }
        dummyWrapSg
        -- Side-loaded VK carrier (Step 2d-β1.5b): two Cons slots,
        -- both compiled; carrier = `Unit /\ Unit /\ Unit`.
        (unit /\ unit /\ unit)
    )
    Kimchi.initialState
