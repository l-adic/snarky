-- | `bindVk` as a step circuit, against OCaml's `bind_vk_step_circuit`
-- | (`dump_side_loaded_main.ml`): allocate a side-loaded key and bind
-- | it to the public input, as a zkApp rule does with
-- | `Zkapp_account.Checked.digest_vk` before `Side_loaded.in_circuit`.
module Pickles.CircuitDiffs.PureScript.BindVk
  ( compileBindVkStep
  ) where

import Prelude

import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField)
import Pickles.Sideload.BoundVk (bindVk)
import Pickles.Sideload.VerificationKey (compileDummy)
import Pickles.Sideload.VerificationKey as SLVK
import Pickles.Types (WrapVkChunks)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, Snarky, exists)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

bindVkStepCircuit
  :: forall r
   . FVar StepField
  -> Snarky StepField (KimchiConstraint StepField) r Unit
bindVkStepCircuit digest = do
  vk <- exists (pure (compileDummy :: SLVK.VerificationKey WrapVkChunks (F StepField) Boolean))
  void $ bindVk digest vk

compileBindVkStep :: Effect (CompiledCircuit StepField)
compileBindVkStep = compile noAdvice (Proxy @(F StepField)) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  bindVkStepCircuit
