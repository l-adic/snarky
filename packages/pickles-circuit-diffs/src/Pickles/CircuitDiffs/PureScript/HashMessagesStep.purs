module Pickles.CircuitDiffs.PureScript.HashMessagesStep
  ( compileHashMessagesStep
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (foldM)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.Field (StepField)
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Types (WrapIPARounds)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertEq)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

-- | hash_messages_for_next_step_proof circuit.
-- |
-- | Input layout (91 fields):
-- |   0-55:  VK commitments (28 comms × 2 coords)
-- |          sigma_comm(7), coefficients_comm(15),
-- |          generic_comm, psm_comm, complete_add_comm, mul_comm, emul_comm,
-- |          endomul_scalar_comm
-- |   56-57: sg_old[0] (x, y)
-- |   58-72: bp_challenges[0] (WrapIPARounds = 15 fields)
-- |   73-74: sg_old[1] (x, y)
-- |   75-89: bp_challenges[1] (WrapIPARounds = 15 fields)
-- |   90:    claimed_digest
-- |
-- | Reference: mina/src/lib/crypto/pickles/step_verifier.ml
-- |   sponge_after_index (lines 1167-1176)
-- |   hash_messages_for_next_step_proof (lines 1178-1188)
hashMessagesStepCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 91 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
hashMessagesStepCircuit inputs = do
  let
    at = unsafeIdx inputs

    -- VK commitments: 28 comms × 2 coords = 56 fields
    -- Order: sigma_comm(7), coefficients_comm(15), then 6 selectors
    -- Each commitment is [| pt |] where pt = (x, y)
    -- index_to_field_elements flattens: for each comm array, g maps each point to [x, y]
    vkFields :: Vector 56 (FVar StepField)
    vkFields = Vector.generate \j -> at (getFinite j)

  -- 1. sponge_after_index: absorb all VK field elements
  spongeAfterIndex <- do
    let sponge0 = initialSpongeCircuit
    foldM (\s x -> Sponge.absorb x s) sponge0 vkFields

  -- 2. Copy sponge (just reuse the value — PureScript is pure, no mutation)
  let sponge = spongeAfterIndex

  -- 3. Absorb to_field_elements_without_index (app_state = unit, so just sg + bp_challenges)
  -- For each proof: absorb sg.x, sg.y, then bp_challenges[0..14]
  let
    absorbProof s proofIdx = do
      let
        sgX = at (56 + proofIdx * 17)
        sgY = at (56 + proofIdx * 17 + 1)

        bpChals :: Vector WrapIPARounds (FVar StepField)
        bpChals = Vector.generate \j -> at (56 + proofIdx * 17 + 2 + getFinite j)
      s1 <- Sponge.absorb sgX s
      s2 <- Sponge.absorb sgY s1
      foldM (\s' x -> Sponge.absorb x s') s2 bpChals

  sponge1 <- absorbProof sponge 0
  sponge2 <- absorbProof sponge1 1

  -- 4. Squeeze digest
  { result: digest } <- Sponge.squeeze sponge2

  -- 5. Assert digest matches claimed
  let claimed = at 90
  assertEq digest claimed

compileHashMessagesStep :: CompiledCircuit StepField
compileHashMessagesStep =
  compilePure (Proxy @(Vector 91 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> hashMessagesStepCircuit inputs)
    Kimchi.initialState
