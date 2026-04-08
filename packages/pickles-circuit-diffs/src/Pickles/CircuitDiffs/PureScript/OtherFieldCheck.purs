module Pickles.CircuitDiffs.PureScript.OtherFieldCheck
  ( compileOtherFieldCheck
  ) where

-- | Isolated circuit for a single Other_field.typ exists + check.
-- | Matches OCaml's other_field_check_step_circuit (19 gates).
-- |
-- | OCaml: exists Other_field.typ ~compute:(fun () -> zero)
-- | where Other_field.typ = (Field.t, Boolean.var) with check that
-- | verifies sOdd is boolean + asserts no forbidden shifted values.

import Prelude

import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Types (StepField)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, Snarky, exists)
import Snarky.Circuit.Kimchi (SplitField, Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-- | Circuit that allocates a single Type2 (SplitField) value via exists.
-- | The CheckedType instance runs:
-- |   1. genericCheck on SplitField (verifies sOdd is boolean)
-- |   2. Forbidden shifted value check (4 values for Pallas→Vesta)
otherFieldCheckCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Unit
  -> Snarky (KimchiConstraint StepField) t m Unit
otherFieldCheckCircuit _ = do
  let
    dummy :: forall a b. Applicative b => b a
    dummy = pure (unsafeCoerce unit)
  _ <- exists (dummy :: _ (Type2 (SplitField (F StepField) Boolean)))
  pure unit

compileOtherFieldCheck :: CompiledCircuit StepField
compileOtherFieldCheck =
  compilePure (Proxy @Unit) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    otherFieldCheckCircuit
    Kimchi.initialState
