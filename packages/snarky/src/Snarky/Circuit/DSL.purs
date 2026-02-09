-- | Main entry point for building circuit libraries.
-- |
-- | Import this module to get everything needed for circuit construction.
-- |
-- | ## The trailing `_` convention
-- |
-- | Functions ending in `_` (like `mul_`, `add_`, `and_`, `not_`) avoid name
-- | collisions with Prelude type classes (`Semiring`, `HeytingAlgebra`, etc.)
-- | and operate directly on circuit variables:
-- |
-- | ```purescript
-- | -- _ functions: take variables, may return Snarky action
-- | mul_ :: FVar f -> FVar f -> Snarky c t m (FVar f)
-- | and_ :: BoolVar f -> BoolVar f -> Snarky c t m (BoolVar f)
-- | add_ :: FVar f -> FVar f -> FVar f  -- pure, no constraints needed
-- | ```
-- |
-- | The Prelude classes are also implemented for `Snarky c t m (FVar f)`, so you
-- | can use `*`, `+`, `&&`, `||` directly on Snarky actions when chaining:
-- |
-- | ```purescript
-- | -- Chaining with Prelude operators
-- | squareAndDouble x = mul_ x x + mul_ x x  -- two muls, added together
-- |
-- | -- Mix of variables and actions
-- | combined a b = mul_ a b * mul_ b a + pure (const_ one)
-- | ```
module Snarky.Circuit.DSL
  ( module ReExports
  ) where

import Snarky.Circuit.CVar (EvaluationError(..), Variable, add_, const_, negate_, scale_, sub_) as ReExports
import Snarky.Circuit.DSL.Assert (class AssertEqual, assertEq, assertEqGeneric, assertEqual_, assertNonZero_, assertNotEqual_, assertSquare_, assert_, isEqual, isEqualGeneric) as ReExports
import Snarky.Circuit.DSL.Bits (packPure, pack_, unpackPure, unpack_) as ReExports
import Snarky.Circuit.DSL.Boolean (class IfThenElse, all_, any_, false_, if_, true_, xor_) as ReExports
import Snarky.Circuit.DSL.Field (equals, equals_, neq_, pow_, sum_) as ReExports
import Snarky.Circuit.DSL.Monad (class CheckedType, class CircuitM, class ConstraintM, AsProver, AsProverT, Snarky(..), addConstraint, and_, check, div_, exists, genericCheck, inv_, mul_, not_, or_, read, readCVar, runAsProver, runAsProverT, throwAsProver) as ReExports
import Snarky.Circuit.DSL.SizedF (SizedF, coerceViaBits, fromBits, fromField, lowestNBits, lowestNBitsPure, toBits, toField, unwrapF, wrapF) as ReExports
import Snarky.Circuit.DSL.Utils (seal) as ReExports
import Snarky.Circuit.Types (class CircuitType, Bool(..), BoolVar, F(..), FVar, UnChecked(..), fieldsToValue, fieldsToVar, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, sizeInFields, valueToFields, varToFields) as ReExports
import Snarky.Constraint.Basic (class BasicSystem, Basic(..), boolean, equal, r1cs) as ReExports