module Pickles.CircuitDiffs.PureScript.SchnorrVerify
  ( compileSchnorrVerify
  ) where

import Prelude

import Data.Foldable (traverse_)
import Data.Tuple.Nested (Tuple4, tuple4, uncurry4)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Mina.ChainId (ChainId(..), signaturePrefix)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F, FVar, Snarky, UnChecked(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.DSL.Monad (check) as DSL
import Snarky.Circuit.Schnorr (Signature(..), pallasParams, shiftConst, verifies)
import Snarky.Circuit.Schnorr.Shifted (assertOnCurveConst, createShifted)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | `schnorr_verify_step_circuit`'s input — the OCaml fixture's typ: the public key, the
-- | signature's `r` and the 255 bits of its `s` (LSB first), and the one-field message (the
-- | +1 output bool brings `public_input_size` to 260).
newtype SchnorrVerifyInput f b pt = SchnorrVerifyInput
  { pk :: pt
  , r :: f
  , sBits :: Vector 255 b
  , message :: Vector 1 f
  }

-- | The wire order.
type SchnorrVerifyTuple f b pt = Tuple4 pt f (Vector 255 b) (Vector 1 f)

toTuple :: forall f b pt. SchnorrVerifyInput f b pt -> SchnorrVerifyTuple f b pt
toTuple (SchnorrVerifyInput i) = tuple4 i.pk i.r i.sBits i.message

fromTuple :: forall f b pt. SchnorrVerifyTuple f b pt -> SchnorrVerifyInput f b pt
fromTuple = uncurry4 \pk r sBits message -> SchnorrVerifyInput { pk, r, sBits, message }

instance
  ( CircuitType f fa fv
  , CircuitType f ba bv
  , CircuitType f pa pv
  ) =>
  CircuitType f (SchnorrVerifyInput fa ba pa) (SchnorrVerifyInput fv bv pv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(SchnorrVerifyTuple fa ba pa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(SchnorrVerifyTuple fa ba pa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(SchnorrVerifyTuple fa ba pa)

schnorrVerifyCircuit
  :: forall r
   . UnChecked (SchnorrVerifyInput (FVar StepField) (BoolVar StepField) (AffinePoint (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r (BoolVar StepField)
schnorrVerifyCircuit (UnChecked (SchnorrVerifyInput { pk, r, sBits, message })) = do
  -- Mirror OCaml's input typ checks, in the same order OCaml
  -- emits them during `constraint_system`:
  --   1. Inner_curve.typ.check on pk = assert_on_curve(pk).
  --   2. 255 × Boolean.typ.check on s_bits.
  assertOnCurveConst pallasParams pk
  traverse_ DSL.check (Vector.toUnfoldable sBits :: Array _)
  -- Then mirror the OCaml dump_schnorr_verify_circuit caller:
  --   let%bind (module S) = Inner_curve.Checked.Shifted.create ()
  --   in Schnorr.Chunked.Checked.verifies (module S) sig pk msg
  shifted <- createShifted pallasParams shiftConst
  verifies (signaturePrefix Mainnet) shifted
    { publicKey: pk
    , signature: Signature { r, s: sBits }
    , message: Vector.toUnfoldable message
    }

compileSchnorrVerify :: Effect (CompiledCircuit StepField)
compileSchnorrVerify =
  compile noAdvice
    (Proxy @(UnChecked (SchnorrVerifyInput (F StepField) Boolean (AffinePoint StepField))))
    (Proxy @Boolean)
    (Proxy @(KimchiConstraint StepField))
    schnorrVerifyCircuit
