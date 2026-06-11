module Pickles.CircuitDiffs.PureScript.SchnorrVerify
  ( SchnorrVerifyInput
  , parseSchnorrVerifyInput
  , compileSchnorrVerify
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (traverse_)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Mina.ChainId (ChainId(..), signaturePrefix)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.Field (StepField)
import Run as Run
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (BoolVar, F, FVar)
import Snarky.Circuit.DSL.Monad (check) as DSL
import Snarky.Circuit.Schnorr (Signature(..), pallasParams, shiftConst, verifies)
import Snarky.Circuit.Schnorr.Shifted (assertOnCurveConst, createShifted)
import Snarky.Circuit.Types (Bool(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | Schnorr verifier circuit-diff input — matches the OCaml fixture's
-- | typ layout: pk(2) + sig.r(1) + sig.s_bits(255) + msg[1](1) = 259
-- | public fields (the +1 output bool brings public_input_size to 260).
type SchnorrVerifyInput f =
  { pk :: AffinePoint (FVar f)
  , r :: FVar f
  , sBits :: Vector 255 (BoolVar f)
  , message :: Array (FVar f)
  }

parseSchnorrVerifyInput
  :: Vector 259 (FVar StepField) -> SchnorrVerifyInput StepField
parseSchnorrVerifyInput inputs =
  let
    at = unsafeIdx inputs
    -- s_bits live at indices 3..257 (LSB first). Coerce FVar → BoolVar;
    -- the boolean constraint is added explicitly below to match OCaml
    -- `Curve.Scalar.typ`'s 255 inline `Boolean.typ` checks.
    sBits = Vector.generate @255 \i ->
      coerce (at (3 + getFinite i)) :: BoolVar StepField
  in
    { pk: AffinePoint { x: at 0, y: at 1 }
    , r: at 2
    , sBits
    , message: Vector.toUnfoldable (at 258 :< Vector.nil)
    }

compileSchnorrVerify :: Effect (CompiledCircuit StepField)
compileSchnorrVerify =
  Run.runBaseEffect $ compile (Proxy @(Vector 259 (F StepField))) (Proxy @Boolean) (Proxy @(KimchiConstraint StepField))
    ( \inputs -> do
        let { pk, r, sBits, message } = parseSchnorrVerifyInput inputs
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
          , message
          }
    )
