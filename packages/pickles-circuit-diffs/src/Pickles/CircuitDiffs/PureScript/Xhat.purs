module Pickles.CircuitDiffs.PureScript.Xhat
  ( xhatCircuit
  , compileXhat
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (WrapField)
import Pickles.PackedStatement (PackedStepPublicInput)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode(..), LagrangeBaseLookup, publicInputCommit)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, Snarky, UnChecked(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, curveParams)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | The Lagrange bases at `nc` chunks each, and the blinding `h`.
type XhatParams nc f =
  { lagrangeAt :: LagrangeBaseLookup nc f
  , blindingH :: AffinePoint (F f)
  }

xhatCircuit
  :: forall @nc pi r
   . PrimeField WrapField
  => Reflectable nc Int
  => PublicInputCommit pi WrapField
  => XhatParams nc WrapField
  -> pi
  -> Snarky WrapField (KimchiConstraint WrapField) r (Vector nc (AffinePoint (FVar WrapField)))
xhatCircuit { lagrangeAt, blindingH } publicInput =
  publicInputCommit @nc
    { curveParams: curveParams (Proxy @VestaG)
    , lagrangeAt
    , blindingH
    , correctionMode: InCircuitCorrections
    }
    publicInput

-- | The comparison target at `nc` chunks per Lagrange base: `xhat_wrap_circuit` at one,
-- | `xhat_wrap_chunks2_circuit` at two. Its input is the packed step statement at one
-- | proof and 15 rounds (OCaml `dump_circuit_impl.ml`).
compileXhat
  :: forall @nc
   . Reflectable nc Int
  => XhatParams nc WrapField
  -> Effect (CompiledCircuit WrapField)
compileXhat srsData =
  compile noAdvice (Proxy @(UnChecked (PackedStepPublicInput 1 15 (F WrapField) Boolean)))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    \(UnChecked statement) -> void $ xhatCircuit @nc srsData statement
