module Pickles.CircuitDiffs.PureScript.Xhat
  ( parseXhatInput
  , xhatCircuit
  , compileXhat
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (tuple3, tuple6)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.Field (WrapField)
import Pickles.PackedStatement (PackedStepPublicInput, fromPackedTuple)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode(..), LagrangeBaseLookup, publicInputCommit)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (Bool(..), BoolVar, F, FVar, SizedF, Snarky)
import Snarky.Circuit.Kimchi (SplitField(..), Type2(..))
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

parseXhatInput :: Vector 34 (FVar WrapField) -> PackedStepPublicInput 1 15 (FVar WrapField) (BoolVar WrapField)
parseXhatInput inputs =
  let
    at = unsafeIdx inputs
    splitField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })
    perProofTuple =
      tuple6
        ( splitField 0 :< splitField 2 :< splitField 4
            :< splitField 6
            :< splitField 8
            :< Vector.nil
        )
        (at 10)
        (asSizedF128 (at 11) :< asSizedF128 (at 12) :< Vector.nil)
        ( asSizedF128 (at 13) :< asSizedF128 (at 14)
            :< asSizedF128 (at 15)
            :< Vector.nil
        )
        ( (Vector.generate \j -> asSizedF128 (at (16 + getFinite j)))
            :: Vector 15 (SizedF 128 (FVar WrapField))
        )
        (coerce (at 31) :: BoolVar WrapField)
    stmtTuple =
      tuple3
        (perProofTuple :< Vector.nil)
        (at 32)
        (at 33 :< Vector.nil)
  in
    fromPackedTuple stmtTuple

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
-- | `xhat_wrap_chunks2_circuit` at two.
compileXhat
  :: forall @nc
   . Reflectable nc Int
  => XhatParams nc WrapField
  -> Effect (CompiledCircuit WrapField)
compileXhat srsData =
  compile noAdvice (Proxy @(Vector 34 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> void $ xhatCircuit @nc srsData (parseXhatInput inputs))
