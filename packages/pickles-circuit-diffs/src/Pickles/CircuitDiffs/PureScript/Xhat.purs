module Pickles.CircuitDiffs.PureScript.Xhat
  ( parseXhatInput
  , xhatCircuit
  , compileXhat
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Tuple.Nested (tuple3, tuple6)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.PackedStatement (PackedStepPublicInput, fromPackedTuple)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode(..), LagrangeBaseLookup, publicInputCommit)
import Pickles.Wrap.Types (Field)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F, FVar, SizedF, Snarky)
import Snarky.Circuit.Kimchi (SplitField(..), Type2(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type XhatParams f =
  { lagrangeAt :: LagrangeBaseLookup f
  , blindingH :: AffinePoint (F f)
  }

parseXhatInput :: Vector 34 (FVar Field) -> PackedStepPublicInput 1 15 (FVar Field) (BoolVar Field)
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
            :: Vector 15 (SizedF 128 (FVar Field))
        )
        (coerce (at 31) :: BoolVar Field)
    stmtTuple =
      tuple3
        (perProofTuple :< Vector.nil)
        (at 32)
        (at 33 :< Vector.nil)
  in
    fromPackedTuple stmtTuple

xhatCircuit
  :: forall pi t m
   . CircuitM Field (KimchiConstraint Field) t m
  => PublicInputCommit pi Field
  => XhatParams Field
  -> pi
  -> Snarky (KimchiConstraint Field) t m (AffinePoint (FVar Field))
xhatCircuit { lagrangeAt, blindingH } publicInput =
  publicInputCommit
    { curveParams: curveParams (Proxy @VestaG)
    , lagrangeAt
    , blindingH
    , correctionMode: InCircuitCorrections
    }
    publicInput

compileXhat :: XhatParams Field -> CompiledCircuit Field
compileXhat srsData =
  compilePure (Proxy @(Vector 34 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ xhatCircuit srsData (parseXhatInput inputs))
    Kimchi.initialState
