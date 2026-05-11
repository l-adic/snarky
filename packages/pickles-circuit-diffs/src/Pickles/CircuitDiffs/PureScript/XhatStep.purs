module Pickles.CircuitDiffs.PureScript.XhatStep
  ( XhatStepPublicInput
  , parseXhatStepInput
  , xhatStepCircuit
  , compileXhatStep
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF10, asSizedF128, unsafeIdx)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode(..), LagrangeBaseLookup, publicInputCommit)
import Pickles.Step.Types (Field)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, SizedF, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type XhatStepParams f =
  { lagrangeAt :: LagrangeBaseLookup f
  , blindingH :: AffinePoint (F f)
  }

type XhatStepPublicInput =
  Tuple
    (Vector 5 (FVar Field))
    ( Tuple (Vector 2 (SizedF 128 (FVar Field)))
        ( Tuple (Vector 3 (SizedF 128 (FVar Field)))
            ( Tuple (Vector 3 (FVar Field))
                (Tuple (Vector 16 (SizedF 128 (FVar Field))) (SizedF 10 (FVar Field)))
            )
        )
    )

parseXhatStepInput :: Vector 30 (FVar Field) -> XhatStepPublicInput
parseXhatStepInput inputs =
  let
    at = unsafeIdx inputs
  in
    Tuple
      ((Vector.generate \j -> at (getFinite j)) :: Vector 5 (FVar Field))
      ( Tuple
          ((Vector.generate \j -> asSizedF128 (at (5 + getFinite j))) :: Vector 2 (SizedF 128 (FVar Field)))
          ( Tuple
              ((Vector.generate \j -> asSizedF128 (at (7 + getFinite j))) :: Vector 3 (SizedF 128 (FVar Field)))
              ( Tuple
                  ((Vector.generate \j -> at (10 + getFinite j)) :: Vector 3 (FVar Field))
                  ( Tuple
                      ((Vector.generate \j -> asSizedF128 (at (13 + getFinite j))) :: Vector 16 (SizedF 128 (FVar Field)))
                      (asSizedF10 (at 29))
                  )
              )
          )
      )

xhatStepCircuit
  :: forall pi t m
   . CircuitM Field (KimchiConstraint Field) t m
  => PublicInputCommit pi Field
  => XhatStepParams Field
  -> pi
  -> Snarky (KimchiConstraint Field) t m (AffinePoint (FVar Field))
xhatStepCircuit { lagrangeAt, blindingH } publicInput =
  publicInputCommit
    { curveParams: curveParams (Proxy @PallasG)
    , lagrangeAt
    , blindingH
    , correctionMode: PureCorrections
    }
    publicInput

compileXhatStep :: XhatStepParams Field -> CompiledCircuit Field
compileXhatStep srsData =
  compilePure (Proxy @(Vector 30 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ xhatStepCircuit srsData (parseXhatStepInput inputs))
    Kimchi.initialState
