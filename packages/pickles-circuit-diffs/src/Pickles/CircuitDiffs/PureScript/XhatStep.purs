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
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode(..), LagrangeBaseLookup, publicInputCommit)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, SizedF, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type XhatStepParams f =
  { lagrangeAt :: LagrangeBaseLookup 1 f
  , blindingH :: AffinePoint (F f)
  }

type XhatStepPublicInput =
  Tuple
    (Vector 5 (FVar StepField))
    ( Tuple (Vector 2 (SizedF 128 (FVar StepField)))
        ( Tuple (Vector 3 (SizedF 128 (FVar StepField)))
            ( Tuple (Vector 3 (FVar StepField))
                (Tuple (Vector 16 (SizedF 128 (FVar StepField))) (SizedF 10 (FVar StepField)))
            )
        )
    )

parseXhatStepInput :: Vector 30 (FVar StepField) -> XhatStepPublicInput
parseXhatStepInput inputs =
  let
    at = unsafeIdx inputs
  in
    Tuple
      ((Vector.generate \j -> at (getFinite j)) :: Vector 5 (FVar StepField))
      ( Tuple
          ((Vector.generate \j -> asSizedF128 (at (5 + getFinite j))) :: Vector 2 (SizedF 128 (FVar StepField)))
          ( Tuple
              ((Vector.generate \j -> asSizedF128 (at (7 + getFinite j))) :: Vector 3 (SizedF 128 (FVar StepField)))
              ( Tuple
                  ((Vector.generate \j -> at (10 + getFinite j)) :: Vector 3 (FVar StepField))
                  ( Tuple
                      ((Vector.generate \j -> asSizedF128 (at (13 + getFinite j))) :: Vector 16 (SizedF 128 (FVar StepField)))
                      (asSizedF10 (at 29))
                  )
              )
          )
      )

xhatStepCircuit
  :: forall pi t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => PublicInputCommit pi StepField
  => XhatStepParams StepField
  -> pi
  -> Snarky (KimchiConstraint StepField) t m (Vector 1 (AffinePoint (FVar StepField)))
xhatStepCircuit { lagrangeAt, blindingH } publicInput =
  publicInputCommit @1
    { curveParams: curveParams (Proxy @PallasG)
    , lagrangeAt
    , blindingH
    , correctionMode: PureCorrections
    }
    publicInput

compileXhatStep :: XhatStepParams StepField -> CompiledCircuit StepField
compileXhatStep srsData =
  compilePure (Proxy @(Vector 30 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ xhatStepCircuit srsData (parseXhatStepInput inputs))
    Kimchi.initialState
