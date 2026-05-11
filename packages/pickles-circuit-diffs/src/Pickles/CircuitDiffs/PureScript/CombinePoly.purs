module Pickles.CircuitDiffs.PureScript.CombinePoly
  ( CombinePolyInput
  , parseCombinePolyInput
  , combinePolyCircuit
  , compileCombinePoly
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Maybe (Maybe(..), fromJust)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.IPA (combinePolynomials)
import Pickles.Wrap.Types (Field)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, SizedF, Snarky, const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type CombinePolyInput f =
  { xHat :: AffinePoint (FVar f)
  , ftComm :: AffinePoint (FVar f)
  , zComm :: AffinePoint (FVar f)
  , wComm :: Vector 15 (AffinePoint (FVar f))
  , xi :: SizedF 128 (FVar f)
  }

parseCombinePolyInput :: Vector 37 (FVar Field) -> CombinePolyInput Field
parseCombinePolyInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
  in
    { xHat: readPt 0
    , ftComm: readPt 2
    , zComm: readPt 4
    , wComm: Vector.generate \j -> readPt (6 + 2 * getFinite j)
    , xi: asSizedF128 (at 36)
    }

combinePolyCircuit
  :: forall t m
   . CircuitM Field (KimchiConstraint Field) t m
  => CombinePolyInput Field
  -> Snarky (KimchiConstraint Field) t m (AffinePoint (FVar Field))
combinePolyCircuit input =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: VestaG)

    dummyPt :: AffinePoint (FVar Field)
    dummyPt = { x: const_ g.x, y: const_ g.y }

    indexComms :: Vector 6 (AffinePoint (FVar Field))
    indexComms = Vector.generate \_ -> dummyPt

    coeffComms :: Vector 15 (AffinePoint (FVar Field))
    coeffComms = Vector.generate \_ -> dummyPt

    sigmaComms :: Vector 6 (AffinePoint (FVar Field))
    sigmaComms = Vector.generate \_ -> dummyPt

    allBases :: Vector 45 (AffinePoint (FVar Field))
    allBases =
      (input.xHat :< input.ftComm :< input.zComm :< Vector.nil)
        `Vector.append` indexComms
        `Vector.append` input.wComm
        `Vector.append` coeffComms
        `Vector.append` sigmaComms
  in
    combinePolynomials allBases (Vector.replicate Nothing) input.xi

compileCombinePoly :: CompiledCircuit Field
compileCombinePoly =
  compilePure (Proxy @(Vector 37 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ combinePolyCircuit (parseCombinePolyInput inputs))
    Kimchi.initialState
