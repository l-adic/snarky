module Pickles.CircuitDiffs.PureScript.CombinePoly
  ( compileCombinePoly
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple.Nested (Tuple5, tuple5, uncurry5)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Partial.Unsafe (unsafePartial)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (WrapField)
import Pickles.IPA (combinePolynomials)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, SizedF, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | `combine_poly_wrap_circuit`'s input (OCaml `dump_circuit_impl.ml`).
newtype CombinePolyInput pt sf = CombinePolyInput
  { xHat :: pt
  , ftComm :: pt
  , zComm :: pt
  , wComm :: Vector 15 pt
  , xi :: sf
  }

-- | The wire order.
type CombinePolyTuple pt sf = Tuple5 pt pt pt (Vector 15 pt) sf

toTuple :: forall pt sf. CombinePolyInput pt sf -> CombinePolyTuple pt sf
toTuple (CombinePolyInput i) = tuple5 i.xHat i.ftComm i.zComm i.wComm i.xi

fromTuple :: forall pt sf. CombinePolyTuple pt sf -> CombinePolyInput pt sf
fromTuple = uncurry5 \xHat ftComm zComm wComm xi -> CombinePolyInput { xHat, ftComm, zComm, wComm, xi }

instance
  ( CircuitType f pa pv
  , CircuitType f sa sv
  ) =>
  CircuitType f (CombinePolyInput pa sa) (CombinePolyInput pv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(CombinePolyTuple pa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(CombinePolyTuple pa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(CombinePolyTuple pa sa)

combinePolyCircuit
  :: forall r
   . UnChecked (CombinePolyInput (AffinePoint (FVar WrapField)) (SizedF 128 (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
combinePolyCircuit (UnChecked (CombinePolyInput input)) =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: VestaG)

    dummyPt :: AffinePoint (FVar WrapField)
    dummyPt = AffinePoint { x: const_ g.x, y: const_ g.y }

    indexComms :: Vector 6 (AffinePoint (FVar WrapField))
    indexComms = Vector.generate \_ -> dummyPt

    coeffComms :: Vector 15 (AffinePoint (FVar WrapField))
    coeffComms = Vector.generate \_ -> dummyPt

    sigmaComms :: Vector 6 (AffinePoint (FVar WrapField))
    sigmaComms = Vector.generate \_ -> dummyPt

    allBases :: Vector 45 (AffinePoint (FVar WrapField))
    allBases =
      (input.xHat :< input.ftComm :< input.zComm :< Vector.nil)
        `Vector.append` indexComms
        `Vector.append` input.wComm
        `Vector.append` coeffComms
        `Vector.append` sigmaComms
  in
    void $ combinePolynomials allBases (Vector.replicate Nothing) input.xi

compileCombinePoly :: Effect (CompiledCircuit WrapField)
compileCombinePoly =
  compile noAdvice
    (Proxy @(UnChecked (CombinePolyInput (AffinePoint WrapField) (SizedF 128 (F WrapField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    combinePolyCircuit
