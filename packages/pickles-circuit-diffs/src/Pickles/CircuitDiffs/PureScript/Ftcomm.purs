module Pickles.CircuitDiffs.PureScript.Ftcomm
  ( FtcommInput(..)
  , compileFtcomm
  ) where

import Prelude

import Data.Maybe (fromJust)
import Data.Tuple.Nested (Tuple4, tuple4, uncurry4)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Partial.Unsafe (unsafePartial)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (WrapField)
import Pickles.IncrementallyVerifyProof (ftComm) as FtComm
import Pickles.Wrap.OtherField as WrapOtherField
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | `ftcomm_{step,wrap}_circuit`'s input (OCaml `dump_circuit_impl.ml`): the shifted scalars
-- | are split Type2 values on the step side, Type1 on the wrap side.
newtype FtcommInput pt s = FtcommInput
  { tComm :: Vector 7 pt
  , perm :: s
  , zetaToSrsLength :: s
  , zetaToDomainSize :: s
  }

-- | The wire order.
type FtcommTuple pt s = Tuple4 (Vector 7 pt) s s s

toTuple :: forall pt s. FtcommInput pt s -> FtcommTuple pt s
toTuple (FtcommInput i) = tuple4 i.tComm i.perm i.zetaToSrsLength i.zetaToDomainSize

fromTuple :: forall pt s. FtcommTuple pt s -> FtcommInput pt s
fromTuple = uncurry4 \tComm perm zetaToSrsLength zetaToDomainSize ->
  FtcommInput { tComm, perm, zetaToSrsLength, zetaToDomainSize }

instance
  ( CircuitType f pa pv
  , CircuitType f sa sv
  ) =>
  CircuitType f (FtcommInput pa sa) (FtcommInput pv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(FtcommTuple pa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(FtcommTuple pa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(FtcommTuple pa sa)

ftcommWrapCircuit
  :: forall r
   . UnChecked (FtcommInput (AffinePoint (FVar WrapField)) (Type1 (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
ftcommWrapCircuit (UnChecked (FtcommInput i)) =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: VestaG)
    sigmaLast = Vector.singleton (AffinePoint { x: const_ g.x, y: const_ g.y })
  in
    void $ FtComm.ftComm WrapOtherField.ipaScalarOps
      { sigmaLast
      , tComm: i.tComm
      , perm: i.perm
      , zetaToSrsLength: i.zetaToSrsLength
      , zetaToDomainSize: i.zetaToDomainSize
      }

compileFtcomm :: Effect (CompiledCircuit WrapField)
compileFtcomm =
  compile noAdvice (Proxy @(UnChecked (FtcommInput (AffinePoint WrapField) (Type1 (F WrapField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    ftcommWrapCircuit
