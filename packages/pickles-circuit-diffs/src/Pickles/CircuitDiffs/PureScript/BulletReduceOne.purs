module Pickles.CircuitDiffs.PureScript.BulletReduceOne
  ( BulletReduceOneInput(..)
  , compileBulletReduceOne
  ) where

import Prelude

import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (WrapField)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, SizedF, Snarky, UnChecked(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (addComplete, endo, endoInv)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | `bullet_reduce_one_{step,wrap}_circuit`'s input (OCaml `dump_circuit_impl.ml`): one
-- | round's `L` and `R` and its raw prechallenge `u`.
newtype BulletReduceOneInput pt sf = BulletReduceOneInput
  { l :: pt
  , r :: pt
  , u :: sf
  }

-- | The wire order.
type BulletReduceOneTuple pt sf = Tuple3 pt pt sf

toTuple :: forall pt sf. BulletReduceOneInput pt sf -> BulletReduceOneTuple pt sf
toTuple (BulletReduceOneInput i) = tuple3 i.l i.r i.u

fromTuple :: forall pt sf. BulletReduceOneTuple pt sf -> BulletReduceOneInput pt sf
fromTuple = uncurry3 \l r u -> BulletReduceOneInput { l, r, u }

instance
  ( CircuitType f pa pv
  , CircuitType f sa sv
  ) =>
  CircuitType f (BulletReduceOneInput pa sa) (BulletReduceOneInput pv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(BulletReduceOneTuple pa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(BulletReduceOneTuple pa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(BulletReduceOneTuple pa sa)

bulletReduceOneCircuit
  :: forall r
   . UnChecked (BulletReduceOneInput (AffinePoint (FVar WrapField)) (SizedF 128 (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
bulletReduceOneCircuit (UnChecked (BulletReduceOneInput i)) = do
  lScaled <- endoInv @WrapField @Vesta.ScalarField @VestaG i.l i.u
  rScaled <- endo @128 @32 i.r i.u
  void $ addComplete lScaled rScaled

compileBulletReduceOne :: Effect (CompiledCircuit WrapField)
compileBulletReduceOne =
  compile noAdvice
    (Proxy @(UnChecked (BulletReduceOneInput (AffinePoint WrapField) (SizedF 128 (F WrapField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    bulletReduceOneCircuit
