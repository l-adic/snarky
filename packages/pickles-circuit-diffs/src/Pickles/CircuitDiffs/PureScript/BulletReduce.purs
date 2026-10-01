module Pickles.CircuitDiffs.PureScript.BulletReduce
  ( BulletReduceInput(..)
  , compileBulletReduce
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (WrapField)
import Pickles.IPA (LrPair, bulletReduceCircuit)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, SizedF, Snarky, UnChecked(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (VestaG)
import Type.Proxy (Proxy(..))

-- | `bullet_reduce_{step,wrap}_circuit`'s input (OCaml `dump_circuit_impl.ml`): the `n`
-- | `(L, R)` pairs, then the `n` raw round prechallenges.
newtype BulletReduceInput n f sf = BulletReduceInput
  { pairs :: Vector n (LrPair f)
  , challenges :: Vector n sf
  }

-- | The wire order.
type BulletReduceTuple n f sf = Tuple2 (Vector n (LrPair f)) (Vector n sf)

toTuple :: forall n f sf. BulletReduceInput n f sf -> BulletReduceTuple n f sf
toTuple (BulletReduceInput i) = tuple2 i.pairs i.challenges

fromTuple :: forall n f sf. BulletReduceTuple n f sf -> BulletReduceInput n f sf
fromTuple = uncurry2 \pairs challenges -> BulletReduceInput { pairs, challenges }

instance
  ( Reflectable n Int
  , CircuitType f (LrPair fa) (LrPair fv)
  , CircuitType f sa sv
  ) =>
  CircuitType f (BulletReduceInput n fa sa) (BulletReduceInput n fv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(BulletReduceTuple n fa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(BulletReduceTuple n fa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(BulletReduceTuple n fa sa)

bulletReduceWrapCircuit
  :: forall r
   . UnChecked (BulletReduceInput 16 (FVar WrapField) (SizedF 128 (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
bulletReduceWrapCircuit (UnChecked (BulletReduceInput i)) =
  void $ bulletReduceCircuit @WrapField @VestaG i

compileBulletReduce :: Effect (CompiledCircuit WrapField)
compileBulletReduce =
  compile noAdvice (Proxy @(UnChecked (BulletReduceInput 16 WrapField (SizedF 128 (F WrapField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    bulletReduceWrapCircuit
