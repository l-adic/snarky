module Snarky.Circuit.Types where

import Prelude

import Data.Array (foldMap)
import Data.Array as Array
import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments(..), Product(..), from, repOf, to)
import Data.Maybe (fromJust)
import Data.Newtype (class Newtype)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple)
import Partial.Unsafe (unsafePartial)
import Prim.Row as Row
import Prim.RowList (class RowToList)
import Prim.RowList as RL
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar)
import Snarky.Circuit.Constraint.Class (class R1CSSystem, boolean)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector, toVector, unVector)
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy(..))

newtype Variable = Variable Int

derive newtype instance Eq Variable
derive newtype instance Show Variable
derive newtype instance Ord Variable

newtype Bool a = Bool a

derive newtype instance Eq a => Eq (Bool a)
derive newtype instance Show a => Show (Bool a)
derive instance Newtype (Bool a) _

newtype F f = F f

derive newtype instance Eq f => Eq (F f)
derive newtype instance Arbitrary f => Arbitrary (F f)
derive newtype instance Show f => Show (F f)
derive newtype instance Semiring f => Semiring (F f)
derive newtype instance Ring f => Ring (F f)
derive newtype instance EuclideanRing f => EuclideanRing (F f)
derive newtype instance CommutativeRing f => CommutativeRing (F f)
derive instance Newtype (F f) _

newtype UnChecked a = UnChecked a

derive instance Eq a => Eq (UnChecked a)
derive newtype instance Show a => Show (UnChecked a)
derive instance Newtype (UnChecked a) _

--------------------------------------------------------------------------------


class (CircuitType f a var, CheckType var c) <= ConstrainedType f a c var | c -> f, f a -> var c

--------------------------------------------------------------------------------

class CircuitType :: Type -> Type -> Type -> Constraint
class CircuitType f a var | var -> f, f a -> var where
  valueToFields :: a -> Array f
  fieldsToValue :: Array f -> a
  sizeInFields :: Proxy f -> Proxy a -> Int
  varToFields :: var -> Array (CVar f Variable)
  fieldsToVar :: Array (CVar f Variable) -> var

instance CircuitType f Unit Unit where
  valueToFields _ = mempty
  fieldsToValue _ = unit
  sizeInFields _ _ = 0
  varToFields _ = mempty
  fieldsToVar _ = unit

instance CircuitType f (F f) (CVar f Variable) where
  valueToFields = Array.singleton <<< coerce
  fieldsToValue a = coerce $ unsafePartial fromJust $ Array.head a
  sizeInFields _ _ = 1
  varToFields = Array.singleton
  fieldsToVar a = unsafePartial fromJust $ Array.head a

instance PrimeField f => CircuitType f Boolean (CVar f (Bool Variable)) where
  valueToFields b = Array.singleton $ if b then one @f else zero
  fieldsToValue a =
    let
      b = unsafePartial fromJust $ Array.head a
    in
      b == one
  sizeInFields _ _ = 1
  fieldsToVar x = coerce $ unsafePartial $ fromJust $ Array.head x
  varToFields = Array.singleton <<< coerce

instance
  ( CircuitType f a avar
  , Generic a arep
  , CircuitType f b bvar
  , Generic b brep
  ) =>
  CircuitType f (Tuple a b) (Tuple avar bvar) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields (Proxy @(Tuple a b))
  fieldsToVar = genericFieldsToVar (Proxy @(Tuple a b))

instance (CircuitType f a var, Reflectable n Int) => CircuitType f (Vector n a) (Vector n var) where
  valueToFields as = foldMap valueToFields (unVector as)
  fieldsToValue as =
    let
      chunks = chunk (sizeInFields (Proxy @f) (Proxy @a)) as
      vals = fieldsToValue <$> chunks
    in
      unsafePartial $ fromJust $ toVector (Proxy @n) vals
  sizeInFields pf _ = reflectType (Proxy @n) * sizeInFields pf (Proxy @a)
  varToFields as = foldMap (varToFields @f @a) (unVector as)
  fieldsToVar as =
    let
      chunks = chunk (sizeInFields (Proxy @f) (Proxy @a)) as
      vals = fieldsToVar @f @a <$> chunks
    in
      unsafePartial $ fromJust $ toVector (Proxy @n) vals

instance CircuitType f a var => CircuitType f (UnChecked a) (CVar f (UnChecked Variable)) where
  valueToFields (UnChecked a) = valueToFields @f @a a
  fieldsToValue a = UnChecked $ fieldsToValue @f @a a
  sizeInFields pf _ = sizeInFields pf (Proxy @a)
  fieldsToVar x = coerce $ unsafePartial $ fromJust $ Array.head x
  varToFields = Array.singleton <<< coerce

instance (RowToList r rl, RowToList var rlvar, RCircuitType f rl rlvar r var) => CircuitType f (Record r) (Record var) where
  fieldsToValue = rFieldsToValue @f @rl @rlvar @r (Proxy @rl)
  valueToFields = rValueToFields @f @rl @rlvar @r (Proxy @rl)
  sizeInFields pf _ = rSizeInFields pf (Proxy @rl) (Proxy @rlvar)
  fieldsToVar = rFieldsToVar @f @rl @rlvar (Proxy @rlvar)
  varToFields = rVarToFields @f @rl @rlvar @r (Proxy @rlvar)

--------------------------------------------------------------------------------

class GCircuitType :: Type -> Type -> Type -> Constraint
class GCircuitType f a var | var -> f, f a -> var where
  gValueToFields :: a -> Array f
  gFieldsToValue :: Array f -> a
  gSizeInFields :: Proxy f -> Proxy a -> Int
  gVarToFields :: var -> Array (CVar f Variable)
  gFieldsToVar :: Array (CVar f Variable) -> var

instance GCircuitType f NoArguments NoArguments where
  gValueToFields _ = mempty
  gFieldsToValue _ = NoArguments
  gSizeInFields _ _ = 0
  gVarToFields _ = mempty
  gFieldsToVar _ = NoArguments

instance CircuitType f a var => GCircuitType f (Argument a) (Argument var) where
  gValueToFields (Argument a) = valueToFields @f @a a
  gFieldsToValue as = Argument $ fieldsToValue @f @a as
  gSizeInFields pf _ = sizeInFields pf (Proxy @a)
  gVarToFields (Argument a) = varToFields @f @a a
  gFieldsToVar as = Argument $ fieldsToVar @f @a as

instance (GCircuitType f a avar, GCircuitType f b bvar) => GCircuitType f (Product a b) (Product avar bvar) where
  gValueToFields (Product a b) = gValueToFields @f @a a <> gValueToFields @f @b b
  gFieldsToValue fs =
    let
      { before: as, after: bs } = Array.splitAt (gSizeInFields (Proxy @f) (Proxy @a)) fs
    in
      Product (gFieldsToValue @f @a as) (gFieldsToValue @f @b bs)
  gSizeInFields pf _ = gSizeInFields pf (Proxy @a) + gSizeInFields pf (Proxy @b)
  gVarToFields (Product a b) = gVarToFields @f @a a <> gVarToFields @f @b b
  gFieldsToVar fs =
    let
      { before: as, after: bs } = Array.splitAt (gSizeInFields (Proxy @f) (Proxy @a)) fs
    in
      Product (gFieldsToVar @f @a as) (gFieldsToVar @f @b bs)

instance GCircuitType f a avar => GCircuitType f (Constructor name a) (Constructor name avar) where
  gValueToFields (Constructor a) = gValueToFields @f @a a
  gFieldsToValue as = Constructor $ gFieldsToValue @f @a as
  gSizeInFields pf _ = gSizeInFields @f @a pf (Proxy @a)
  gVarToFields (Constructor a) = gVarToFields @f @a a
  gFieldsToVar fs = Constructor $ gFieldsToVar @f @a fs

genericValueToFields :: forall f a var rep. Generic a rep => GCircuitType f rep var => a -> Array f
genericValueToFields = gValueToFields @f @rep <<< from

genericFieldsToValue :: forall f a var rep. Generic a rep => GCircuitType f rep var => Array f -> a
genericFieldsToValue = to <<< gFieldsToValue @f @rep

genericSizeInFields :: forall f a b rep. Generic a rep => GCircuitType f rep b => Proxy f -> Proxy a -> Int
genericSizeInFields pf pa = gSizeInFields @f @rep @b pf (repOf pa)

genericVarToFields
  :: forall f a rep var var'
   . Generic var var'
  => Generic a rep
  => GCircuitType f rep var'
  => Proxy a
  -> var
  -> Array (CVar f Variable)
genericVarToFields _ var = gVarToFields @f @rep $ from var

genericFieldsToVar
  :: forall f a rep var var'
   . Generic var var'
  => Generic a rep
  => GCircuitType f rep var'
  => Proxy a
  -> Array (CVar f Variable)
  -> var
genericFieldsToVar _ fs = to $ gFieldsToVar @f @rep fs

--------------------------------------------------------------------------------

class RCircuitType :: Type -> RL.RowList Type -> RL.RowList Type -> Row Type -> Row Type -> Constraint
class RCircuitType f rl rlvar r var | rl -> r, rlvar -> var, var -> f, f r -> var where
  rValueToFields :: Proxy rl -> Record r -> Array f
  rFieldsToValue :: Proxy rl -> Array f -> Record r
  rSizeInFields :: Proxy f -> Proxy rl -> Proxy rlvar -> Int
  rVarToFields :: Proxy rlvar -> Record var -> Array (CVar f Variable)
  rFieldsToVar :: Proxy rlvar -> Array (CVar f Variable) -> Record var

instance RCircuitType f RL.Nil RL.Nil () () where
  rValueToFields _ _ = mempty
  rFieldsToValue _ _ = {}
  rSizeInFields _ _ _ = 0
  rVarToFields _ _ = mempty
  rFieldsToVar _ _ = {}

instance
  ( IsSymbol s
  , Row.Cons s a rest r
  , Row.Cons s avar restvars vars
  , Row.Lacks s rest
  , Row.Lacks s restvars
  , CircuitType f a avar
  , RCircuitType f tail tailvars rest restvars
  ) =>
  RCircuitType f (RL.Cons s a tail) (RL.Cons s avar tailvars) r vars where
  rValueToFields _ r =
    let
      afs = valueToFields @f @a $ Record.get (Proxy @s) r
      asfs = rValueToFields @f @tail @tailvars (Proxy @tail) $ Record.delete (Proxy @s) r
    in
      afs <> asfs
  rFieldsToValue _ fs =
    let
      { before, after } = Array.splitAt (sizeInFields (Proxy @f) (Proxy @a)) fs
      a = fieldsToValue @f @a before
      as = rFieldsToValue @f @tail @tailvars (Proxy @tail) after
    in
      Record.insert (Proxy @s) a as
  rSizeInFields pf _ _ = sizeInFields pf (Proxy @a) + rSizeInFields pf (Proxy @tail) (Proxy @tailvars)
  rVarToFields _ r =
    let
      afs = varToFields @f @a $ Record.get (Proxy @s) r
      asfs = rVarToFields @f @tail (Proxy @tailvars) $ Record.delete (Proxy @s) r
    in
      afs <> asfs
  rFieldsToVar _ fs =
    let
      { before, after } = Array.splitAt (sizeInFields (Proxy @f) (Proxy @a)) fs
      a = fieldsToVar @f @a before
      as = rFieldsToVar @f @tail (Proxy @tailvars) after
    in
      Record.insert (Proxy @s) a as

chunk :: forall a. Int -> Array a -> Array (Array a)
chunk n arr
  | n <= 0 = []
  | Array.null arr = []
  | otherwise =
      let
        current = Array.take n arr
        rest = Array.drop n arr
      in
        [ current ] <> chunk n rest

--------------------------------------------------------------------------------

class CheckType var c where
  check :: var -> Array c

instance CheckType (CVar f Variable) c where
  check _ = mempty

instance CheckType (UnChecked a) c where
  check _ = mempty

instance R1CSSystem (CVar f Variable) c => CheckType (CVar f (Bool Variable)) c where
  check var = Array.singleton $ boolean (coerce var :: CVar f Variable)

instance (CheckType avar c, CheckType bvar c) => CheckType (Tuple avar bvar) c where
  check = genericCheck

instance (RowToList r rl, RCheckType rl r c) => CheckType (Record r) c where
  check :: Record r -> Array c
  check = rCheck (Proxy @rl)

--------------------------------------------------------------------------------

class GCheckType var c where
  gCheck :: var -> Array c

instance GCheckType NoArguments c where
  gCheck _ = mempty

instance CheckType var c => GCheckType (Argument var) c where
  gCheck (Argument a) = check a

instance (GCheckType avar c, GCheckType bvar c) => GCheckType (Product avar bvar) c where
  gCheck (Product a b) = gCheck a <> gCheck b

instance GCheckType var c => GCheckType (Constructor name var) c where
  gCheck (Constructor a) = gCheck a

genericCheck :: forall var rep c. Generic var rep => GCheckType rep c => var -> Array c
genericCheck = gCheck @rep <<< from

--------------------------------------------------------------------------------

class RCheckType :: RL.RowList Type -> Row Type -> Type -> Constraint
class RCheckType rl var c | rl -> var where
  rCheck :: Proxy rl -> Record var -> Array c

instance RCheckType RL.Nil () c where
  rCheck _ _ = mempty

instance
  ( IsSymbol s
  , Row.Cons s var rest r
  , Row.Lacks s rest
  , CheckType var c
  , RCheckType tail rest c
  ) =>
  RCheckType (RL.Cons s a tail) r c where
  rCheck _ r =
    let
      afs = check $ Record.get (Proxy @s) r
      asfs = rCheck (Proxy @tail) $ Record.delete (Proxy @s) r
    in
      afs <> asfs