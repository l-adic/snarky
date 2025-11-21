module Snarky.Circuit.Types
  ( Variable(..)
  , F(..)
  , Bool(..)
  , UnChecked(..)
  , class ConstrainedType
  , valueToFields
  , fieldsToValue
  , sizeInFields
  , varToFields
  , fieldsToVar
  , check
  , genericValueToFields
  , genericFieldsToValue
  , genericSizeInFields
  , genericVarToFields
  , genericFieldsToVar
  , genericCheck

  -- Obligatory exports
  , class GConstrainedType
  , gValueToFields
  , gFieldsToValue
  , gSizeInFields
  , gVarToFields
  , gFieldsToVar
  , gCheck

  , class RConstrainedType
  , rValueToFields
  , rFieldsToValue
  , rSizeInFields
  , rVarToFields
  , rFieldsToVar
  , rCheck
  ) where

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
derive instance Generic (Bool f) _

newtype F f = F f

derive newtype instance Eq f => Eq (F f)
derive newtype instance Arbitrary f => Arbitrary (F f)
derive newtype instance Show f => Show (F f)
derive newtype instance Semiring f => Semiring (F f)
derive newtype instance Ring f => Ring (F f)
derive newtype instance EuclideanRing f => EuclideanRing (F f)
derive newtype instance CommutativeRing f => CommutativeRing (F f)
derive instance Newtype (F f) _
derive instance Generic (F f) _

newtype UnChecked a = UnChecked a

derive instance Eq a => Eq (UnChecked a)
derive newtype instance Show a => Show (UnChecked a)
derive instance Newtype (UnChecked a) _
derive instance Generic (UnChecked f) _

--------------------------------------------------------------------------------

class ConstrainedType :: Type -> Type -> Type -> Type -> Constraint
class ConstrainedType f a c var | c -> f, f a -> var c, var -> f where
  valueToFields :: a -> Array f
  fieldsToValue :: Array f -> a
  sizeInFields :: Proxy f -> Proxy a -> Int
  varToFields :: var -> Array (CVar f Variable)
  fieldsToVar :: Array (CVar f Variable) -> var
  check :: var -> Array c

instance ConstrainedType f Unit c Unit where
  valueToFields _ = mempty
  fieldsToValue _ = unit
  sizeInFields _ _ = 0
  varToFields _ = mempty
  fieldsToVar _ = unit
  check _ = mempty

instance ConstrainedType f (F f) c (CVar f Variable) where
  valueToFields = Array.singleton <<< coerce
  fieldsToValue a = coerce $ unsafePartial fromJust $ Array.head a
  sizeInFields _ _ = 1
  varToFields = Array.singleton
  fieldsToVar a = unsafePartial fromJust $ Array.head a
  check _ = mempty

instance (PrimeField f, R1CSSystem (CVar f Variable) c) => ConstrainedType f Boolean c (CVar f (Bool Variable)) where
  valueToFields b = Array.singleton $ if b then one @f else zero
  fieldsToValue a =
    let
      b = unsafePartial fromJust $ Array.head a
    in
      b == one
  sizeInFields _ _ = 1
  fieldsToVar x = coerce $ unsafePartial $ fromJust $ Array.head x
  varToFields = Array.singleton <<< coerce
  check var = Array.singleton $ boolean (coerce var :: CVar f Variable)

instance
  ( ConstrainedType f a c avar
  , ConstrainedType f b c bvar
  ) =>
  ConstrainedType f (Tuple a b) c (Tuple avar bvar) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields (Proxy @(Tuple a b))
  fieldsToVar = genericFieldsToVar (Proxy @(Tuple a b))
  check = genericCheck (Proxy @(Tuple a b))

instance (ConstrainedType f a c var, Reflectable n Int) => ConstrainedType f (Vector n a) c (Vector n var) where
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
  check var = foldMap (check @f @a) (unVector var)

instance ConstrainedType f a c var => ConstrainedType f (UnChecked a) c (UnChecked var) where
  valueToFields (UnChecked a) = valueToFields @f @a a
  fieldsToValue a = UnChecked $ fieldsToValue @f @a a
  sizeInFields pf _ = sizeInFields pf (Proxy @a)
  varToFields (UnChecked a) = varToFields @f @a a
  fieldsToVar a = UnChecked $ fieldsToVar @f @a a
  check _ = mempty

instance (RowToList r rl, RowToList var rlvar, RConstrainedType f rl rlvar r c var) => ConstrainedType f (Record r) c (Record var) where
  fieldsToValue = rFieldsToValue @f @rl @rlvar @r @c (Proxy @rl)
  valueToFields = rValueToFields @f @rl @rlvar @r @c (Proxy @rl)
  sizeInFields pf _ = rSizeInFields @f @rl @rlvar @r @c pf (Proxy @rl) (Proxy @rlvar)
  fieldsToVar = rFieldsToVar @f @rl @rlvar @r @c (Proxy @rlvar)
  varToFields = rVarToFields @f @rl @rlvar @r @c (Proxy @rlvar)
  check = rCheck @f @rl @rlvar @r @c (Proxy @rl)

--------------------------------------------------------------------------------

class GConstrainedType :: Type -> Type -> Type -> Type -> Constraint
class GConstrainedType f a c var | c -> f, f a -> var c, var -> f where
  gValueToFields :: a -> Array f
  gFieldsToValue :: Array f -> a
  gSizeInFields :: Proxy f -> Proxy a -> Int
  gVarToFields :: var -> Array (CVar f Variable)
  gFieldsToVar :: Array (CVar f Variable) -> var
  gCheck :: var -> Array c

instance GConstrainedType f NoArguments c NoArguments where
  gValueToFields _ = mempty
  gFieldsToValue _ = NoArguments
  gSizeInFields _ _ = 0
  gVarToFields _ = mempty
  gFieldsToVar _ = NoArguments
  gCheck _ = mempty

instance ConstrainedType f a c var => GConstrainedType f (Argument a) c (Argument var) where
  gValueToFields (Argument a) = valueToFields @f @a a
  gFieldsToValue as = Argument $ fieldsToValue @f @a as
  gSizeInFields pf _ = sizeInFields pf (Proxy @a)
  gVarToFields (Argument a) = varToFields @f @a a
  gFieldsToVar as = Argument $ fieldsToVar @f @a as
  gCheck (Argument a) = check @f @a a

instance (GConstrainedType f a c avar, GConstrainedType f b c bvar) => GConstrainedType f (Product a b) c (Product avar bvar) where
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
  gCheck (Product a b) = gCheck @f @a a <> gCheck @f @b b

instance GConstrainedType f a c avar => GConstrainedType f (Constructor name a) c (Constructor name avar) where
  gValueToFields (Constructor a) = gValueToFields @f @a a
  gFieldsToValue as = Constructor $ gFieldsToValue @f @a as
  gSizeInFields pf _ = gSizeInFields @f @a pf (Proxy @a)
  gVarToFields (Constructor a) = gVarToFields @f @a a
  gFieldsToVar fs = Constructor $ gFieldsToVar @f @a fs
  gCheck (Constructor a) = gCheck @f @a a

genericValueToFields :: forall f a c var rep. Generic a rep => GConstrainedType f rep c var => a -> Array f
genericValueToFields = gValueToFields @f @rep <<< from

genericFieldsToValue :: forall f a c var rep. Generic a rep => GConstrainedType f rep c var => Array f -> a
genericFieldsToValue = to <<< gFieldsToValue @f @rep

genericSizeInFields :: forall f a b c rep. Generic a rep => GConstrainedType f rep c b => Proxy f -> Proxy a -> Int
genericSizeInFields pf pa = gSizeInFields @f @rep @c @b pf (repOf pa)

genericVarToFields
  :: forall f a c rep var var'
   . Generic var var'
  => Generic a rep
  => GConstrainedType f rep c var'
  => Proxy a
  -> var
  -> Array (CVar f Variable)
genericVarToFields _ var = gVarToFields @f @rep $ from var

genericFieldsToVar
  :: forall f a c rep var var'
   . Generic var var'
  => Generic a rep
  => GConstrainedType f rep c var'
  => Proxy a
  -> Array (CVar f Variable)
  -> var
genericFieldsToVar _ fs = to $ gFieldsToVar @f @rep fs

genericCheck
  :: forall f a c rep var var'
   . Generic var var'
  => Generic a rep
  => GConstrainedType f rep c var'
  => Proxy a
  -> var
  -> Array c
genericCheck _ var = gCheck @f @rep @c $ from var

--------------------------------------------------------------------------------

class RConstrainedType :: Type -> RL.RowList Type -> RL.RowList Type -> Row Type -> Type -> Row Type -> Constraint
class RConstrainedType f rl rlvar r c var | rl -> r, rlvar -> var, var -> f, f r -> var c, c -> f, rl -> rlvar where
  rValueToFields :: Proxy rl -> Record r -> Array f
  rFieldsToValue :: Proxy rl -> Array f -> Record r
  rSizeInFields :: Proxy f -> Proxy rl -> Proxy rlvar -> Int
  rVarToFields :: Proxy rlvar -> Record var -> Array (CVar f Variable)
  rFieldsToVar :: Proxy rlvar -> Array (CVar f Variable) -> Record var
  rCheck :: Proxy rl -> Record var -> Array c

instance RConstrainedType f RL.Nil RL.Nil () c () where
  rValueToFields _ _ = mempty
  rFieldsToValue _ _ = {}
  rSizeInFields _ _ _ = 0
  rVarToFields _ _ = mempty
  rFieldsToVar _ _ = {}
  rCheck _ _ = mempty

instance
  ( IsSymbol s
  , Row.Cons s a rest r
  , Row.Cons s avar restvars vars
  , Row.Lacks s rest
  , Row.Lacks s restvars
  , ConstrainedType f a c avar
  , RConstrainedType f tail tailvars rest c restvars
  ) =>
  RConstrainedType f (RL.Cons s a tail) (RL.Cons s avar tailvars) r c vars where
  rValueToFields _ r =
    let
      afs = valueToFields @f @a $ Record.get (Proxy @s) r
      asfs = rValueToFields @f @tail @tailvars @rest @c (Proxy @tail) $ Record.delete (Proxy @s) r
    in
      afs <> asfs
  rFieldsToValue _ fs =
    let
      { before, after } = Array.splitAt (sizeInFields (Proxy @f) (Proxy @a)) fs
      a = fieldsToValue @f @a before
      as = rFieldsToValue @f @tail @tailvars @rest @c (Proxy @tail) after
    in
      Record.insert (Proxy @s) a as
  rSizeInFields pf _ _ = sizeInFields pf (Proxy @a) + rSizeInFields @f @tail @tailvars @rest @c pf (Proxy @tail) (Proxy @tailvars)
  rVarToFields _ r =
    let
      afs = varToFields @f @a $ Record.get (Proxy @s) r
      asfs = rVarToFields @f @tail @tailvars @rest @c (Proxy @tailvars) $ Record.delete (Proxy @s) r
    in
      afs <> asfs
  rFieldsToVar _ fs =
    let
      { before, after } = Array.splitAt (sizeInFields (Proxy @f) (Proxy @a)) fs
      a = fieldsToVar @f @a before
      as = rFieldsToVar @f @tail @tailvars @rest @c (Proxy @tailvars) after
    in
      Record.insert (Proxy @s) a as
  rCheck _ r =
    let
      afs = check @f @a $ Record.get (Proxy @s) r
      asfs = rCheck @f @tail @tailvars @rest @c (Proxy @tail) $ Record.delete (Proxy @s) r
    in
      afs <> asfs

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