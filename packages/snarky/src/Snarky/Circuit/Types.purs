-- | Core types for circuit values and the CircuitType class.
-- |
-- | This module defines the fundamental types used to represent values in
-- | circuits, both in their "value" form (concrete field elements) and their
-- | "variable" form (circuit expressions).
-- |
-- | ## Type Pairs
-- |
-- | Each circuit type has a value form and a variable form:
-- |
-- | | Value Type | Variable Type | Description |
-- | |------------|---------------|-------------|
-- | | `F f`      | `FVar f`      | Field element |
-- | | `Boolean`  | `BoolVar f`   | Boolean (0 or 1) |
-- | | `Tuple a b`| `Tuple av bv` | Product types |
-- | | `Vector n a`| `Vector n av`| Fixed-size arrays |
-- | | `Record r` | `Record rv`   | Records |
-- |
-- | ## The CircuitType Class
-- |
-- | The `CircuitType` class provides conversions between value and variable
-- | representations, and tracks the "size in fields" (number of field elements)
-- | needed to represent a type.
-- |
-- | ```purescript
-- | -- A point has 2 field elements
-- | type Point f = { x :: F f, y :: F f }
-- | -- sizeInFields @Point = 2
-- |
-- | -- Convert values to/from field arrays
-- | valueToFields { x: F 1, y: F 2 } = [1, 2]
-- | fieldsToValue [1, 2] = { x: F 1, y: F 2 }
-- | ```
-- |
-- | ## Generic Derivation
-- |
-- | For custom types with `Generic` instances, use the `generic*` helpers:
-- |
-- | ```purescript
-- | newtype MyType = MyType { a :: F Field, b :: Boolean }
-- | derive instance Generic MyType _
-- |
-- | instance CircuitType Field MyType MyTypeVar where
-- |   valueToFields = genericValueToFields
-- |   fieldsToValue = genericFieldsToValue
-- |   -- ... etc
-- | ```
module Snarky.Circuit.Types
  ( F(..)
  , Bool(..)
  , UnChecked(..)
  , FVar
  , BoolVar
  , class CircuitType
  , valueToFields
  , fieldsToValue
  , sizeInFields
  , varToFields
  , fieldsToVar
  , genericValueToFields
  , genericFieldsToValue
  , genericSizeInFields
  , genericVarToFields
  , genericFieldsToVar
  -- Obligatory exports
  , class GCircuitType
  , gValueToFields
  , gFieldsToValue
  , gSizeInFields
  , gVarToFields
  , gFieldsToVar
  , class RCircuitType
  , rValueToFields
  , rFieldsToValue
  , rSizeInFields
  , rVarToFields
  , rFieldsToVar
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldMap)
import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments(..), Product(..), from, repOf, to)
import Data.Maybe (fromJust)
import Data.Newtype (class Newtype)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple)
import Data.Vector (Vector, toVector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import Prim.Row as Row
import Prim.RowList (class RowToList)
import Prim.RowList as RL
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar, Variable)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField, endoBase, endoScalar, fromBigInt, modulus, pow, toBigInt)
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy(..))

-- | Wrapper for boolean values in circuits.
-- |
-- | `Bool` wraps a representation type `a` to indicate it represents a boolean.
-- | For values, `a` is typically `Boolean`. For variables, `a` is `Variable`.
newtype Bool a = Bool a

derive newtype instance Eq a => Eq (Bool a)
derive newtype instance Show a => Show (Bool a)
derive newtype instance Arbitrary a => Arbitrary (Bool a)
derive instance Newtype (Bool a) _
derive instance Generic (Bool f) _

-- | Wrapper for field elements in their value form.
-- |
-- | `F f` wraps a field element to distinguish it from raw field values
-- | when used with the `CircuitType` class.
newtype F f = F f

instance FieldSizeInBits f n => FieldSizeInBits (F f) n

derive newtype instance Eq f => Eq (F f)
derive newtype instance Ord f => Ord (F f)
derive newtype instance Arbitrary f => Arbitrary (F f)
derive newtype instance Show f => Show (F f)
derive newtype instance Semiring f => Semiring (F f)
derive newtype instance Ring f => Ring (F f)
derive newtype instance EuclideanRing f => EuclideanRing (F f)
derive newtype instance CommutativeRing f => CommutativeRing (F f)
derive newtype instance DivisionRing f => DivisionRing (F f)
derive newtype instance PoseidonField f => PoseidonField (F f)

instance HasEndo f f' => HasEndo (F f) (F f') where
  endoBase = coerce (endoBase :: f)
  endoScalar = coerce (endoScalar :: f')

derive instance Newtype (F f) _
derive instance Generic (F f) _

instance PrimeField f => PrimeField (F f) where
  fromBigInt x = F $ fromBigInt x
  toBigInt (F x) = toBigInt x
  modulus = modulus @f
  pow (F f) n = F $ pow @f f n

-- | Wrapper indicating a value should not have constraints checked.
-- |
-- | When introducing a variable with `exists`, the `CheckedType` class
-- | normally adds constraints (e.g., boolean range checks). Wrapping in
-- | `UnChecked` skips these checks, useful when the value is already
-- | constrained through other means.
-- |
-- | For example, in elliptic curve addition, if both input points have
-- | on-curve constraints, the sum is mathematically guaranteed to be on
-- | the curve - no additional check is needed for the result.
newtype UnChecked a = UnChecked a

derive instance Eq a => Eq (UnChecked a)
derive newtype instance Show a => Show (UnChecked a)
derive newtype instance Arbitrary a => Arbitrary (UnChecked a)
derive instance Newtype (UnChecked a) _
derive instance Generic (UnChecked f) _

-- | A boolean variable in the circuit.
-- |
-- | This is a field expression tagged to indicate it represents a boolean
-- | (constrained to be 0 or 1).
type BoolVar f = CVar f (Bool Variable)

-- | A field variable in the circuit.
-- |
-- | This is the primary type for circuit expressions - an affine combination
-- | of circuit variables over field `f`.
type FVar f = CVar f Variable

--------------------------------------------------------------------------------

-- | Type class for converting between value and variable representations.
-- |
-- | Every circuit type has:
-- | - A **value form** (`a`): concrete field elements used during proving
-- | - A **variable form** (`var`): circuit expressions used during compilation
-- |
-- | The class provides bidirectional conversion to/from arrays of field elements,
-- | which is how values are serialized for the constraint system.
-- |
-- | **Functional dependencies:**
-- | - `a f -> var`: The value type and field determine the variable type
-- | - `var -> f`: The variable type determines the field
class CircuitType :: Type -> Type -> Type -> Constraint
class CircuitType f a var | a f -> var, var -> f where
  -- | Convert a value to an array of field elements
  valueToFields :: a -> Array f
  -- | Reconstruct a value from an array of field elements
  fieldsToValue :: Array f -> a
  -- | The number of field elements needed to represent this type
  sizeInFields :: Proxy f -> Proxy a -> Int
  -- | Convert a variable to an array of field variable expressions
  varToFields :: var -> Array (FVar f)
  -- | Reconstruct a variable from an array of field variable expressions
  fieldsToVar :: Array (FVar f) -> var

instance CircuitType f Unit Unit where
  valueToFields _ = mempty
  fieldsToValue _ = unit
  sizeInFields _ _ = 0
  varToFields _ = mempty
  fieldsToVar _ = unit

instance CircuitType f (F f) (FVar f) where
  valueToFields = Array.singleton <<< coerce
  fieldsToValue a = coerce $ unsafePartial fromJust $ Array.head a
  sizeInFields _ _ = 1
  varToFields = Array.singleton
  fieldsToVar a = unsafePartial fromJust $ Array.head a

instance (PrimeField f) => CircuitType f Boolean (BoolVar f) where
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
  , CircuitType f b bvar
  ) =>
  CircuitType f (Tuple a b) (Tuple avar bvar) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(Tuple a b)
  fieldsToVar = genericFieldsToVar @(Tuple a b)

instance CircuitType f a var => CircuitType f (UnChecked a) (UnChecked var) where
  valueToFields (UnChecked a) = valueToFields @f @a a
  fieldsToValue a = UnChecked $ fieldsToValue @f @a a
  sizeInFields pf _ = sizeInFields pf (Proxy @a)
  varToFields (UnChecked a) = varToFields @f @a a
  fieldsToVar a = UnChecked $ fieldsToVar @f @a a

instance (CircuitType f a var, Reflectable n Int) => CircuitType f (Vector n a) (Vector n var) where
  valueToFields as = foldMap valueToFields as
  fieldsToValue as =
    let
      elemSize = sizeInFields (Proxy @f) (Proxy @a)
      vecLen = reflectType (Proxy @n)
      -- Handle zero-sized elements: chunk 0 returns [], so we need to
      -- generate vecLen elements directly
      vals =
        if elemSize == 0 then Array.replicate vecLen (fieldsToValue @f @a [])
        else fieldsToValue @f @a <$> Vector.chunk elemSize as
    in
      unsafePartial $ fromJust $ toVector @n vals
  sizeInFields pf _ = reflectType (Proxy @n) * sizeInFields pf (Proxy @a)
  varToFields as = foldMap (varToFields @f @a) as
  fieldsToVar as =
    let
      elemSize = sizeInFields (Proxy @f) (Proxy @a)
      vecLen = reflectType (Proxy @n)
      -- Handle zero-sized elements: chunk 0 returns [], so we need to
      -- generate vecLen elements directly
      vals =
        if elemSize == 0 then Array.replicate vecLen (fieldsToVar @f @a [])
        else fieldsToVar @f @a <$> Vector.chunk elemSize as
    in
      unsafePartial $ fromJust $ toVector @n vals

instance (RowToList r rl, RowToList var rlvar, RCircuitType f rl rlvar r var) => CircuitType f (Record r) (Record var) where
  fieldsToValue = rFieldsToValue @f @rl @rlvar @r (Proxy @rl)
  valueToFields = rValueToFields @f @rl @rlvar @r (Proxy @rl)
  sizeInFields pf _ = rSizeInFields @f @rl @rlvar @r pf (Proxy @rl) (Proxy @rlvar)
  fieldsToVar = rFieldsToVar @f @rl @rlvar @r (Proxy @rlvar)
  varToFields = rVarToFields @f @rl @rlvar @r (Proxy @rlvar)

--------------------------------------------------------------------------------

class GCircuitType :: Type -> Type -> Type -> Constraint
class GCircuitType f a var | f a -> var, var -> f where
  gValueToFields :: a -> Array f
  gFieldsToValue :: Array f -> a
  gSizeInFields :: Proxy f -> Proxy a -> Int
  gVarToFields :: var -> Array (FVar f)
  gFieldsToVar :: Array (FVar f) -> var

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
  :: forall f @a rep var var'
   . Generic var var'
  => Generic a rep
  => GCircuitType f rep var'
  => var
  -> Array (FVar f)
genericVarToFields var = gVarToFields @f @rep $ from var

genericFieldsToVar
  :: forall f @a rep var var'
   . Generic var var'
  => Generic a rep
  => GCircuitType f rep var'
  => Array (FVar f)
  -> var
genericFieldsToVar fs = to $ gFieldsToVar @f @rep fs

--------------------------------------------------------------------------------

class RCircuitType :: Type -> RL.RowList Type -> RL.RowList Type -> Row Type -> Row Type -> Constraint
class RCircuitType f rl rlvar r var | rl -> r, rlvar -> var, var -> f, f r -> var, rl -> rlvar where
  rValueToFields :: Proxy rl -> Record r -> Array f
  rFieldsToValue :: Proxy rl -> Array f -> Record r
  rSizeInFields :: Proxy f -> Proxy rl -> Proxy rlvar -> Int
  rVarToFields :: Proxy rlvar -> Record var -> Array (FVar f)
  rFieldsToVar :: Proxy rlvar -> Array (FVar f) -> Record var

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
      asfs = rValueToFields @f @tail @tailvars @rest (Proxy @tail) $ Record.delete (Proxy @s) r
    in
      afs <> asfs
  rFieldsToValue _ fs =
    let
      { before, after } = Array.splitAt (sizeInFields (Proxy @f) (Proxy @a)) fs
      a = fieldsToValue @f @a before
      as = rFieldsToValue @f @tail @tailvars @rest (Proxy @tail) after
    in
      Record.insert (Proxy @s) a as
  rSizeInFields pf _ _ = sizeInFields pf (Proxy @a) + rSizeInFields @f @tail @tailvars @rest pf (Proxy @tail) (Proxy @tailvars)
  rVarToFields _ r =
    let
      afs = varToFields @f @a $ Record.get (Proxy @s) r
      asfs = rVarToFields @f @tail @tailvars @rest (Proxy @tailvars) $ Record.delete (Proxy @s) r
    in
      afs <> asfs
  rFieldsToVar _ fs =
    let
      { before, after } = Array.splitAt (sizeInFields (Proxy @f) (Proxy @a)) fs
      a = fieldsToVar @f @a before
      as = rFieldsToVar @f @tail @tailvars @rest (Proxy @tailvars) after
    in
      Record.insert (Proxy @s) a as
