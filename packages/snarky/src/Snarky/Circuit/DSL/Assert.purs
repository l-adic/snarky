-- | Assertion operations that add constraints without returning values.
-- |
-- | Use these when you want to enforce a condition rather than compute a boolean
-- | result. `assertNonZero_` works by computing the inverse (which fails if zero).
-- | The `AssertEqual` class provides generic equality assertions for compound types.
module Snarky.Circuit.DSL.Assert
  ( assertNonZero_
  , assertEqual_
  , assertNotEqual_
  , assertSquare_
  , assert_
  , class AssertEqual
  , assertEq
  , isEqual
  , assertEqGeneric
  , isEqualGeneric
  , class GAssertEqual
  , gAssertEqual
  , gIsEqual
  , class RAssertEqual
  , rAssertEqual
  , rIsEqual
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Traversable (for)
import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments, Product(..), from)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Prim.Row as Row
import Prim.RowList (class RowToList)
import Prim.RowList as RL
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const), const_, sub_)
import Snarky.Circuit.DSL.Field (equals_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, addConstraint, and_, inv_, mul_)
import Snarky.Circuit.Types (Bool(..), BoolVar, FVar)
import Snarky.Constraint.Basic (equal)
import Type.Proxy (Proxy(..))

assertNonZero_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Snarky c t m Unit
assertNonZero_ v = void $ inv_ v

assertEqual_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky c t m Unit
assertEqual_ x y = case x, y of
  Const f, Const g ->
    if f == g then pure unit
    else unsafeThrow $ "assertEqual: constants " <> show f <> " != " <> show g
  _, _ -> do
    addConstraint $ equal x y

assertNotEqual_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky c t m Unit
assertNotEqual_ x y = assertNonZero_ (x `sub_` y)

assertSquare_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky c t m Unit
assertSquare_ x y = do
  xSquared <- mul_ x x
  assertEqual_ xSquared y

assert_
  :: forall f c t m
   . CircuitM f c t m
  => BoolVar f
  -> Snarky c t m Unit
assert_ v = assertEqual_ (coerce v) (const_ $ one @f)

-- | AND all booleans together. Empty array returns true.
allBools
  :: forall f c t m
   . CircuitM f c t m
  => Array (BoolVar f)
  -> Snarky c t m (BoolVar f)
allBools bs = case Array.uncons bs of
  Nothing -> pure $ Const one
  Just { head, tail } ->
    Array.foldM (\acc b -> and_ acc b) head tail

--------------------------------------------------------------------------------
-- | Generic AssertEqual class for asserting equality of circuit variables

class AssertEqual :: Type -> Type -> Type -> Constraint
class AssertEqual f c var | c -> f, var -> f where
  assertEq :: forall t m. CircuitM f c t m => var -> var -> Snarky c t m Unit
  isEqual :: forall t m. CircuitM f c t m => var -> var -> Snarky c t m (BoolVar f)

-- Base instance for FVar
instance AssertEqual f c (FVar f) where
  assertEq = assertEqual_
  isEqual = equals_

-- Base instance for BoolVar
instance AssertEqual f c (BoolVar f) where
  assertEq x y = assertEqual_ (coerce x) (coerce y)
  isEqual x y = equals_ (coerce x) (coerce y)

-- Instance for Unit
instance AssertEqual f c Unit where
  assertEq _ _ = pure unit
  isEqual _ _ = pure $ Const one

-- Instance for Tuple
instance (AssertEqual f c a, AssertEqual f c b) => AssertEqual f c (Tuple a b) where
  assertEq (Tuple a1 b1) (Tuple a2 b2) = do
    assertEq @f a1 a2
    assertEq @f b1 b2
  isEqual (Tuple a1 b1) (Tuple a2 b2) = do
    r1 <- isEqual @f a1 a2
    r2 <- isEqual @f b1 b2
    and_ r1 r2

-- Instance for Vector
instance AssertEqual f c a => AssertEqual f c (Vector n a) where
  assertEq v1 v2 = for_ (Vector.zip v1 v2) \(Tuple a1 a2) -> assertEq @f a1 a2
  isEqual v1 v2 = do
    bools <- Vector.toUnfoldable <$> for (Vector.zip v1 v2) \(Tuple a1 a2) -> isEqual @f a1 a2
    allBools bools

-- Instance for Records
instance (RowToList r rl, RAssertEqual f c rl r) => AssertEqual f c (Record r) where
  assertEq = rAssertEqual @f @c (Proxy @rl)
  isEqual = rIsEqual @f @c (Proxy @rl)

--------------------------------------------------------------------------------
-- | Generic rep instances for AssertEqual

class GAssertEqual :: Type -> Type -> Type -> Constraint
class GAssertEqual f c rep where
  gAssertEqual :: forall t m. CircuitM f c t m => rep -> rep -> Snarky c t m Unit
  gIsEqual :: forall t m. CircuitM f c t m => rep -> rep -> Snarky c t m (BoolVar f)

instance GAssertEqual f c NoArguments where
  gAssertEqual _ _ = pure unit
  gIsEqual _ _ = pure $ Const one

instance AssertEqual f c a => GAssertEqual f c (Argument a) where
  gAssertEqual (Argument a1) (Argument a2) = assertEq @f a1 a2
  gIsEqual (Argument a1) (Argument a2) = isEqual @f a1 a2

instance (GAssertEqual f c a, GAssertEqual f c b) => GAssertEqual f c (Product a b) where
  gAssertEqual (Product a1 b1) (Product a2 b2) = do
    gAssertEqual @f @c a1 a2
    gAssertEqual @f @c b1 b2
  gIsEqual (Product a1 b1) (Product a2 b2) = do
    r1 <- gIsEqual @f @c a1 a2
    r2 <- gIsEqual @f @c b1 b2
    and_ r1 r2

instance GAssertEqual f c a => GAssertEqual f c (Constructor name a) where
  gAssertEqual (Constructor a1) (Constructor a2) = gAssertEqual @f @c a1 a2
  gIsEqual (Constructor a1) (Constructor a2) = gIsEqual @f @c a1 a2

-- | Generic assertEqual for types with Generic instance
assertEqGeneric
  :: forall f c t m var rep
   . Generic var rep
  => CircuitM f c t m
  => GAssertEqual f c rep
  => var
  -> var
  -> Snarky c t m Unit
assertEqGeneric x y = gAssertEqual @f @c (from x) (from y)

-- | Generic isEqual for types with Generic instance
isEqualGeneric
  :: forall f c t m var rep
   . Generic var rep
  => CircuitM f c t m
  => GAssertEqual f c rep
  => var
  -> var
  -> Snarky c t m (BoolVar f)
isEqualGeneric x y = gIsEqual @f @c (from x) (from y)

--------------------------------------------------------------------------------
-- | Row list instances for AssertEqual on records

class RAssertEqual :: Type -> Type -> RL.RowList Type -> Row Type -> Constraint
class RAssertEqual f c (rl :: RL.RowList Type) (r :: Row Type) | rl -> r where
  rAssertEqual :: forall t m. CircuitM f c t m => Proxy rl -> Record r -> Record r -> Snarky c t m Unit
  rIsEqual :: forall t m. CircuitM f c t m => Proxy rl -> Record r -> Record r -> Snarky c t m (BoolVar f)

instance RAssertEqual f c RL.Nil () where
  rAssertEqual _ _ _ = pure unit
  rIsEqual _ _ _ = pure $ Const one

instance
  ( IsSymbol s
  , Row.Cons s a rest r
  , Row.Lacks s rest
  , AssertEqual f c a
  , RAssertEqual f c tail rest
  ) =>
  RAssertEqual f c (RL.Cons s a tail) r where
  rAssertEqual _ r1 r2 = do
    assertEq @f (Record.get (Proxy @s) r1) (Record.get (Proxy @s) r2)
    rAssertEqual @f @c (Proxy @tail) (Record.delete (Proxy @s) r1) (Record.delete (Proxy @s) r2)
  rIsEqual _ r1 r2 = do
    fieldEq <- isEqual @f (Record.get (Proxy @s) r1) (Record.get (Proxy @s) r2)
    restEq <- rIsEqual @f @c (Proxy @tail) (Record.delete (Proxy @s) r1) (Record.delete (Proxy @s) r2)
    and_ fieldEq restEq