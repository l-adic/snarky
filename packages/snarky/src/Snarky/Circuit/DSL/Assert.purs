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
  , assertEqGeneric
  , class GAssertEqual
  , gAssertEqual
  , class RAssertEqual
  , rAssertEqual
  ) where

import Prelude

import Data.Foldable (for_)
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
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, addConstraint, inv_, mul_)
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

--------------------------------------------------------------------------------
-- | Generic AssertEqual class for asserting equality of circuit variables

class AssertEqual :: Type -> Type -> ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> Type -> Constraint
class AssertEqual f c t m var | c -> f, var -> f, t -> f where
  assertEq :: var -> var -> Snarky c t m Unit

-- Base instance for FVar
instance CircuitM f c t m => AssertEqual f c t m (FVar f) where
  assertEq = assertEqual_

-- Base instance for BoolVar
instance CircuitM f c t m => AssertEqual f c t m (BoolVar f) where
  assertEq x y = assertEqual_ (coerce x) (coerce y)

-- Instance for Unit
instance Applicative (Snarky c t m) => AssertEqual f c t m Unit where
  assertEq _ _ = pure unit

-- Instance for Tuple
instance (AssertEqual f c t m a, AssertEqual f c t m b, Bind (t m)) => AssertEqual f c t m (Tuple a b) where
  assertEq (Tuple a1 b1) (Tuple a2 b2) = do
    assertEq @f a1 a2
    assertEq @f b1 b2

-- Instance for Vector
instance (AssertEqual f c t m a, Applicative (t m)) => AssertEqual f c t m (Vector n a) where
  assertEq v1 v2 = for_ (Vector.zip v1 v2) \(Tuple a1 a2) -> assertEq @f a1 a2

-- Instance for Records
instance (RowToList r rl, RAssertEqual f c t m rl r) => AssertEqual f c t m (Record r) where
  assertEq = rAssertEqual @f @c @t @m (Proxy @rl)

--------------------------------------------------------------------------------
-- | Generic rep instances for AssertEqual

class GAssertEqual :: Type -> Type -> ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> Type -> Constraint
class GAssertEqual f c t m rep where
  gAssertEqual :: rep -> rep -> Snarky c t m Unit

instance Applicative (Snarky c t m) => GAssertEqual f c t m NoArguments where
  gAssertEqual _ _ = pure unit

instance AssertEqual f c t m a => GAssertEqual f c t m (Argument a) where
  gAssertEqual (Argument a1) (Argument a2) = assertEq @f a1 a2

instance (GAssertEqual f c t m a, GAssertEqual f c t m b, Bind (t m)) => GAssertEqual f c t m (Product a b) where
  gAssertEqual (Product a1 b1) (Product a2 b2) = do
    gAssertEqual @f @c @t @m a1 a2
    gAssertEqual @f @c @t @m b1 b2

instance GAssertEqual f c t m a => GAssertEqual f c t m (Constructor name a) where
  gAssertEqual (Constructor a1) (Constructor a2) = gAssertEqual @f @c @t @m a1 a2

-- | Generic assertEqual for types with Generic instance
assertEqGeneric
  :: forall f c t m var rep
   . Generic var rep
  => GAssertEqual f c t m rep
  => var
  -> var
  -> Snarky c t m Unit
assertEqGeneric x y = gAssertEqual @f @c @t @m (from x) (from y)

--------------------------------------------------------------------------------
-- | Row list instances for AssertEqual on records

class RAssertEqual :: Type -> Type -> ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> RL.RowList Type -> Row Type -> Constraint
class RAssertEqual f c t m (rl :: RL.RowList Type) (r :: Row Type) | rl -> r where
  rAssertEqual :: Proxy rl -> Record r -> Record r -> Snarky c t m Unit

instance Applicative (Snarky c t m) => RAssertEqual f c t m RL.Nil () where
  rAssertEqual _ _ _ = pure unit

instance
  ( IsSymbol s
  , Row.Cons s a rest r
  , Row.Lacks s rest
  , AssertEqual f c t m a
  , RAssertEqual f c t m tail rest
  , Bind (t m)
  ) =>
  RAssertEqual f c t m (RL.Cons s a tail) r where
  rAssertEqual _ r1 r2 = do
    assertEq @f (Record.get (Proxy @s) r1) (Record.get (Proxy @s) r2)
    rAssertEqual @f @c @t @m (Proxy @tail) (Record.delete (Proxy @s) r1) (Record.delete (Proxy @s) r2)