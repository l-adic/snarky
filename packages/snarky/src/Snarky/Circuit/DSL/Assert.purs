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

class AssertEqual :: Type -> Type -> Type -> Constraint
class AssertEqual f c var | c -> f, var -> f where
  assertEq :: forall t m. CircuitM f c t m => var -> var -> Snarky c t m Unit

-- Base instance for FVar
instance AssertEqual f c (FVar f) where
  assertEq = assertEqual_

-- Base instance for BoolVar
instance AssertEqual f c (BoolVar f) where
  assertEq x y = assertEqual_ (coerce x) (coerce y)

-- Instance for Unit
instance AssertEqual f c Unit where
  assertEq _ _ = pure unit

-- Instance for Tuple
instance (AssertEqual f c a, AssertEqual f c b) => AssertEqual f c (Tuple a b) where
  assertEq (Tuple a1 b1) (Tuple a2 b2) = do
    assertEq @f a1 a2
    assertEq @f b1 b2

-- Instance for Vector
instance AssertEqual f c a => AssertEqual f c (Vector n a) where
  assertEq v1 v2 = for_ (Vector.zip v1 v2) \(Tuple a1 a2) -> assertEq @f a1 a2

-- Instance for Records
instance (RowToList r rl, RAssertEqual f c rl r) => AssertEqual f c (Record r) where
  assertEq = rAssertEqual @f @c (Proxy @rl)

--------------------------------------------------------------------------------
-- | Generic rep instances for AssertEqual

class GAssertEqual :: Type -> Type -> Type -> Constraint
class GAssertEqual f c rep where
  gAssertEqual :: forall t m. CircuitM f c t m => rep -> rep -> Snarky c t m Unit

instance GAssertEqual f c NoArguments where
  gAssertEqual _ _ = pure unit

instance AssertEqual f c a => GAssertEqual f c (Argument a) where
  gAssertEqual (Argument a1) (Argument a2) = assertEq @f a1 a2

instance (GAssertEqual f c a, GAssertEqual f c b) => GAssertEqual f c (Product a b) where
  gAssertEqual (Product a1 b1) (Product a2 b2) = do
    gAssertEqual @f @c a1 a2
    gAssertEqual @f @c b1 b2

instance GAssertEqual f c a => GAssertEqual f c (Constructor name a) where
  gAssertEqual (Constructor a1) (Constructor a2) = gAssertEqual @f @c a1 a2

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

--------------------------------------------------------------------------------
-- | Row list instances for AssertEqual on records

class RAssertEqual :: Type -> Type -> RL.RowList Type -> Row Type -> Constraint
class RAssertEqual f c (rl :: RL.RowList Type) (r :: Row Type) | rl -> r where
  rAssertEqual :: forall t m. CircuitM f c t m => Proxy rl -> Record r -> Record r -> Snarky c t m Unit

instance RAssertEqual f c RL.Nil () where
  rAssertEqual _ _ _ = pure unit

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