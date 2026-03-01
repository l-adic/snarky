-- | Boolean operations for circuits.
-- |
-- | These operations work on `BoolVar` (field elements constrained to 0 or 1).
-- | For small arrays, `all_`/`any_` use direct `and_`/`or_`. For larger arrays,
-- | they use sum-based checks which can be more constraint-efficient.
module Snarky.Circuit.DSL.Boolean
  ( class IfThenElse
  , if_
  , class RIfThenElse
  , rIfThenElse
  , class GIfThenElse
  , gIfThenElse
  , true_
  , false_
  , xor_
  , all_
  , any_
  ) where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (Argument(..), Constructor(..), NoArguments(..), Product(..))
import Data.HeytingAlgebra (ff, tt)
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Prim.Row as Row
import Prim.RowList (class RowToList)
import Prim.RowList as RL
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const, ScalarMul), const_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL.Field (equals_, sum_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, addConstraint, and_, exists, not_, or_, read, readCVar)
import Snarky.Circuit.Types (Bool(..), BoolVar, F(..), FVar, UnChecked(..))
import Snarky.Constraint.Basic (r1cs)
import Snarky.Curves.Class (class PrimeField, fromBigInt)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | IfThenElse class for conditional selection of circuit variables

class IfThenElse :: Type -> Type -> Type -> Constraint
class IfThenElse f c var | c -> f, var -> f where
  if_ :: forall t m. CircuitM f c t m => BoolVar f -> var -> var -> Snarky c t m var

-- Base instance for FVar
-- if b then x else y = b * x + (1 - b) * y = b * (x - y) + y
instance IfThenElse f c (FVar f) where
  if_ b thenBranch elseBranch = case b of
    Const b_ -> pure $ if b_ == one then thenBranch else elseBranch
    _ -> case thenBranch, elseBranch of
      Const t, Const e -> pure $
        ScalarMul t (coerce b) `CVar.add_` (CVar.scale_ e (Const one `CVar.sub_` coerce b))
      _, _ -> do
        r <- exists do
          bVal <- readCVar $ coerce b
          if bVal == one then readCVar thenBranch else readCVar elseBranch
        addConstraint $ r1cs
          { left: coerce b
          , right: thenBranch `CVar.sub_` elseBranch
          , output: r `CVar.sub_` elseBranch
          }
        pure r

-- Base instance for BoolVar
-- Same formula, just coerced
instance IfThenElse f c (BoolVar f) where
  if_ b x y = coerce <$> if_ @f @c b (coerce x :: FVar f) (coerce y)

-- Instance for Unit
instance IfThenElse f c Unit where
  if_ _ _ _ = pure unit

-- Instance for Tuple
-- Process snd before fst to match OCaml's reverse array evaluation order.
instance (IfThenElse f c a, IfThenElse f c b) => IfThenElse f c (Tuple a b) where
  if_ b (Tuple a1 b1) (Tuple a2 b2) = do
    b' <- if_ @f b b1 b2
    a <- if_ @f b a1 a2
    pure $ Tuple a b'

-- Instance for Vector
instance IfThenElse f c a => IfThenElse f c (Vector n a) where
  if_ b v1 v2 = sequence $ Vector.zipWith (\x y -> if_ @f b x y) v1 v2

-- Instance for Records
instance (RowToList r rl, RIfThenElse f c rl r) => IfThenElse f c (Record r) where
  if_ b r1 r2 = rIfThenElse @f @c (Proxy @rl) b r1 r2

--------------------------------------------------------------------------------
-- | Generic rep instances for IfThenElse

class GIfThenElse :: Type -> Type -> Type -> Constraint
class GIfThenElse f c rep where
  gIfThenElse :: forall t m. CircuitM f c t m => BoolVar f -> rep -> rep -> Snarky c t m rep

instance GIfThenElse f c NoArguments where
  gIfThenElse _ _ _ = pure NoArguments

instance IfThenElse f c a => GIfThenElse f c (Argument a) where
  gIfThenElse b (Argument a1) (Argument a2) = Argument <$> if_ @f b a1 a2

-- Process snd before fst to match OCaml's reverse array evaluation order.
instance (GIfThenElse f c a, GIfThenElse f c b) => GIfThenElse f c (Product a b) where
  gIfThenElse b (Product a1 b1) (Product a2 b2) = do
    b' <- gIfThenElse @f @c b b1 b2
    a <- gIfThenElse @f @c b a1 a2
    pure $ Product a b'

instance GIfThenElse f c a => GIfThenElse f c (Constructor name a) where
  gIfThenElse b (Constructor a1) (Constructor a2) = Constructor <$> gIfThenElse @f @c b a1 a2

--------------------------------------------------------------------------------
-- | Row list instances for IfThenElse on records

class RIfThenElse :: Type -> Type -> RL.RowList Type -> Row Type -> Constraint
class RIfThenElse f c (rl :: RL.RowList Type) (r :: Row Type) | rl -> r where
  rIfThenElse :: forall t m. CircuitM f c t m => Proxy rl -> BoolVar f -> Record r -> Record r -> Snarky c t m (Record r)

instance RIfThenElse f c RL.Nil () where
  rIfThenElse _ _ _ _ = pure {}

instance
  ( IsSymbol s
  , Row.Cons s a rest r
  , Row.Lacks s rest
  , IfThenElse f c a
  , RIfThenElse f c tail rest
  ) =>
  RIfThenElse f c (RL.Cons s a tail) r where
  -- Process tail before head to match OCaml's reverse array evaluation order.
  -- OCaml's Monad_sequence.Array.init processes elements from n-1 down to 0,
  -- so for {x, y} it evaluates y first, then x.
  rIfThenElse _ b r1 r2 = do
    rest <- rIfThenElse @f @c (Proxy @tail) b (Record.delete (Proxy @s) r1) (Record.delete (Proxy @s) r2)
    val <- if_ @f b (Record.get (Proxy @s) r1) (Record.get (Proxy @s) r2)
    pure $ Record.insert (Proxy @s) val rest

--------------------------------------------------------------------------------

true_ :: forall f. PrimeField f => BoolVar f
true_ = const_ one

false_ :: forall f. PrimeField f => BoolVar f
false_ = const_ zero

xor_
  :: forall f c t m
   . CircuitM f c t m
  => BoolVar f
  -> BoolVar f
  -> Snarky c t m (BoolVar f)
xor_ a b = case a, b of
  Const aVal, Const bVal -> pure $ Const $ if (aVal == bVal) then zero else one
  Const aVal, _
    | aVal == zero -> pure b
    | aVal == one -> pure $ not_ b
  _, Const bVal
    | bVal == zero -> pure a
    | bVal == one -> pure $ not_ a
  _, _ -> do
    UnChecked res <- exists do
      F aVal <- read (coerce a :: FVar f)
      F bVal <- read (coerce b :: FVar f)
      pure $ UnChecked (aVal /= bVal)
    addConstraint $
      r1cs
        { left: coerce a `CVar.add_` coerce a
        , right: coerce b
        , output: coerce a `CVar.add_` coerce b `CVar.sub_` coerce res
        }
    pure res

any_
  :: forall f c t m
   . CircuitM f c t m
  => Array (BoolVar f)
  -> Snarky c t m (BoolVar f)
any_ as =
  case Array.uncons as of
    Nothing -> ff
    Just { head: a0, tail } -> case Array.uncons tail of
      Nothing -> pure a0
      Just { head: a1, tail: rest } ->
        if Array.null rest then a0 `or_` a1
        else not $ equals_ (sum_ (coerce as)) (Const zero)

all_
  :: forall f c t m
   . CircuitM f c t m
  => Array (BoolVar f)
  -> Snarky c t m (BoolVar f)
all_ as =
  case Array.uncons as of
    Nothing -> tt
    Just { head: a0, tail } -> case Array.uncons tail of
      Nothing -> pure a0
      Just { head: a1, tail: rest } ->
        if Array.null rest then a0 `and_` a1
        else
          let
            n = fromBigInt $ BigInt.fromInt $ Array.length as
          in
            equals_ (Const n) (sum_ (coerce as))