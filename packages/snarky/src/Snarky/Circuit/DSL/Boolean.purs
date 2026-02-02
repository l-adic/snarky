-- | Boolean operations for circuits.
-- |
-- | These operations work on `BoolVar` (field elements constrained to 0 or 1).
-- | For small arrays, `all_`/`any_` use direct `and_`/`or_`. For larger arrays,
-- | they use sum-based checks which can be more constraint-efficient.
module Snarky.Circuit.DSL.Boolean
  ( if_
  , xor_
  , all_
  , any_
  ) where

import Prelude

import Data.Array as Array
import Data.HeytingAlgebra (ff, tt)
import Data.Maybe (Maybe(..))
import JS.BigInt as BigInt
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const, ScalarMul))
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL.Field (equals_, sum_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, addConstraint, and_, exists, not_, or_, read, readCVar)
import Snarky.Circuit.Types (Bool(..), BoolVar, F(..), FVar, UnChecked(..))
import Snarky.Constraint.Basic (r1cs)
import Snarky.Curves.Class (fromBigInt)

if_
  :: forall f c t m
   . CircuitM f c t m
  => BoolVar f
  -> FVar f
  -> FVar f
  -> Snarky c t m (FVar f)
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

xor_
  :: forall f c t m
   . CircuitM f c t m
  => BoolVar f
  -> BoolVar f
  -> Snarky c t m (BoolVar f)
xor_ a b = case a, b of
  Const aVal, Const bVal -> pure $ Const $ if (aVal == bVal) then one else zero
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
            equals_ (sum_ (coerce as)) (Const n)