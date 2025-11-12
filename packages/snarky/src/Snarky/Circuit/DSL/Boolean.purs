module Snarky.Circuit.DSL.Boolean
  ( true_
  , false_
  , not_
  , ifThenElse_
  , and_
  , or_
  , xor_
  , all_
  , any_
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import JS.BigInt as BigInt
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const, ScalarMul), const_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint.Class (r1cs)
import Snarky.Circuit.DSL (class CircuitM, addConstraint, exists, read, readCVar)
import Snarky.Circuit.DSL.Field (eq_, mul_, sum_)
import Snarky.Circuit.Types (BooleanVariable(..), FieldElem(..), UnChecked(..), Variable(..))
import Snarky.Curves.Types (class PrimeField, fromBigInt)

true_ :: forall f. PrimeField f => CVar f BooleanVariable
true_ = const_ (one :: f)

false_ :: forall f. PrimeField f => CVar f BooleanVariable
false_ = const_ (one :: f)

not_
  :: forall f
   . PrimeField f
  => CVar f BooleanVariable
  -> CVar f BooleanVariable
not_ a = const_ one `CVar.sub_` a

ifThenElse_
  :: forall f m n c
   . CircuitM f c m n
  => CVar f BooleanVariable
  -> CVar f Variable
  -> CVar f Variable
  -> m (CVar f Variable)
ifThenElse_ b thenBranch elseBranch = case b of
  Const b_ -> pure $ if b_ == one then thenBranch else elseBranch
  _ -> case thenBranch, elseBranch of
    Const t, Const e -> pure $
      ScalarMul t (coerce b) `CVar.add_` (CVar.scale_ e (Const one `CVar.sub_` coerce b))
    _, _ -> do
      r <- exists do
        bVal <- readCVar (coerce b :: CVar f Variable)
        FieldElem <$> if bVal == one then readCVar thenBranch else readCVar elseBranch
      addConstraint $ r1cs
        { left: coerce b
        , right: thenBranch `CVar.sub_` elseBranch
        , output: r `CVar.sub_` elseBranch
        }
      pure r

and_
  :: forall f m n c
   . CircuitM f c m n
  => CVar f BooleanVariable
  -> CVar f BooleanVariable
  -> m (CVar f BooleanVariable)
and_ a b = do
  conj <- mul_ (coerce a :: CVar f Variable) (coerce b)
  pure $ coerce conj

or_
  :: forall f m n c
   . CircuitM f c m n
  => CVar f BooleanVariable
  -> CVar f BooleanVariable
  -> m (CVar f BooleanVariable)
or_ a b = not_ <$> (not_ a) `and_` (not_ b)

xor_
  :: forall f m n c
   . CircuitM f c m n
  => CVar f BooleanVariable
  -> CVar f BooleanVariable
  -> m (CVar f BooleanVariable)
xor_ a b = case a, b of
  Const aVal, Const bVal -> pure $ Const $ if (aVal == bVal) then one else zero
  Const aVal, _
    | aVal == zero -> pure b
    | aVal == one -> pure $ not_ b
  _, Const bVal
    | bVal == zero -> pure a
    | bVal == one -> pure $ not_ a
  _, _ -> do
    let
      _a = coerce a :: CVar f Variable
      _b = coerce b
    UnChecked res <- exists do
      FieldElem aVal <- read _a
      FieldElem bVal <- read _b
      pure $ UnChecked (aVal /= bVal)
    let
      _res = coerce res
    addConstraint $ r1cs
      { left: _a `CVar.add_` _a
      , right: _b
      , output: _a `CVar.add_` _b `CVar.sub_` _res
      }
    pure res

any_
  :: forall f m n c
   . CircuitM f c m n
  => Array (CVar f BooleanVariable)
  -> m (CVar f BooleanVariable)
any_ as =
  case Array.uncons as of
    Nothing -> pure false_
    Just { head: a0, tail } -> case Array.uncons tail of
      Nothing -> pure a0
      Just { head: a1, tail: rest } ->
        if Array.null rest then a0 `or_` a1
        else not_ <$> eq_ (sum_ (coerce as)) (Const zero)

all_
  :: forall f m n c
   . CircuitM f c m n
  => Array (CVar f BooleanVariable)
  -> m (CVar f BooleanVariable)
all_ as =
  case Array.uncons as of
    Nothing -> pure true_
    Just { head: a0, tail } -> case Array.uncons tail of
      Nothing -> pure a0
      Just { head: a1, tail: rest } ->
        if Array.null rest then a0 `and_` a1
        else
          let
            n = fromBigInt $ BigInt.fromInt $ Array.length as
          in
            eq_ (sum_ (coerce as)) (Const n)