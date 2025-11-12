module Snarky.Circuit.DSL.Field
  ( mul_
  , square_
  , eq_
  , neq_
  , inv_
  , div_
  , sum_
  ) where

import Prelude

import Data.Array (foldl)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const, ScalarMul), sub_, const_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint (R1CS(..))
import Snarky.Circuit.DSL (class CircuitM, addConstraint, exists, readCVar)
import Snarky.Circuit.Types (BooleanVariable(..), FieldElem(..), Variable(..))
import Snarky.Curves.Types (class PrimeField)

mul_
  :: forall f m n
   . CircuitM f m n
  => CVar f Variable
  -> CVar f Variable
  -> m (CVar f Variable)
mul_ a b =
  case a, b of
    Const f, Const f' -> pure $ Const (f * f')
    Const f, c -> pure $ ScalarMul f c
    c, Const f -> pure $ ScalarMul f c
    _, _ -> do
      z <- exists do
        aVal <- readCVar a
        bVal <- readCVar b
        pure $ FieldElem $ aVal * bVal
      addConstraint $ R1CS { left: a, right: b, output: z }
      pure z

square_
  :: forall m f n
   . CircuitM f m n
  => CVar f Variable
  -> m (CVar f Variable)
square_ = case _ of
  Const f -> pure $ Const (f * f)
  a -> do
    z <- exists do
      aVal <- readCVar a
      pure $ FieldElem (aVal * aVal)
    addConstraint $ R1CS { left: a, right: a, output: z }
    pure z

eq_
  :: forall f m n
   . CircuitM f m n
  => CVar f Variable
  -> CVar f Variable
  -> m (CVar f BooleanVariable)
eq_ a b = case a `CVar.sub_` b of
  Const f -> pure $ Const $ if f == zero then one else zero
  _ -> do
    let z = a `CVar.sub_` b
    Tuple r zInv <- exists do
      zVal <- readCVar z
      pure $
        if zVal == zero then Tuple (FieldElem (one :: f)) (FieldElem zero)
        else Tuple (FieldElem zero) (FieldElem $ recip zVal)
    addConstraint $ R1CS { left: zInv, right: z, output: Const one `CVar.sub_` r }
    addConstraint $ R1CS { left: r, right: z, output: Const zero }
    pure $ coerce r

neq_
  :: forall f m n
   . CircuitM f m n
  => CVar f Variable
  -> CVar f Variable
  -> m (CVar f BooleanVariable)
neq_ a b = eq_ a b <#>
  \c -> const_ one `sub_` c

inv_
  :: forall f m n
   . CircuitM f m n
  => CVar f Variable
  -> m (CVar f Variable)
inv_ = case _ of
  Const a -> pure
    if a == zero then unsafeCrashWith "inv: expected nonzero arg"
    else Const (recip a)
  a -> do
    aInv <- exists do
      aVal <- readCVar a
      pure $ FieldElem $ if aVal == zero then zero else recip aVal
    addConstraint $ R1CS { left: a, right: aInv, output: Const one }
    pure aInv

div_
  :: forall m f n
   . CircuitM f m n
  => CVar f Variable
  -> CVar f Variable
  -> m (CVar f Variable)
div_ a b = inv_ b >>= mul_ a

sum_
  :: forall f
   . PrimeField f
  => Array (CVar f Variable)
  -> CVar f Variable
sum_ = foldl CVar.add_ (Const zero)