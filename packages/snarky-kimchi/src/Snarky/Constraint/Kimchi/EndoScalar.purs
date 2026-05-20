module Snarky.Constraint.Kimchi.EndoScalar
  ( EndoScalar
  , EndoScalarRound
  , Rows
  , reduce
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Snarky.Circuit.DSL (FVar, Variable)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, GateKind(..), KimchiRow)

type EndoScalarRound f =
  { n0 :: FVar f
  , n8 :: FVar f
  , a0 :: FVar f
  , a8 :: FVar f
  , b0 :: FVar f
  , b8 :: FVar f
  , xs :: Vector 8 (FVar f)
  }

type EndoScalar f = Array (EndoScalarRound f)

newtype Rows f = Rows (Array (KimchiRow f))

instance ToKimchiRows f (Rows f) where
  toKimchiRows (Rows as) = as

reduce
  :: forall f m
   . PlonkReductionM m f
  => EndoScalar f
  -> m (Rows f)
reduce cs = Rows <$>
  traverse reduceRound cs
  where
  -- OCaml's Endoscale_scalar_round.map evaluates record fields right-to-left,
  -- so reduce_to_v is called on xs, b8, a8, b0, a0, n8, n0 in that order.
  -- This matters for constant deduplication: b0 and a0 are both Const 2 in
  -- the first round, so whichever is reduced first creates the variable and
  -- the second reuses it via cached_constants.
  reduceRound c = do
    xs <- traverse reduceToVariable c.xs
    b8 <- reduceToVariable c.b8
    a8 <- reduceToVariable c.a8
    b0 <- reduceToVariable c.b0
    a0 <- reduceToVariable c.a0
    n8 <- reduceToVariable c.n8
    n0 <- reduceToVariable c.n0
    let
      variables =
        let
          vs = Just n0 :< Just n8 :< Just a0 :< Just b0 :< Just a8 :< Just b8 :< (Just <$> xs)
        in
          vs `Vector.append` (Nothing :< Vector.nil)
    pure { kind: EndoScalar, coeffs: mempty, variables }
