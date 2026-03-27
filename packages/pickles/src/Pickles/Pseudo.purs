-- | Pseudo-selection circuits for dynamic dispatch over a fixed set of options.
-- |
-- | Used in wrap_main to select domain parameters based on which_branch
-- | and wrap_domain_index.
-- |
-- | Reference: mina/src/lib/crypto/pickles/pseudo/pseudo.ml
-- |            mina/src/lib/crypto/pickles_base/one_hot_vector/one_hot_vector.ml
module Pickles.Pseudo
  ( oneHotVector
  , mask
  , choose
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt (fromInt)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, const_, equals_, label, mul_)
import Snarky.Circuit.DSL.Assert (assertNonZero_)
import Snarky.Circuit.DSL.Field (sum_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, fromBigInt)
import Safe.Coerce (coerce)

-- | Create a one-hot vector from a field variable index.
-- |
-- | For each j in [0..n-1], computes Field.equal (Field.of_int j) index.
-- | Then asserts at least one entry is true via assert_non_zero(sum(bits)).
-- |
-- | Constraint generation (utils.ml:65-78, utils.ml:361):
-- |   - n × Field.equal: each allocates (r, inv) via exists + 2 R1CS constraints
-- |   - 1 × assert_non_zero(num_true): inv(sum) = 1 R1CS constraint
-- |
-- | Reference: one_hot_vector.ml:21-24
oneHotVector
  :: forall n f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Reflectable n Int
  => FVar f
  -> Snarky (KimchiConstraint f) t m (Vector n (BoolVar f))
oneHotVector index = label "one-hot-vector" do
  -- OCaml Vector.init evaluates right-to-left (j=n-1 first, j=0 last)
  vRev <- traverse (\j -> equals_ (const_ (fromBigInt (fromInt (getFinite j)))) index)
    (Vector.reverse (Vector.generate identity :: Vector n _))
  let v = Vector.reverse vRev
  assertNonZero_ (sum_ (Vector.toUnfoldable (map (coerce :: BoolVar f -> FVar f) v)))
  pure v

-- | Mask-select: compute ∑ bits[i] * xs[i].
-- |
-- | Each bit is coerced to a field and multiplied with the corresponding value.
-- | Results are summed via Cvar addition (no constraints for the sum).
-- |
-- | Constraint generation (pseudo.ml:23-28):
-- |   - n × Field.mul (b :> t) x: each generates 1 R1CS if b is non-constant
-- |   - fold with Field.(+): pure CVar addition, 0 constraints
-- |
-- | Reference: pseudo.ml:23-28
mask
  :: forall n f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Reflectable n Int
  => Vector n (BoolVar f)
  -> Vector n (FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
mask bits xs = label "pseudo-mask" do
  -- OCaml Vector.map evaluates right-to-left (::  constructor)
  termsRev <- traverse (\(Tuple b x) -> mul_ (coerce b :: FVar f) x) $
    Vector.reverse (Vector.zip bits xs)
  let terms = Vector.reverse termsRev
  pure $ sum_ (Vector.toUnfoldable terms)

-- | Choose a value from a vector using a one-hot selector.
-- |
-- | Maps each option through f, then mask-selects.
-- |
-- | Reference: pseudo.ml:30-31
choose
  :: forall n a f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Reflectable n Int
  => Vector n (BoolVar f)
  -> Vector n a
  -> (a -> FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
choose bits xs f = mask bits (map f xs)
