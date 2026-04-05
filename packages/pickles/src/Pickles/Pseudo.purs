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
  , PlonkDomain
  , toDomain
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (getFinite)
import Data.Foldable (foldM, foldl)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt (fromInt)
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (sub_)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, const_, equals_, label, mul_, seal, square_)
import Snarky.Circuit.DSL.Assert (assertNonZero_)
import Snarky.Circuit.DSL.Field (sum_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, fromBigInt)

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

-- | Plonk domain with dynamically-selected parameters.
-- |
-- | Reference: plonk_checks.ml plonk_domain object type
type PlonkDomain f t m =
  { generator :: FVar f
  , shifts :: Vector 7 (FVar f)
  , vanishingPolynomial :: FVar f -> Snarky (KimchiConstraint f) t m (FVar f)
  }

-- | Pseudo.Domain.to_domain: construct a plonk domain from a one-hot selection
-- | over possible domain sizes.
-- |
-- | Shifts optimization: if all domain sizes produce identical shifts (which
-- | they do in practice), returns constants with 0 constraints. The OCaml
-- | implementation fails at runtime if shifts differ (disabled_not_the_same).
-- |
-- | Generator: selected via mask, generates n R1CS constraints.
-- |
-- | VanishingPolynomial: lazy closure that when called:
-- |   1. Builds pow2_pows via repeated squaring (max_log2 Square constraints)
-- |   2. Selects x^(2^log2_size) via choose/mask (n R1CS constraints)
-- |   3. Subtracts 1 and seals (exists + assertEqual = 1 R1CS)
-- |
-- | Reference: pseudo.ml:103-128
toDomain
  :: forall n f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Reflectable n Int
  => Compare 0 n LT
  => { shifts :: Int -> Vector 7 f
     , domainGenerator :: Int -> f
     }
  -> Vector n (BoolVar f)
  -> Vector n Int
  -> Snarky (KimchiConstraint f) t m (PlonkDomain f t m)
toDomain { shifts: getShifts, domainGenerator } which log2s = do
  -- Shifts: all domains have same shifts, return constants (pseudo.ml:61-73)
  let shifts_ = map const_ (getShifts (Vector.head log2s))
  -- Generator: mask-select over domain generators (pseudo.ml:95-96)
  generator <- mask which (map (\d -> const_ (domainGenerator d)) log2s)
  let
    maxLog2 = foldl max 0 log2s
    -- Vanishing polynomial closure (pseudo.ml:118-127)
    vanishingPolynomial x = do
      -- pow2_pows = [x, x^2, x^4, ..., x^(2^max_log2)]
      pow2Pows <- buildPow2Pows x maxLog2
      zetaToN <- choose which log2s
        (\log2 -> unsafePartial $ fromJust $ Array.index pow2Pows log2)
      seal (zetaToN `sub_` const_ one)
  pure { generator, shifts: shifts_, vanishingPolynomial }
  where
  buildPow2Pows z n = do
    Tuple _ acc <- foldM
      ( \(Tuple prev acc) _ -> do
          sq <- square_ prev
          pure (Tuple sq (Array.snoc acc sq))
      )
      (Tuple z [ z ])
      (Array.range 1 n)
    pure acc
