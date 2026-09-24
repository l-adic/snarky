-- | Selection over a fixed set of options by a one-hot vector of
-- | circuit bits, and the plonk domain built that way.
-- | `Pickles.Wrap.Main` selects on the branch and the wrap domain
-- | index; `Pickles.Step.FinalizeOtherProof` selects the prev proof's
-- | domain generator.
module Pickles.Pseudo
  ( oneHotVector
  , mask
  , choose
  , PlonkDomain
  , toDomain
  , buildPow2Pows
  ) where

import Prelude

import Data.Fin (Finite, getFinite)
import Data.Foldable (foldl)
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import JS.BigInt (fromInt)
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (add_, sub_)
import Snarky.Circuit.DSL (Bool(..), BoolVar, FVar, Snarky, const_, equals_, label, mul_, seal, square_)
import Snarky.Circuit.DSL.Assert (assertNonZero_)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, fromBigInt)

-- | The bits `index == j` for `j` in `[0..n-1]`, asserted to contain
-- | at least one true entry.
oneHotVector
  :: forall @n f r
   . PrimeField f
  => Reflectable n Int
  => FVar f
  -> Snarky f (KimchiConstraint f) r (Vector n (BoolVar f))
oneHotVector index = label "one-hot-vector" do
  -- The comparison for `j = n-1` is emitted first and `j = 0` last;
  -- that order fixes the constraint sequence.
  let indices = Vector.generate @n identity
  vRev <- traverse (\j -> equals_ (const_ (fromBigInt (fromInt (getFinite j)))) index)
    (Vector.reverse indices)
  let
    v = Vector.reverse vRev

    asFields :: Vector n (FVar f)
    asFields = map coerce v
  assertNonZero_ (foldl add_ (const_ zero) asFields)
  pure v

-- | `∑ bits[i] * xs[i]`. Only the products cost constraints; the sum
-- | is `CVar` addition.
mask
  :: forall n f r
   . PrimeField f
  => Reflectable n Int
  => Vector n (BoolVar f)
  -> Vector n (FVar f)
  -> Snarky f (KimchiConstraint f) r (FVar f)
mask bits xs = label "pseudo-mask" do
  -- The last product is emitted first; that order fixes the
  -- constraint sequence.
  let
    boolToField = coerce
  termsRev <- traverse (\(Tuple b x) -> mul_ (boolToField b) x) $
    Vector.reverse (Vector.zip bits xs)
  let terms = Vector.reverse termsRev
  pure $ foldl add_ (const_ zero) terms

-- | `mask` over the options mapped through `f`.
choose
  :: forall n a f r
   . PrimeField f
  => Reflectable n Int
  => Vector n (BoolVar f)
  -> Vector n a
  -> (a -> FVar f)
  -> Snarky f (KimchiConstraint f) r (FVar f)
choose bits xs f = mask bits (map f xs)

-- | A plonk domain whose parameters were selected in-circuit. The
-- | vanishing polynomial is a closure so its constraints are emitted
-- | where it is applied, not where the domain is built.
type PlonkDomain f r =
  { generator :: FVar f
  , shifts :: Vector 7 (FVar f)
  , vanishingPolynomial :: FVar f -> Snarky f (KimchiConstraint f) r (FVar f)
  }

-- | The plonk domain selected by `which` from the candidate sizes
-- | `log2s`, which index a `buildPow2Pows` table of `maxLog2` entries.
-- |
-- | `shifts` are emitted as constants whichever candidate is selected,
-- | so every candidate must have exactly these shifts.
toDomain
  :: forall @maxLog2 maxPred n f r
   . PrimeField f
  => Reflectable n Int
  => Reflectable maxLog2 Int
  => Add 1 maxPred maxLog2
  => Add maxPred 1 maxLog2
  => { shifts :: Vector 7 f
     , domainGenerator :: Int -> f
     }
  -> Vector n (BoolVar f)
  -> Vector n (Finite maxLog2)
  -> Snarky f (KimchiConstraint f) r (PlonkDomain f r)
toDomain { shifts, domainGenerator } which log2s = do
  generator <- mask which (map (\d -> const_ (domainGenerator (getFinite d))) log2s)
  let
    vanishingPolynomial x = do
      pow2Pows <- buildPow2Pows x
      zetaToN <- choose which log2s
        (\log2 -> Vector.index pow2Pows log2)
      seal (zetaToN `sub_` const_ one)
  pure { generator, shifts: map const_ shifts, vanishingPolynomial }

-- | `[x, x^2, x^4, …, x^(2^(k-1))]`: entry `i` is `x^(2^i)`, at a cost
-- | of `k-1` Square constraints.
buildPow2Pows
  :: forall @k kPred f r
   . Add 1 kPred k
  => Add kPred 1 k
  => Reflectable k Int
  => PrimeField f
  => FVar f
  -> Snarky f (KimchiConstraint f) r (Vector k (FVar f))
buildPow2Pows x = do
  -- The tail of a `k`-sized vector drives the `k-1` squarings.
  let { tail: drivers } = Vector.uncons (Vector.generate identity)
  Tuple rest _ <- mapAccumM
    ( \prev _ -> do
        sq <- square_ prev
        pure (Tuple sq sq)
    )
    x
    drivers
  pure (x :< rest)
