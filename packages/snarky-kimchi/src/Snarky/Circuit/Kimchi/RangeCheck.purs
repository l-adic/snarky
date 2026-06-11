-- | Range checks built on the Kimchi `EndoScalar` gate.
-- |
-- | `EndoScalar.toField @8` decomposes a 128-bit value across 8 rows
-- | (16 bits each), which doubles as a 128-bit range check. The helpers
-- | here use that to split a field element into its low/high 128-bit
-- | halves and range-check them, giving a cheaper alternative to bit
-- | unpacking for proving a value fits in 128 bits.
module Snarky.Circuit.Kimchi.RangeCheck
  ( rangeCheck128
  , lowest128Bits
  , lowest128Bits'
  , lowest128BitsPure
  ) where

import Prelude

import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..))
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.DSL (F(..), FVar, SizedF, Snarky, UnChecked(..), add_, assertEqual_, exists, fromField, read, scale_)
import Snarky.Circuit.DSL as SizedF
import Snarky.Circuit.Kimchi.EndoScalar as EndoScalar
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, toBigInt)

-- | Assert that a value fits in 128 bits, using the `EndoScalar` gate as
-- | the range check (the same primitive `lowest128Bits` uses to constrain
-- | its halves). Cheaper than unpacking to bits and zeroing the tail.
-- |
-- | The `endo` argument is the EndoScalar constant for the circuit field
-- | `f` — derive it from `HasEndo` (`endoScalar`) at the call site, where
-- | the field is concrete.
rangeCheck128
  :: forall f r
   . FieldSizeInBits f 255
  => PrimeField f
  => FVar f -- ^ endo constant
  -> SizedF 128 (FVar f) -- ^ value to range-check
  -> Snarky f (KimchiConstraint f) r Unit
rangeCheck128 endo v = void $ EndoScalar.toField @8 v endo

-- | Extract the lowest 128 bits of a field element, with range checking
-- | via EndoScalar gate decomposition.
-- |
-- | Matches OCaml's `lowest_128_bits ~constrain_low_bits:true`:
-- | 1. Witness lo, hi such that x = lo + hi * 2^128
-- | 2. Range-check hi via EndoScalar.toField (discarding result)
-- | 3. Range-check lo via EndoScalar.toField (discarding result)
-- | 4. Assert x = lo + hi * 2^128
-- | 5. Return lo
-- |
-- | The endo parameter is a raw FVar f (the EndoScalar constant for the circuit field).
lowest128Bits
  :: forall f r
   . PrimeField f
  => FieldSizeInBits f 255
  => PrimeField f
  => FVar f -- ^ endo constant
  -> FVar f -- ^ x (sponge squeeze output)
  -> Snarky f (KimchiConstraint f) r (SizedF 128 (FVar f))
lowest128Bits = lowest128Bits' true

-- | Parameterized version: `constrainLowBits` controls whether lo is range-checked.
-- |
-- | - `true`: matches OCaml's `squeeze_challenge` (constrain_low_bits:true)
-- | - `false`: matches OCaml's `squeeze_scalar` (constrain_low_bits:false, only hi checked)
lowest128Bits'
  :: forall f r
   . PrimeField f
  => FieldSizeInBits f 255
  => PrimeField f
  => Boolean
  -> FVar f -- ^ endo constant
  -> FVar f -- ^ x (sponge squeeze output)
  -> Snarky f (KimchiConstraint f) r (SizedF 128 (FVar f))
lowest128Bits' constrainLowBits endo x = do
  -- Witness lo (first) and hi (second), matching OCaml's Typ.(field * field)
  UnChecked (Tuple lo hi) <- exists do
    F xVal <- read x
    let
      xBig = toBigInt xVal

      lo :: SizedF 128 (F f)
      lo = unsafePartial $ fromJust $ SizedF.fromField @128 (fromBigInt (mod xBig two128))

      hi :: SizedF 128 (F f)
      hi = unsafePartial $ fromJust $ SizedF.fromField @128 (fromBigInt (div xBig two128))
    pure $ UnChecked (Tuple lo hi)
  -- Range check hi via EndoScalar (discard result) — hi first, matching OCaml
  void $ EndoScalar.toField @8 hi endo
  -- Range check lo via EndoScalar (discard result) — only when constrain_low_bits:true
  when constrainLowBits $ void $ EndoScalar.toField @8 lo endo
  -- Assert x = lo + hi * 2^128
  assertEqual_ x (add_ (SizedF.toField lo) (scale_ (fromBigInt two128) $ SizedF.toField hi))
  pure lo
  where
  two128 = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)

-- | Pure version: extract lowest 128 bits of a field element.
lowest128BitsPure
  :: forall f
   . PrimeField f
  => FieldSizeInBits f 255
  => f
  -> SizedF 128 f
lowest128BitsPure x =
  let
    xBig = toBigInt x
    two128 = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)
    lo = fromBigInt (mod xBig two128)
  in
    unsafePartial $ fromJust (fromField @128 lo)
