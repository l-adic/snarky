-- | Deterministic dummy IPA challenges.
-- |
-- | Mirrors OCaml's `mina/src/lib/pickles/dummy.ml`. Dummy challenges are
-- | deterministic constants derived from a BLAKE2s-based random oracle
-- | (OCaml's `ro.ml`). They're used as padding when a circuit expects multiple
-- | previous proofs but fewer actually exist.
-- |
-- | The random oracle works as follows (matching `ro.ml`):
-- | 1. `BLAKE2s-256(string)` → raw bytes → each byte to 8 bits LSB-first
-- | 2. Counter starts at 0, each call increments then hashes `"chal_" <> show counter`
-- | 3. Take first 128 bits → pack into a field element via `fromBits`
-- |
-- | Counter ordering follows OCaml module initialization:
-- | - Wrap challenges use counters 1..WrapIPARounds (eagerly evaluated first)
-- | - Step challenges use counters (WrapIPARounds+1)..(WrapIPARounds+StepIPARounds)
-- |
-- | Expanded challenges are the raw 128-bit scalar challenges expanded to full
-- | field elements via `toFieldPure` with the circuit's endo scalar.
-- |
-- | Reference: mina/src/lib/pickles/dummy.ml, mina/src/lib/pickles/ro.ml
module Pickles.Dummy
  ( dummyWrapChallengesExpanded
  , dummyWrapChallengesRaw
  , dummyStepChallengesExpanded
  , dummyStepChallengesRaw
  ) where

import Prelude

import Data.Array as Array
import Data.Blake2s (blake2s256Bits)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Types (StepField, StepIPARounds, WrapField, WrapIPARounds)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (SizedF, fromBits)
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, EndoScalar(..), endoScalar)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Type.Proxy (Proxy(..))

-- | Raw 128-bit Wrap dummy challenges (counters 1..WrapIPARounds).
dummyWrapChallengesRaw :: Vector WrapIPARounds (SizedF 128 WrapField)
dummyWrapChallengesRaw = wrapRaw.challenges

-- | Expanded Wrap dummy challenges (full Fq field elements).
-- |
-- | These are the values needed for `messagesForNextWrapProof` hash padding.
dummyWrapChallengesExpanded :: Vector WrapIPARounds WrapField
dummyWrapChallengesExpanded = map (\c -> toFieldPure c wrapEndo) dummyWrapChallengesRaw

-- | Raw 128-bit Step dummy challenges (counters WrapIPARounds+1..WrapIPARounds+StepIPARounds).
dummyStepChallengesRaw :: Vector StepIPARounds (SizedF 128 StepField)
dummyStepChallengesRaw = stepRaw.challenges

-- | Expanded Step dummy challenges (full Fp field elements).
dummyStepChallengesExpanded :: Vector StepIPARounds StepField
dummyStepChallengesExpanded = map (\c -> toFieldPure c stepEndo) dummyStepChallengesRaw

-------------------------------------------------------------------------------
-- Random oracle (ro.ml)
-------------------------------------------------------------------------------

-- | `bits_random_oracle ~length s` — BLAKE2s-256 of a string, truncated to `length` bits.
-- |
-- | Bit ordering: LSB-first per byte, matching OCaml's
-- | `Char.to_int c |> List.init 8 ~f:(fun i -> (c lsr i) land 1 = 1)`.
bitsRandomOracle :: Int -> String -> Array Boolean
bitsRandomOracle length s = Array.take length (blake2s256Bits s)

-- | One step of the "chal" random oracle: increment counter, produce a
-- | scalar challenge from `BLAKE2s("chal_" <> show counter)`.
scalarChal
  :: forall @n @m @f
   . FieldSizeInBits f m
  => Reflectable n Int
  => Compare n m LT
  => PrimeField f
  => Int
  -> { counter :: Int, challenge :: SizedF n f }
scalarChal counter =
  let
    next = counter + 1
    n = reflectType (Proxy @n)
    bits = bitsRandomOracle n ("chal_" <> show next)
    challenge = fromBits $ unsafePartial fromJust $ Vector.toVector @n bits
  in
    { counter: next, challenge }

-- | Generate `n` raw scalar challenges starting from the given counter.
generateChallenges
  :: forall @n f
   . Compare 128 255 LT
  => FieldSizeInBits f 255
  => PrimeField f
  => Reflectable n Int
  => Int
  -> { counter :: Int, challenges :: Vector n (SizedF 128 f) }
generateChallenges startCounter =
  let
    n = reflectType (Proxy @n)
    go { counter, acc } _idx =
      let
        { counter: next, challenge } = scalarChal @128 @255 counter
      in
        { counter: next, acc: acc <> [ challenge ] }
    result = Array.foldl go { counter: startCounter, acc: [] }
      (Array.range 0 (n - 1))
  in
    { counter: result.counter
    , challenges: unsafePartial fromJust $ Vector.toVector @n result.acc
    }

-------------------------------------------------------------------------------
-- Internal constants
-------------------------------------------------------------------------------

wrapRaw :: { counter :: Int, challenges :: Vector WrapIPARounds (SizedF 128 WrapField) }
wrapRaw = generateChallenges @WrapIPARounds 0

stepRaw :: { counter :: Int, challenges :: Vector StepIPARounds (SizedF 128 StepField) }
stepRaw = generateChallenges @StepIPARounds wrapRaw.counter

wrapEndo :: WrapField
wrapEndo = let EndoScalar e = endoScalar @Pallas.BaseField @Pallas.ScalarField in e

stepEndo :: StepField
stepEndo = let EndoScalar e = endoScalar @Vesta.BaseField @Vesta.ScalarField in e
