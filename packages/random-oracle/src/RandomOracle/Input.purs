-- | Random Oracle Input types for structured input packing.
-- |
-- | This module provides the `Chunked` input format which allows
-- | combining full field elements with packed chunks (small values
-- | that can be combined into a single field element).
module RandomOracle.Input
  ( Chunked(..)
  , PackedChunk
  , field
  , fieldElements
  , append
  , packToFields
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import JS.BigInt as BigInt
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromInt, pow)
import Type.Proxy (Proxy(..))

-- | A packed chunk is a field value with a known bit length.
-- | The invariant is that 0 <= value < 2^length
type PackedChunk f = { value :: f, length :: Int }

-- | Chunked input format for random oracle.
-- |
-- | This format allows efficient packing of values when we know their bit lengths.
-- | For example, a 64-bit value and a 32-bit value can be packed into a single
-- | field element if the field has more than 96 bits.
type Chunked f =
  { fieldElements :: Array f
  , packeds :: Array (PackedChunk f)
  }

-- | Create a chunked input from a single field element
field :: forall f. f -> Chunked f
field x = { fieldElements: [ x ], packeds: [] }

-- | Create a chunked input from multiple field elements
fieldElements :: forall f. Array f -> Chunked f
fieldElements xs = { fieldElements: xs, packeds: [] }

-- | Append two chunked inputs
append :: forall f. Chunked f -> Chunked f -> Chunked f
append t1 t2 =
  { fieldElements: t1.fieldElements <> t2.fieldElements
  , packeds: t1.packeds <> t2.packeds
  }

-- | Greedy left-to-right bit-packer. Concatenates `packeds` entries
-- | into single field elements as long as the accumulated bit-length
-- | stays strictly below `size_in_bits`; otherwise flushes the current
-- | accumulator and starts a new one. Output is
-- | `fieldElements ++ <packed-chunks>`.
-- |
-- | Mirrors `Random_oracle_input.Chunked.pack_to_fields`
-- | (`mina/src/lib/crypto/random_oracle_input/random_oracle_input.ml:59`).
packToFields
  :: forall f n
   . PrimeField f
  => FieldSizeInBits f n
  => Chunked f
  -> Array f
packToFields { fieldElements: fes, packeds } =
  let
    sizeInBits = reflectType (Proxy :: Proxy n)
    shiftLeft a k = a * pow (fromInt 2 :: f) (BigInt.fromInt k)
    -- ((rev-flushed, current acc), current bit-length)
    Tuple (Tuple revFlushed acc) accN =
      foldl
        ( \(Tuple (Tuple xs accField) accN_) { value, length } ->
            let
              n' = length + accN_
            in
              if n' < sizeInBits then
                Tuple (Tuple xs (shiftLeft accField length + value)) n'
              else
                Tuple (Tuple (Array.cons accField xs) value) length
        )
        (Tuple (Tuple [] zero) 0)
        packeds
    chunks =
      Array.reverse $
        if accN > 0 then Array.cons acc revFlushed else revFlushed
  in
    fes <> chunks

