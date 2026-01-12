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
  , packed
  , packeds
  , append
  , packToFields
  ) where

import Prelude

import Data.Array (foldl, snoc)
import Data.Reflectable (reflectType)
import JS.BigInt as BigInt
import Snarky.Curves.Class (class FieldSizeInBits, fromInt, pow)
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

-- | Create a chunked input from a single packed value
packed :: forall f. f -> Int -> Chunked f
packed x len = { fieldElements: [], packeds: [ { value: x, length: len } ] }

-- | Create a chunked input from multiple packed values
packeds :: forall f. Array (PackedChunk f) -> Chunked f
packeds xs = { fieldElements: [], packeds: xs }

-- | Append two chunked inputs
append :: forall f. Chunked f -> Chunked f -> Chunked f
append t1 t2 =
  { fieldElements: t1.fieldElements <> t2.fieldElements
  , packeds: t1.packeds <> t2.packeds
  }

-- | Pack chunked input into field elements.
-- |
-- | This greedily combines packed chunks from left to right into field elements,
-- | ensuring the combined value doesn't overflow the field.
packToFields :: forall @n f. FieldSizeInBits f n => Chunked f -> Array f
packToFields { fieldElements: fields, packeds: chunks } =
  let
    sizeBits = reflectType (Proxy @n)

    packChunk
      :: { accBits :: Int
         , acc :: f
         , packed :: Array f
         }
      -> PackedChunk f
      -> { accBits :: Int
         , acc :: f
         , packed :: Array f
         }
    packChunk state chunk =
      let
        newBits = chunk.length + state.accBits
      in
        if newBits < sizeBits then
          -- Combine with accumulator: shift accumulator left and add chunk
          let
            newAcc = (state.acc * pow (fromInt 2) (BigInt.fromInt chunk.length)) + chunk.value
          in
            state { acc = newAcc, accBits = newBits }
        else
          -- Flush accumulator and start new one
          let
            newPacked =
              if state.accBits > 0 then snoc state.packed state.acc
              else state.packed
          in
            { packed: newPacked, acc: chunk.value, accBits: chunk.length }

    -- Fold over packed chunks, accumulating into field elements
    result = foldl packChunk { packed: [], acc: zero, accBits: 0 } chunks

    -- Get final packed elements
    finalPacked =
      if result.accBits > 0 then snoc result.packed result.acc
      else result.packed
  in
    fields <> finalPacked
