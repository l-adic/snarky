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
  ) where

import Prelude

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

