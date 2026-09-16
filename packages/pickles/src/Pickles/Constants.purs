-- | Value-level protocol constants. The ones that are type-level
-- | naturals live in `Pickles.Types` instead.
module Pickles.Constants
  ( zkRowsByDefault
  , zkRowsForNumChunks
  , roughDomainsLog2
  ) where

import Prelude

-- | Kimchi's `zk_rows` at one chunk.
zkRowsByDefault :: Int
zkRowsByDefault = 3

-- | Kimchi's `zk_rows` as a function of `num_chunks`. The formula is
-- | fixed by the backend (`kimchi`'s `constraints.rs`), not chosen
-- | here.
zkRowsForNumChunks :: Int -> Int
zkRowsForNumChunks nc = (16 * nc + 5) `div` 7

-- | Placeholder domain log2 for the sizing pre-pass. Each rule's step
-- | circuit is built at this domain only so its gate count can be
-- | measured; the real pass then uses the log2 that count implies.
roughDomainsLog2 :: Int
roughDomainsLog2 = 20
