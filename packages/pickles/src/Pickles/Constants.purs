-- | Pickles-wide value-level protocol constants. The corresponding
-- | type-level numerics live in `Pickles.Types` (`StepIPARounds`,
-- | `WrapIPARounds`, etc.); this module covers values that don't fit
-- | naturally as type-level naturals.
module Pickles.Constants
  ( zkRows
  , zkRowsForNumChunks
  , roughDomainsLog2
  ) where

import Prelude

-- | Kimchi's zero-knowledge masking row count for `num_chunks = 1`.
-- | Mirrors OCaml's `Plonk_checks.zk_rows_by_default`. For chunked
-- | circuits (`num_chunks > 1`) use `zkRowsForNumChunks` — kimchi
-- | bumps zk_rows for chunked proofs (formula in `constraints.rs`).
zkRows :: Int
zkRows = 3

-- | Kimchi's `zk_rows` derived from `num_chunks`. Mirrors the formula
-- | in `kimchi/src/circuits/constraints.rs:759-761`:
-- |   `zk_rows = (16 * num_chunks + 5) / 7`
-- | Values: nc=1 → 3, nc=2 → 5, nc=3 → 7, nc=4 → 9.
zkRowsForNumChunks :: Int -> Int
zkRowsForNumChunks nc = (16 * nc + 5) `div` 7

-- | OCaml `Fix_domains.rough_domains` placeholder log2. The pre-pass
-- | builds each rule's step circuit with this domain so the gate count
-- | can be measured; the real-pass replaces it with the precise log2
-- | derived from that count.
roughDomainsLog2 :: Int
roughDomainsLog2 = 20
