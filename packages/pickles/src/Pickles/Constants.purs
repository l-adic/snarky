-- | Pickles-wide value-level protocol constants. The corresponding
-- | type-level numerics live in `Pickles.Types` (`StepIPARounds`,
-- | `WrapIPARounds`, etc.); this module covers values that don't fit
-- | naturally as type-level naturals.
module Pickles.Constants
  ( zkRows
  , roughDomainsLog2
  ) where

-- | Kimchi's zero-knowledge masking row count, written into every
-- | `Plonk_minimal`-style record. Mirrors OCaml's `Plonk_checks.zk_rows`.
zkRows :: Int
zkRows = 3

-- | OCaml `Fix_domains.rough_domains` placeholder log2. The pre-pass
-- | builds each rule's step circuit with this domain so the gate count
-- | can be measured; the real-pass replaces it with the precise log2
-- | derived from that count.
roughDomainsLog2 :: Int
roughDomainsLog2 = 20
