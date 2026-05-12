-- | Horner combine for chunked polynomial evaluations.
-- |
-- | When a polynomial doesn't fit in a single SRS-sized slice, the prover
-- | commits to chunks `e[0], e[1], ..., e[n-1]` representing
-- |   P(x) = e[0] + e[1] * x^N + e[2] * x^(2N) + ... + e[n-1] * x^((n-1)*N)
-- | where `N = 2^rounds` is the SRS-poly size. This module recombines
-- | the chunks at evaluation point `pt` into the single scalar `P(pt)`
-- | via Horner's method.
-- |
-- | Reference (production OCaml):
-- |   `mina/src/lib/crypto/pickles/plonk_checks/plonk_checks.ml:90-100`
-- |     `let actual_evaluation (module Field) (e : Field.t array) (pt : Field.t)`
-- |     `    ~rounds : Field.t = ...`
-- |
-- | Validation strategy: no in-isolation golden tests. Correctness is
-- | exercised end-to-end via Checkpoint 4's chunks2 witness-byte-equality
-- | (any error in this Horner combine cascades to combined_inner_product
-- | divergence at the byte level vs OCaml). See `docs/chunking.md` and
-- | `docs/chunking-ffi-audit.md`.
module Pickles.PlonkChecks.Chunks
  ( actualEvaluation
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Data.Vector (Vector)
import Data.Vector as Vector

-- | Horner combine for `n` chunked evaluations at point `pt^(2^rounds)`.
-- |
-- | Returns `e[0] + ptN * (e[1] + ptN * (... + ptN * e[n-1]))`
-- | where `ptN = pt^(2^rounds)`. Algebraically:
-- |   Σ_{i=0..n-1} e[i] * ptN^i
-- |
-- | At `n=1` returns `e[0]` unchanged (identity).
-- |
-- | The implementation mirrors the OCaml 6-liner exactly:
-- |   1. Compute `ptN` via `rounds` rounds of squaring `pt`.
-- |   2. Reverse the input array.
-- |   3. Fold from the new head with accumulator update `acc' = fx + ptN * acc`.
-- | At `n=0` (no chunks) returns `zero` — this branch is unreachable
-- | in practice because kimchi always emits ≥1 chunk per polynomial, but
-- | the total type signature requires it.
actualEvaluation
  :: forall @n f
   . Semiring f
  => Vector n f
  -> f
  -> Int
  -> f
actualEvaluation xs pt rounds =
  let
    ptN = squareN rounds pt
    xsRev = Array.reverse (Vector.toUnfoldable xs)
  in
    case Array.uncons xsRev of
      Just { head, tail } -> foldl (\acc fx -> fx + ptN * acc) head tail
      Nothing -> zero

-- | `squareN n x = x^(2^n)`. n=0 → x, n=1 → x*x, n=2 → (x*x)^2 = x^4, etc.
squareN :: forall f. Semiring f => Int -> f -> f
squareN n x = go n x
  where
  go 0 acc = acc
  go i acc = go (i - 1) (acc * acc)
