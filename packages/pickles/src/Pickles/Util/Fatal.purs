-- | Labeled partial-function helpers for Pickles.
-- |
-- | The Pickles codebase has many places where we convert runtime
-- | data into statically-sized containers (`Array a -> Vector n a`,
-- | `Array a -> SizedF n (F f)`) under an invariant that the runtime
-- | length matches `n` by construction. `Data.Maybe.fromJust` + a
-- | bare `unsafePartial` hides these sites — if the invariant ever
-- | breaks you get `Failed pattern match at Data.Maybe line 288`
-- | with no context.
-- |
-- | `fromJust'` attaches a **label** to the crash so the source of
-- | an invariant violation is self-documenting. Conventions:
-- |
-- |   * Label names the callsite's role, not the operation.
-- |     Good:  "wrap VK coeff (expected 15 points from column_comms)"
-- |     Bad:   "Vector.toVector"
-- |
-- |   * Include the type-level size when it's the precondition:
-- |     "step VK sigma-6 (Array.take 6 raw, expected ≥ 6 elems)"
-- |
-- |   * Prefer a data-dependent description of WHY the invariant is
-- |     believed to hold, so a crash tells the debugger the premise
-- |     that's been violated.
-- |
-- | Usage:
-- |
-- | ```
-- | fromJust' "wrap VK coeff (15 points)" (Vector.toVector @15 coeff15Raw)
-- | ```
module Pickles.Util.Fatal
  ( fromJust'
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafeCrashWith)

-- | Unwrap a `Maybe a`, crashing with a labeled message on `Nothing`.
-- | Replaces `unsafePartial $ Data.Maybe.fromJust` everywhere the
-- | runtime value is expected to be `Just` by a construction-level
-- | invariant.
fromJust' :: forall a. String -> Maybe a -> a
fromJust' _ (Just a) = a
fromJust' label Nothing =
  unsafeCrashWith
    ("Pickles.Util.Fatal.fromJust': Nothing at label " <> show label)
