-- | `BoundVk`'s constructor, for the two callers that need a key the
-- | rule has not bound: the circuit-diff harnesses, which reproduce an
-- | OCaml rule that binds nothing, and the tests that pair with them.
-- |
-- | Application code imports `Pickles.Sideload.BoundVk`, where the only
-- | way to obtain a `BoundVk` is `bindVk`.
module Pickles.Sideload.BoundVk.Internal
  ( BoundVk(..)
  , unsafeUnboundVk
  ) where

import Pickles.Field (StepField)
import Pickles.Sideload.VerificationKey (VerificationKey) as SLVK
import Pickles.Types (WrapVkChunks)
import Snarky.Circuit.DSL (BoolVar, FVar)

-- | A side-loaded verification key a rule has tied to its own
-- | statement. The step circuit verifies that slot's previous proof
-- | against it.
newtype BoundVk = BoundVk
  (SLVK.VerificationKey WrapVkChunks (FVar StepField) (BoolVar StepField))

-- | A key with no binding, which leaves the slot certifying nothing
-- | about which child it verified.
unsafeUnboundVk
  :: SLVK.VerificationKey WrapVkChunks (FVar StepField) (BoolVar StepField)
  -> BoundVk
unsafeUnboundVk = BoundVk
