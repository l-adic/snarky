-- | Public API for the Pickles recursive zero-knowledge proof system.
-- |
-- | A re-export facade: `import Pickles`, plus `import Pickles.Sideload`
-- | for side-loading. Everything not re-exported here stays reachable
-- | directly but is not part of the public surface.
module Pickles
  ( module Pickles.Field
  , module Pickles.ProofsVerified
  , module Pickles.Slots
  , module Pickles.Types
  , module Pickles.Prove.Step
  , module Pickles.Prove.Compile
  , module Pickles.Prove.Slot
  , module Pickles.Sideload.BoundVk
  , module Pickles.Step.Slots
  , module Pickles.Verify
  ) where

import Pickles.Field (StepField, WrapField)
import Pickles.ProofsVerified (ProofsVerified(..))
import Pickles.Prove.Compile (BranchProver(..), CompiledProof(..), PrevSlot(..), RuleEntry, RulesCons, RulesNil, SideLoadedPrev(..), Tag(..), compileMulti, mkRuleEntry)
import Pickles.Prove.Slot (SlotWrapKey(..))
import Pickles.Prove.Step (StepRule)
import Pickles.Sideload.BoundVk (BoundVk)
import Pickles.Slots (SideLoadedSlot, Slot)
import Pickles.Step.Slots (PrevStatement(..), SideLoadedPrevStatement(..), SideLoadedPrevValue, prevValues, toPrevs)
import Pickles.Types (PaddedLength, StatementIO(..), StepIPARounds, WrapIPARounds, WrapVkChunks)
import Pickles.Verify (VerifiableProof, Verifier, mkVerifier, toVerifiable, verify, verifyBatch, wrapPublicInputOf)
