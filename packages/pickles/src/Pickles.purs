-- | Public API for the Pickles recursive zero-knowledge proof system.
-- |
-- | A re-export facade: `import Pickles`, plus `import Pickles.Sideload`
-- | for side-loading. Everything not re-exported here stays reachable
-- | directly but is not part of the public surface.
module Pickles
  ( module Pickles.Field
  , module Pickles.ProofsVerified
  , module Pickles.Sideload.Bundle
  , module Pickles.Slots
  , module Pickles.Types
  , module Pickles.Prove.Step
  , module Pickles.Prove.Compile
  , module Pickles.Step.Slots
  , module Pickles.Verify
  ) where

import Pickles.Field (StepField, WrapField)
import Pickles.ProofsVerified (ProofsVerified(..))
import Pickles.Prove.Compile (BranchProver(..), CompiledProof(..), PrevSlot(..), RuleEntry, RulesCons, RulesNil, SlotWrapKey(..), Tag(..), compileMulti, mkRuleEntry)
import Pickles.Prove.Step (StepRule)
-- The one side-loading name on the main path: a rule with no
-- side-loaded slot still names `NoSideLoadedVk` once per slot.
import Pickles.Sideload.Bundle (SlotProveVk(..))
import Pickles.Slots (Slot)
import Pickles.Step.Slots (PrevStatement(..), prevValues, toPrevs)
import Pickles.Types (PaddedLength, StatementIO(..), StepIPARounds, WrapIPARounds, WrapVkChunks)
import Pickles.Verify (VerifiableProof, Verifier, mkVerifier, toVerifiable, verify, verifyBatch, wrapPublicInputOf)
