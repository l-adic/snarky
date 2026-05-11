-- | Public API for the Pickles recursive zero-knowledge proof system.
-- |
-- | This module is a thin re-export facade. Library consumers should
-- | `import Pickles` (and `import Pickles.Sideload` for the side-
-- | loading feature) rather than reaching into the underlying source
-- | modules directly. Internal-only modules — base-case dummy
-- | assembly, the pure reference prover, circuit primitives, kimchi
-- | FFI, etc. — are not re-exported here; they remain reachable
-- | directly for niche needs but aren't part of the public surface.
module Pickles
  ( module Pickles.Field
  , module Pickles.ProofsVerified
  , module Pickles.Slots
  , module Pickles.Wrap.Slots
  , module Pickles.Types
  , module Pickles.Step.Advice
  , module Pickles.Prove.Step
  , module Pickles.Prove.Compile
  , module Pickles.Verify
  ) where

import Pickles.Field (StepField, WrapField)
import Pickles.ProofsVerified (ProofsVerified(..))
import Pickles.Prove.Compile (BranchProver(..), CompiledProof(..), PrevSlot(..), RuleEntry, RulesCons, RulesNil, SlotWrapKey(..), Tag(..), compileMulti, mkRuleEntry)
import Pickles.Prove.Step (StepRule)
import Pickles.Slots (Compiled, SideLoaded, Slot, SlotKind)
import Pickles.Step.Advice (getPrevAppStates)
import Pickles.Types (PaddedLength, StatementIO(..), StepIPARounds, WrapIPARounds)
import Pickles.Verify (Verifier, mkVerifier, verify, wrapPublicInputOf)
import Pickles.Wrap.Slots (NoSlots, Slots1, Slots2)
