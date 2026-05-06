-- | Two_phase_chain wrap_main fixture: 2 branches sharing one wrap key.
-- |
-- | Configuration:
-- |   branches=2 (make_zero + increment)
-- |   step_widths=[0; 1]   (make_zero=0 prev, increment=1 prev)
-- |   slots = Slots1 1       (mpv=N1, single slot of width 1)
-- |   per-branch step domains: [9; 14] — make_zero compiles to a tiny
-- |     step circuit (no verify_one), increment compiles to a full one;
-- |     the domains DIFFER, so wrap_main goes through the per-branch
-- |     `lagrange_with_correction` dispatch path.
-- |   Features.none
-- |
-- | Step VKs are derived deterministically by recompiling each branch's
-- | step CS (which we match byte-for-byte via
-- | `compileStepMainTwoPhaseChain{MakeZero,Increment}`) and running the
-- | kimchi commitment pipeline. Mirrors the deterministic-VK fix family.
-- |
-- | Note: the returned `WrapArtifact`'s `stepCs` / `stepDomainLog2` fields
-- | reflect the INCREMENT branch (the last-compiled, "main" branch). For
-- | multi-branch wraps without a parent consumer, these fields are
-- | informational only.
module Pickles.CircuitDiffs.PureScript.WrapMainTwoPhaseChain
  ( WrapMainTwoPhaseChainParams
  , compileWrapMainTwoPhaseChain
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.StepMainTwoPhaseChainIncrement (StepMainTwoPhaseChainIncrementParams, compileStepMainTwoPhaseChainIncrement)
import Pickles.CircuitDiffs.PureScript.StepMainTwoPhaseChainMakeZero (StepMainTwoPhaseChainMakeZeroParams, compileStepMainTwoPhaseChainMakeZero)
import Pickles.ProofFFI (pallasSrsLagrangeCommitmentAt)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Types (StepField, WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Pickles.Wrap.Slots (Slots1)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | Two_phase_chain needs per-branch SRS access (not just `lagrangeAt`)
-- | because the branches' step domains differ.
type WrapMainTwoPhaseChainParams =
  { vestaSrs :: CRS VestaG
  , lagrangeAt :: LagrangeBaseLookup WrapField
  , blindingH :: AffinePoint (F WrapField)
  , makeZeroStepSrsData :: StepMainTwoPhaseChainMakeZeroParams
  , incrementStepSrsData :: StepMainTwoPhaseChainIncrementParams
  }

compileWrapMainTwoPhaseChain
  :: WrapMainTwoPhaseChainParams -> Effect WrapArtifact
compileWrapMainTwoPhaseChain { vestaSrs, lagrangeAt, blindingH, makeZeroStepSrsData, incrementStepSrsData } = do
  -- Compile both branches' step CSes. make_zero first (so its artifact
  -- is available for increment's per-branch FOP domain dispatch).
  makeZeroArt <- compileStepMainTwoPhaseChainMakeZero makeZeroStepSrsData
  incrementArt <- compileStepMainTwoPhaseChainIncrement makeZeroArt incrementStepSrsData
  vestaSrs' <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  let
    -- @0 for make_zero (n=0 prev_challenges), @1 for increment (n=1).
    makeZeroVK = deriveStepVKFromCompiled @0 vestaSrs' makeZeroArt.stepCs
    incrementVK = deriveStepVKFromCompiled @1 vestaSrs' incrementArt.stepCs

    -- Per-branch lagrange lookup at each branch's step domain log2.
    -- Both values derived from artifacts (no hardcoded 9 / 14).
    perBranchLookup i =
      ((coerce (pallasSrsLagrangeCommitmentAt vestaSrs makeZeroArt.stepDomainLog2 i)) :: AffinePoint (F WrapField))
        :< ((coerce (pallasSrsLagrangeCommitmentAt vestaSrs incrementArt.stepDomainLog2 i)) :: AffinePoint (F WrapField))
        :< Vector.nil

    config :: WrapMainConfig 2
    config =
      { stepWidths: 0 :< 1 :< Vector.nil
      , domainLog2s: makeZeroArt.stepDomainLog2 :< incrementArt.stepDomainLog2 :< Vector.nil
      , stepKeys: makeZeroVK :< incrementVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Just perBranchLookup
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- Slots1 1: mpv=1, single slot of max width 1.
  wrapCs <- compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @2 @(Slots1 1) config stmt)
    Kimchi.initialState
  pure
    { stepCs: incrementArt.stepCs
    , stepDomainLog2: incrementArt.stepDomainLog2
    , wrapCs
    , wrapVk: deriveWrapVKFromCompiled @2 pallasSrs wrapCs
    }
