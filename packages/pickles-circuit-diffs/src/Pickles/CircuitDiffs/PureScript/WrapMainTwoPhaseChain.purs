-- | Two_phase_chain wrap_main fixture: 2 branches sharing one wrap key.
-- |
-- | Configuration:
-- |   branches=2 (make_zero + increment)
-- |   step_widths=[0; 1]   (make_zero=0 prev, increment=1 prev)
-- |   padded=[[0; 0]; [0; 1]] — slot 0 unused, slot 1 holds the prev for
-- |     increment; make_zero contributes 0 in both slots
-- |   slots = Slots1 1       (mpv=N1, single slot of width 1)
-- |   per-branch step domains: [9; 14] — make_zero compiles to a tiny
-- |     step circuit (no verify_one), increment compiles to a full one;
-- |     the domains DIFFER, so wrap_main goes through the per-branch
-- |     `lagrange_with_correction` dispatch path (wrap_verifier.ml:429-443)
-- |     rather than the shared-domain fast path.
-- |   Features.none
-- |
-- | OCaml dump target: `wrap_main_two_phase_chain_circuit.json`
-- | produced by `dump_two_phase_chain.exe`'s wrap CS construction
-- | (the only wrap in a multi-rule compile_promise — both branches
-- | share one wrap VK with `choose_key`-style step VK dispatch).
-- |
-- | Step VKs are derived deterministically by recompiling each branch's
-- | step CS (which we now match byte-for-byte via
-- | `compileStepMainTwoPhaseChain{MakeZero,Increment}`) and running the
-- | kimchi commitment pipeline. Mirrors the deterministic-VK fix family
-- | (wrap_main_circuit, wrap_main_n2, wrap_main_add_one_return,
-- | wrap_main_tree_proof_return).
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
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, deriveStepVKFromCompiled)
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
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Circuit.DSL (F(..))
import Type.Proxy (Proxy(..))

-- | Two_phase_chain needs per-branch SRS access (not just `lagrangeAt`)
-- | because the branches' step domains differ — the wrap_main config's
-- | `perBranchLagrangeAt` lookup queries the SRS at each branch's domain.
type WrapMainTwoPhaseChainParams =
  { vestaSrs :: CRS VestaG
  , lagrangeAt :: LagrangeBaseLookup WrapField
  , blindingH :: AffinePoint (F WrapField)
  , makeZeroStepSrsData :: StepMainTwoPhaseChainMakeZeroParams
  , incrementStepSrsData :: StepMainTwoPhaseChainIncrementParams
  }

compileWrapMainTwoPhaseChain
  :: WrapMainTwoPhaseChainParams -> Effect (CompiledCircuit WrapField)
compileWrapMainTwoPhaseChain { vestaSrs, lagrangeAt, blindingH, makeZeroStepSrsData, incrementStepSrsData } = do
  -- Recompile both branches' step CSes and derive per-branch step VKs.
  -- The wrap CS embeds these as compile-time constants via
  -- `choose_key`-style Pseudo dispatch over the runtime branch index.
  -- Same step CS shape (we match `step_main_two_phase_chain_*_circuit`
  -- byte-for-byte) + same Vesta SRS + same kimchi commitment algorithm
  -- = same VK constants OCaml's `compile_promise` produces.
  makeZeroBuiltState <- compileStepMainTwoPhaseChainMakeZero makeZeroStepSrsData
  incrementBuiltState <- compileStepMainTwoPhaseChainIncrement incrementStepSrsData
  pallasSrs <- createCRS @StepField
  let
    -- @0 for make_zero (n=0 prev_challenges in its kimchi CS),
    -- @1 for increment (n=1).
    makeZeroVK = deriveStepVKFromCompiled @0 pallasSrs makeZeroBuiltState
    incrementVK = deriveStepVKFromCompiled @1 pallasSrs incrementBuiltState

    -- Per-branch lagrange lookup: at each PI index `i`, return one constant
    -- lagrange basis point per branch (each at that branch's step domain
    -- log2). Mirrors `buildWrapMainConfigMulti`'s per-branch path.
    perBranchLookup i =
      ((coerce (pallasSrsLagrangeCommitmentAt vestaSrs 9 i)) :: AffinePoint (F WrapField))
        :< ((coerce (pallasSrsLagrangeCommitmentAt vestaSrs 14 i)) :: AffinePoint (F WrapField))
        :< Vector.nil

    config :: WrapMainConfig 2
    config =
      { stepWidths: 0 :< 1 :< Vector.nil
      , domainLog2s: 9 :< 14 :< Vector.nil
      , stepKeys: makeZeroVK :< incrementVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Just perBranchLookup
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- Slots1 1: mpv=1, single slot of max width 1. OCaml's
  -- `compile_promise` for two_phase_chain uses
  -- `~max_proofs_verified:(module Nat.N1)` (per
  -- `dump_two_phase_chain.ml:92`); the shared wrap VK is sized for the
  -- MAX prev count across both rules — make_zero has 0 prevs, increment
  -- has 1 → max = 1.
  compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @2 @(Slots1 1) config stmt)
    Kimchi.initialState
