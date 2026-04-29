-- | Two_phase_chain wrap_main fixture: 2 branches sharing one wrap key.
-- |
-- | Configuration:
-- |   branches=2 (make_zero + increment)
-- |   step_widths=[0; 1]   (make_zero=0 prev, increment=1 prev)
-- |   padded=[[0; 0]; [0; 1]] — slot 0 unused, slot 1 holds the prev for
-- |     increment; make_zero contributes 0 in both slots
-- |   slots = Slots2 0 1     (slot maxima across branches)
-- |   per-branch step domains: [9; 14] — make_zero compiles to a tiny
-- |     step circuit (no verify_one), increment compiles to a full one;
-- |     the domains DIFFER, so wrap_main goes through the per-branch
-- |     `lagrange_with_correction` dispatch path (wrap_verifier.ml:429-443)
-- |     rather than the shared-domain fast path.
-- |   Features.none
-- |
-- | OCaml dump target: `wrap_main_two_phase_chain_circuit.json` produced by
-- | `dump_circuit_impl.ml` with `Wrap_main_for_dump.build_multi_domain` —
-- | `pi_branches=2`, `padded=[[0;0];[0;1]]`, `step_widths=[0;1]`,
-- | `step_domains_log2=[9;14]`.
module Pickles.CircuitDiffs.PureScript.WrapMainTwoPhaseChain
  ( WrapMainTwoPhaseChainParams
  , compileWrapMainTwoPhaseChain
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt)
import Pickles.ProofFFI (pallasSrsLagrangeCommitmentAt)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Types (WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Pickles.Wrap.Slots (Slots2)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | Two_phase_chain needs per-branch SRS access (not just `lagrangeAt`)
-- | because the branches' step domains differ — the wrap_main config's
-- | `perBranchLagrangeAt` lookup queries the SRS at each branch's domain.
type WrapMainTwoPhaseChainParams =
  { vestaSrs :: CRS VestaG
  , lagrangeAt :: LagrangeBaseLookup WrapField
  , blindingH :: AffinePoint (F WrapField)
  }

compileWrapMainTwoPhaseChain :: WrapMainTwoPhaseChainParams -> CompiledCircuit WrapField
compileWrapMainTwoPhaseChain { vestaSrs, lagrangeAt, blindingH } =
  let
    { x: F dummyX, y: F dummyY } = dummyVestaPt

    dummyPt :: AffinePoint _
    dummyPt = { x: const_ dummyX, y: const_ dummyY }
    dummyVK =
      { sigmaComm: Vector.replicate dummyPt :: _ 7 _
      , coefficientsComm: Vector.replicate dummyPt :: _ 15 _
      , genericComm: dummyPt
      , psmComm: dummyPt
      , completeAddComm: dummyPt
      , mulComm: dummyPt
      , emulComm: dummyPt
      , endomulScalarComm: dummyPt
      }

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
      , stepKeys: dummyVK :< dummyVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Just perBranchLookup
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  in
    unsafePerformEffect $
      compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
        (\stmt -> wrapMain @2 @(Slots2 0 1) config stmt)
        Kimchi.initialState
