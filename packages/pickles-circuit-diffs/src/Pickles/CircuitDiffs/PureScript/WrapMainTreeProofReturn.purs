-- | N=2 wrapper for the wrap_main library circuit (Tree_proof_return).
-- |
-- | Configuration: branches=1, step_widths=[2], heterogeneous prev slots
-- | [0, 2] (slot 0 = No_recursion_return proof, slot 1 = Tree_proof_return
-- | self), wrap domain 2^13, Features.none.
-- |
-- | OCaml dump target: `wrap_main_tree_proof_return_circuit.json` produced
-- | by `mina/src/lib/crypto/pickles/dump_circuit_impl.ml` with
-- | `step_widths:[2]`, `padded:[[0];[2]]`, `domain_log2:13`.
module Pickles.CircuitDiffs.PureScript.WrapMainTreeProofReturn
  ( compileWrapMainTreeProofReturn
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.Types (WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Pickles.Wrap.Slots (Slots2)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F(..), const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

compileWrapMainTreeProofReturn :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapMainTreeProofReturn { lagrangeAt, blindingH } =
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

    config :: WrapMainConfig 1
    config =
      -- N=2 Tree_proof_return: single branch, step_widths=[2], wrap
      -- domain 2^13 (from compile.wrap_domains.h.log2 in
      -- dump_tree_proof_return).
      { stepWidths: 2 :< Vector.nil
      , domainLog2s: 13 :< Vector.nil
      , stepKeys: dummyVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  in
    unsafePerformEffect $
      compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
        (\stmt -> wrapMain @1 @(Slots2 0 2) config stmt)
        Kimchi.initialState
