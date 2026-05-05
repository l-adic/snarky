-- | N=1 wrap_main library circuit for the side-loaded main parent
-- | (`Simple_chain` from `dump_side_loaded_main.ml`).
-- |
-- | Configuration: branches=1, step_widths=[1], slot shape `Slots2 0 2`
-- | (slot 0 unused, slot 1 holds the side-loaded prev with bound 2),
-- | wrap_domain=2^14, Features.none. Mirrors OCaml dumper params at
-- | `dump_circuit_impl.ml`'s `wrap_main_side_loaded_main_circuit`
-- | entry: `padded:[[0]; [2]]`, `step_widths:[1]`, `domain_log2:14`.
-- |
-- | Distinct from `compileWrapMainN1` (which is for Simple_chain N1
-- | with `Slots2 0 1`) — the slot's bound differs, exercising
-- | wrap_main's Pseudo dispatch over `Vector 0 / Vector 2` instead of
-- | `Vector 0 / Vector 1`.
module Pickles.CircuitDiffs.PureScript.WrapMainSideLoadedMain
  ( compileWrapMainSideLoadedMain
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
import Pickles.Wrap.Slots (Slots1)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F(..), const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

compileWrapMainSideLoadedMain :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapMainSideLoadedMain { lagrangeAt, blindingH } =
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
      { stepWidths: 1 :< Vector.nil
      , domainLog2s: 14 :< Vector.nil
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
        (\stmt -> wrapMain @1 @(Slots1 2) config stmt)
        Kimchi.initialState
