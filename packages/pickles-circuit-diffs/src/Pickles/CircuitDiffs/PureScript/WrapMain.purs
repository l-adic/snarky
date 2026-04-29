-- | N1 wrapper for the wrap_main library circuit.
-- |
-- | Configuration: branches=1, step_widths=[1], Max_widths_by_slot=[N0; N1],
-- | Features.none. The slot widths come from the [[0]; [1]] padded vector
-- | passed to `Wrap_main.wrap_main` in `dump_circuit_impl.ml` for this fixture.
module Pickles.CircuitDiffs.PureScript.WrapMain
  ( compileWrapMainN1
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

compileWrapMainN1 :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapMainN1 { lagrangeAt, blindingH } =
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
      -- domainLog2 = 14 mirrors production Simple_chain N1 (verified
      -- via OCaml `compile.wrap_domains.h.log2` trace). This is the
      -- step proof's eval domain that the wrap circuit's lagrange
      -- base lookup is parameterized by. The matching OCaml fixture
      -- in dump_circuit_impl.ml was likewise updated to ~domain_log2:14.
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
        (\stmt -> wrapMain @1 @(Slots2 0 1) config stmt)
        Kimchi.initialState
