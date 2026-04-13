-- | N2 wrapper for the wrap_main library circuit.
-- |
-- | Configuration: branches=2, step_widths=[0;2], Max_widths_by_slot=[N2;N2],
-- | Features.none. The slot widths come from the [[0;2]; [0;2]] padded vector
-- | passed to `Wrap_main.wrap_main` in `dump_circuit_impl.ml` for this fixture.
module Pickles.CircuitDiffs.PureScript.WrapMainN2
  ( compileWrapMainN2
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.Types (WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F(..), const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

compileWrapMainN2 :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapMainN2 { lagrangeAt, blindingH } =
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

    config :: WrapMainConfig 2
    config =
      { stepWidths: 0 :< 2 :< Vector.nil
      , domainLog2s: 16 :< 16 :< Vector.nil
      , stepKeys: dummyVK :< dummyVK :< Vector.nil
      , lagrangeAt
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  in
    unsafePerformEffect $
      compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
        (\stmt -> wrapMain @2 @2 @2 config stmt)
        Kimchi.initialState
