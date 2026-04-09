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
import Data.Vector ((:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.Types (WrapField)
import Pickles.Wrap.Main (WrapMainConfig, compileWrapMain)
import Snarky.Circuit.DSL (F(..), const_)
import Snarky.Data.EllipticCurve (AffinePoint)

compileWrapMainN1 :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapMainN1 { lagrangeComms, blindingH } =
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
      , domainLog2s: 16 :< Vector.nil
      , stepKeys: dummyVK :< Vector.nil
      , lagrangeComms
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  in
    compileWrapMain @1 @0 @1 config
