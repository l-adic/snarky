-- | N=0 wrapper for the wrap_main library circuit (Add_one_return).
-- |
-- | Configuration: branches=1, step_widths=[0], Max_widths_by_slot=[N0; N0],
-- | Features.none. The slot widths come from the [[0]; [0]] padded vector
-- | passed to `Wrap_main.wrap_main` in `dump_circuit_impl.ml` for this fixture.
-- |
-- | **N = 0**: no previous proofs in the step proof being wrapped. This is
-- | the only N=0 wrap fixture in the suite — the step proof's own public
-- | input has no unfinalized_proofs slots and no messages_for_next_wrap_proof
-- | entries, so the wrap circuit's verify-one-of-step is a minimal
-- | configuration compared to Simple_chain (step_widths=[1]) and
-- | Simple_chain_n2 (step_widths=[0;2]).
-- |
-- | OCaml dump target: `wrap_main_add_one_return_circuit.json` produced by
-- | `mina/src/lib/crypto/pickles/dump_circuit_impl.ml` with
-- | `step_widths:[0]`, `padded:[[0];[0]]`, `domain_log2:13`.
module Pickles.CircuitDiffs.PureScript.WrapMainAddOneReturn
  ( compileWrapMainAddOneReturn
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
import Pickles.Wrap.Slots (Slots2)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F(..), const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

compileWrapMainAddOneReturn :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapMainAddOneReturn { lagrangeAt, blindingH } =
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
      -- N=0 Add_one_return: single branch, step_widths=[0], wrap domain
      -- 2^13 (from compile.wrap_domains.h.log2 in dump_add_one_return).
      { stepWidths: 0 :< Vector.nil
      , domainLog2s: 13 :< Vector.nil
      , stepKeys: dummyVK :< Vector.nil
      , lagrangeAt
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  in
    unsafePerformEffect $
      compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
        (\stmt -> wrapMain @1 @(Slots2 0 0) config stmt)
        Kimchi.initialState
