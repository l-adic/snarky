-- | The wrap circuit's `x_hat` at two branches, through
-- | `maskedLagrangeAt`, matching `xhat_wrap_branches_{same,diff}_circuit`.
-- | The 35 inputs are the branch index, then the 34 inputs of
-- | `xhat_wrap_circuit`. With one shared step domain the
-- | conditional-add bases are masked constants; with per-branch domains
-- | the bases and corrections are masked per branch.
module Pickles.CircuitDiffs.PureScript.XhatBranches
  ( XhatBranchesParams
  , compileXhatBranches
  ) where

import Prelude

import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.CircuitDiffs.PureScript.Xhat (parseXhatInput, xhatCircuit)
import Pickles.Field (WrapField)
import Pickles.Pseudo as Pseudo
import Pickles.Wrap.Main (maskedLagrangeAt)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | The branches' step domain log2s, each branch's Lagrange bases at its
-- | own domain, and the blinding `h`.
type XhatBranchesParams =
  { domainLog2s :: Vector 2 Int
  , lagrangeTable :: Int -> Vector 2 (Vector 1 (AffinePoint (F WrapField)))
  , blindingH :: AffinePoint (F WrapField)
  }

compileXhatBranches :: XhatBranchesParams -> Effect (CompiledCircuit WrapField)
compileXhatBranches params =
  compile noAdvice (Proxy @(Vector 35 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    \inputs -> do
      let { head: branchIndex, tail } = Vector.uncons inputs
      whichBranch <- Pseudo.oneHotVector @2 branchIndex
      void $ xhatCircuit @1
        { lagrangeAt: maskedLagrangeAt whichBranch params.domainLog2s params.lagrangeTable
        , blindingH: params.blindingH
        }
        (parseXhatInput tail)
