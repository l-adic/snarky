-- | The wrap circuit's `x_hat` at two branches, through
-- | `maskedLagrangeAt`, matching `xhat_wrap_branches_{same,diff}_circuit`.
-- | With one shared step domain the conditional-add bases are masked
-- | constants; with per-branch domains the bases and corrections are
-- | masked per branch.
module Pickles.CircuitDiffs.PureScript.XhatBranches
  ( XhatBranchesParams
  , compileXhatBranches
  ) where

import Prelude

import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.CircuitDiffs.PureScript.Xhat (xhatCircuit)
import Pickles.Field (WrapField)
import Pickles.PackedStatement (PackedStepPublicInput)
import Pickles.Pseudo as Pseudo
import Pickles.Wrap.Main (maskedLagrangeAt)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, UnChecked(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
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

-- | `xhat_wrap_branches_{same,diff}_circuit`'s input: the branch index, then
-- | `xhat_wrap_circuit`'s packed statement.
newtype XhatBranchesInput f stmt = XhatBranchesInput
  { branchIndex :: f
  , statement :: stmt
  }

-- | The wire order.
type XhatBranchesTuple f stmt = Tuple2 f stmt

toTuple :: forall f stmt. XhatBranchesInput f stmt -> XhatBranchesTuple f stmt
toTuple (XhatBranchesInput i) = tuple2 i.branchIndex i.statement

fromTuple :: forall f stmt. XhatBranchesTuple f stmt -> XhatBranchesInput f stmt
fromTuple = uncurry2 \branchIndex statement -> XhatBranchesInput { branchIndex, statement }

instance
  ( CircuitType f fa fv
  , CircuitType f sa sv
  ) =>
  CircuitType f (XhatBranchesInput fa sa) (XhatBranchesInput fv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(XhatBranchesTuple fa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(XhatBranchesTuple fa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(XhatBranchesTuple fa sa)

compileXhatBranches :: XhatBranchesParams -> Effect (CompiledCircuit WrapField)
compileXhatBranches params =
  compile noAdvice
    (Proxy @(UnChecked (XhatBranchesInput (F WrapField) (PackedStepPublicInput 1 15 (F WrapField) Boolean))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    \(UnChecked (XhatBranchesInput i)) -> do
      whichBranch <- Pseudo.oneHotVector @2 i.branchIndex
      void $ xhatCircuit @1
        { lagrangeAt: maskedLagrangeAt whichBranch params.domainLog2s params.lagrangeTable
        , blindingH: params.blindingH
        }
        i.statement
