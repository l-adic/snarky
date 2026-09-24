-- | `wrapFinalizePrevProofs`, the wrap circuit's finalize block, at two
-- | branches and two slots, matching `wrap_finalize_n2_circuit`. Branch
-- | 0's slots are pinned to wrap domains `[N1, N1]`, branch 1's to
-- | `[N0, N2]`.
-- |
-- | The 295 inputs are the branch index, then per slot the inputs of
-- | `finalize_other_proof_wrap_circuit` at the wrap circuit's 15 rounds
-- | (145), `shouldFinalize` and the wrap domain index.
module Pickles.CircuitDiffs.PureScript.WrapFinalize
  ( compileWrapFinalizeN2
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.CircuitDiffs.PureScript.FopWrap (parseFopWrapInputAt)
import Pickles.Field (WrapField)
import Pickles.ProofsVerified (ProofsVerified(..))
import Pickles.Pseudo as Pseudo
import Pickles.Types (WrapIPARounds)
import Pickles.Wrap.Main (wrapFinalizePrevProofs)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (Bool(..), F, FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

wrapFinalizeN2Circuit
  :: forall r
   . Vector 295 (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
wrapFinalizeN2Circuit inputs = do
  let
    { head: branchIndex, tail } = Vector.uncons inputs
    slots = map slot (Vector.chunks @147 tail)
    slot v =
      let
        { before, after } = Vector.splitAt @145 v
        fop = parseFopWrapInputAt @WrapIPARounds (unsafeIdx before)
        { head: shouldFinalize, tail: rest } = Vector.uncons after
      in
        { unfinalized:
            { deferredValues:
                { plonk: fop.plonk
                , combinedInnerProduct: fop.combinedInnerProduct
                , b: fop.b
                , xi: fop.xi
                , bulletproofChallenges: fop.bulletproofChallenges
                }
            , shouldFinalize: coerce shouldFinalize
            , spongeDigestBeforeEvaluations: fop.spongeDigestBeforeEvaluations
            }
        , evals: fop.allEvals
        , prevChallenges: fop.prevChallenges
        , domainIndex: Vector.head rest
        }
    pins =
      (Just N1 :< Just N1 :< Vector.nil)
        :< (Just N0 :< Just N2 :< Vector.nil)
        :< Vector.nil
  whichBranch <- Pseudo.oneHotVector @2 branchIndex
  _ <- wrapFinalizePrevProofs whichBranch pins
    (map _.domainIndex slots)
    (map _.unfinalized slots)
    (map _.evals slots)
    (map _.prevChallenges slots)
  pure unit

compileWrapFinalizeN2 :: Effect (CompiledCircuit WrapField)
compileWrapFinalizeN2 =
  compile noAdvice (Proxy @(Vector 295 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    wrapFinalizeN2Circuit
