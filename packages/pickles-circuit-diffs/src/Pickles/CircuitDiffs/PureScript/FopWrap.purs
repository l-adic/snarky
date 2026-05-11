module Pickles.CircuitDiffs.PureScript.FopWrap
  ( FopWrapInput
  , parseFopWrapInput
  , fopWrapCircuit
  , compileFopWrap
  ) where

import Prelude

import Data.Fin (Finite, getFinite)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx, wrapDomainLog2, wrapEndo, wrapSrsLengthLog2)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.Step.FinalizeOtherProof (DomainMode(..), FinalizeOtherProofOutput)
import Pickles.Wrap.FinalizeOtherProof (pow2PowMul, wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.Types (Field)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), F, FVar, SizedF, Snarky, const_, sub_)
import Snarky.Circuit.Kimchi (Type2(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

type FopWrapInput =
  { plonk ::
      { alpha :: SizedF 128 (FVar Field)
      , beta :: SizedF 128 (FVar Field)
      , gamma :: SizedF 128 (FVar Field)
      , zeta :: SizedF 128 (FVar Field)
      , zetaToSrsLength :: Type2 (FVar Field)
      , zetaToDomainSize :: Type2 (FVar Field)
      , perm :: Type2 (FVar Field)
      }
  , combinedInnerProduct :: Type2 (FVar Field)
  , b :: Type2 (FVar Field)
  , xi :: SizedF 128 (FVar Field)
  , bulletproofChallenges :: Vector 16 (SizedF 128 (FVar Field))
  , spongeDigestBeforeEvaluations :: FVar Field
  , allEvals ::
      { ftEval1 :: FVar Field
      , publicEvals :: { zeta :: FVar Field, omegaTimesZeta :: FVar Field }
      , witnessEvals :: Vector 15 { zeta :: FVar Field, omegaTimesZeta :: FVar Field }
      , coeffEvals :: Vector 15 { zeta :: FVar Field, omegaTimesZeta :: FVar Field }
      , zEvals :: { zeta :: FVar Field, omegaTimesZeta :: FVar Field }
      , sigmaEvals :: Vector 6 { zeta :: FVar Field, omegaTimesZeta :: FVar Field }
      , indexEvals :: Vector 6 { zeta :: FVar Field, omegaTimesZeta :: FVar Field }
      }
  , prevChallenges :: Vector 2 (Vector 16 (FVar Field))
  }

parseFopWrapInput :: Vector 148 (FVar Field) -> FopWrapInput
parseFopWrapInput inputs =
  let
    at = unsafeIdx inputs

    evalPair :: forall n. Int -> Finite n -> { zeta :: FVar Field, omegaTimesZeta :: FVar Field }
    evalPair base j =
      { zeta: at (base + 2 * getFinite j)
      , omegaTimesZeta: at (base + 2 * getFinite j + 1)
      }
  in
    { plonk:
        { alpha: asSizedF128 (at 0)
        , beta: asSizedF128 (at 1)
        , gamma: asSizedF128 (at 2)
        , zeta: asSizedF128 (at 3)
        , zetaToSrsLength: Type2 (at 4)
        , zetaToDomainSize: Type2 (at 5)
        , perm: Type2 (at 6)
        }
    , combinedInnerProduct: Type2 (at 7)
    , b: Type2 (at 8)
    , xi: asSizedF128 (at 9)
    , bulletproofChallenges: Vector.generate \j -> asSizedF128 (at (10 + getFinite j))
    , spongeDigestBeforeEvaluations: at 147
    , allEvals:
        { ftEval1: at 114
        , publicEvals: { zeta: at 26, omegaTimesZeta: at 27 }
        , witnessEvals: Vector.generate (evalPair 28)
        , coeffEvals: Vector.generate (evalPair 58)
        , zEvals: { zeta: at 88, omegaTimesZeta: at 89 }
        , sigmaEvals: Vector.generate (evalPair 90)
        , indexEvals: Vector.generate (evalPair 102)
        }
    , prevChallenges: Vector.generate \j ->
        Vector.generate \k -> at (115 + 16 * getFinite j + getFinite k)
    }

fopWrapCircuit
  :: forall t m
   . CircuitM Field (KimchiConstraint Field) t m
  => FopWrapInput
  -> Snarky (KimchiConstraint Field) t m (FinalizeOtherProofOutput 16 Field)
fopWrapCircuit input =
  let
    unfinalized =
      { deferredValues:
          { plonk: input.plonk
          , combinedInnerProduct: input.combinedInnerProduct
          , b: input.b
          , xi: input.xi
          , bulletproofChallenges: input.bulletproofChallenges
          }
      , shouldFinalize: coerce (const_ one :: FVar Field)
      , spongeDigestBeforeEvaluations: input.spongeDigestBeforeEvaluations
      }
    params =
      { domains:
          { generator: const_ (LinFFI.domainGenerator @Field wrapDomainLog2)
          , log2: wrapDomainLog2
          } :< Vector.nil
      , shifts: map const_ (LinFFI.domainShifts @Field wrapDomainLog2)
      , srsLengthLog2: wrapSrsLengthLog2
      , endo: wrapEndo
      , linearizationPoly: Linearization.vesta
      , domainMode: KnownDomainsMode
      }
    vanishingPoly z = do
      zetaToN <- pow2PowMul z wrapDomainLog2
      pure (zetaToN `sub_` const_ one)
  in
    wrapFinalizeOtherProofCircuit params vanishingPoly
      { unfinalized
      , witness: { allEvals: input.allEvals }
      , prevChallenges: input.prevChallenges
      }

compileFopWrap :: CompiledCircuit Field
compileFopWrap =
  compilePure (Proxy @(Vector 148 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ fopWrapCircuit (parseFopWrapInput inputs))
    Kimchi.initialState
