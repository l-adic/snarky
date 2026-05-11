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
import Pickles.Types (WrapField)
import Pickles.Wrap.FinalizeOtherProof (pow2PowMul, wrapFinalizeOtherProofCircuit)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), F, FVar, SizedF, Snarky, const_, sub_)
import Snarky.Circuit.Kimchi (Type2(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

type FopWrapInput =
  { plonk ::
      { alpha :: SizedF 128 (FVar WrapField)
      , beta :: SizedF 128 (FVar WrapField)
      , gamma :: SizedF 128 (FVar WrapField)
      , zeta :: SizedF 128 (FVar WrapField)
      , zetaToSrsLength :: Type2 (FVar WrapField)
      , zetaToDomainSize :: Type2 (FVar WrapField)
      , perm :: Type2 (FVar WrapField)
      }
  , combinedInnerProduct :: Type2 (FVar WrapField)
  , b :: Type2 (FVar WrapField)
  , xi :: SizedF 128 (FVar WrapField)
  , bulletproofChallenges :: Vector 16 (SizedF 128 (FVar WrapField))
  , spongeDigestBeforeEvaluations :: FVar WrapField
  , allEvals ::
      { ftEval1 :: FVar WrapField
      , publicEvals :: { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      , witnessEvals :: Vector 15 { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      , coeffEvals :: Vector 15 { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      , zEvals :: { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      , sigmaEvals :: Vector 6 { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      , indexEvals :: Vector 6 { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      }
  , prevChallenges :: Vector 2 (Vector 16 (FVar WrapField))
  }

parseFopWrapInput :: Vector 148 (FVar WrapField) -> FopWrapInput
parseFopWrapInput inputs =
  let
    at = unsafeIdx inputs

    evalPair :: forall n. Int -> Finite n -> { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
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
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => FopWrapInput
  -> Snarky (KimchiConstraint WrapField) t m (FinalizeOtherProofOutput 16 WrapField)
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
      , shouldFinalize: coerce (const_ one :: FVar WrapField)
      , spongeDigestBeforeEvaluations: input.spongeDigestBeforeEvaluations
      }
    params =
      { domains:
          { generator: const_ (LinFFI.domainGenerator @WrapField wrapDomainLog2)
          , log2: wrapDomainLog2
          } :< Vector.nil
      , shifts: map const_ (LinFFI.domainShifts @WrapField wrapDomainLog2)
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

compileFopWrap :: CompiledCircuit WrapField
compileFopWrap =
  compilePure (Proxy @(Vector 148 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> void $ fopWrapCircuit (parseFopWrapInput inputs))
    Kimchi.initialState
