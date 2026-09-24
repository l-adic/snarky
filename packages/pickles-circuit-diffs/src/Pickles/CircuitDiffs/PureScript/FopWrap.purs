module Pickles.CircuitDiffs.PureScript.FopWrap
  ( FopWrapInput
  , FopWrapInputAt
  , parseFopWrapInput
  , parseFopWrapInputAt
  , fopWrapCircuit
  , compileFopWrap
  ) where

import Prelude

import Data.Fin (Finite, getFinite)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx, wrapDomainLog2, wrapEndo, wrapSrsLengthLog2)
import Pickles.Constants (zkRowsByDefault)
import Pickles.Field (WrapField)
import Pickles.FinalizeOtherProof (DomainMode(..), Output)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.Wrap.FinalizeOtherProof (pow2PowMul, wrapFinalizeOtherProofCircuit)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (Bool(..), F, FVar, SizedF, Snarky, const_, sub_)
import Snarky.Circuit.Kimchi (Type2(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

-- | The 16-round input `finalize_other_proof_wrap_circuit` takes.
type FopWrapInput = FopWrapInputAt 16

-- | One slot's finalize input at `rounds` bullet-proof rounds.
type FopWrapInputAt rounds =
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
  , bulletproofChallenges :: Vector rounds (SizedF 128 (FVar WrapField))
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
  , prevChallenges :: Vector 2 (Vector rounds (FVar WrapField))
  }

parseFopWrapInput :: Vector 148 (FVar WrapField) -> FopWrapInput
parseFopWrapInput inputs = parseFopWrapInputAt @16 (unsafeIdx inputs)

-- | One slot's finalize input read through `at`, in the layout of
-- | `finalize_other_proof_wrap_circuit` at `rounds` rounds: the deferred
-- | values with `rounds` challenges, the evaluations, the two padded
-- | previous-challenge vectors and the sponge digest.
parseFopWrapInputAt
  :: forall @rounds
   . Reflectable rounds Int
  => (Int -> FVar WrapField)
  -> FopWrapInputAt rounds
parseFopWrapInputAt at =
  let
    r = reflectType (Proxy @rounds)
    -- the evaluations follow the challenges; the previous challenges and
    -- the digest follow the evaluations
    ev = 10 + r
    prev = ev + 89

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
    , spongeDigestBeforeEvaluations: at (prev + 2 * r)
    , allEvals:
        { ftEval1: at (ev + 88)
        , publicEvals: { zeta: at ev, omegaTimesZeta: at (ev + 1) }
        , witnessEvals: Vector.generate (evalPair (ev + 2))
        , coeffEvals: Vector.generate (evalPair (ev + 32))
        , zEvals: { zeta: at (ev + 62), omegaTimesZeta: at (ev + 63) }
        , sigmaEvals: Vector.generate (evalPair (ev + 64))
        , indexEvals: Vector.generate (evalPair (ev + 76))
        }
    , prevChallenges: Vector.generate \j ->
        Vector.generate \k -> at (prev + r * getFinite j + getFinite k)
    }

fopWrapCircuit
  :: forall r
   . PrimeField WrapField
  => FopWrapInput
  -> Snarky WrapField (KimchiConstraint WrapField) r (Output 16 WrapField)
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
      , zkRows: zkRowsByDefault
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
      , allEvals: input.allEvals
      , prevChallenges: input.prevChallenges
      }

compileFopWrap :: Effect (CompiledCircuit WrapField)
compileFopWrap =
  compile noAdvice (Proxy @(Vector 148 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> void $ fopWrapCircuit (parseFopWrapInput inputs))
