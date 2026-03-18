module Pickles.CircuitDiffs.PureScript.IvpWrap
  ( IvpWrapInput
  , IvpWrapParams
  , parseIvpWrapInput
  , ivpWrapCircuit
  , compileIvpWrap
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, dummyVestaPt, unsafeIdx, wrapEndo)
import Pickles.PackedStatement (PackedStepPublicInput, fromPackedTuple)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode(..))
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Types (WrapField)
import Pickles.Verify (incrementallyVerifyProof)
import Pickles.Wrap.OtherField as WrapOtherField
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, assertEq, assertEqual_, const_)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type IvpWrapParams =
  { lagrangeComms :: Array (AffinePoint (F WrapField))
  , blindingH :: AffinePoint (F WrapField)
  }

type IvpWrapInput pi =
  { publicInput :: pi
  , deferredValues ::
      { plonk ::
          { alpha :: SizedF 128 (FVar WrapField)
          , beta :: SizedF 128 (FVar WrapField)
          , gamma :: SizedF 128 (FVar WrapField)
          , zeta :: SizedF 128 (FVar WrapField)
          , perm :: Type1 (FVar WrapField)
          , zetaToSrsLength :: Type1 (FVar WrapField)
          , zetaToDomainSize :: Type1 (FVar WrapField)
          }
      , combinedInnerProduct :: Type1 (FVar WrapField)
      , b :: Type1 (FVar WrapField)
      , xi :: SizedF 128 (FVar WrapField)
      , bulletproofChallenges :: Vector 16 (SizedF 128 (FVar WrapField))
      }
  , wComm :: Vector 15 (AffinePoint (FVar WrapField))
  , zComm :: AffinePoint (FVar WrapField)
  , tComm :: Vector 7 (AffinePoint (FVar WrapField))
  , opening ::
      { delta :: AffinePoint (FVar WrapField)
      , sg :: AffinePoint (FVar WrapField)
      , lr :: Vector 16 { l :: AffinePoint (FVar WrapField), r :: AffinePoint (FVar WrapField) }
      , z1 :: Type1 (FVar WrapField)
      , z2 :: Type1 (FVar WrapField)
      }
  , claimedDigest :: FVar WrapField
  }

parseIvpWrapInput :: Vector 177 (FVar WrapField) -> IvpWrapInput (PackedStepPublicInput 1 15 (FVar WrapField) (BoolVar WrapField))
parseIvpWrapInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    splitField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    perProofTuple =
      Tuple
        ( splitField 0 :< splitField 2 :< splitField 4
            :< splitField 6
            :< splitField 8
            :< Vector.nil
        )
        ( Tuple (at 10)
            ( Tuple (asSizedF128 (at 11) :< asSizedF128 (at 12) :< Vector.nil)
                ( Tuple
                    ( asSizedF128 (at 13) :< asSizedF128 (at 14)
                        :< asSizedF128 (at 15)
                        :< Vector.nil
                    )
                    ( Tuple
                        ( (Vector.generate \j -> asSizedF128 (at (16 + getFinite j)))
                            :: Vector 15 (SizedF 128 (FVar WrapField))
                        )
                        (coerce (at 31) :: BoolVar WrapField)
                    )
                )
            )
        )
    stmtTuple =
      Tuple
        (perProofTuple :< Vector.nil)
        (Tuple (at 32) (at 33 :< Vector.nil))
  in
    { publicInput: fromPackedTuple stmtTuple
    , deferredValues:
        { plonk:
            { alpha: asSizedF128 (at 34)
            , beta: asSizedF128 (at 35)
            , gamma: asSizedF128 (at 36)
            , zeta: asSizedF128 (at 37)
            , perm: Type1 (at 38)
            , zetaToSrsLength: Type1 (at 39)
            , zetaToDomainSize: Type1 (at 40)
            }
        , combinedInnerProduct: Type1 (at 41)
        , b: Type1 (at 42)
        , xi: asSizedF128 (at 43)
        , bulletproofChallenges: Vector.generate \j -> asSizedF128 (at (44 + getFinite j))
        }
    , wComm: Vector.generate \j -> readPt (60 + 2 * getFinite j)
    , zComm: readPt 90
    , tComm: Vector.generate \j -> readPt (92 + 2 * getFinite j)
    , opening:
        { delta: readPt 106
        , sg: readPt 108
        , lr: Vector.generate \j ->
            { l: readPt (110 + 4 * getFinite j)
            , r: readPt (110 + 4 * getFinite j + 2)
            }
        , z1: Type1 (at 174)
        , z2: Type1 (at 175)
        }
    , claimedDigest: at 176
    }

ivpWrapCircuit
  :: forall pi t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => PublicInputCommit pi WrapField
  => IvpWrapParams
  -> IvpWrapInput pi
  -> Snarky (KimchiConstraint WrapField) t m Unit
ivpWrapCircuit { lagrangeComms, blindingH } input = do
  let
    constDummyPt = let { x: F x', y: F y' } = dummyVestaPt in { x: const_ x', y: const_ y' }

    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeComms
      , blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }
    ivpInput =
      { publicInput: input.publicInput
      , sgOld: Vector.nil
      -- VK data as circuit variables (dummy constants for circuit-diff test)
      , sigmaCommLast: constDummyPt
      , columnComms:
          { index: (Vector.replicate constDummyPt) :: Vector 6 _
          , coeff: (Vector.replicate constDummyPt) :: Vector 15 _
          , sigma: (Vector.replicate constDummyPt) :: Vector 6 _
          }
      , deferredValues: input.deferredValues
      , wComm: input.wComm
      , zComm: input.zComm
      , tComm: input.tComm
      , opening: input.opening
      }
  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @VestaG WrapOtherField.ipaScalarOps ivpParams ivpInput
  assertEqual_ output.spongeDigestBeforeEvaluations input.claimedDigest
  for_ (Vector.zip input.deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) ->
    assertEq c1 c2

compileIvpWrap :: IvpWrapParams -> CompiledCircuit WrapField
compileIvpWrap srsData =
  compilePure (Proxy @(Vector 177 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> ivpWrapCircuit srsData (parseIvpWrapInput inputs))
    Kimchi.initialState
