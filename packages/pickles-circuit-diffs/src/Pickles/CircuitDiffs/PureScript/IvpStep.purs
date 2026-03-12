module Pickles.CircuitDiffs.PureScript.IvpStep
  ( IvpStepInput
  , IvpStepParams
  , parseIvpStepInput
  , ivpStepCircuit
  , compileIvpStep
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF10, asSizedF128, compiledCircuit, dummyPallasPt, dummyWrapSg, stepEndo, unsafeIdx)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode(..))
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (StepField)
import Pickles.Verify (incrementallyVerifyProof)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F, FVar, SizedF, Snarky, assertEq, assertEqual_, const_)
import Snarky.Circuit.Kimchi (SplitField(..), Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type IvpStepPublicInput =
  Tuple
    (Vector 5 (FVar StepField))
    ( Tuple (Vector 2 (SizedF 128 (FVar StepField)))
        ( Tuple (Vector 3 (SizedF 128 (FVar StepField)))
            ( Tuple (Vector 3 (FVar StepField))
                (Tuple (Vector 16 (SizedF 128 (FVar StepField))) (SizedF 10 (FVar StepField)))
            )
        )
    )

type IvpStepParams =
  { lagrangeComms :: Array (AffinePoint (F StepField))
  , blindingH :: AffinePoint (F StepField)
  }

type IvpStepInput pi =
  { publicInput :: pi
  , deferredValues ::
      { plonk ::
          { alpha :: SizedF 128 (FVar StepField)
          , beta :: SizedF 128 (FVar StepField)
          , gamma :: SizedF 128 (FVar StepField)
          , zeta :: SizedF 128 (FVar StepField)
          , perm :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
          , zetaToSrsLength :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
          , zetaToDomainSize :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
          }
      , combinedInnerProduct :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
      , b :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
      , xi :: SizedF 128 (FVar StepField)
      , bulletproofChallenges :: Vector 15 (SizedF 128 (FVar StepField))
      }
  , wComm :: Vector 15 (AffinePoint (FVar StepField))
  , zComm :: AffinePoint (FVar StepField)
  , tComm :: Vector 7 (AffinePoint (FVar StepField))
  , opening ::
      { delta :: AffinePoint (FVar StepField)
      , sg :: AffinePoint (FVar StepField)
      , lr :: Vector 15 { l :: AffinePoint (FVar StepField), r :: AffinePoint (FVar StepField) }
      , z1 :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
      , z2 :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
      }
  , claimedDigest :: FVar StepField
  }

parseIvpStepInput :: Vector 175 (FVar StepField) -> IvpStepInput IvpStepPublicInput
parseIvpStepInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    readOtherField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    publicInput =
      Tuple
        ((Vector.generate \j -> at (getFinite j)) :: Vector 5 (FVar StepField))
        ( Tuple
            ((Vector.generate \j -> asSizedF128 (at (5 + getFinite j))) :: Vector 2 (SizedF 128 (FVar StepField)))
            ( Tuple
                ((Vector.generate \j -> asSizedF128 (at (7 + getFinite j))) :: Vector 3 (SizedF 128 (FVar StepField)))
                ( Tuple
                    ((Vector.generate \j -> at (10 + getFinite j)) :: Vector 3 (FVar StepField))
                    ( Tuple
                        ((Vector.generate \j -> asSizedF128 (at (13 + getFinite j))) :: Vector 16 (SizedF 128 (FVar StepField)))
                        (asSizedF10 (at 29))
                    )
                )
            )
        )
  in
    { publicInput
    , deferredValues:
        { plonk:
            { alpha: asSizedF128 (at 30)
            , beta: asSizedF128 (at 31)
            , gamma: asSizedF128 (at 32)
            , zeta: asSizedF128 (at 33)
            , perm: readOtherField 34
            , zetaToSrsLength: readOtherField 36
            , zetaToDomainSize: readOtherField 38
            }
        , combinedInnerProduct: readOtherField 40
        , b: readOtherField 42
        , xi: asSizedF128 (at 44)
        , bulletproofChallenges: Vector.generate \j -> asSizedF128 (at (45 + getFinite j))
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
        , z1: readOtherField 170
        , z2: readOtherField 172
        }
    , claimedDigest: at 174
    }

ivpStepCircuit
  :: forall pi t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => PublicInputCommit pi StepField
  => IvpStepParams
  -> IvpStepInput pi
  -> Snarky (KimchiConstraint StepField) t m Unit
ivpStepCircuit { lagrangeComms, blindingH } input = do
  let
    constDummySg :: AffinePoint (FVar StepField)
    constDummySg = { x: const_ dummyWrapSg.x, y: const_ dummyWrapSg.y }

    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeComms
      , blindingH
      , correctionMode: PureCorrections
      , sigmaCommLast: dummyPallasPt
      , columnComms:
          { index: (Vector.replicate dummyPallasPt) :: Vector 6 _
          , coeff: (Vector.replicate dummyPallasPt) :: Vector 15 _
          , sigma: (Vector.replicate dummyPallasPt) :: Vector 6 _
          }
      , indexDigest: zero
      , endo: stepEndo
      , groupMapParams: groupMapParams (Proxy @PallasG)
      , useOptSponge: false
      }
    ivpInput =
      { publicInput: input.publicInput
      , sgOld: constDummySg :< constDummySg :< Vector.nil
      , deferredValues: input.deferredValues
      , wComm: input.wComm
      , zComm: input.zComm
      , tComm: input.tComm
      , opening: input.opening
      }
  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @PallasG StepOtherField.ipaScalarOps ivpParams ivpInput
  assertEqual_ output.spongeDigestBeforeEvaluations input.claimedDigest
  for_ (Vector.zip input.deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) ->
    assertEq c1 c2

compileIvpStep :: IvpStepParams -> CompiledCircuit StepField
compileIvpStep srsData = compiledCircuit @StepField $
  compilePure (Proxy @(Vector 175 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> ivpStepCircuit srsData (parseIvpStepInput inputs))
    Kimchi.initialState
