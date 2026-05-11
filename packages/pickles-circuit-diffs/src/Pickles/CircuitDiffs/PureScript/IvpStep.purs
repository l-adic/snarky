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
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF10, asSizedF128, dummyPallasPt, dummyWrapSg, stepEndo, unsafeIdx)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Step.Types (Field)
import Pickles.Verify (incrementallyVerifyProof)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, assertEq, assertEqual_, const_)
import Snarky.Circuit.Kimchi (SplitField(..), Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type IvpStepPublicInput =
  Tuple
    (Vector 5 (FVar Field))
    ( Tuple (Vector 2 (SizedF 128 (FVar Field)))
        ( Tuple (Vector 3 (SizedF 128 (FVar Field)))
            ( Tuple (Vector 3 (FVar Field))
                (Tuple (Vector 16 (SizedF 128 (FVar Field))) (SizedF 10 (FVar Field)))
            )
        )
    )

type IvpStepParams =
  { lagrangeAt :: LagrangeBaseLookup Field
  , blindingH :: AffinePoint (F Field)
  }

type IvpStepInput pi =
  { publicInput :: pi
  , deferredValues ::
      { plonk ::
          { alpha :: SizedF 128 (FVar Field)
          , beta :: SizedF 128 (FVar Field)
          , gamma :: SizedF 128 (FVar Field)
          , zeta :: SizedF 128 (FVar Field)
          , perm :: Type2 (SplitField (FVar Field) (BoolVar Field))
          , zetaToSrsLength :: Type2 (SplitField (FVar Field) (BoolVar Field))
          , zetaToDomainSize :: Type2 (SplitField (FVar Field) (BoolVar Field))
          }
      , combinedInnerProduct :: Type2 (SplitField (FVar Field) (BoolVar Field))
      , b :: Type2 (SplitField (FVar Field) (BoolVar Field))
      , xi :: SizedF 128 (FVar Field)
      , bulletproofChallenges :: Vector 15 (SizedF 128 (FVar Field))
      }
  , wComm :: Vector 15 (AffinePoint (FVar Field))
  , zComm :: AffinePoint (FVar Field)
  , tComm :: Vector 7 (AffinePoint (FVar Field))
  , opening ::
      { delta :: AffinePoint (FVar Field)
      , sg :: AffinePoint (FVar Field)
      , lr :: Vector 15 { l :: AffinePoint (FVar Field), r :: AffinePoint (FVar Field) }
      , z1 :: Type2 (SplitField (FVar Field) (BoolVar Field))
      , z2 :: Type2 (SplitField (FVar Field) (BoolVar Field))
      }
  , claimedDigest :: FVar Field
  }

parseIvpStepInput :: Vector 175 (FVar Field) -> IvpStepInput IvpStepPublicInput
parseIvpStepInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    readOtherField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    publicInput =
      Tuple
        ((Vector.generate \j -> at (getFinite j)) :: Vector 5 (FVar Field))
        ( Tuple
            ((Vector.generate \j -> asSizedF128 (at (5 + getFinite j))) :: Vector 2 (SizedF 128 (FVar Field)))
            ( Tuple
                ((Vector.generate \j -> asSizedF128 (at (7 + getFinite j))) :: Vector 3 (SizedF 128 (FVar Field)))
                ( Tuple
                    ((Vector.generate \j -> at (10 + getFinite j)) :: Vector 3 (FVar Field))
                    ( Tuple
                        ((Vector.generate \j -> asSizedF128 (at (13 + getFinite j))) :: Vector 16 (SizedF 128 (FVar Field)))
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
   . CircuitM Field (KimchiConstraint Field) t m
  => PublicInputCommit pi Field
  => IvpStepParams
  -> IvpStepInput pi
  -> Snarky (KimchiConstraint Field) t m Unit
ivpStepCircuit { lagrangeAt, blindingH } input = do
  let
    constDummySg :: AffinePoint (FVar Field)
    constDummySg = { x: const_ dummyWrapSg.x, y: const_ dummyWrapSg.y }

    constDummyPt = let { x: F x', y: F y' } = dummyPallasPt in { x: const_ x', y: const_ y' }

    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeAt
      , blindingH
      , correctionMode: PureCorrections
      , endo: stepEndo
      , groupMapParams: groupMapParams (Proxy @PallasG)
      , useOptSponge: false
      }
    ivpInput =
      { publicInput: input.publicInput
      , sgOld: constDummySg :< constDummySg :< Vector.nil
      , sgOldMask: Vector.replicate ((const_ one))
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
    incrementallyVerifyProof @PallasG StepOtherField.ipaScalarOps ivpParams ivpInput Nothing
  assertEqual_ output.spongeDigestBeforeEvaluations input.claimedDigest
  for_ (Vector.zip input.deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) ->
    assertEq c1 c2

compileIvpStep :: IvpStepParams -> CompiledCircuit Field
compileIvpStep srsData =
  compilePure (Proxy @(Vector 175 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> ivpStepCircuit srsData (parseIvpStepInput inputs))
    Kimchi.initialState
