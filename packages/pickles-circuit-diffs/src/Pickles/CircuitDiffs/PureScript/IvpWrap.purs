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
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (tuple3, tuple6)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, dummyVestaPt, unsafeIdx, wrapEndo)
import Pickles.PackedStatement (PackedStepPublicInput, fromPackedTuple)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Verify (incrementallyVerifyProof)
import Pickles.Wrap.OtherField as WrapOtherField
import Pickles.Wrap.Types (Field)
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
  { lagrangeAt :: LagrangeBaseLookup Field
  , blindingH :: AffinePoint (F Field)
  }

type IvpWrapInput pi =
  { publicInput :: pi
  , deferredValues ::
      { plonk ::
          { alpha :: SizedF 128 (FVar Field)
          , beta :: SizedF 128 (FVar Field)
          , gamma :: SizedF 128 (FVar Field)
          , zeta :: SizedF 128 (FVar Field)
          , perm :: Type1 (FVar Field)
          , zetaToSrsLength :: Type1 (FVar Field)
          , zetaToDomainSize :: Type1 (FVar Field)
          }
      , combinedInnerProduct :: Type1 (FVar Field)
      , b :: Type1 (FVar Field)
      , xi :: SizedF 128 (FVar Field)
      , bulletproofChallenges :: Vector 16 (SizedF 128 (FVar Field))
      }
  , wComm :: Vector 15 (AffinePoint (FVar Field))
  , zComm :: AffinePoint (FVar Field)
  , tComm :: Vector 7 (AffinePoint (FVar Field))
  , opening ::
      { delta :: AffinePoint (FVar Field)
      , sg :: AffinePoint (FVar Field)
      , lr :: Vector 16 { l :: AffinePoint (FVar Field), r :: AffinePoint (FVar Field) }
      , z1 :: Type1 (FVar Field)
      , z2 :: Type1 (FVar Field)
      }
  , claimedDigest :: FVar Field
  }

parseIvpWrapInput :: Vector 177 (FVar Field) -> IvpWrapInput (PackedStepPublicInput 1 15 (FVar Field) (BoolVar Field))
parseIvpWrapInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    splitField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    perProofTuple =
      tuple6
        ( splitField 0 :< splitField 2 :< splitField 4
            :< splitField 6
            :< splitField 8
            :< Vector.nil
        )
        (at 10)
        (asSizedF128 (at 11) :< asSizedF128 (at 12) :< Vector.nil)
        ( asSizedF128 (at 13) :< asSizedF128 (at 14)
            :< asSizedF128 (at 15)
            :< Vector.nil
        )
        ( (Vector.generate \j -> asSizedF128 (at (16 + getFinite j)))
            :: Vector 15 (SizedF 128 (FVar Field))
        )
        (coerce (at 31) :: BoolVar Field)
    stmtTuple =
      tuple3
        (perProofTuple :< Vector.nil)
        (at 32)
        (at 33 :< Vector.nil)
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
   . CircuitM Field (KimchiConstraint Field) t m
  => PublicInputCommit pi Field
  => IvpWrapParams
  -> IvpWrapInput pi
  -> Snarky (KimchiConstraint Field) t m Unit
ivpWrapCircuit { lagrangeAt, blindingH } input = do
  let
    constDummyPt = let { x: F x', y: F y' } = dummyVestaPt in { x: const_ x', y: const_ y' }

    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeAt
      , blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }
    ivpInput =
      { publicInput: input.publicInput
      , sgOld: Vector.nil
      , sgOldMask: Vector.nil
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
    incrementallyVerifyProof @VestaG WrapOtherField.ipaScalarOps ivpParams ivpInput Nothing
  assertEqual_ output.spongeDigestBeforeEvaluations input.claimedDigest
  for_ (Vector.zip input.deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) ->
    assertEq c1 c2

compileIvpWrap :: IvpWrapParams -> CompiledCircuit Field
compileIvpWrap srsData =
  compilePure (Proxy @(Vector 177 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> ivpWrapCircuit srsData (parseIvpWrapInput inputs))
    Kimchi.initialState
