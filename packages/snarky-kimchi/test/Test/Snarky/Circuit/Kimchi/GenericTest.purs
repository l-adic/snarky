module Test.Snarky.Circuit.Kimchi.GenericTest
  ( spec
  ) where

import Prelude

import Control.Monad.Except (throwError)
import Control.Monad.Gen (suchThat)
import Data.Array (concatMap)
import Data.Either (Either(..))
import Data.Maybe (fromJust)
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Effect.Exception (error)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolver)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createCRS, createProverIndex, verifyProverIndex)
import Snarky.Circuit.Curves (add_)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (class KimchiVerify, AuxState(..), KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Constraint.Kimchi.Wire (toKimchiRows)
import Snarky.Curves.Class (class HasEndo, class PrimeField, class WeierstrassCurve, endoScalar)
import Snarky.Data.EllipticCurve (AffinePoint, addAffine, genAffinePoint, toAffine)
import Test.QuickCheck (class Arbitrary)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

spec
  :: forall g g' f f'
   . KimchiConstraint.KimchiVerify f f'
  => Arbitrary g
  => PrimeField f
  => WeierstrassCurve f g
  => KimchiVerify f f'
  => HasEndo f' f
  => CircuitGateConstructor f g'
  => Proxy g
  -> Proxy (KimchiConstraint f)
  -> Spec Unit
spec pg pc =
  describe "Kimchi Generic (EC Add)" do

    it "unsafeAdd Circuit generates valid Generic constraints" $ unsafePartial do
      let
        f :: Tuple (AffinePoint (F f)) (AffinePoint (F f)) -> AffinePoint (F f)
        f (Tuple x y) = unsafePartial $ fromJust $ toAffine $ addAffine x y

        s :: CircuitBuilderState (KimchiGate f) (AuxState f)
        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(AffinePoint (F f)))
            pc
            (uncurry add_)
            Kimchi.initialState

        { constraintSystem, constraints } = makeConstraintSystem @f
          { constraints: concatMap toKimchiRows s.constraints
          , publicInputs: s.publicInputs
          , unionFind: (un AuxState s.aux).wireState.unionFind
          }

        solver :: Solver f (KimchiGate f) (Tuple (AffinePoint (F f)) (AffinePoint (F f))) (AffinePoint (F f))
        solver = makeSolver pc (uncurry add_)

        gen = do
          p1 <- genAffinePoint pg
          p2 <- genAffinePoint pg `suchThat` \p ->
            let
              { x: x1, y: y1 } = p1
              { x: x2, y: y2 } = p
            in
              x1 /= x2 && y1 /= negate y2
          pure $ Tuple p1 p2

      --circuitSpecPure'
      --  { builtState: s
      --  , checker: KimchiConstraint.eval
      --  , solver: solver
      --  , testFunction: satisfied f
      --  , postCondition: Kimchi.postConditio liftEffect n
      --  }
      --  gen

      liftEffect do
        k <- randomSampleOne gen
        crs <- createCRS
        case runSolver solver k of
          Left e -> throwError $ error (show e)
          Right (Tuple _ assignments) -> do
            let
              { witness, publicInputs } = makeWitness
                { assignments
                , constraints
                , publicInputs: s.publicInputs
                }
              endo = endoScalar @f' @f
              proverIndex = createProverIndex
                { endo
                , constraintSystem
                , crs
                }
              result = verifyProverIndex
                { proverIndex
                , witness
                , publicInputs
                }
            result `shouldEqual` true