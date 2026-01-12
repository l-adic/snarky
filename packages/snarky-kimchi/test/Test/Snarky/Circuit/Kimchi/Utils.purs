module Test.Snarky.Circuit.Kimchi.Utils where

import Prelude

import Control.Monad.Error.Class (throwError)
import Data.Array (concatMap)
import Data.Either (Either(..))
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (error)
import Prim.Int (class Add)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, runSolver)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createCRS, createProverIndex, verifyProverIndex)
import Snarky.Circuit.DSL.Bits (packPure)
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, endoBase)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, randomSampleOne)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

gen128BitElem :: forall f n _l. FieldSizeInBits f n => Reflectable _l Int => Add 128 _l n => Gen (F f)
gen128BitElem = do
  v <- Vector.generator (Proxy @128) arbitrary
  let v' = v `Vector.append` (Vector.generate $ const false)
  pure $ F $ packPure v'

verifyCircuit
  :: forall f f' g' a b
   . HasEndo f f'
  => CircuitGateConstructor f g'
  => { gen :: Gen a
     , solver :: Solver f (KimchiGate f) a b
     , s :: CircuitBuilderState (KimchiGate f) (AuxState f)
     }
  -> Effect Unit
verifyCircuit { gen, solver, s } = do
  k <- randomSampleOne gen
  crs <- createCRS
  case runSolver solver k of
    Left e -> throwError $ error (show e)
    Right (Tuple _ assignments) -> do
      let
        { constraintSystem, constraints } = makeConstraintSystem @f
          { constraints: concatMap toKimchiRows s.constraints
          , publicInputs: s.publicInputs
          , unionFind: (un AuxState s.aux).wireState.unionFind
          }
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables constraints
          , publicInputs: s.publicInputs
          }
        endo = endoBase
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