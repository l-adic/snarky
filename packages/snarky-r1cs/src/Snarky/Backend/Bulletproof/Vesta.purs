module Snarky.Backend.Bulletproof.Vesta
  ( module Snarky.Backend.Bulletproof.Types
  , crsCreate
  , crsSize
  , witnessCreate
  , witnessSize
  , statementCreate
  , circuitCreate
  , circuitN
  , circuitQ
  , circuitIsSatisfiedBy
  , prove
  , verify
  ) where

import Data.Function.Uncurried (Fn2, Fn4, Fn5, Fn6, runFn2, runFn4, runFn5, runFn6)
import Foreign (Foreign)
import Simple.JSON (write)
import Snarky.Backend.Bulletproof.Types (CRS, Witness, Statement, Circuit, Proof, CircuitDimensions, Entry, CircuitMatrix, CircuitVector)
import Snarky.Curves.Vesta (ScalarField)

crsCreate :: { size :: Int, seed :: Int } -> CRS
crsCreate { size, seed } = runFn2 vestaCrsCreate size seed

crsSize :: CRS -> Int
crsSize = vestaCrsSize

witnessCreate
  :: { left :: Array ScalarField
     , right :: Array ScalarField
     , output :: Array ScalarField
     , v :: Array ScalarField
     , seed :: Int
     }
  -> Witness
witnessCreate { left, right, output, v, seed } =
  runFn5 vestaWitnessCreate left right output v seed

witnessSize :: Witness -> Int
witnessSize = vestaWitnessSize

statementCreate :: { crs :: CRS, witness :: Witness } -> Statement
statementCreate { crs, witness } = runFn2 vestaStatementCreate crs witness

circuitCreate
  :: { dimensions :: CircuitDimensions
     , weightsLeft :: CircuitMatrix ScalarField
     , weightsRight :: CircuitMatrix ScalarField
     , weightsOutput :: CircuitMatrix ScalarField
     , weightsAuxiliary :: CircuitMatrix ScalarField
     , constants :: CircuitVector ScalarField
     }
  -> Circuit
circuitCreate { dimensions, weightsLeft, weightsRight, weightsOutput, weightsAuxiliary, constants } =
  runFn6 vestaCircuitCreate dimensions
    (write weightsLeft)
    (write weightsRight)
    (write weightsOutput)
    (write weightsAuxiliary)
    (write constants)

circuitN :: Circuit -> Int
circuitN = vestaCircuitN

circuitQ :: Circuit -> Int
circuitQ = vestaCircuitQ

circuitIsSatisfiedBy :: { circuit :: Circuit, witness :: Witness } -> Boolean
circuitIsSatisfiedBy { circuit, witness } = runFn2 vestaCircuitIsSatisfiedBy circuit witness

prove
  :: { crs :: CRS
     , circuit :: Circuit
     , witness :: Witness
     , seed :: Int
     }
  -> Proof
prove { crs, circuit, witness, seed } =
  runFn4 vestaProve crs circuit witness seed

verify
  :: { crs :: CRS
     , circuit :: Circuit
     , statement :: Statement
     , proof :: Proof
     }
  -> Boolean
verify { crs, circuit, statement, proof } =
  runFn4 vestaVerify crs circuit statement proof

foreign import vestaCrsCreate :: Fn2 Int Int CRS
foreign import vestaCrsSize :: CRS -> Int
foreign import vestaWitnessCreate :: Fn5 (Array ScalarField) (Array ScalarField) (Array ScalarField) (Array ScalarField) Int Witness
foreign import vestaWitnessSize :: Witness -> Int
foreign import vestaStatementCreate :: Fn2 CRS Witness Statement
foreign import vestaCircuitCreate :: Fn6 CircuitDimensions Foreign Foreign Foreign Foreign Foreign Circuit
foreign import vestaCircuitN :: Circuit -> Int
foreign import vestaCircuitQ :: Circuit -> Int
foreign import vestaCircuitIsSatisfiedBy :: Fn2 Circuit Witness Boolean
foreign import vestaProve :: Fn4 CRS Circuit Witness Int Proof
foreign import vestaVerify :: Fn4 CRS Circuit Statement Proof Boolean
