module Snarky.Backend.Bulletproof.Impl.Pallas
  ( module Snarky.Backend.Bulletproof.Types
  , crsCreate
  , witnessCreate
  , statementCreate
  , circuitCreate
  , circuitIsSatisfiedBy
  , prove
  , verify
  ) where

import Data.Function.Uncurried (Fn2, Fn4, Fn5, Fn6, runFn2, runFn4, runFn5, runFn6)
import Foreign (Foreign)
import Simple.JSON (write)
import Snarky.Backend.Bulletproof.Types (CRS, Witness, Statement, Circuit, Proof, CircuitDimensions, Entry, CircuitMatrix, CircuitVector)
import Snarky.Curves.Pallas (ScalarField, G)

crsCreate :: { size :: Int, seed :: Int } -> CRS G
crsCreate { size, seed } = runFn2 pallasCrsCreate size seed

witnessCreate
  :: { left :: Array ScalarField
     , right :: Array ScalarField
     , output :: Array ScalarField
     , v :: Array ScalarField
     , seed :: Int
     }
  -> Witness G
witnessCreate { left, right, output, v, seed } =
  runFn5 pallasWitnessCreate left right output v seed

statementCreate :: { crs :: CRS G, witness :: Witness G } -> Statement G
statementCreate { crs, witness } = runFn2 pallasStatementCreate crs witness

circuitCreate
  :: { dimensions :: CircuitDimensions
     , weightsLeft :: CircuitMatrix ScalarField
     , weightsRight :: CircuitMatrix ScalarField
     , weightsOutput :: CircuitMatrix ScalarField
     , weightsAuxiliary :: CircuitMatrix ScalarField
     , constants :: CircuitVector ScalarField
     }
  -> Circuit G
circuitCreate { dimensions, weightsLeft, weightsRight, weightsOutput, weightsAuxiliary, constants } =
  runFn6 pallasCircuitCreate dimensions
    (write weightsLeft)
    (write weightsRight)
    (write weightsOutput)
    (write weightsAuxiliary)
    (write constants)

circuitIsSatisfiedBy :: { circuit :: Circuit G, witness :: Witness G } -> Boolean
circuitIsSatisfiedBy { circuit, witness } = runFn2 pallasCircuitIsSatisfiedBy circuit witness

prove
  :: { crs :: CRS G
     , circuit :: Circuit G
     , witness :: Witness G
     , seed :: Int
     }
  -> Proof G
prove { crs, circuit, witness, seed } =
  runFn4 pallasProve crs circuit witness seed

verify
  :: { crs :: CRS G
     , circuit :: Circuit G
     , statement :: Statement G
     , proof :: Proof G
     }
  -> Boolean
verify { crs, circuit, statement, proof } =
  runFn4 pallasVerify crs circuit statement proof

foreign import pallasCrsCreate :: Fn2 Int Int (CRS G)
foreign import pallasWitnessCreate :: Fn5 (Array ScalarField) (Array ScalarField) (Array ScalarField) (Array ScalarField) Int (Witness G)
foreign import pallasStatementCreate :: Fn2 (CRS G) (Witness G) (Statement G)
foreign import pallasCircuitCreate :: Fn6 CircuitDimensions Foreign Foreign Foreign Foreign Foreign (Circuit G)
foreign import pallasCircuitIsSatisfiedBy :: Fn2 (Circuit G) (Witness G) Boolean
foreign import pallasProve :: Fn4 (CRS G) (Circuit G) (Witness G) Int (Proof G)
foreign import pallasVerify :: Fn4 (CRS G) (Circuit G) (Statement G) (Proof G) Boolean
