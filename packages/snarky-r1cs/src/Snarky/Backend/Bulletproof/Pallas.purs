module Snarky.Backend.Bulletproof.Pallas
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
import Snarky.Backend.Bulletproof.Types (CRS, Witness, Statement, Circuit, Proof, CircuitDimensions, Entry, Matrix, Vector)
import Snarky.Curves.Pallas (ScalarField)

-- FFI imports
foreign import pallasCrsCreate :: Fn2 Int Int CRS
foreign import pallasCrsSize :: CRS -> Int
foreign import pallasWitnessCreate :: Fn5 (Array ScalarField) (Array ScalarField) (Array ScalarField) (Array ScalarField) Int Witness
foreign import pallasWitnessSize :: Witness -> Int
foreign import pallasStatementCreate :: Fn2 CRS Witness Statement
foreign import pallasCircuitCreate :: Fn6 CircuitDimensions Foreign Foreign Foreign Foreign Foreign Circuit
foreign import pallasCircuitN :: Circuit -> Int
foreign import pallasCircuitQ :: Circuit -> Int
foreign import pallasCircuitIsSatisfiedBy :: Fn2 Circuit Witness Boolean
foreign import pallasProve :: Fn4 CRS Circuit Witness Int Proof
foreign import pallasVerify :: Fn4 CRS Circuit Statement Proof Boolean

-- Exported functions with record arguments

-- | Create a new CRS (Common Reference String) for circuits of size n
crsCreate :: { size :: Int, seed :: Int } -> CRS
crsCreate { size, seed } = runFn2 pallasCrsCreate size seed

-- | Get the size of a CRS
crsSize :: CRS -> Int
crsSize = pallasCrsSize

-- | Create a witness from field arrays and random seed
witnessCreate
  :: { left :: Array ScalarField
     , right :: Array ScalarField
     , output :: Array ScalarField
     , v :: Array ScalarField
     , seed :: Int
     }
  -> Witness
witnessCreate { left, right, output, v, seed } =
  runFn5 pallasWitnessCreate left right output v seed

-- | Get the size of a witness
witnessSize :: Witness -> Int
witnessSize = pallasWitnessSize

-- | Create a statement from a CRS and witness
statementCreate :: { crs :: CRS, witness :: Witness } -> Statement
statementCreate { crs, witness } = runFn2 pallasStatementCreate crs witness

-- | Create a circuit from weight matrices and constants
circuitCreate
  :: { dimensions :: CircuitDimensions
     , weightsLeft :: Matrix ScalarField
     , weightsRight :: Matrix ScalarField
     , weightsOutput :: Matrix ScalarField
     , weightsAuxiliary :: Matrix ScalarField
     , constants :: Vector ScalarField
     }
  -> Circuit
circuitCreate { dimensions, weightsLeft, weightsRight, weightsOutput, weightsAuxiliary, constants } =
  runFn6 pallasCircuitCreate dimensions
    (write weightsLeft)
    (write weightsRight)
    (write weightsOutput)
    (write weightsAuxiliary)
    (write constants)

-- | Get the number of variables (n) in a circuit
circuitN :: Circuit -> Int
circuitN = pallasCircuitN

-- | Get the number of constraints (q) in a circuit  
circuitQ :: Circuit -> Int
circuitQ = pallasCircuitQ

-- | Check if a witness satisfies a circuit
circuitIsSatisfiedBy :: { circuit :: Circuit, witness :: Witness } -> Boolean
circuitIsSatisfiedBy { circuit, witness } = runFn2 pallasCircuitIsSatisfiedBy circuit witness

-- | Generate a proof for a circuit
prove
  :: { crs :: CRS
     , circuit :: Circuit
     , witness :: Witness
     , seed :: Int
     }
  -> Proof
prove { crs, circuit, witness, seed } =
  runFn4 pallasProve crs circuit witness seed

-- | Verify a proof  
verify
  :: { crs :: CRS
     , circuit :: Circuit
     , statement :: Statement
     , proof :: Proof
     }
  -> Boolean
verify { crs, circuit, statement, proof } =
  runFn4 pallasVerify crs circuit statement proof

