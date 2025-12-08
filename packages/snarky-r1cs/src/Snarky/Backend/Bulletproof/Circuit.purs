module Snarky.Backend.Bulletproof.Circuit
  ( CRS
  , Witness
  , Statement
  , Circuit
  , Proof
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
  , circuitToRecord
  , witnessToRecord
  ) where

import Prelude

import Data.Function.Uncurried (Fn2, Fn4, Fn5, runFn2, runFn4, runFn5)
import Snarky.Curves.Pallas (ScalarField)

-- Opaque types for circuit components
foreign import data CRS :: Type
foreign import data Witness :: Type
foreign import data Statement :: Type
foreign import data Circuit :: Type
foreign import data Proof :: Type

-- FFI imports
foreign import pallasCrsCreate :: Fn2 Int Int CRS
foreign import pallasCrsSize :: CRS -> Int
foreign import pallasWitnessCreate :: Fn5 (Array ScalarField) (Array ScalarField) (Array ScalarField) (Array ScalarField) Int Witness
foreign import pallasWitnessSize :: Witness -> Int
foreign import pallasStatementCreate :: Fn2 CRS Witness Statement
foreign import pallasCircuitCreate :: Fn5 (Array (Array ScalarField)) (Array (Array ScalarField)) (Array (Array ScalarField)) (Array (Array ScalarField)) (Array ScalarField) Circuit
foreign import pallasCircuitN :: Circuit -> Int
foreign import pallasCircuitQ :: Circuit -> Int
foreign import pallasCircuitIsSatisfiedBy :: Fn2 Circuit Witness Boolean
foreign import pallasProve :: Fn4 CRS Circuit Witness Int Proof
foreign import pallasVerify :: Fn4 CRS Circuit Statement Proof Boolean

-- Getter functions for round-trip testing
foreign import pallasCircuitGetWeightsLeft :: Circuit -> Array (Array ScalarField)
foreign import pallasCircuitGetWeightsRight :: Circuit -> Array (Array ScalarField)
foreign import pallasCircuitGetWeightsOutput :: Circuit -> Array (Array ScalarField)
foreign import pallasCircuitGetWeightsAuxiliary :: Circuit -> Array (Array ScalarField)
foreign import pallasCircuitGetConstants :: Circuit -> Array ScalarField
foreign import pallasWitnessGetLeft :: Witness -> Array ScalarField
foreign import pallasWitnessGetRight :: Witness -> Array ScalarField
foreign import pallasWitnessGetOutput :: Witness -> Array ScalarField
foreign import pallasWitnessGetAuxiliary :: Witness -> Array ScalarField

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
  :: { weightsLeft :: Array (Array ScalarField)
     , weightsRight :: Array (Array ScalarField)
     , weightsOutput :: Array (Array ScalarField)
     , weightsAuxiliary :: Array (Array ScalarField)
     , constants :: Array ScalarField
     }
  -> Circuit
circuitCreate { weightsLeft, weightsRight, weightsOutput, weightsAuxiliary, constants } =
  runFn5 pallasCircuitCreate weightsLeft weightsRight weightsOutput weightsAuxiliary constants

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

-- | Convert a Rust Circuit back to PureScript record for testing
circuitToRecord
  :: Circuit
  -> { weightsLeft :: Array (Array ScalarField)
     , weightsRight :: Array (Array ScalarField)
     , weightsOutput :: Array (Array ScalarField)
     , weightsAuxiliary :: Array (Array ScalarField)
     , constants :: Array ScalarField
     , n :: Int
     , q :: Int
     }
circuitToRecord circuit =
  { weightsLeft: pallasCircuitGetWeightsLeft circuit
  , weightsRight: pallasCircuitGetWeightsRight circuit
  , weightsOutput: pallasCircuitGetWeightsOutput circuit
  , weightsAuxiliary: pallasCircuitGetWeightsAuxiliary circuit
  , constants: pallasCircuitGetConstants circuit
  , n: circuitN circuit
  , q: circuitQ circuit
  }

-- | Convert a Rust Witness back to PureScript record for testing  
witnessToRecord
  :: Witness
  -> { left :: Array ScalarField
     , right :: Array ScalarField
     , output :: Array ScalarField
     , auxiliary :: Array ScalarField
     , size :: Int
     }
witnessToRecord witness =
  { left: pallasWitnessGetLeft witness
  , right: pallasWitnessGetRight witness
  , output: pallasWitnessGetOutput witness
  , auxiliary: pallasWitnessGetAuxiliary witness
  , size: witnessSize witness
  }