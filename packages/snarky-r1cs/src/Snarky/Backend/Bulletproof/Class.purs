module Snarky.Backend.Bulletproof.Class where

import Snarky.Backend.Bulletproof.Impl.Pallas as Pallas
import Snarky.Backend.Bulletproof.Impl.Vesta as Vesta
import Snarky.Backend.Bulletproof.Types (CRS, Circuit, CircuitDimensions, CircuitMatrix, CircuitVector, Proof, Statement, Witness, CircuitGates)
import Snarky.Curves.Pallas as PallasC
import Snarky.Curves.Vesta as VestaC

class Bulletproof g f | g -> f where
  crsCreate :: { size :: Int, seed :: Int } -> CRS g
  witnessCreate
    :: { left :: Array f
       , right :: Array f
       , output :: Array f
       , v :: Array f
       , seed :: Int
       }
    -> Witness g
  statementCreate :: { crs :: CRS g, witness :: Witness g } -> Statement g
  circuitCreate
    :: CircuitGates f
    -> Circuit g
  circuitIsSatisfiedBy :: { circuit :: Circuit g, witness :: Witness g } -> Boolean
  prove
    :: { crs :: CRS g
       , circuit :: Circuit g
       , witness :: Witness g
       , seed :: Int
       }
    -> Proof g
  verify
    :: { crs :: CRS g
       , circuit :: Circuit g
       , statement :: Statement g
       , proof :: Proof g
       }
    -> Boolean

instance Bulletproof PallasC.G PallasC.ScalarField where
  crsCreate = Pallas.crsCreate
  witnessCreate = Pallas.witnessCreate
  statementCreate = Pallas.statementCreate
  circuitCreate = Pallas.circuitCreate
  circuitIsSatisfiedBy = Pallas.circuitIsSatisfiedBy
  prove = Pallas.prove
  verify = Pallas.verify

instance Bulletproof VestaC.G VestaC.ScalarField where
  crsCreate = Vesta.crsCreate
  witnessCreate = Vesta.witnessCreate
  statementCreate = Vesta.statementCreate
  circuitCreate = Vesta.circuitCreate
  circuitIsSatisfiedBy = Vesta.circuitIsSatisfiedBy
  prove = Vesta.prove
  verify = Vesta.verify