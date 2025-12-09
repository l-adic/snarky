module Snarky.Backend.Bulletproof.Class where

import Prelude

import Data.Array as Array
import Data.Newtype (unwrap)
import Snarky.Backend.Bulletproof.Impl.Pallas as Pallas
import Snarky.Backend.Bulletproof.Impl.Vesta as Vesta
import Snarky.Backend.Bulletproof.Types (CRS, Circuit, GatesWitness, Gates, Proof, Statement, Witness, toCircuitGates, toCircuitWitness)
import Snarky.Curves.Pallas as PallasC
import Snarky.Curves.Vesta as VestaC

class Bulletproof g f | g -> f where
  createWitness :: { witness :: GatesWitness f, seed :: Int } -> Witness g
  createCircuit :: { gates :: Gates f, dimensions :: { q :: Int, n :: Int, m :: Int } } -> Circuit g
  createCrs :: { size :: Int, seed :: Int } -> CRS g
  createStatement :: { crs :: CRS g, witness :: Witness g } -> Statement g
  createProof
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
  circuitIsSatisfiedBy :: { circuit :: Circuit g, witness :: Witness g } -> Boolean

instance Bulletproof PallasC.G PallasC.ScalarField where
  createWitness { witness, seed } =
    let
      n = Array.length witness.al
      paddedWitness = unwrap $ toCircuitWitness witness n
    in
      Pallas.witnessCreate
        { left: paddedWitness.al
        , right: paddedWitness.ar
        , output: paddedWitness.ao
        , v: paddedWitness.v
        , seed
        }
  createCircuit { gates, dimensions } =
    Pallas.circuitCreate (unwrap $ toCircuitGates gates dimensions)
  createCrs = Pallas.crsCreate
  createStatement = Pallas.statementCreate
  createProof = Pallas.prove
  verify = Pallas.verify
  circuitIsSatisfiedBy = Pallas.circuitIsSatisfiedBy

instance Bulletproof VestaC.G VestaC.ScalarField where
  createWitness { witness, seed } =
    let
      n = Array.length witness.al
      paddedWitness = unwrap $ toCircuitWitness witness n
    in
      Vesta.witnessCreate
        { left: paddedWitness.al
        , right: paddedWitness.ar
        , output: paddedWitness.ao
        , v: paddedWitness.v
        , seed
        }
  createCircuit { gates, dimensions } =
    Vesta.circuitCreate (unwrap $ toCircuitGates gates dimensions)
  createCrs = Vesta.crsCreate
  createStatement = Vesta.statementCreate
  createProof = Vesta.prove
  verify = Vesta.verify
  circuitIsSatisfiedBy = Vesta.circuitIsSatisfiedBy