module Snarky.Backend.Groth16.Gate
  ( Gates
  , Matrix
  , Vector
  , GatesWitness
  , emptyGates
  , makeGates
  , makeGatesWitness
  , satisfies
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Data.Array (all, mapWithIndex)
import Data.Array as Array
import Data.FoldableWithIndex as ArrayWithIndex
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe, fromMaybe)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Snarky.Circuit.CVar (EvaluationError(..), Variable)
import Snarky.Constraint.Groth16 (R1CS(..))
import Snarky.Curves.Class (class PrimeField)

type Vector f = Map Int f
type Matrix f = Array (Vector f)

-- For Groth16, Gates represent the A, B, C matrices of R1CS constraints
type Gates f =
  { a :: Matrix f -- A matrix for constraints (A·z) * (B·z) = (C·z)
  , b :: Matrix f -- B matrix 
  , c :: Matrix f -- C matrix
  }

emptyGates :: forall f. Gates f
emptyGates =
  { a: mempty
  , b: mempty
  , c: mempty
  }

-- For Groth16, witness contains private inputs and public inputs separately
type GatesWitness f =
  { witness :: Array f -- private witness values
  , publicInputs :: Array f -- public input values
  }

-- Convert R1CS constraints directly to A, B, C matrices
-- This is simpler than bulletproofs because no preprocessing is needed
makeGates
  :: forall f
   . PrimeField f
  => { publicInputs :: Array Variable
     , constraints :: Array (R1CS f)
     }
  -> Gates f
makeGates { publicInputs, constraints } =
  let
    -- For Groth16, we need to map variables to their positions in z = [1, public_inputs, witness]
    -- Position 0 is constant 1, positions 1..m are public inputs, rest are witness
    _publicInputMap = Map.fromFoldable $
      mapWithIndex (\i var -> Tuple var (i + 1)) publicInputs -- +1 because position 0 is constant

    -- Process each constraint to extract A, B, C matrix rows
    processConstraint :: R1CS f -> { a :: Vector f, b :: Vector f, c :: Vector f }
    processConstraint (R1CS { left: _left, right: _right, output: _output }) =
      -- For simplicity, this is a placeholder implementation
      -- In practice, you would need to extract coefficients from the CVar expressions
      -- and map them to the correct positions in the constraint matrices
      { a: Map.empty, b: Map.empty, c: Map.empty }

    rows = map processConstraint constraints

  in
    { a: map _.a rows
    , b: map _.b rows
    , c: map _.c rows
    }

makeGatesWitness
  :: forall f m
   . PrimeField f
  => MonadThrow (EvaluationError f) m
  => { assignments :: Map Variable f
     , constraints :: Array (R1CS f)
     , publicInputs :: Array Variable
     }
  -> m (GatesWitness f)
makeGatesWitness { assignments, constraints: _constraints, publicInputs } = do
  -- Extract public input values
  publicInputValues <- for publicInputs \var ->
    case Map.lookup var assignments of
      Nothing -> throwError (MissingVariable var :: EvaluationError f)
      Just val -> pure val

  -- For private witness, we need to extract the private variables used in constraints
  -- This is a simplified implementation - in practice you'd need to determine
  -- which variables are private vs public and extract their values

  -- For now, create empty witness array - this would need proper implementation
  let witnessValues = []

  pure
    { witness: witnessValues
    , publicInputs: publicInputValues
    }

-- Check if witness satisfies the gates (R1CS constraints)
satisfies
  :: forall f
   . PrimeField f
  => GatesWitness f
  -> Gates f
  -> Boolean
satisfies witness gates =
  -- For Groth16, we need to check that for each constraint i:
  -- (A_i · z) * (B_i · z) = (C_i · z)
  -- where z = [1, public_inputs, private_witness]

  let
    -- Combine constant 1, public inputs, and private witness into full assignment vector
    fullAssignment = [ one ] <> witness.publicInputs <> witness.witness

    -- Check each constraint
    checkConstraint :: Int -> Boolean
    checkConstraint i =
      let
        aRow = fromMaybe Map.empty $ Array.index gates.a i
        bRow = fromMaybe Map.empty $ Array.index gates.b i
        cRow = fromMaybe Map.empty $ Array.index gates.c i

        -- Compute A_i · z
        aVal = innerProduct fullAssignment aRow
        -- Compute B_i · z  
        bVal = innerProduct fullAssignment bRow
        -- Compute C_i · z
        cVal = innerProduct fullAssignment cRow

      in
        aVal * bVal == cVal

  in
    all checkConstraint (Array.range 0 (Array.length gates.a - 1))

  where
  innerProduct :: Array f -> Map Int f -> f
  innerProduct assignment coeffs =
    ArrayWithIndex.foldlWithIndex
      (\i acc val -> maybe acc (\coeff -> acc + val * coeff) (Map.lookup i coeffs))
      zero
      assignment

