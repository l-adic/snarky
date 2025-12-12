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
import Data.Foldable (foldl)
import Data.FoldableWithIndex as ArrayWithIndex
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe, fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Snarky.Circuit.CVar (EvaluationError(..), Variable, reduceToAffineExpression, AffineExpression(..), CVar(..))
import Snarky.Constraint.Groth16 (R1CS(..))
import Snarky.Curves.Class (class PrimeField)

type Vector f = Map Int f
type Matrix f = Array (Vector f)

-- For Groth16, Gates represent the A, B, C matrices of R1CS constraints
type Gates f =
  { a :: Matrix f -- A matrix for constraints (A·z) * (B·z) = (C·z)
  , b :: Matrix f -- B matrix 
  , c :: Matrix f -- C matrix
  , publicInputIndices :: Array Int -- Which positions in witness are public
  }

emptyGates :: forall f. Gates f
emptyGates =
  { a: mempty
  , b: mempty
  , c: mempty
  , publicInputIndices: mempty
  }

-- For Groth16, unified witness array following bulletproofs pattern
type GatesWitness f = Array f -- Full witness: [1, public..., private...]

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
    -- Collect all variables from a CVar using fold
    collectVariables :: CVar f Variable -> Set Variable
    collectVariables = foldl (flip Set.insert) mempty

    -- Get all variables from all constraints
    allVariables = Set.unions $ Array.concatMap
      ( \(R1CS { left, right, output }) ->
          [ collectVariables left, collectVariables right, collectVariables output ]
      )
      constraints
    publicInputSet = Set.fromFoldable publicInputs
    witnessVariables = Set.difference allVariables publicInputSet

    -- Create complete variable mapping: z = [1, public_inputs, witness]
    -- Position 0 is constant 1, positions 1..m are public inputs, rest are witness
    publicInputMap = Map.fromFoldable $
      mapWithIndex (\i var -> Tuple var (i + 1)) publicInputs -- +1 because position 0 is constant

    -- Get witness variables in ascending order (Set.toUnfoldable returns sorted order)
    witnessVariablesOrdered = Set.toUnfoldable witnessVariables

    witnessMap = Map.fromFoldable $
      mapWithIndex (\i var -> Tuple var (i + 1 + Array.length publicInputs)) witnessVariablesOrdered

    variableMap = Map.union publicInputMap witnessMap

    -- Convert affine expression to coefficient vector
    affineToVector :: AffineExpression f -> Vector f
    affineToVector (AffineExpression { constant, terms }) =
      let
        -- Add constant term at position 0 (if present)
        constantMap = case constant of
          Nothing -> Map.empty
          Just c -> Map.singleton 0 c

        -- Add variable terms at their mapped positions
        variableCoeffs = Map.fromFoldable $ Array.mapMaybe
          ( \(Tuple var coeff) ->
              case Map.lookup var variableMap of
                Just pos -> Just (Tuple pos coeff)
                Nothing -> Nothing -- This shouldn't happen if we collected all variables correctly
          )
          terms
      in
        Map.union constantMap variableCoeffs

    -- Process each constraint to extract A, B, C matrix rows
    processConstraint :: R1CS f -> { a :: Vector f, b :: Vector f, c :: Vector f }
    processConstraint (R1CS { left, right, output }) =
      let
        -- Reduce each CVar to affine form and convert to coefficient vectors
        aVec = affineToVector $ reduceToAffineExpression left
        bVec = affineToVector $ reduceToAffineExpression right
        cVec = affineToVector $ reduceToAffineExpression output
      in
        { a: aVec, b: bVec, c: cVec }

    rows = map processConstraint constraints

    -- Generate public input indices: positions 1 to (length publicInputs)
    publicIndices = Array.mapWithIndex (\i _ -> i + 1) publicInputs

  in
    { a: map _.a rows
    , b: map _.b rows
    , c: map _.c rows
    , publicInputIndices: publicIndices
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
makeGatesWitness { assignments, constraints, publicInputs } = do
  -- Extract public input values
  publicInputValues <- for publicInputs \var ->
    case Map.lookup var assignments of
      Nothing -> throwError (MissingVariable var :: EvaluationError f)
      Just val -> pure val

  -- Extract witness variables (same logic as in makeGates)
  let
    -- Collect all variables from a CVar using fold
    collectVariables :: CVar f Variable -> Set Variable
    collectVariables = foldl (flip Set.insert) mempty

    -- Get all variables from all constraints
    allVariables = Set.unions $ Array.concatMap
      ( \(R1CS { left, right, output }) ->
          [ collectVariables left, collectVariables right, collectVariables output ]
      )
      constraints
    publicInputSet = Set.fromFoldable publicInputs
    witnessVariables = Set.difference allVariables publicInputSet

    -- Get witness variables in ascending order (Set.toUnfoldable returns sorted order)
    witnessVariablesOrdered = Set.toUnfoldable witnessVariables

  -- Extract witness values in consistent order
  witnessValues <- for witnessVariablesOrdered \var ->
    case Map.lookup var assignments of
      Nothing -> throwError (MissingVariable var :: EvaluationError f)
      Just val -> pure val

  -- Create unified witness: [1, public..., private...]
  let
    fullWitness = [ one ] <> publicInputValues <> witnessValues

  pure fullWitness

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
  -- where z is the full witness array: [1, public_inputs, private_witness]

  let
    -- witness is already the full assignment vector
    fullAssignment = witness

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

