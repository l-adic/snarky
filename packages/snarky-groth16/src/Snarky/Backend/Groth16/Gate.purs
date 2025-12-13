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

type Gates f =
  { a :: Matrix f
  , b :: Matrix f
  , c :: Matrix f
  , publicInputIndices :: Array Int
  }

emptyGates :: forall f. Gates f
emptyGates =
  { a: mempty
  , b: mempty
  , c: mempty
  , publicInputIndices: mempty
  }

type GatesWitness f = Array f

makeGates
  :: forall f
   . PrimeField f
  => { publicInputs :: Array Variable
     , constraints :: Array (R1CS f)
     }
  -> Gates f
makeGates { publicInputs, constraints } =
  let
    collectVariables :: CVar f Variable -> Set Variable
    collectVariables = foldl (flip Set.insert) mempty

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
      mapWithIndex (\i var -> Tuple var (i + 1)) publicInputs

    witnessVariablesOrdered = Set.toUnfoldable witnessVariables

    witnessMap = Map.fromFoldable $
      mapWithIndex (\i var -> Tuple var (i + 1 + Array.length publicInputs)) witnessVariablesOrdered

    variableMap = Map.union publicInputMap witnessMap

    affineToVector :: AffineExpression f -> Vector f
    affineToVector (AffineExpression { constant, terms }) =
      let
        constantMap = case constant of
          Nothing -> Map.empty
          Just c -> Map.singleton 0 c

        variableCoeffs = Map.fromFoldable $ Array.mapMaybe
          ( \(Tuple var coeff) ->
              case Map.lookup var variableMap of
                Just pos -> Just (Tuple pos coeff)
                Nothing -> Nothing -- This shouldn't happen if we collected all variables correctly
          )
          terms
      in
        Map.union constantMap variableCoeffs

    processConstraint :: R1CS f -> { a :: Vector f, b :: Vector f, c :: Vector f }
    processConstraint (R1CS { left, right, output }) =
      let
        aVec = affineToVector $ reduceToAffineExpression left
        bVec = affineToVector $ reduceToAffineExpression right
        cVec = affineToVector $ reduceToAffineExpression output
      in
        { a: aVec, b: bVec, c: cVec }

    rows = map processConstraint constraints

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
  publicInputValues <- for publicInputs \var ->
    case Map.lookup var assignments of
      Nothing -> throwError (MissingVariable var :: EvaluationError f)
      Just val -> pure val

  let
    collectVariables :: CVar f Variable -> Set Variable
    collectVariables = foldl (flip Set.insert) mempty

    allVariables = Set.unions $ Array.concatMap
      ( \(R1CS { left, right, output }) ->
          [ collectVariables left, collectVariables right, collectVariables output ]
      )
      constraints
    publicInputSet = Set.fromFoldable publicInputs
    witnessVariables = Set.difference allVariables publicInputSet

    witnessVariablesOrdered = Set.toUnfoldable witnessVariables

  witnessValues <- for witnessVariablesOrdered \var ->
    case Map.lookup var assignments of
      Nothing -> throwError (MissingVariable var :: EvaluationError f)
      Just val -> pure val

  let
    fullWitness = Array.cons one $ publicInputValues <> witnessValues

  pure fullWitness

-- Check if witness satisfies the gates (R1CS constraints)
satisfies
  :: forall f
   . PrimeField f
  => GatesWitness f
  -> Gates f
  -> Boolean
satisfies witness gates =
  let

    checkConstraint :: Int -> Boolean
    checkConstraint i =
      let
        aRow = fromMaybe Map.empty $ Array.index gates.a i
        bRow = fromMaybe Map.empty $ Array.index gates.b i
        cRow = fromMaybe Map.empty $ Array.index gates.c i

        aVal = innerProduct witness aRow
        bVal = innerProduct witness bRow
        cVal = innerProduct witness cRow

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

