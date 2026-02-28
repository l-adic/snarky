module Snarky.Backend.Kimchi
  ( makeConstraintSystem
  , makeGateData
  , makePublicInputRows
  , makeWitness
  , placeVariables
  ) where

import Prelude

import Control.Monad.State (evalState)
import Data.Array ((:))
import Data.Array as Array
import Data.Fin (getFinite)
import Data.Foldable (foldl)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), uncurry)
import Data.UnionFind (UnionFindData, find)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, circuitGateNew, constraintSystemCreate)
import Snarky.Backend.Kimchi.Types (ConstraintSystem, Gate, Wire, gateWiresNewFromWires, wireNew)
import Snarky.Circuit.DSL (Variable)
import Snarky.Constraint.Kimchi.Types (GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField)

-- figure out the cell placement for each variable. 
-- since we can use the same variable in multiple constraints,
-- naturally this is a one to many mapping.
placeVariables
  :: forall f
   . Array (KimchiRow f)
  -> Map Variable (Array (Tuple Int Int))
placeVariables rows =
  foldlWithIndex
    ( \i acc row ->
        foldlWithIndex
          ( \j m mVar -> case mVar of
              Nothing -> m
              Just var -> Map.insertWith append var [ Tuple i (getFinite j) ] m
          )
          acc
          row.variables
    )
    Map.empty
    rows

-- Kimchi backend has a special format for public inputs
makePublicInputRows
  :: forall f
   . PrimeField f
  => Array Variable
  -> Array (KimchiRow f)
makePublicInputRows =
  map
    ( \var ->
        { kind: GenericPlonkGate
        , coeffs: one : Array.replicate 4 zero
        , variables: Just var :< Vector.generate (const Nothing)
        }
    )

-- Take the equivalence classes given by equality
-- constraints and the equivalence classes given
-- by variable layout and create a wire mapping
-- (i,j) |-> wire meaning that we are wiring the cell
-- to the existing wire. These wires create a cyclic list,
-- meaning if you follow in order you end up back at the
-- start, closing the loop for the perumutation argument
makeWireMapping
  :: UnionFindData Variable
  -> Map Variable (Array (Tuple Int Int))
  -> Map (Tuple Int Int) Wire
makeWireMapping uf variablePlacement =
  let
    -- mapping from the canonical root to the list
    -- of all cells equivalent to that root,
    -- filtered to only include permutation columns (0-6)
    m =
      foldl
        ( \acc (Tuple var cells) ->
            let
              root = getRoot var
              permCells = Array.filter (\(Tuple _ j) -> j < 7) cells
            in
              Map.insertWith append root permCells acc
        )
        Map.empty
        (Map.toUnfoldable variablePlacement :: Array _)
    classes =
      map
        ( \xs ->
            let
              xsSorted = Array.sort xs
            in
              Map.fromFoldable $ Array.zip xsSorted (rotateLeft xsSorted)
        )
        (Map.values m)
  in
    uncurry wireNew <$> Map.unions classes
  where
  rotateLeft xs = case Array.uncons xs of
    Just { head, tail } -> tail `Array.snoc` head
    Nothing -> xs
  getRoot x = evalState (find x) uf

makeGates
  :: forall f g
   . CircuitGateConstructor f g
  => Map (Tuple Int Int) Wire
  -> Array (KimchiRow f)
  -> Array (Gate f)
makeGates wireMap rows =
  mapWithIndex
    ( \i { kind, coeffs } ->
        let
          wires = makeGateWires i
        in
          circuitGateNew kind wires coeffs
    )
    rows
  where
  makeGateWires i =
    gateWiresNewFromWires $ Vector.generate \j ->
      case Map.lookup (Tuple i (getFinite j)) wireMap of
        Just w -> w
        Nothing -> wireNew i (getFinite j)

-- | Build gates and constraint rows without creating a full ConstraintSystem.
-- | Use this when you only need the gate data (e.g., for JSON serialization).
makeGateData
  :: forall @f g
   . CircuitGateConstructor f g
  => PrimeField f
  => { constraints :: Array (KimchiRow f)
     , publicInputs :: Array Variable
     , unionFind :: UnionFindData Variable
     }
  -> { constraints :: Array (KimchiRow f)
     , gates :: Array (Gate f)
     , publicInputSize :: Int
     }
makeGateData arg =
  let
    publicInputRows = makePublicInputRows arg.publicInputs
    rows = publicInputRows <> arg.constraints
    placement = placeVariables rows
    wireMapping = makeWireMapping arg.unionFind placement
    gates = makeGates wireMapping rows
    publicInputSize = Array.length publicInputRows
  in
    { constraints: rows
    , gates
    , publicInputSize
    }

makeConstraintSystem
  :: forall @f g
   . CircuitGateConstructor f g
  => PrimeField f
  => { constraints :: Array (KimchiRow f)
     , publicInputs :: Array Variable
     , unionFind :: UnionFindData Variable
     }
  -> { constraintSystem :: ConstraintSystem f
     , constraints :: Array (KimchiRow f)
     , gates :: Array (Gate f)
     , publicInputSize :: Int
     }
makeConstraintSystem arg =
  let
    gd = makeGateData @f arg
  in
    { constraintSystem: constraintSystemCreate @f gd.gates gd.publicInputSize
    , constraints: gd.constraints
    , gates: gd.gates
    , publicInputSize: gd.publicInputSize
    }

makeWitness
  :: forall f
   . PrimeField f
  => { assignments :: Map Variable f
     , constraints :: Array (Vector 15 (Maybe Variable))
     , publicInputs :: Array Variable
     }
  -> { publicInputs :: Array f
     , witness :: Vector 15 (Array f)
     }
makeWitness { assignments, constraints, publicInputs: fs } =
  let
    witness =
      Vector.generate \i ->
        map
          ( \row ->
              case row !! i of
                Nothing -> zero
                Just v -> case Map.lookup v assignments of
                  Nothing -> unsafeThrow $ "Missing witness variable assignment in witness: " <> show v
                  Just f -> f

          )
          constraints
    publicInputs =
      map
        ( \v -> case Map.lookup v assignments of
            Nothing -> unsafeThrow $ "Missing public input variable assignment in witness: " <> show v
            Just f -> f
        )
        fs
  in
    { witness, publicInputs }
