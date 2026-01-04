module Snarky.Backend.Kimchi where

import Prelude

import Control.Monad.State (evalState)
import Data.Array ((:))
import Data.Array as Array
import Data.Foldable (foldl)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), uncurry)
import Data.UnionFind (UnionFindData, find)
import Snarky.Backend.Kimchi.Circuit (class CircuitGateConstructor, Wire, circuitGateNew, constraintSystemCreate, gateWiresNewFromWires, wireNew)
import Snarky.Circuit.CVar (Variable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Fin (getFinite)
import Snarky.Data.Vector ((:<))
import Snarky.Data.Vector as Vector

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
    -- of all cells equivalent to that root
    m =
      foldl
        ( \acc (Tuple var cells) ->
            let
              root = getRoot var
            in
              Map.insertWith append root cells acc
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
  :: forall f gate cs
   . CircuitGateConstructor f gate cs
  => Map (Tuple Int Int) Wire
  -> Array (KimchiRow f)
  -> Array gate
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
        Nothing -> wireNew i (getFinite j)
        Just w -> w

makeConstraintSystem
  :: forall f gate cs
   . CircuitGateConstructor f gate cs
  => PrimeField f
  => { constraints :: Array (KimchiRow f)
     , publicInputs :: Array Variable
     , unionFind :: UnionFindData Variable
     }
  -> cs
makeConstraintSystem arg =
  let
    publicInputRows = makePublicInputRows arg.publicInputs
    rows = publicInputRows <> arg.constraints
    placement = placeVariables rows
    wireMapping = makeWireMapping arg.unionFind placement
    gates = makeGates wireMapping rows
  in
    constraintSystemCreate @f gates (Array.length publicInputRows)
