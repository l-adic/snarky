module Snarky.Backend.Kimchi
  ( makeConstraintSystemWithPrevChallenges
  , makeGateData
  , makePublicInputRows
  , makeWitness
  , placeVariables
  ) where

import Prelude

import Data.Array ((:))
import Data.Array as Array
import Data.Fin (getFinite)
import Data.Foldable (foldl)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FoldableWithIndex (forWithIndex_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, uncurry)
import Data.UnionFind (UnionFindData, find)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Effect (Effect, forE, foreachE)
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Backend.DenseStore (DenseStore)
import Snarky.Backend.DenseStore as DenseStore
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, circuitGateNew)
import Snarky.Backend.Kimchi.Types (Gate, Wire, gateWiresNewFromWires, wireNew)
import Snarky.Circuit.CVar (Variable(..))
import Snarky.Circuit.DSL (Variable)
import Snarky.Constraint.Kimchi.Types (GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField)

-- figure out the cell placement for each variable. 
-- since we can use the same variable in multiple constraints,
-- naturally this is a one to many mapping.
-- Dense by variable index: slot v = the cells where variable v appears,
-- in (row-major) discovery order — same order `Map.insertWith append`
-- produced.
placeVariables
  :: forall f
   . Array (KimchiRow f)
  -> DenseStore (Array (Tuple Int Int))
placeVariables rows = unsafePerformEffect do
  store <- DenseStore.fresh
  forEWithIndex rows \i row ->
    forWithIndex_ row.variables \j mVar -> case mVar of
      Nothing -> pure unit
      Just (Variable v) -> DenseStore.pushAt v (Tuple i (getFinite j)) store
  pure store
  where
  -- stack-safe indexed Effect loop (a row has 15 cells, so the inner
  -- `forWithIndex_` is fine; the outer loop is circuit-sized)
  forEWithIndex :: forall a. Array a -> (Int -> a -> Effect Unit) -> Effect Unit
  forEWithIndex xs f = forE 0 (Array.length xs) \i ->
    case Array.index xs i of
      Just x -> f i x
      Nothing -> pure unit

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
-- The wire map is dense by cell key `i * 16 + j` (j < 16): cell ->
-- next cell in its permutation cycle.
makeWireMapping
  :: UnionFindData Variable
  -> DenseStore (Array (Tuple Int Int))
  -> DenseStore Wire
makeWireMapping uf variablePlacement = unsafePerformEffect do
  -- per-root permutation cells (cols 0-6), in the same order the Map
  -- version accumulated them (ascending variable index)
  rootCells <- DenseStore.fresh
  foreachE (DenseStore.toEntries Tuple variablePlacement) \(Tuple v cells) -> do
    let Variable root = fst (find (Variable v) uf)
    foreachE (Array.filter (\(Tuple _ j) -> j < 7) cells) \cell ->
      DenseStore.pushAt root cell rootCells
  wireMap <- DenseStore.fresh
  foreachE (DenseStore.toEntries (\_ cells -> cells) rootCells) \cells -> do
    let xsSorted = Array.sort cells
    foreachE (Array.zip xsSorted (rotateLeft xsSorted)) \(Tuple (Tuple i j) target) ->
      DenseStore.setAt (i * 16 + j) (uncurry wireNew target) wireMap
  pure wireMap
  where
  rotateLeft xs = case Array.uncons xs of
    Just { head, tail } -> tail `Array.snoc` head
    Nothing -> xs

makeGates
  :: forall f g
   . CircuitGateConstructor f g
  => DenseStore Wire
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
      case DenseStore.getAt (i * 16 + getFinite j) wireMap of
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

-- | Build the raw circuit data (`gates` + `constraints` rows +
-- | `publicInputSize`) and carry the `prevChallengesCount` /
-- | `maxPolySize` parameters through to the caller. Previously this
-- | also called `constraintSystemCreate(WithPrevChallenges)` to produce
-- | an intermediate `ConstraintSystem` value, but that PS-level type
-- | has been collapsed away — `createProverIndex` now takes the raw
-- | data and does CS-creation internally. `prevChallengesCount` is the
-- | number of inductive hypotheses this circuit verifies recursively
-- | at the kimchi layer (mirrors OCaml's
-- | `Kimchi_bindings.Protocol.Constraint_system.create` which takes
-- | the count as part of the gate vector). `maxPolySize` is the SRS's
-- | `max_poly_size`, needed at index-create time to compute
-- | `num_chunks` and `zk_rows`.
makeConstraintSystemWithPrevChallenges
  :: forall @f g
   . CircuitGateConstructor f g
  => PrimeField f
  => { constraints :: Array (KimchiRow f)
     , publicInputs :: Array Variable
     , unionFind :: UnionFindData Variable
     , prevChallengesCount :: Int
     , maxPolySize :: Int
     }
  -> { constraints :: Array (KimchiRow f)
     , gates :: Array (Gate f)
     , publicInputSize :: Int
     , prevChallengesCount :: Int
     , maxPolySize :: Int
     }
makeConstraintSystemWithPrevChallenges arg =
  let
    gd = makeGateData @f
      { constraints: arg.constraints
      , publicInputs: arg.publicInputs
      , unionFind: arg.unionFind
      }
  in
    { constraints: gd.constraints
    , gates: gd.gates
    , publicInputSize: gd.publicInputSize
    , prevChallengesCount: arg.prevChallengesCount
    , maxPolySize: arg.maxPolySize
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
