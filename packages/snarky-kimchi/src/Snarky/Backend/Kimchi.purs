module Snarky.Backend.Kimchi
  ( makeConstraintSystemWithPrevChallenges
  , makeGateData
  , makePublicInputRows
  , makeWitness

  ) where

import Prelude

import Control.Monad.ST (run) as ST
import Control.Monad.ST.Internal (for, foreach) as STI
import Data.Array ((:))
import Data.Array as Array
import Data.Array.ST as STA
import Data.Fin (Finite, finites, getFinite)
import Data.Foldable (foldl)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Int.Bits (and, shl, shr)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.UnionFind.Mutable (MutableUF)
import Data.UnionFind.Mutable as MutableUF
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception.Unsafe (unsafeThrow)
import Safe.Coerce (coerce)
import Snarky.Backend.Assignments (Frozen, lookupFrozen)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, circuitGateNew)
import Snarky.Backend.Kimchi.Types (Gate, Wire, gateWiresNewFromWires, wireNew)
import Snarky.Circuit.CVar (Variable(..))
import Snarky.Circuit.DSL (Variable)
import Snarky.Constraint.Kimchi.Types (GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField)

-- | The columns of a row that take part in the permutation argument.
permutationCols :: Array (Finite 15)
permutationCols = Array.take 7 finites

-- | A permutation cell: a row and one of its wired columns. It is one
-- | `Int`, eight to a row, so an array of cells is an array of plain
-- | numbers and a cell is its own index into an array with a slot per
-- | cell.
newtype Cell = Cell Int

-- | The cell at a row and a column.
cellAt :: Int -> Int -> Cell
cellAt row col = Cell ((row `shl` 3) + col)

-- | A cell's slot in an array with one per cell.
slot :: Cell -> Int
slot (Cell c) = c

-- | The wire that points to a cell.
wireTo :: Cell -> Wire
wireTo (Cell c) = wireNew (c `shr` 3) (c `and` 7)

-- | What a class's latest cell is before the class has one.
noCell :: Cell
noCell = Cell (-1)

-- | The wiring of the permutation cells: at a cell's slot, the cell
-- | that one points to. The cells holding variables of one union-find
-- | class form a cycle, in row-major order; any other cell points to
-- | itself.
-- |
-- | One pass over the rows, in order, so each class's cells arrive
-- | sorted. `last` holds a class's latest cell, and the class's cells
-- | are a cycle throughout: a new cell takes over the latest one's
-- | pointer, which is to the first, and the latest points to it. Both
-- | stores hold cells only, and the region-quantified `ST.run` proves
-- | the mutation local.
makeWireMapping
  :: forall f
   . Array Int
  -> Array (KimchiRow f)
  -> Array Cell
makeWireMapping roots rows = ST.run do
  next <- STA.thaw selfWired
  last <- STA.thaw (Array.replicate numClasses noCell)
  STI.for 0 numRows \i -> case Array.index rows i of
    Nothing -> pure unit
    Just row -> STI.foreach permutationCols \j -> case row.variables !! j of
      Nothing -> pure unit
      Just (Variable v) -> do
        let
          cls = fromMaybe v (Array.index roots v)
          cell = cellAt i (getFinite j)
        latest <- STA.peek cls last
        case latest of
          Just l | slot l >= 0 -> do
            first <- STA.peek (slot l) next
            _ <- STA.poke (slot cell) (fromMaybe cell first) next
            void $ STA.poke (slot l) cell next
          _ -> pure unit
        void $ STA.poke cls cell last
  STA.freeze next
  where
  numRows = Array.length rows

  -- Every cell starts wired to itself.
  selfWired :: Array Cell
  selfWired = if numRows == 0 then [] else coerce (Array.range 0 (slot (cellAt numRows 0) - 1))

  -- A class is keyed by its root: a union-find element, or a variable
  -- the union-find never saw, which is its own.
  numClasses = foldl
    ( \n row -> foldl
        ( \n' j -> case row.variables !! j of
            Just (Variable v) -> max n' (v + 1)
            Nothing -> n'
        )
        n
        permutationCols
    )
    (Array.length roots)
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

makeGates
  :: forall f g
   . CircuitGateConstructor f g
  => Array Cell
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
      let
        cell = cellAt i (getFinite j)
      in
        wireTo (fromMaybe cell (Array.index wireMap (slot cell)))

-- | Build gates and constraint rows without creating a full ConstraintSystem.
-- | Use this when you only need the gate data (e.g., for JSON serialization).
makeGateData
  :: forall @f g
   . CircuitGateConstructor f g
  => PrimeField f
  => { constraints :: Array (KimchiRow f)
     , publicInputs :: Array Variable
     , unionFind :: MutableUF
     }
  -> Effect
       { constraints :: Array (KimchiRow f)
       , gates :: Array (Gate f)
       , publicInputSize :: Int
       }
makeGateData arg = do
  roots <- MutableUF.rootOf arg.unionFind
  let
    publicInputRows = makePublicInputRows arg.publicInputs
    rows = publicInputRows <> arg.constraints
    wireMapping = makeWireMapping roots rows
    gates = makeGates wireMapping rows
    publicInputSize = Array.length publicInputRows
  pure
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
     , unionFind :: MutableUF
     , prevChallengesCount :: Int
     , maxPolySize :: Int
     }
  -> Effect
       { constraints :: Array (KimchiRow f)
       , gates :: Array (Gate f)
       , publicInputSize :: Int
       , prevChallengesCount :: Int
       , maxPolySize :: Int
       }
makeConstraintSystemWithPrevChallenges arg = do
  gd <- makeGateData @f
    { constraints: arg.constraints
    , publicInputs: arg.publicInputs
    , unionFind: arg.unionFind
    }
  pure
    { constraints: gd.constraints
    , gates: gd.gates
    , publicInputSize: gd.publicInputSize
    , prevChallengesCount: arg.prevChallengesCount
    , maxPolySize: arg.maxPolySize
    }

makeWitness
  :: forall f
   . PrimeField f
  => { assignments :: Frozen f
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
                Just v -> case lookupFrozen v assignments of
                  Nothing -> unsafeThrow $ "Missing witness variable assignment in witness: " <> show v
                  Just f -> f

          )
          constraints
    publicInputs =
      map
        ( \v -> case lookupFrozen v assignments of
            Nothing -> unsafeThrow $ "Missing public input variable assignment in witness: " <> show v
            Just f -> f
        )
        fs
  in
    { witness, publicInputs }
