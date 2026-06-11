module Snarky.Backend.Kimchi
  ( makeConstraintSystemWithPrevChallenges
  , makeGateData
  , makePublicInputRows
  , makeWitness

  ) where

import Prelude

import Control.Monad.ST (run) as ST
import Control.Monad.ST.Internal (foreach) as STI
import Data.Array ((:))
import Data.Array as Array
import Data.Fin (getFinite)
import Data.Foldable (foldl)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FoldableWithIndex (forWithIndex_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..), fst, uncurry)
import Data.UnionFind.Mutable (MutableUF)
import Data.UnionFind.Mutable as MutableUF
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception.Unsafe (unsafeThrow)
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
-- One pure ST pass: place variables into cells (dense by variable
-- index, row-major discovery order — same order `Map.insertWith append`
-- produced), group permutation cells (cols 0-6) by union-find root, and
-- lay each class's cycle into a frozen wire table keyed by cell
-- `i * 16 + j`. Region-quantified `ST.run` proves the mutation is local.
makeWireMapping
  :: forall f
   . Array Int
  -> Array (KimchiRow f)
  -> Array (Maybe Wire)
makeWireMapping roots rows = ST.run do
  placement <- DenseStore.fresh
  STI.foreach (mapWithIndex Tuple rows) \(Tuple i row) ->
    forWithIndex_ row.variables \j mVar -> case mVar of
      Nothing -> pure unit
      Just (Variable v) -> DenseStore.pushAt v (Tuple i (getFinite j)) placement
  rootCells <- DenseStore.fresh
  placementEntries <- DenseStore.toEntries Tuple placement
  STI.foreach placementEntries \(Tuple v cells) -> do
    let root = fromMaybe v (Array.index roots v)
    STI.foreach (Array.filter (\(Tuple _ j) -> j < 7) cells) \cell ->
      DenseStore.pushAt root cell rootCells
  wireMap <- DenseStore.fresh
  classes <- DenseStore.toEntries (\_ cells -> cells) rootCells
  STI.foreach classes \cells -> do
    let xsSorted = Array.sort cells
    STI.foreach (Array.zip xsSorted (rotateLeft xsSorted)) \(Tuple (Tuple i j) target) ->
      DenseStore.setAt (i * 16 + j) (uncurry wireNew target) wireMap
  DenseStore.freeze wireMap
  where
  rotateLeft xs = case Array.uncons xs of
    Just { head, tail } -> tail `Array.snoc` head
    Nothing -> xs

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
  => Array (Maybe Wire)
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
      case join (Array.index wireMap (i * 16 + getFinite j)) of
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
