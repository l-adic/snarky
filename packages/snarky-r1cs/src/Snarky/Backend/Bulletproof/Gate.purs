module Snarky.Backend.Bulletproof.Gate
  ( Gates
  , SparseMatrix
  , SortedR1CS
  , Witness
  , emptyGates
  , makeGates
  , makeWitness
  , satisfies
  , sortR1CS
  , toGates
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.State (State, evalState, get, modify_)
import Data.Array (all, catMaybes, fold, mapWithIndex, zipWith)
import Data.Array as Array
import Data.FoldableWithIndex as Arrat
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isNothing, maybe)
import Data.Newtype (class Newtype, un)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (foldl, for)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (Tuple(..), fst)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Backend.Bulletproof.Types (Matrix, Vector, Entry(..))
import Snarky.Circuit.CVar (AffineExpression(..), EvaluationError(..), Variable, reduceToAffineExpression)
import Snarky.Circuit.CVar as CVar
import Snarky.Constraint.R1CS (R1CS(..))
import Snarky.Curves.Class (class PrimeField)

newtype GateIndex = GateIndex Int

derive instance Eq GateIndex
derive instance Ord GateIndex
derive newtype instance Show GateIndex

derive instance Newtype GateIndex _

data Placement = L | R | O | V | C

instance Show Placement where
  show = case _ of
    L -> "L"
    R -> "R"
    O -> "O"
    V -> "V"
    C -> "C"

type S f =
  { currentIndex :: GateIndex
  , varPlacements :: Map Variable { index :: GateIndex, placement :: Placement, coeff :: f }
  }

initS :: forall f. S f
initS = { currentIndex: GateIndex 0, varPlacements: Map.empty }

newtype GateExpression f = GateExpression (Array { index :: GateIndex, coeff :: f, placement :: Placement })

derive newtype instance Semigroup (GateExpression f)
derive newtype instance Monoid (GateExpression f)

makeGateExpression
  :: forall f
   . PrimeField f
  => GateIndex
  -> R1CS f
  -> State (S f) (Array (GateExpression f))
makeGateExpression index (R1CS { left, right, output }) = do
  let
    g placement cvar = do
      let
        (AffineExpression { constant, terms }) = reduceToAffineExpression cvar
        constantTerm = constant <#> \c -> GateExpression [ { index, placement: C, coeff: c } ]
      xs <- case List.fromFoldable terms of
        List.Nil -> pure $
          GateExpression
            [ { index, placement, coeff: -one } ]
        List.Cons (Tuple _ f) List.Nil | f == zero -> pure $
          GateExpression
            [ { index, placement, coeff: -one }
            ]
        List.Cons (Tuple v f) List.Nil -> do
          { varPlacements } <- get
          case Map.lookup v varPlacements of
            Nothing -> do
              modify_ \s ->
                s { varPlacements = Map.insert v { index, placement, coeff: recip f } s.varPlacements }
              pure mempty
            Just x -> pure $
              GateExpression
                [ { index, placement, coeff: -one }
                , x { coeff = f * x.coeff }
                ]
        _ -> GateExpression <$> do
          { varPlacements } <- get
          prev <- for terms \(Tuple v f) -> do
            case Map.lookup v varPlacements of
              Nothing -> unsafeCrashWith $ "The impossible happened, missing variable " <> show v
              Just x -> pure x { coeff = f * x.coeff }
          pure $ Array.cons { index, placement, coeff: -one } prev
      pure $ maybe xs (\x -> x <> xs) constantTerm
  l <- g L left
  r <- g R right
  o <- g O output
  pure [ l, r, o ]

gateExpressionToRow
  :: forall f
   . PrimeField f
  => GateExpression f
  -> R f
gateExpressionToRow (GateExpression terms) =
  foldl
    ( \acc term ->
        if term.coeff == zero then acc
        else case term.placement of
          L -> acc { wl = Map.insertWith add (un GateIndex term.index) term.coeff acc.wl }
          R -> acc { wr = Map.insertWith add (un GateIndex term.index) term.coeff acc.wr }
          O -> acc { wo = Map.insertWith add (un GateIndex term.index) term.coeff acc.wo }
          V -> acc { wv = Map.insertWith add (un GateIndex term.index) term.coeff acc.wv }
          C -> acc { c = acc.c + term.coeff }
    )
    defaultRow
    terms

type R f =
  { wl :: Map Int f
  , wr :: Map Int f
  , wo :: Map Int f
  , wv :: Map Int f
  , c :: f
  }

defaultRow :: forall f. PrimeField f => R f
defaultRow =
  { wl: Map.empty
  , wr: Map.empty
  , wo: Map.empty
  , wv: Map.empty
  , c: zero
  }

type Gates f =
  { wl :: SparseMatrix f
  , wr :: SparseMatrix f
  , wo :: SparseMatrix f
  , wv :: SparseMatrix f
  , c :: Array f
  }

emptyGates :: forall f. Gates f
emptyGates =
  { wl: mempty
  , wr: mempty
  , wo: mempty
  , wv: mempty
  , c: mempty
  }

makeGates
  :: forall f
   . PrimeField f
  => { publicInputs :: Array Variable
     , constraints :: SortedR1CS f
     }
  -> Gates f
makeGates { publicInputs, constraints } =
  let

    publicInputIndices = Map.fromFoldable $
      mapWithIndex
        ( \i var ->
            Tuple var { index: GateIndex i, placement: V, coeff: one }
        )
        publicInputs

    f :: Int -> R1CS f -> State (S f) (Array (R f))
    f i c = do
      expr <- makeGateExpression (GateIndex i) c
      pure $ map gateExpressionToRow expr

    SortedR1CS cs = constraints

    rows :: Array (R f)
    rows = fold $ evalState (traverseWithIndex f cs) (initS { varPlacements = publicInputIndices })

  in
    foldl
      ( \acc r ->
          if Map.isEmpty r.wl && Map.isEmpty r.wr && Map.isEmpty r.wo && Map.isEmpty r.wv && r.c == zero then acc
          else
            acc
              { wl = acc.wl `Array.snoc` r.wl
              , wr = acc.wr `Array.snoc` r.wr
              , wo = acc.wo `Array.snoc` r.wo
              , wv = acc.wv `Array.snoc` r.wv
              , c = acc.c `Array.snoc` r.c
              }
      )
      emptyGates
      rows

type Witness f =
  { al :: Array f
  , ar :: Array f
  , ao :: Array f
  , v :: Array f
  }

makeWitness
  :: forall f m
   . PrimeField f
  => MonadThrow (EvaluationError f) m
  => { assignments :: Map Variable f
     , constraints :: SortedR1CS f
     , publicInputs :: Array Variable
     }
  -> m (Witness f)
makeWitness { assignments, constraints: SortedR1CS cs, publicInputs } = do
  v <- for publicInputs \var ->
    case Map.lookup var assignments of
      Nothing -> throwError $ MissingVariable var
      Just val -> pure val

  let lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var assignments

  gateWires <- for cs \(R1CS { left, right, output }) -> do
    lVal <- CVar.eval lookup left
    rVal <- CVar.eval lookup right

    let oValCalculated = lVal * rVal

    oValExpected <- CVar.eval lookup output

    when (oValCalculated /= oValExpected)
      $ throwError
      $ FailedAssertion "Multiplication mismatch"

    pure { l: lVal, r: rVal, o: oValCalculated }

  pure
    { al: map _.l gateWires
    , ar: map _.r gateWires
    , ao: map _.o gateWires
    , v
    }

satisfies
  :: forall f
   . PrimeField f
  => Witness f
  -> Gates f
  -> Boolean
satisfies { al, ar, ao, v } g =
  let
    c1 = al `hadamard` ar == ao

    lhs = (innerProduct al <$> g.wl)
      `addVec` (innerProduct ar <$> g.wr)
      `addVec` (innerProduct ao <$> g.wo)
      `addVec` (innerProduct v <$> g.wv)
      `addVec` g.c

    c2 = all (eq zero) lhs
  in
    c1 && c2
  where
  innerProduct :: Array f -> Map Int f -> f
  innerProduct as bs =
    Arrat.foldlWithIndex
      ( \i acc a -> maybe acc (\b -> acc + mul a b) (Map.lookup i bs)
      )
      zero
      as
  hadamard = Array.zipWith mul
  addVec = zipWith add

-- | Convert Gates to tuple format for efficient FFI transfer
toGates
  :: forall f
   . PrimeField f
  => Gates f
  -> { q :: Int, n :: Int, m :: Int } -- q = constraints, n = multiplication gates, m = public inputs
  -> { dimensions :: { n :: Int, m :: Int, q :: Int }
     , weightsLeft :: Matrix f
     , weightsRight :: Matrix f
     , weightsOutput :: Matrix f
     , weightsAuxiliary :: Matrix f
     , constants :: Vector f
     }
toGates gates { q, n, m } =
  let
    paddedN = nextPowerOf2 n

    mapToEntries :: Map Int f -> Array (Entry f)
    mapToEntries sparseMap =
      map (\(Tuple i v) -> Entry (Tuple i v)) (Map.toUnfoldable $ Map.filter (\x -> x /= zero) sparseMap)

    mapToEntriesNeg :: Map Int f -> Array (Entry f)
    mapToEntriesNeg sparseMap =
      map (\(Tuple i v) -> Entry (Tuple i (negate v))) (Map.toUnfoldable $ Map.filter (\x -> x /= zero) sparseMap)

  in
    { dimensions: { n: paddedN, m, q }
    , weightsLeft: map mapToEntries gates.wl
    , weightsRight: map mapToEntries gates.wr
    , weightsOutput: map mapToEntries gates.wo
    , weightsAuxiliary: map mapToEntriesNeg gates.wv
    , constants:
        Array.filter (\(Entry (Tuple _ f)) -> f /= zero) $
          Array.mapWithIndex (\i c -> Entry (Tuple i (negate c))) gates.c
    }
  where
  nextPowerOf2 :: Int -> Int
  nextPowerOf2 k =
    let
      go power acc
        | acc >= n = acc
        | otherwise = go (power + 1) (acc * 2)
    in
      if k <= 1 then 1 else go 1 1

--------------------------------------------------------------------------------

newtype SortedR1CS f = SortedR1CS (Array (R1CS f))

sortR1CS :: forall f. PrimeField f => Array (R1CS f) -> SortedR1CS f
sortR1CS constraints =
  let
    toAffine (R1CS { left, right, output }) =
      { left: reduceToAffineExpression left
      , right: reduceToAffineExpression right
      , output: reduceToAffineExpression output
      }
    indexed = Array.mapWithIndex (\i c -> Tuple i (toAffine c)) constraints

    introducerOf :: Map Variable Int
    introducerOf = Map.fromFoldable $ do
      Tuple idx gate <- indexed
      var <- Set.toUnfoldable (introducedVars gate)
      pure (Tuple var idx)

    dependencies :: Array (Tuple Int (Set Int))
    dependencies = indexed <#> \(Tuple idx gate) ->
      let
        deps = Set.fromFoldable $ catMaybes $
          Set.toUnfoldable (neededVars gate) <#> \v -> Map.lookup v introducerOf
      in
        Tuple idx (Set.delete idx deps)

    order = topoSortIndices dependencies
  in
    SortedR1CS $ Array.mapMaybe (\idx -> Array.index constraints idx) order
  where
  topoSortIndices dependencies =
    let
      depsMap = Map.fromFoldable dependencies

      visit :: Set Int -> Int -> { visited :: Set Int, order :: Array Int } -> { visited :: Set Int, order :: Array Int }
      visit localVisited idx acc
        | Set.member idx acc.visited || Set.member idx localVisited = acc
        | otherwise =
            let
              deps = fromMaybe Set.empty (Map.lookup idx depsMap)
              localVisited' = Set.insert idx localVisited
              acc' = Array.foldl (\a d -> visit localVisited' d a) acc (Set.toUnfoldable deps)
            in
              { visited: Set.insert idx acc'.visited, order: Array.snoc acc'.order idx }

      result = foldl
        (\acc (Tuple idx _) -> visit Set.empty idx acc)
        { visited: Set.empty, order: [] }
        dependencies
    in
      result.order

  neededVars { left, right, output } =
    varsIfNonTrivial left <> varsIfNonTrivial right <> varsIfNonTrivial output
    where
    varsIfNonTrivial expr@(AffineExpression { terms })
      | isTrivial expr = Set.empty
      | otherwise = Set.fromFoldable (fst <$> terms)

  introducedVars { left, right, output } =
    Set.fromFoldable $ catMaybes
      [ trivialVar left
      , trivialVar right
      , trivialVar output
      ]
    where
    trivialVar expr@(AffineExpression { terms })
      | isTrivial expr = fst <$> Array.head terms
      | otherwise = Nothing

  isTrivial (AffineExpression { constant, terms }) =
    (isNothing constant || constant == Just zero) && Array.length terms == 1

type SparseMatrix f = Array (Map Int f)