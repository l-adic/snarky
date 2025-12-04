module Snarky.Backend.Bulletproof.Gate
  ( Matrix
  , Gates
  , makeGates
  , emptyGates
  , gatesInfo
  , SortedR1CS
  , sortR1CS
  , Witness
  , makeWitness
  , satisfies
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.State (State, evalState, get, modify_)
import Data.Array (all, catMaybes, fold, mapWithIndex, replicate, zipWith)
import Data.Array as Array
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
              pure $ GateExpression []
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
        case term.placement of
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

type Matrix f = Array (Array f)

type Gates f =
  { wl :: Matrix f
  , wr :: Matrix f
  , wo :: Matrix f
  , wv :: Matrix f
  , c :: Array f
  }

dim :: forall f. Matrix f -> Tuple Int Int
dim m =
  let
    nCols =
      case Array.uncons m of
        Just { head } -> Array.length head
        Nothing -> 0
    nRows = Array.length m
  in
    Tuple nRows nCols

gatesInfo :: forall f. Gates f -> String
gatesInfo gs = Array.intercalate "\n"
  [ "dim W_l: " <> formatDim (dim gs.wl)
  , "dim W_r: " <> formatDim (dim gs.wr)
  , "dim W_o: " <> formatDim (dim gs.wo)
  , "dim W_v: " <> formatDim (dim gs.wv)
  , "dim c: " <> (show $ Array.length gs.c) <> " x 1"

  ]
  where
  formatDim :: Tuple Int Int -> String
  formatDim (Tuple r c) = show r <> " x " <> show c

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
    let

      toMatrixRow :: Int -> Map Int f -> Array f
      toMatrixRow nCols m =
        Array.updateAtIndices (Map.toUnfoldable m :: Array (Tuple Int f))
          (replicate nCols zero)
      q = Array.length rows
      _m = Array.length publicInputs
    in
      foldl
        ( \acc r ->
            acc
              { wl = acc.wl `Array.snoc` toMatrixRow q r.wl
              , wr = acc.wr `Array.snoc` toMatrixRow q r.wr
              , wo = acc.wo `Array.snoc` toMatrixRow q r.wo
              , wv = acc.wv `Array.snoc` toMatrixRow _m r.wv
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
  innerProduct as bs = Array.foldl (\acc (Tuple a b) -> acc + a * b) zero (Array.zip as bs)
  hadamard = Array.zipWith mul
  addVec = zipWith add

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