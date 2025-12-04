module Snarky.Backend.Bulletproof.Gate where

--  ( GateConstraint(..)
--  , Matrix
--  , MulGate
--  , Witness
--  , makeGates
--  , makeMulGate
--  , r1csToGateConstraint
--  )
--  where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.State (State, evalState, get, modify_, put)
import Data.Array (fold, mapWithIndex, replicate, zipWith)
import Data.Array as Array
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, over, un)
import Data.Traversable (foldl, for)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (Tuple(..))
import Debug (trace, traceM)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.CVar (AffineExpression(..), CVar, EvaluationError(..), Variable, reduceToAffineExpression)
import Snarky.Circuit.CVar as CVar
import Snarky.Constraint.R1CS (R1CS(..))
import Snarky.Curves.Class (class PrimeField)

newtype GateIndex = GateIndex Int

derive instance Eq GateIndex
derive instance Ord GateIndex
derive newtype instance Show GateIndex

derive instance Newtype GateIndex _

data Placement = L | R | O | V | C

type S f =
  { currentIndex :: GateIndex
  , oMap :: Map Variable { index :: GateIndex, placement :: Placement, coeff :: f }
  }

initS :: forall f. S f
initS = { currentIndex: GateIndex 0, oMap: Map.empty }

freshGateIndex :: forall f. State (S f) GateIndex
freshGateIndex = do
  s@{ currentIndex } <- get
  put s { currentIndex = over GateIndex (add 1) currentIndex }
  pure currentIndex

newtype GateExpression f = GateExpression (Array { index :: GateIndex, coeff :: f, placement :: Placement })

derive newtype instance Semigroup (GateExpression f)
derive newtype instance Monoid (GateExpression f)

makeGateExpression
  :: forall f
   . PrimeField f
  => GateIndex
  -> R1CS f
  -> State (S f) (Array (GateExpression f))
makeGateExpression baseIndex c@(R1CS { left, right, output }) = do
  traceM $ "makeGateExpression: " <> show baseIndex
  traceM $ show  c
  let
    g :: Int -> Placement -> CVar f Variable -> State (S f) (GateExpression f)
    g offset placement cvar = do
      let
        AffineExpression { constant, terms } = reduceToAffineExpression cvar
        index = over GateIndex (add offset) baseIndex
        constantTerm = constant <#> \c -> GateExpression [ { index, placement: C, coeff: c } ]
      xs <- case List.fromFoldable terms of
        List.Nil -> pure $
          GateExpression
            [ { index, placement, coeff: one } ]
        List.Cons (Tuple _ f) List.Nil | f == zero -> pure $
          GateExpression
            [ { index, placement, coeff: one }
            ]
        List.Cons (Tuple v f) List.Nil | f /= zero -> do
          { oMap } <- get
          case Map.lookup v oMap of
            Nothing -> do
              modify_ \s ->
                s { oMap = Map.insert v { index, placement, coeff: recip f } s.oMap }
              pure $ GateExpression []
            Just x -> pure $
              GateExpression
                [ { index, placement, coeff: f }
                , x {coeff = -x.coeff}
                ]
        _ -> GateExpression <$> do
          { oMap } <- get
          prev <- for terms \(Tuple v f) -> do
            case Map.lookup v oMap of
              Nothing -> unsafeCrashWith "Shit"
              Just x -> pure x { coeff = -f * x.coeff }
          pure $ Array.cons { index, placement, coeff: one } prev
      pure $ maybe xs (\x -> x <> xs) constantTerm
  l <- g 0 L left
  r <- g 1 R right
  o <- g 2 O output
  pure [ l, r, o ]

gateExpressionToRow
  :: forall f
   . PrimeField f
  => GateExpression f
  -> R f
gateExpressionToRow (GateExpression terms) = trace ("get expression to row") \_ -> trace terms \_ ->
  let
    r = 
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
  in
    r { wv = map negate r.wv, c = negate r.c }

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
     , constraints :: Array (R1CS f)
     }
  -> Gates f
makeGates { publicInputs, constraints } =
    let

      publicInputIndices = Map.fromFoldable $ 
        mapWithIndex 
          ( \i var -> 
            Tuple var {index: GateIndex i, placement: V, coeff: one}
          ) 
          publicInputs

      f :: Int -> R1CS f -> State (S f) (Array (R f))
      f i c = map gateExpressionToRow <$> makeGateExpression (GateIndex i) c 

      rows :: Array (R f)
      rows = fold $ evalState (traverseWithIndex f constraints) (initS {oMap = publicInputIndices})
    in
    trace (show rows) \_ ->
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
     , constraints :: Array (R1CS f)
     , publicInputs :: Array Variable
     }
  -> m (Witness f)
makeWitness { assignments, constraints, publicInputs } = do
  -- 1. Construct v (Public Inputs)
  v <- for publicInputs \var ->
    case Map.lookup var assignments of
      Nothing -> throwError $ MissingVariable var
      Just val -> pure val

  let lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var assignments

  -- 2. Construct Gate Wires (al, ar, ao)
  gateWires <- for constraints \(R1CS { left, right, output }) -> do
    lVal <- CVar.eval lookup left
    rVal <- CVar.eval lookup right

    -- In Bulletproofs, ao is DEFINED as al * ar.
    let oValCalculated = lVal * rVal

    -- However, we must ensure this matches the assignment provided 
    -- for the output variable/expression to ensure consistency.
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

    rhs = (innerProduct v <$> g.wv) `addVec` g.c

    c2 = lhs == rhs
  in
    c1 && c2
  where
  innerProduct as bs = Array.foldl (\acc (Tuple a b) -> acc + a * b) zero (Array.zip as bs)
  hadamard = Array.zipWith mul
  addVec = zipWith add