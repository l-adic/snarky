module Snarky.Backend.Bulletproof.Gate
  ( Gates
  , Matrix
  , makeGates
  , eval
  , MulGate
  , makeMulGates
  , Witness
  , makeWitness
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Data.Array (zipWith)
import Data.Array as Array
import Data.Bifunctor (lmap, rmap)
import Data.Foldable (fold, foldM, foldMap)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromJust, fromMaybe, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (foldl)
import Data.Tuple (Tuple(..), snd)
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.CVar (AffineExpression(..), CVar, EvaluationError(..), Variable, evalAffineExpression, getVariable, reduceToAffineExpression, scaleAffineExpression, subAffineExpression)
import Snarky.Constraint.R1CS (R1CS(..))
import Snarky.Curves.Class (class PrimeField)

data GateConstraint f
  = Mul (AffineExpression f) (AffineExpression f) (AffineExpression f)
  | Linear (AffineExpression f)

r1csToGateConstraint
  :: forall f
   . PrimeField f
  => R1CS f
  -> GateConstraint f
r1csToGateConstraint (R1CS _l _r _o) =
  let
    l@(AffineExpression { constant: constantL, terms: termsL }) = reduceToAffineExpression _l
    r@(AffineExpression { constant: constantR, terms: termsR }) = reduceToAffineExpression _r
    o = reduceToAffineExpression _o
  in
    if Array.null termsL then Linear $ (scaleAffineExpression (fromMaybe zero constantL) r) `subAffineExpression` o
    else if Array.null termsR then Linear $ (scaleAffineExpression (fromMaybe zero constantR) l) `subAffineExpression` o
    else Mul l r o

-- m_{i,j} = m !! i !! j
-- so a matrix is an array of rows
type Matrix f = Array (Array f)

type Gates f =
  { wl :: Matrix f
  , wr :: Matrix f
  , wo :: Matrix f
  , wv :: Matrix f
  , c :: Array f
  }

makeGates
  :: forall f
   . PrimeField f
  => Array (R1CS f)
  -> Gates f
makeGates constraints =
  let
    cs = map r1csToGateConstraint constraints

    Tuple mulGates linearGates =
      Array.foldl
        ( \acc g ->
            case g of
              Linear c -> rmap (flip Array.snoc c) acc
              Mul l r o -> lmap (flip Array.snoc { l, r, o }) acc
        )
        mempty
        cs
    nMuls = Array.length mulGates
    zeroRow = Array.replicate nMuls (zero @f)

    addMulGate index { l: AffineExpression l, r: AffineExpression r, o: AffineExpression o } =
      let
        oneHot = unsafePartial $ fromJust $ Array.updateAt index one $ Array.replicate nMuls zero
      in
        { wl: [ oneHot, zeroRow, zeroRow ]
        , wr: [ zeroRow, oneHot, zeroRow ]
        , wo: [ zeroRow, zeroRow, oneHot ]
        , wv: [ toDenseRow l.terms, toDenseRow r.terms, toDenseRow o.terms ]
        , c:
            let
              orZero = fromMaybe zero
            in
              [ orZero l.constant, orZero r.constant, orZero o.constant ]
        }

    addLinearGate (AffineExpression e) =
      { wl: [ zeroRow ]
      , wr: [ zeroRow ]
      , wo: [ zeroRow ]
      , wv: [ toDenseRow e.terms ]
      , c: [ fromMaybe zero e.constant ]
      }
  in
    fold $ mapWithIndex addMulGate mulGates <> map addLinearGate linearGates

  where
  vars :: Set Variable
  vars =
    let
      collectVariables :: CVar f Variable -> Set Variable
      collectVariables = foldl (flip Set.insert) Set.empty
    in
      foldMap
        ( \(R1CS l r o) ->
            foldMap collectVariables [ l, r, o ]
        )
        constraints
  nVars = Set.size vars

  toDenseRow :: Array (Tuple Variable f) -> Array f
  toDenseRow as =
    Array.updateAtIndices (map (lmap getVariable) as) $
      Array.replicate nVars zero

type Witness f =
  { al :: Array f
  , ar :: Array f
  , ao :: Array f
  , v :: Array f
  }

type MulGate f =
  { l :: AffineExpression f
  , r :: AffineExpression f
  , o :: AffineExpression f
  }

makeMulGates
  :: forall f
   . PrimeField f
  => Array (R1CS f)
  -> Array (MulGate f)
makeMulGates cs =
  foldl
    ( \acc r1cs -> case r1csToGateConstraint r1cs of
        Linear _ -> acc
        Mul l r o -> acc `Array.snoc` { l, r, o }
    )
    mempty
    cs

makeWitness
  :: forall f m
   . PrimeField f
  => MonadThrow (EvaluationError f) m
  => { assignments :: Map Variable f
     , mulGates :: Array (MulGate f)
     }
  -> m (Witness f)
makeWitness { assignments, mulGates } =
  let
    lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var assignments
    makeWire { l, r, o } = do
      al <- evalAffineExpression l lookup
      ar <- evalAffineExpression r lookup
      ao <- evalAffineExpression o lookup
      pure { al, ar, ao }
    v = snd <$> Map.toUnfoldable assignments
  in
    ( foldM
        ( \acc m ->
            makeWire m <#> \wire ->
              acc
                { al = acc.al `Array.snoc` wire.al
                , ar = acc.ar `Array.snoc` wire.ar
                , ao = acc.ao `Array.snoc` wire.ao
                }
        )
        { al: mempty, ar: mempty, ao: mempty }
        mulGates
    ) <#> \{ al, ar, ao } ->
      { al, ar, ao, v }

eval
  :: forall f
   . PrimeField f
  => Witness f
  -> Gates f
  -> Boolean
eval { al, ar, ao, v } g =
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