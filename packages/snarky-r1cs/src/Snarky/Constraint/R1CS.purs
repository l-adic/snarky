module Snarky.Constraint.R1CS
  ( R1CS(..)
  , genWithAssignments
  , eval
  , Gates
  , Matrix
  , makeGates
  , evalGates
  , Witness
  , makeWitness
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (Except)
import Data.Array (fold, foldMap, mapWithIndex, zipWith)
import Data.Array as Array
import Data.Bifunctor (lmap, rmap)
import Data.Foldable (foldM)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromJust, fromMaybe, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (foldl)
import Data.Tuple (Tuple(..), snd)
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.CVar (AffineExpression(..), CVar, EvaluationError(..), Variable, const_, evalAffineExpression, getVariable, reduceToAffineExpression, scaleAffineExpression, subAffineExpression, sub_)
import Snarky.Circuit.CVar as CVar
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck.Gen (Gen)
import Type.Proxy (Proxy)

data R1CS f = R1CS (CVar f Variable) (CVar f Variable) (CVar f Variable)

genWithAssignments
  :: forall f
   . PrimeField f
  => Proxy f
  -> Gen
       { r1cs :: R1CS f
       , assignments :: Map Variable f
       }
genWithAssignments pf =
  Basic.genWithAssignments pf <#> \{ basic, assignments } ->
    { r1cs: Basic.fromBasic basic
    , assignments
    }

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> R1CS f
  -> m Boolean
eval lookup (R1CS l r o) = ado
  left <- CVar.eval lookup l
  right <- CVar.eval lookup r
  output <- CVar.eval lookup o
  in left * right == output

instance PrimeField f => Basic.BasicSystem f (R1CS f) where
  r1cs { left, right, output } = R1CS left right output
  boolean v = R1CS v v v
  equal a b = R1CS (const_ one) (sub_ a b) (const_ zero)

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
makeGates _cs =
  let
    cs = map r1csToGateConstraint _cs
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
        _cs
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

makeWitness
  :: forall f
   . PrimeField f
  => Map Variable f
  -> Array (R1CS f)
  -> Except (EvaluationError Variable) (Witness f)
makeWitness assignments cs =
  let
    mulGates =
      foldl
        ( \acc r1cs -> case r1csToGateConstraint r1cs of
            Linear _ -> acc
            Mul l r o -> acc `Array.snoc` { l, r, o }
        )
        mempty
        cs
    lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var assignments
    makeWire { l, r, o } = do
      al <- evalAffineExpression l lookup
      ar <- evalAffineExpression r lookup
      ao <- evalAffineExpression o lookup
      pure { al, ar, ao }

    v = snd <$> Map.toUnfoldable assignments

  in
    foldM
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
      <#> \{ al, ar, ao } -> { al, ar, ao, v }

evalGates
  :: forall f
   . PrimeField f
  => Witness f
  -> Gates f
  -> Boolean
evalGates { al, ar, ao, v } g =
  let
    c1 = al `hadamard` ar == ao
    c2 =
      let
        lhs = (innerProduct al <$> g.wl)
          `addVec` (innerProduct ar <$> g.wr)
          `addVec` (innerProduct ao <$> g.wo)

        rhs = (innerProduct v <$> g.wv) `addVec` g.c
      in
        lhs == rhs
  in
    c1 && c2
  where
  innerProduct as bs = Array.foldl (\acc (Tuple a b) -> acc + a * b) zero (Array.zip as bs)
  hadamard = Array.zipWith mul
  addVec = zipWith add