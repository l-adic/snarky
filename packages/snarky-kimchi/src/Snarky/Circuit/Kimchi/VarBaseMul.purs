module Snarky.Circuit.Kimchi.VarBaseMul where

import Prelude

import Control.Monad.State (StateT(..), runStateT)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..), fst)
import Prim.Int (class Mul)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (EvaluationError(..))
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky, addConstraint, assertEqual_, const_, exists, read, readCVar, throwAsProver)
import Snarky.Circuit.DSL as Bits
import Snarky.Circuit.DSL.Bits (unpackPure)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Types (FVar, BoolVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Constraint.Kimchi.VarBaseMul (ScaleRound)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Snarky.Types.Shifted (Type1(..))
import Type.Proxy (Proxy(..))

varBaseMul
  :: forall t m n k f
   . FieldSizeInBits f n
  => Mul 5 k n
  => Reflectable k Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> Type1 (FVar f)
  -> Snarky (KimchiConstraint f) t m
       { g :: AffinePoint (FVar f)
       , lsb_bits :: Vector n (BoolVar f)
       , k :: Proxy k
       }
varBaseMul base (Type1 t) = do
  lsb_bits :: Vector n (BoolVar f) <- exists do
    F vVal <- readCVar t
    pure $ unpackPure vVal
  { p } <- addComplete base base
  let
    msb_fbits :: Vector n (FVar f)
    msb_fbits = coerce $ Vector.reverse lsb_bits

    chunks :: Vector k (Vector 5 (FVar f))
    chunks = Vector.chunks (Proxy @5) msb_fbits
  Tuple rounds_rev { nAccPrev: nAcc, acc: g } <- mapAccumM
    ( \s bs -> do
        nAcc <- exists do
          nAccPrevVal :: F f <- readCVar s.nAccPrev
          bsVal :: Vector 5 (F f) <- read bs
          pure $ foldl (\a b -> double a + b) nAccPrevVal bsVal
        Tuple accs slopes <- Vector.unzip <<< fst <$> do
          mapAccumM
            ( \a b -> exists do
                { x: xAcc, y: yAcc } :: AffinePoint _ <- read a
                bVal <- readCVar b
                { x: xBase, y: yBase } :: AffinePoint _ <- read base
                s1 <-
                  let
                    d = xAcc - xBase
                  in
                    if d == zero then throwAsProver $ DivisionByZero
                      { context: "varBaseMul"
                      , expression: Just "xAcc - xBase"
                      }
                    else pure $ (yAcc - (yBase * (double bVal - one))) / d
                let
                  s1Squared = s1 * s1
                  s2 = (double yAcc / (double xAcc + xBase - s1Squared)) - s1
                  xRes = (xBase + (s2 * s2) - s1Squared)
                  yRes = (xAcc - xRes) * s2 - yAcc
                  a' = { x: xRes, y: yRes }
                pure $ Tuple (Tuple a' s1) a'
            )
            s.acc
            bs
        pure $ Tuple
          ( { accs: Vector.vCons s.acc accs
            , bits: bs
            , slopes
            , nPrev: s.nAccPrev
            , nNext: nAcc
            , base
            } :: ScaleRound f
          )
          { nAccPrev: nAcc, acc: Vector.last accs }

    )
    { nAccPrev: const_ zero, acc: p }
    chunks
  let rounds = Vector.reverse rounds_rev
  addConstraint $ KimchiVarBaseMul $ Vector.unVector rounds
  assertEqual_ nAcc t
  pure { g, lsb_bits: coerce lsb_bits, k: Proxy }
  where
  double x = x + x

mapAccumM
  :: forall m s t a b
   . Monad m
  => Traversable t
  => (s -> a -> m (Tuple b s))
  -> s
  -> t a
  -> m (Tuple (t b) s)
mapAccumM f initial xs = runStateT (traverse step xs) initial
  where
  step x = StateT (\s -> f s x)