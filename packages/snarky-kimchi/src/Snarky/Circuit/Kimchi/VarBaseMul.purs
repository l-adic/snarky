module Snarky.Circuit.Kimchi.VarBaseMul
  ( scaleFast1
  , scaleFast2
  ) where

import Prelude

import Data.Foldable (foldl, traverse_)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Prim.Int (class Add, class Mul)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (EvaluationError(..))
import Snarky.Circuit.Curves as EllipticCurve
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky, addConstraint, assertEqual_, const_, exists, if_, read, readCVar, throwAsProver)
import Snarky.Circuit.DSL as Bits
import Snarky.Circuit.DSL.Bits (unpackPure)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Circuit.Types (BoolVar, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Constraint.Kimchi.VarBaseMul (ScaleRound)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (Type1(..), Type2(..))

varBaseMul
  :: forall t m @n bitsUsed l @nChunks f
   . FieldSizeInBits f n
  => Add bitsUsed l n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> Type1 (FVar f)
  -> Snarky (KimchiConstraint f) t m
       { g :: AffinePoint (FVar f)
       , lsbBits :: Vector n (FVar f)
       }
varBaseMul base (Type1 t) = do
  lsbBits <- exists do
    F vVal <- readCVar t
    pure $ unpackPure vVal
  { p } <- addComplete base base
  let
    msbBits :: Vector n (FVar f)
    msbBits = coerce $ Vector.reverse lsbBits

    msbBitsUsed = Vector.take @bitsUsed msbBits

    chunks :: Vector nChunks (Vector 5 (FVar f))
    chunks = Vector.chunks @5 msbBitsUsed
  Tuple rounds_rev { nAccPrev: nAcc, acc: g } <- mapAccumM
    ( \s bs -> do
        nAcc <- exists do
          nAccPrevVal :: F f <- readCVar s.nAccPrev
          bsVal <- read @(Vector _ _) bs
          pure $ foldl (\a b -> double a + b) nAccPrevVal bsVal
        Tuple accs slopes <- Vector.unzip <<< fst <$> do
          mapAccumM
            ( \a b -> exists do
                { x: xAcc, y: yAcc } <- read @(AffinePoint _) a
                bVal <- readCVar b
                { x: xBase, y: yBase } <- read @(AffinePoint _) base
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
          ( { accs: s.acc :< accs
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
  addConstraint $ KimchiVarBaseMul $ Vector.toUnfoldable rounds
  assertEqual_ nAcc t
  pure { g, lsbBits: coerce lsbBits }
  where
  double x = x + x

{-
scaleFast1 g a ~ scalarMul (fromShifted a) g

where ~ means that the LHS is a circuit which computes
the pure function on the RHS. This is used when the modulus
of the scalar field is smaller than the modulus of the circuit field.
-}
scaleFast1
  :: forall t m n @nChunks f
   . FieldSizeInBits f n
  => Add n 0 n -- trivial but required for some dumb reason
  => Mul 5 nChunks n
  => Reflectable nChunks Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> Type1 (FVar f)
  -> Snarky (KimchiConstraint f) t m
       (AffinePoint (FVar f))
scaleFast1 p t = do
  { g } <- varBaseMul @n @nChunks p t
  pure g

{-
scaleFast2 g a ~ scalarMul (fromShifted a) g

where ~ means that the LHS is a circuit which computes
the pure function on the RHS. This is used when the modulus
of the scalar field is larger than the modulus of the circuit field.
-}
scaleFast2
  :: forall t m f n @nChunks sDiv2Bits bitsUsed _l
   . FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits 1 n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> Type2 (FVar f) (BoolVar f)
  -> Snarky (KimchiConstraint f) t m
       (AffinePoint (FVar f))
scaleFast2 base (Type2 { sDiv2, sOdd }) = do
  { g, lsbBits } <- varBaseMul @n @nChunks base (Type1 sDiv2)
  let { after } = Vector.splitAt @sDiv2Bits lsbBits
  traverse_ (\x -> assertEqual_ x (const_ zero)) after
  if_ sOdd g =<< do
    negBase <- EllipticCurve.negate base
    { p } <- addComplete g negBase
    pure p
