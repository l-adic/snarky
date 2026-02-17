module Snarky.Circuit.Kimchi.VarBaseMul
  ( scaleFast1
  , scaleFast2
  , scaleFast2'
  , splitFieldVar
  , splitField
  , joinField
  ) where

import Prelude

import Data.Foldable (foldl, traverse_)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import JS.BigInt as BigInt
import Prim.Int (class Add, class Mul)
import Safe.Coerce (coerce)
import Snarky.Circuit.Curves as EllipticCurve
import Snarky.Circuit.DSL (class CircuitM, BoolVar, EvaluationError(..), F(..), FVar, Snarky, addConstraint, assertEqual_, const_, exists, if_, read, readCVar, throwAsProver, unpackPure)
import Snarky.Circuit.DSL as Bits
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Constraint.Kimchi.VarBaseMul (ScaleRound)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromInt, toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (Type1(..), Type2(..))

varBaseMul
  :: forall t m n @nChunks @bitsUsed l f
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
    -- Take bottom bitsUsed LSB bits, then reverse to MSB-first within range.
    -- Matches OCaml's: List.take num_bits |> Array.of_list_rev_map
    lsbBitsUsed = Vector.take @bitsUsed lsbBits

    msbBitsUsed :: Vector bitsUsed (FVar f)
    msbBitsUsed = coerce $ Vector.reverse lsbBitsUsed

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
  :: forall t m n @nChunks @bitsUsed f _l
   . FieldSizeInBits f n
  => Add bitsUsed _l n
  => Mul 5 nChunks bitsUsed
  => Reflectable nChunks Int
  => Reflectable bitsUsed Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> Type1 (FVar f)
  -> Snarky (KimchiConstraint f) t m
       (AffinePoint (FVar f))
scaleFast1 p t = do
  { g } <- varBaseMul @nChunks @bitsUsed p t
  pure g

{-
scaleFast2 g a ~ scalarMul (fromShifted a) g

where ~ means that the LHS is a circuit which computes
the pure function on the RHS. This is used when the modulus
of the scalar field is larger than the modulus of the circuit field.
-}
scaleFast2
  :: forall t m f n @nChunks sDiv2Bits @bitsUsed _l
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
  { g, lsbBits } <- varBaseMul @nChunks @bitsUsed base (Type1 sDiv2)
  let { after } = Vector.splitAt @sDiv2Bits lsbBits
  traverse_ (\x -> assertEqual_ x (const_ zero)) after
  if_ sOdd g =<< do
    negBase <- EllipticCurve.negate base
    { p } <- addComplete g negBase
    pure p

-- | Split a field element into parity decomposition and constrain it.
-- | Witnesses (sDiv2, sOdd) where s = 2*sDiv2 + sOdd, then asserts the relationship.
splitFieldVar
  :: forall t m f c
   . CircuitM f c t m
  => FVar f
  -> Snarky c t m ({ sDiv2 :: (FVar f), sOdd :: (BoolVar f) })
splitFieldVar s = do
  res@{ sDiv2, sOdd } <- exists do
    F sVal <- readCVar s
    pure $ splitField (F sVal)
  assertEqual_ s =<< do
    pure (const_ $ fromInt 2) * pure sDiv2 + pure (coerce sOdd)
  pure res

splitField :: forall f. PrimeField f => F f -> { sDiv2 :: F f, sOdd :: Boolean }
splitField (F s) =
  let
    sBigInt = toBigInt s
    sOdd = BigInt.odd sBigInt
    sDiv2 = (if sOdd then s - one else s) / fromInt 2
  in
    { sDiv2: F sDiv2, sOdd }

joinField :: forall f. PrimeField f => { sDiv2 :: f, sOdd :: Boolean } -> f
joinField { sDiv2, sOdd } =
  let
    two = fromInt 2
  in
    two * sDiv2 + (if sOdd then one else zero)

{-
scaleFast2' g s ~ [s + 2^n] * g

Like scaleFast2 but takes a raw field element instead of a pre-split Type2.
Splits s into (sDiv2, sOdd) where s = 2*sDiv2 + sOdd (parity decomposition),
constrains the split, then delegates to scaleFast2 which adds the 2^n shift
via varBaseMul. This matches OCaml's scale_fast2'.
-}
scaleFast2'
  :: forall t m f n @nChunks sDiv2Bits bitsUsed _l
   . FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits 1 n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> FVar f
  -> Snarky (KimchiConstraint f) t m
       (AffinePoint (FVar f))
scaleFast2' base s = do
  split <- splitFieldVar s
  scaleFast2 @nChunks @bitsUsed base (Type2 split)
