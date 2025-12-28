module Snarky.Circuit.Kimchi.VarBaseMul
  ( scaleFast1
  , scaleFast2
  , class DivMod
  ) where

import Prelude

import Control.Monad.State (StateT(..), runStateT)
import Data.Foldable (foldl, traverse_)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..), fst)
import JS.BigInt as BigInt
import Prim.Int (class Mul, class Add, class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (EvaluationError(..))
import Snarky.Circuit.Curves as EllipticCurve
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky, addConstraint, assertEqual_, const_, exists, read, readCVar, throwAsProver)
import Snarky.Circuit.DSL as Bits
import Snarky.Circuit.DSL.Bits (unpackPure)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Types (FVar, BoolVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Constraint.Kimchi.VarBaseMul (ScaleRound)
import Snarky.Curves.Class (class FieldSizeInBits, fromInt, toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Snarky.Types.Shifted (Type1(..), Type2(..))
import Type.Proxy (Proxy(..))

varBaseMul
  :: forall t m n bitsUsed l k f
   . FieldSizeInBits f n
  => Add bitsUsed l n
  => Mul 5 k bitsUsed
  => Reflectable bitsUsed Int
  => CircuitM f (KimchiConstraint f) t m
  => Proxy k
  -> Proxy bitsUsed
  -> AffinePoint (FVar f)
  -> Type1 (FVar f)
  -> Snarky (KimchiConstraint f) t m
       { g :: AffinePoint (FVar f)
       , lsbBits :: Vector n (FVar f)
       }
varBaseMul _ pbu base (Type1 t) = do
  lsbBits :: Vector n (BoolVar f) <- exists do
    F vVal <- readCVar t
    pure $ unpackPure vVal
  { p } <- addComplete base base
  let
    msbBits :: Vector n (FVar f)
    msbBits = coerce $ Vector.reverse lsbBits

    msbBitsUsed = Vector.take pbu msbBits

    chunks :: Vector k (Vector 5 (FVar f))
    chunks = Vector.chunks (Proxy @5) msbBitsUsed
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
  pure { g, lsbBits: coerce lsbBits }
  where
  double x = x + x

scaleFast1
  :: forall t m n @k f
   . FieldSizeInBits f n
  => Add n 0 n -- trivial but required for some dumb reason
  => Mul 5 k n
  => Reflectable k Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> Type1 (FVar f)
  -> Snarky (KimchiConstraint f) t m
       (AffinePoint (FVar f))
scaleFast1 p t = do
  { g } <- varBaseMul (Proxy @k) (Proxy @n) p t
  pure g

scaleFast2'
  :: forall t m f @n @nChunks sDiv2Bits bitsUsed _l
   . FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits 1 n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> Type2 (FVar f)
  -> BoolVar f
  -> Snarky (KimchiConstraint f) t m
       (AffinePoint (FVar f))
scaleFast2' base (Type2 sDiv2) sOdd = do
  { g, lsbBits } <- varBaseMul (Proxy @nChunks) (Proxy @bitsUsed) base (Type1 sDiv2)
  let { after } = Vector.splitAt (Proxy @sDiv2Bits) lsbBits
  traverse_ (\x -> assertEqual_ x (const_ zero)) after
  EllipticCurve.if_ sOdd g =<< do
    negBase <- EllipticCurve.negate base
    { p } <- addComplete g negBase
    pure p

{-

  let scale_fast2' (type scalar_field)
      (module Scalar_field : Scalar_field_intf
        with type Constant.t = scalar_field ) g (s : Scalar_field.t) ~num_bits =
    let ((s_div_2, s_odd) as s_parts) =
      with_label __LOC__ (fun () ->
          exists
            Typ.(Scalar_field.typ * Boolean.typ)
            ~compute:
              As_prover.(
                fun () ->
                  let s = read Scalar_field.typ s in
                  let open Scalar_field.Constant in
                  let s_odd = Bigint.test_bit (to_bigint s) 0 in
                  ((if s_odd then s - one else s) / of_int 2, s_odd)) )
    in

    (* In this case, it's safe to use this field to compute

       2 s_div_2 + b

       in the other field. *)
    with_label __LOC__ (fun () ->
        Field.Assert.equal Field.((of_int 2 * s_div_2) + (s_odd :> Field.t)) s ) ;
    scale_fast2 g (Pickles_types.Shifted_value.Type2.Shifted_value s_parts)
      ~num_bits

-}
scaleFast2
  :: forall t m f @n @nChunks sDiv2Bits bitsUsed _l
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
scaleFast2 base s = do
  { sDiv2, sOdd } <- exists do
    sVal <- readCVar s
    let
      sBigInt = toBigInt sVal
      sOdd = BigInt.odd sBigInt
    pure
      { sDiv2: (if sOdd then sVal - one else sVal) / fromInt 2
      , sOdd: BigInt.odd sBigInt
      }
  assertEqual_ s =<< do
    pure (const_ $ fromInt 2) * pure sDiv2 + pure (coerce sOdd)
  scaleFast2' @n @nChunks base (Type2 sDiv2) sOdd

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

-- quotient + remainder = numerator / denominator
class (Compare 0 denominator LT) <= DivMod (numerator :: Int) (denominator :: Int) (quotient :: Int) (remainder :: Int) | numerator denominator -> quotient remainder

instance
  ( Compare 0 denominator LT
  , Add quotient remainder k
  , Mul denominator k numerator
  ) =>
  DivMod numerator denominator quotient remainder