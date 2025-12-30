module Snarky.Circuit.Kimchi.EndoScale where

import Prelude

import Data.Array.NonEmpty (mapWithIndex)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Traversable (foldl)
import Data.Tuple (Tuple(..))
import Effect.Exception.Unsafe (unsafeThrow)
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, addConstraint, add_, assertEqual_, const_, exists, mul_, read, readCVar, scale_)
import Snarky.Circuit.DSL.Bits (unpackPure)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (class FieldSizeInBits, fromInt)
import Snarky.Data.Fin (unsafeFinite, getFinite)
import Snarky.Data.Vector (Vector, chunks, (!!))
import Snarky.Data.Vector as Vector

newtype ScalarChallenge f = ScalarChallenge f

toField
  :: forall f t m n _l
   . FieldSizeInBits f n
  => Add 128 _l n
  => CircuitM f (KimchiConstraint f) t m
  => ScalarChallenge (FVar f)
  -> FVar f
  -> Snarky (KimchiConstraint f) t m (FVar f)
toField (ScalarChallenge scalar) endo = do
  lsbBits :: Vector 128 (BoolVar f) <- exists do
    F vVal <- readCVar scalar
    pure $ Vector.take @128 $ unpackPure $ vVal
  let
    msbBits :: Vector 128 (FVar f)
    msbBits = coerce $ Vector.reverse lsbBits

    nibblesByRow :: Vector 8 (Vector 8 (FVar f))
    nibblesByRow =
      let
        f :: Vector 2 (FVar f) -> FVar f
        f v = (v !! unsafeFinite 0) `add_` scale_ (fromInt 2) (v !! unsafeFinite 1)
      in
        {-
          chunks @2 = [(b0, b1), (b2, b3) ..., (b127,128)]

          chunks @8 _ = [ [(b0,b1), ... (b14, b15)]
                        , [(b16, b17), .. (b30, b31)]
                        ,...
                        , [(b112, b113) ... (b126, b127)]
                        ]
        
        -}
        chunks @8 $ map f (chunks @2 msbBits)

  Tuple rowsRev { a, b, n } <- mapAccumM
    ( \st nibble -> do
        let
          double x = x + x
        { n8, a8, b8 } <- exists do
          xs :: Vector 8 (F f) <- read nibble
          { a: a0, b: b0, n: n0 } <- read @{ a :: F f, b :: F f, n :: F f } st
          let
            n8 = foldl (\acc x -> double (double acc) + x) n0 xs
            a8 = foldl (\acc x -> double acc + aF x) a0 xs
            b8 = foldl (\acc x -> double acc + bF x) b0 xs
          pure { n8, a8, b8 }
        pure $ Tuple
          { n0: st.n, a0: st.a, b0: st.b, xs: nibble, n8, a8, b8 }
          { n: n8, a: a8, b: b8 }
    )
    { a: const_ $ fromInt 2
    , b: const_ $ fromInt 2
    , n: const_ $ zero
    }
    nibblesByRow
  addConstraint $ KimchiEndoScale (Vector.reverse rowsRev)
  --assertEqual_ n scalar
  a `mul_` endo <#>
    add_ b

  where
  aF :: F f -> F f
  aF x
    | x == zero = zero
    | x == one = zero
    | x == fromInt 2 = -one
    | x == fromInt 3 = one
    | otherwise = unsafeThrow ("Unexpected aF application: " <> show x)

  bF :: F f -> F f
  bF x
    | x == zero = -one
    | x == one = one
    | x == fromInt 2 = zero
    | x == fromInt 3 = zero
    | otherwise = unsafeThrow ("Unexpected bF application: " <> show x)

{-

Fin n = [0,..,n-1]
Fin m = [0,..,m-1]

(n - 1) + (m - 1) = n + m - 1)


-}