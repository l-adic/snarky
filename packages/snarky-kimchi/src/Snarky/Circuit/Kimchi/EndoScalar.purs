module Snarky.Circuit.Kimchi.EndoScalar
  ( toField
  , toFieldPure
  , expandToEndoScalar
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Traversable (foldl)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, chunks, (!!))
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.CVar (CVar(..))
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, SizedF, Snarky, addConstraint, add_, assertEqual_, coerceViaBits, const_, exists, mul_, read, scale_, toBits)
import Snarky.Circuit.DSL as SizedF
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField, EndoScalar(..), endoScalar, fromInt)

-- | Circuit version of endomorphism scalar decomposition.
-- | Takes a 128-bit scalar challenge and endo constant, returns effective scalar.
-- | Computes `a * endo + b` where (a, b) is the GLV decomposition.
-- | The endo parameter is a raw field element — callers should unwrap
-- | the appropriate newtype (EndoBase or EndoScalar) depending on context.
-- | This is used in conjunction with EndoMul.
toField
  :: forall f t m n
   . FieldSizeInBits f n
  => CircuitM f (KimchiConstraint f) t m
  => Compare 128 n LT
  => SizedF 128 (FVar f)
  -> FVar f
  -> Snarky (KimchiConstraint f) t m (FVar f)
toField scalar endo = do
  -- Create nybble variables directly (like OCaml's `exists Field.typ`).
  -- Bits only exist in the prover — the EndoMulScalar gate constrains the nybbles.
  nibblesByRow :: Vector 8 (Vector 8 (FVar f)) <- exists do
    vVal :: SizedF 128 (F f) <- read scalar
    let
      msbBits = Vector.reverse $ toBits vVal

      pairs :: Vector 64 (Vector 2 Boolean)
      pairs = chunks @2 msbBits

      nybbles :: Vector 64 (F f)
      nybbles = map
        ( \v ->
            let
              b0 = v !! unsafeFinite 1
              b1 = v !! unsafeFinite 0
            in
              F $ boolToField b0 + fromInt 2 * boolToField b1
        )
        pairs
    pure $ chunks @8 nybbles

  Tuple rowsRev { a, b, n } <- mapAccumM
    ( \st nibble -> do
        let
          double x = x + x
        { n8, a8, b8 } <- exists do
          xs :: Vector 8 _ <- read nibble
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
  addConstraint $ KimchiEndoScalar rowsRev
  assertEqual_ n (SizedF.toField scalar)
  case endo of
    Const e -> pure $ scale_ e a `add_` b
    _ -> a `mul_` endo <#> add_ b

  where
  boolToField :: Boolean -> f
  boolToField b = if b then one else zero

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

-- | Pure/constant version of endomorphism scalar decomposition.
-- | Given a 128-bit scalar challenge and the endomorphism coefficient, computes
-- | `a * endo + b` where (a, b) is the decomposition of the scalar.
-- | The endo parameter is a raw field element — callers should unwrap
-- | the appropriate newtype (EndoBase or EndoScalar) depending on context.
toFieldPure
  :: forall f n
   . PrimeField f
  => FieldSizeInBits f n
  => Compare 128 n LT
  => SizedF 128 f
  -> f
  -> f
toFieldPure challenge endo =
  let
    bits :: Vector 128 Boolean
    bits = Vector.reverse $ toBits challenge

    chunked :: Vector 64 (Vector 2 Boolean)
    chunked = Vector.chunks @2 bits

    processChunk
      :: { a :: f, b :: f }
      -> Vector 2 Boolean
      -> { a :: f, b :: f }
    processChunk st v =
      let
        bitEven = v !! unsafeFinite 1
        bitOdd = v !! unsafeFinite 0
        s = if bitEven then one else -one
      in
        if bitOdd then { a: double st.a + s, b: double st.b }
        else { a: double st.a, b: double st.b + s }

    { a, b } = foldl processChunk { a: fromInt 2, b: fromInt 2 } chunked
  in
    a * endo + b
  where
  double x = x + x

expandToEndoScalar
  :: forall f f' n
   . HasEndo f f'
  => FieldSizeInBits f n
  => FieldSizeInBits f' n
  => PrimeField f'
  => Compare 128 n LT
  => SizedF 128 f
  -> f'
expandToEndoScalar f =
  let
    EndoScalar e = endoScalar @f @f'
  in
    toFieldPure (coerceViaBits f) e