-- | `unpack_full` + `lt_bitstring_value` — port of OCaml
-- | `Field.Checked.unpack_full` / `lt_bitstring_value` in
-- | `mina/src/lib/snarky/src/base/snark0.ml:404-483`.
-- |
-- | Plain `unpack_` only emits the boolean checks and the linear-
-- | combination assertion that the bits reconstruct the field
-- | element. That allows the prover to pick a non-canonical bit
-- | decomposition (any representative congruent mod `p` works), so
-- | the resulting LSB doesn't necessarily reflect the canonical
-- | integer parity. `unpack_full` adds a strict `lt_bitstring_value
-- | bits modulus_bits` check (in MSB-first orientation) to lock the
-- | decomposition to the canonical `< p` representative — the form
-- | `is_even` needs to be sound.
-- |
-- | The `lt_bitstring_value` algorithm builds a Binary AND/OR tree
-- | of bit comparisons (one node per bit, structured by the modulus
-- | bit pattern), folds adjacent same-typed nodes into N-ary lists,
-- | and evaluates leaves-first via `allBools`/`anyBools`.
module Snarky.Circuit.DSL.UnpackFull
  ( unpackFull
  ) where

import Prelude

import Data.Array as Array
import Data.List (List(..), (:))
import Data.List as List
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL.Assert (allBools, assert_)
import Snarky.Circuit.DSL.Bits (unpack_)
import Snarky.Circuit.DSL.Boolean (false_)
import Snarky.Circuit.DSL.Field (equals_, sum_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, not_, or_)
import Snarky.Circuit.Types (Bool(..), BoolVar, FVar)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, modulus)
import Type.Proxy (Proxy(..))

-- | `unpack_full x` — decompose `x` into `size_in_bits` LSB-first bits
-- | with the canonical `< modulus` check. Mirrors OCaml
-- | `Field.Checked.unpack_full` (snark0.ml:470-483).
unpackFull
  :: forall f c t m n
   . CircuitM f c t m
  => PrimeField f
  => FieldSizeInBits f n
  => Reflectable n Int
  => FVar f
  -> Snarky c t m (Vector n (BoolVar f))
unpackFull x = do
  bits <- unpack_ x (Proxy @n)
  -- lt_bitstring_value takes MSB-first; our bits are LSB-first.
  let msbBits = Array.reverse (Vector.toUnfoldable bits)
  let modBits = modulusBitsMsb @f @n
  lt <- ltBitstringValue msbBits modBits
  assert_ lt
  pure bits

-- | MSB-first bit decomposition of the field modulus, length
-- | `size_in_bits`. Computed once at module load.
modulusBitsMsb
  :: forall @f @n
   . PrimeField f
  => FieldSizeInBits f n
  => Reflectable n Int
  => Array Boolean
modulusBitsMsb =
  let
    n = reflectType (Proxy :: Proxy n)
    p = modulus @f
    one' = BigInt.fromInt 1
    -- LSB-first: bit i = (p >> i) & 1
    lsb = Array.range 0 (n - 1) <#> \i ->
      BigInt.and (BigInt.shr p (BigInt.fromInt i)) one' == one'
  in
    Array.reverse lsb

-- | Binary tree of bit comparisons. Internal representation for
-- | `lt_bitstring_value`'s recursive descent. Mirrors OCaml
-- | `Expr.Binary.t` (snark0.ml:408).
data Binary a = BLit a | BAnd a (Binary a) | BOr a (Binary a)

-- | N-ary normalisation that groups runs of same-typed nodes into a
-- | single list. Mirrors OCaml `Expr.Nary.of_binary` (snark0.ml:414).
data Nary a = NLit a | NAnd (List (Nary a)) | NOr (List (Nary a))

ofBinary :: forall a. Binary a -> Nary a
ofBinary = case _ of
  BLit x -> NLit x
  BAnd x (BAnd y t) -> NAnd (NLit x : NLit y : ofBinary t : Nil)
  BOr x (BOr y t) -> NOr (NLit x : NLit y : ofBinary t : Nil)
  BAnd x t -> NAnd (NLit x : ofBinary t : Nil)
  BOr x t -> NOr (NLit x : ofBinary t : Nil)

-- | OCaml `Boolean.any`
-- | (`mina/src/lib/snarky/src/base/utils.ml:231-243`):
-- |   * empty → `false_`
-- |   * `[b]` → `b`
-- |   * `[b1; b2]` → `b1 || b2` (1 R1CS, via `not ((not b1) && (not b2))`)
-- |   * `bs (n ≥ 3)` → `not (equal (sum bs) 0)` (~3 R1CS)
anyBools
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => Array (BoolVar f)
  -> Snarky c t m (BoolVar f)
anyBools bs = case Array.length bs of
  0 -> pure false_
  1 -> pure $ unsafePartial (Array.unsafeIndex bs 0)
  2 ->
    let
      b1 = unsafePartial (Array.unsafeIndex bs 0)
      b2 = unsafePartial (Array.unsafeIndex bs 1)
    in
      or_ b1 b2
  _ -> do
    -- OCaml `Boolean.any bs = not (equal (sum bs) 0)` for n≥3
    -- (utils.ml:239-243). Sum-first, constant-second.
    allZero <- equals_
      (sum_ (map (coerce :: BoolVar f -> FVar f) bs))
      (const_ (zero :: f))
    pure (not_ allZero)

evalNary
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => Nary (BoolVar f)
  -> Snarky c t m (BoolVar f)
evalNary = case _ of
  NLit x -> pure x
  NAnd xs -> do
    vs <- traverse evalNary xs
    allBools (Array.fromFoldable vs)
  NOr xs -> do
    vs <- traverse evalNary xs
    anyBools (Array.fromFoldable vs)
  where
  traverse :: forall a b. (a -> Snarky c t m b) -> List a -> Snarky c t m (List b)
  traverse f xs = case xs of
    Nil -> pure Nil
    h : rest -> do
      h' <- f h
      rest' <- traverse f rest
      pure (h' : rest')

-- | `lt_bitstring_value xs ys` — `xs < ys` for MSB-first bit-vectors
-- | of equal length. Direct port of OCaml `lt_bitstring_value`
-- | (`snark0.ml:404-468`): bit-by-bit compare, building a
-- | `Binary AND/OR` tree, normalising to N-ary, evaluating.
ltBitstringValue
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => Array (BoolVar f)
  -> Array Boolean
  -> Snarky c t m (BoolVar f)
ltBitstringValue xs0 ys0 =
  let
    xs = List.fromFoldable xs0
    ys = List.fromFoldable ys0
  in
    evalNary (ofBinary (ltBinary xs ys))

-- | Build the Binary comparison tree. Both inputs MSB-first, same
-- | length. Mirrors OCaml `lt_binary`.
ltBinary
  :: forall f
   . PrimeField f
  => List (BoolVar f)
  -> List Boolean
  -> Binary (BoolVar f)
ltBinary xs ys = case xs, ys of
  Nil, Nil -> BLit false_
  x : Nil, false : Nil -> BLit (case x of _ -> false_)
  x : Nil, true : Nil -> BLit (not_ x)
  x1 : _x2 : Nil, true : false : Nil -> BLit (not_ x1)
  _x1 : _x2 : Nil, false : false : Nil -> BLit false_
  x : xs', false : ys' -> BAnd (not_ x) (ltBinary xs' ys')
  x : xs', true : ys' -> BOr (not_ x) (ltBinary xs' ys')
  _, _ -> BLit false_
