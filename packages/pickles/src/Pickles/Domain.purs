-- | Pure-PureScript domain / vanishing / Lagrange-basis math over a
-- | `TwoAdicField`. Mirrors the Rust functions in
-- | `kimchi/src/circuits/polynomials/permutation.rs` and
-- | `kimchi/src/circuits/expr.rs:132 unnormalized_lagrange_basis`.
-- |
-- | Previously these were foreign-imported FFI calls into snarky-crypto
-- | (`pallas_*` / `vesta_*` variants in `Pickles.ProofFFI` and
-- | `Pickles.Linearization.FFI`). They are pure field arithmetic, so they
-- | belong in PureScript — the typeclass + `PrimeField` ops + the new
-- | `TwoAdicField` constants (`twoAdicRoot`, `twoAdicity`) are sufficient.
-- |
-- | Each helper is generic over the field `f`. Pickles' wrap-circuit math
-- | runs in `WrapField` (= Fq), step-circuit math in `StepField` (= Fp).
module Pickles.Domain
  ( domainGenerator
  , evalVanishesOnLastNRows
  , permutationVanishingPolynomial
  , vanishesOnZkAndPreviousRows
  , unnormalizedLagrangeBasis
  , bPoly
  , computeB0
  ) where

import Prelude

import Data.Array (length, (..))
import Data.Array as Array
import Data.Foldable (foldl, product)
import Data.Maybe (Maybe(..))
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Snarky.Curves.Class (class PrimeField, class TwoAdicField, pow, twoAdicRoot, twoAdicity)

-- | 2^log2-th primitive root of unity in `f`.
-- |
-- | Computed as `twoAdicRoot` squared `(twoAdicity - log2)` times — i.e.,
-- | raise the 2^twoAdicity-th root of unity to the 2^(twoAdicity - log2)
-- | power, which gives a 2^log2-th root by Lagrange's theorem.
domainGenerator :: forall @f. TwoAdicField f => Int -> f
domainGenerator log2 = repeatedSquare (twoAdicity @f - log2) (twoAdicRoot @f)
  where
  repeatedSquare :: Int -> f -> f
  repeatedSquare 0 acc = acc
  repeatedSquare k acc = repeatedSquare (k - 1) (acc * acc)

-- | Domain size as a `BigInt`, equal to `2^log2`.
domainSize :: Int -> BigInt
domainSize log2 = BigInt.shl one (BigInt.fromInt log2)

-- | Evaluates the polynomial
-- |   ∏_{j=0}^{n-1} (pt - ω^(domainSize - n + j))
-- | at `pt`, where ω is the 2^domainLog2-th root of unity.
-- |
-- | Direct port of `eval_vanishes_on_last_n_rows` in
-- | `kimchi/src/circuits/polynomials/permutation.rs:68`.
evalVanishesOnLastNRows :: forall @f. TwoAdicField f => Int -> Int -> f -> f
evalVanishesOnLastNRows _ 0 _ = one
evalVanishesOnLastNRows log2 n pt =
  let
    omega = domainGenerator @f log2
    startOffset = domainSize log2 - BigInt.fromInt n
    firstTerm = pow omega startOffset
    initial = { acc: pt - firstTerm, term: firstTerm }
    final = foldl
      ( \{ acc, term } _ ->
          let
            term' = term * omega
          in
            { acc: acc * (pt - term'), term: term' }
      )
      initial
      (1 .. (n - 1))
  in
    final.acc

-- | Permutation vanishing polynomial evaluated at `pt`:
-- |   (pt - ω^(n - zkRows)) * (pt - ω^(n - zkRows + 1)) * (pt - ω^(n - 1))
-- |
-- | Mirrors `eval_permutation_vanishing_polynomial`. Note that the
-- | snarky-crypto wrapper `pallas_permutation_vanishing_polynomial` /
-- | `vesta_permutation_vanishing_polynomial` calls
-- | `eval_vanishes_on_last_n_rows(log2, zk_rows, pt)` (no `+ 1`), which is
-- | what we mirror here.
permutationVanishingPolynomial
  :: forall @f
   . TwoAdicField f
  => { domainLog2 :: Int, zkRows :: Int, pt :: f }
  -> f
permutationVanishingPolynomial { domainLog2, zkRows, pt } =
  evalVanishesOnLastNRows @f domainLog2 zkRows pt

-- | The `VanishesOnZeroKnowledgeAndPreviousRows` term used in the
-- | linearization. Equals
-- |   `eval_vanishes_on_last_n_rows(log2, zk_rows + 1, pt)`
-- | — note the `+ 1`, in contrast to `permutationVanishingPolynomial`.
vanishesOnZkAndPreviousRows
  :: forall @f
   . TwoAdicField f
  => { domainLog2 :: Int, zkRows :: Int, pt :: f }
  -> f
vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt } =
  evalVanishesOnLastNRows @f domainLog2 (zkRows + 1) pt

-- | Unnormalized i-th Lagrange basis polynomial evaluated at `pt`:
-- |   (pt^n - 1) / (pt - ω^i),   n = 2^domainLog2
-- |
-- | When `zkRows > 0` the effective index is shifted:
-- |   actual = n - zkRows + offset
-- | mirroring snarky-crypto's `pallas_unnormalized_lagrange_basis`. Negative
-- | `actual` is handled by raising ω to `|actual|` and then inverting.
unnormalizedLagrangeBasis
  :: forall @f
   . TwoAdicField f
  => { domainLog2 :: Int, zkRows :: Int, offset :: Int, pt :: f }
  -> f
unnormalizedLagrangeBasis { domainLog2, zkRows, offset, pt } =
  let
    n = domainSize domainLog2
    -- The pre-shift logic mirrors kimchi's snarky-crypto wrapper: when
    -- zkRows is positive we treat `offset` as a delta from the
    -- "end-minus-zkRows" anchor.
    actualBig =
      if zkRows > 0 then n - BigInt.fromInt zkRows + BigInt.fromInt offset
      else BigInt.fromInt offset

    omega = domainGenerator @f domainLog2

    -- Compute ω^actual, handling negative powers via inversion. We compute
    -- ω^|actual| first (using `pow` which only accepts non-negative
    -- exponents on the field side), then invert if `actual` was negative.
    omegaPow =
      if actualBig < zero then
        recip (pow omega (negate actualBig))
      else
        pow omega actualBig

    ptN = pow pt n
  in
    (ptN - one) / (pt - omegaPow)

-- | IPA `b_poly` bilinear form for an `Array`-shaped challenge vector:
-- |   b(x) = ∏_{i=0}^{k-1} (1 + chals[i] * x^(2^(k-1-i)))
-- |
-- | Mirrors `poly-commitment/src/commitment.rs:416 b_poly`. The
-- | `Pickles.IPA` module has a `Vector d`-typed version of the same
-- | algorithm; this one is for callers that only have an unsized `Array`
-- | (e.g. the `ProofFFI.computeB0` shim).
bPoly :: forall f. PrimeField f => Array f -> f -> f
bPoly chals x =
  let
    k = length chals
  in
    case k of
      0 -> one
      _ ->
        let
          -- powTwos[i] = x^(2^i), computed by repeated squaring.
          powTwos = squaresFrom (k - 1) x
          terms = Array.mapWithIndex
            ( \i c -> case Array.index powTwos (k - 1 - i) of
                Just p -> one + c * p
                Nothing -> one -- unreachable: powTwos has length k
            )
            chals
        in
          product terms
  where
  squaresFrom :: Int -> f -> Array f
  squaresFrom n x0 =
    let
      go 0 acc = acc
      go i acc =
        let
          prev = case Array.last acc of
            Just p -> p
            Nothing -> x0 -- unreachable: acc starts non-empty
        in
          go (i - 1) (Array.snoc acc (prev * prev))
    in
      go n [ x0 ]

-- | `compute_b0` from snarky-crypto:
-- |   b_poly(chals, zeta) + evalscale * b_poly(chals, zetaOmega)
-- |
-- | Mirrors `pallas_compute_b0` / `vesta_compute_b0` in the Rust FFI,
-- | which evaluate the IPA `b` polynomial at zeta and zeta·ω and combine
-- | linearly with `evalscale`.
computeB0
  :: forall f
   . PrimeField f
  => { challenges :: Array f, zeta :: f, zetaOmega :: f, evalscale :: f }
  -> f
computeB0 { challenges, zeta, zetaOmega, evalscale } =
  bPoly challenges zeta + evalscale * bPoly challenges zetaOmega
