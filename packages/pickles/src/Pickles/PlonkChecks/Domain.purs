-- | The domain-dependent scalars of `finalize_other_proof`, shared by the
-- | step and wrap verifiers: the negative powers of the domain generator and
-- | the permutation vanishing polynomial (OCaml `plonk_checks.ml`
-- | `scalars_env`), and the step side's known-domain selection and vanishing
-- | polynomial (OCaml `step_verifier.ml` `finalize_other_proof` and
-- | `pseudo.ml` `Pseudo.Domain.to_domain`).
module Pickles.PlonkChecks.Domain
  ( OmegaPowers
  , omegaPowers
  , zkPolynomial
  , knownDomainWhiches
  , knownDomainVanishingPolynomial
  , buildPow2PowsArray
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldr)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Pickles.Constants (zkRowsByDefault)
import Pickles.Pseudo as Pseudo
import Snarky.Circuit.DSL (class BasicSystem, BoolVar, FVar, Snarky, const_, equals_, inv_, label, mul_, seal, square_, sub_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, fromInt)

-- | `ω⁻¹`, `ω^{-(zkRows-1)}` and `ω^{-zkRows}` for the domain generator `ω`.
type OmegaPowers f =
  { omegaToMinus1 :: FVar f
  , omegaToZkPlus1 :: FVar f
  , omegaToZk :: FVar f
  }

-- | The negative generator powers (plonk_checks.ml:248-264): `ω⁻¹ = 1/gen`,
-- | `ω⁻² = ω⁻¹ · ω⁻¹` (OCaml's `square x = x * x`, an R1CS row), then
-- | `zkRows − 3` further multiplications by `ω⁻¹` (none at the default
-- | `zkRows = 3`) reaching `ω^{-(zkRows-1)}`, and one more for `ω^{-zkRows}`.
-- |
-- | Requires `zkRows ≥ 3` (kimchi's minimum, `zkRowsByDefault`); a smaller
-- | value has no `ω^{-(zkRows-1)}` distinct from the two rows above and is
-- | rejected, as OCaml's `Array.init` at a negative length raises.
omegaPowers
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => { generator :: FVar f, zkRows :: Int }
  -> Snarky f c r (OmegaPowers f)
omegaPowers { generator, zkRows }
  | zkRows < zkRowsByDefault = unsafeThrow $
      "Pickles.PlonkChecks.Domain.omegaPowers: zkRows = " <> show zkRows
        <> " is below kimchi's minimum "
        <> show zkRowsByDefault
  | otherwise =
      do
        omegaToMinus1 <- inv_ generator
        omegaToMinus2 <- mul_ omegaToMinus1 omegaToMinus1
        omegaToZkPlus1 <- go omegaToMinus1 omegaToMinus2 (zkRows - zkRowsByDefault)
        omegaToZk <- mul_ omegaToZkPlus1 omegaToMinus1
        pure { omegaToMinus1, omegaToZkPlus1, omegaToZk }
      where
      go omegaToMinus1 term i
        | i <= 0 = pure term
        | otherwise = do
            next <- mul_ term omegaToMinus1
            go omegaToMinus1 next (i - 1)

-- | The permutation vanishing polynomial at `ζ`,
-- | `(ζ − ω⁻¹)(ζ − ω^{-(zkRows-1)})(ζ − ω^{-zkRows})` (plonk_checks.ml:273-279):
-- | two rows.
zkPolynomial
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> OmegaPowers f
  -> Snarky f c r (FVar f)
zkPolynomial zeta { omegaToMinus1, omegaToZkPlus1, omegaToZk } = do
  t1 <- mul_ (zeta `sub_` omegaToMinus1) (zeta `sub_` omegaToZkPlus1)
  mul_ t1 (zeta `sub_` omegaToZk)

-- | Which known domain is the prev proof's: one `equals_` of the runtime
-- | `domain_log2` against each domain's, emitted last-to-first (OCaml's
-- | right-to-left `Vector.map`, step_verifier.ml:880-893), in domain order.
knownDomainWhiches
  :: forall nd f c r rd
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Vector nd { log2 :: Int | rd }
  -> Snarky f c r (Vector nd (BoolVar f))
knownDomainWhiches domainLog2Var domains = do
  rev <- traverse (\d -> equals_ (const_ (fromInt d.log2)) domainLog2Var) (Vector.reverse domains)
  pure (Vector.reverse rev)

-- | `ζⁿ − 1` for the selected known domain (`Pseudo.Domain.to_domain`'s
-- | `vanishing_polynomial`, pseudo.ml:118-127): the table `ζ^{2^i}` for
-- | `i` up to the largest domain's log2 by squaring, the entry at each
-- | domain's log2 selected by the which bits, minus one, sealed.
knownDomainVanishingPolynomial
  :: forall nd f r rd
   . PrimeField f
  => Reflectable nd Int
  => Vector nd (BoolVar f)
  -> Vector nd { log2 :: Int | rd }
  -> FVar f
  -> Snarky f (KimchiConstraint f) r (FVar f)
knownDomainVanishingPolynomial whiches domains zeta = do
  let maxLog2 = foldr max 0 (map _.log2 domains)
  pow2Pows <- buildPow2PowsArray zeta maxLog2
  -- every `log2 ≤ maxLog2`, so the index is always in range
  let pow2AtLog2 = map (\d -> fromMaybe (const_ zero) (Array.index pow2Pows d.log2)) domains
  masked <- Pseudo.mask whiches pow2AtLog2
  label "seal_domain_vanishing" $ seal (masked `sub_` const_ one)

-- | `[x, x², x⁴, …, x^(2^maxLog2)]` by `maxLog2` Square rows (`pseudo.ml:119-123`).
buildPow2PowsArray
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Int
  -> Snarky f c r (Array (FVar f))
buildPow2PowsArray x maxLog2 = go [ x ] maxLog2
  where
  go acc i
    | i <= 0 = pure acc
    | otherwise = case Array.last acc of
        Nothing -> pure acc -- unreachable: acc is non-empty
        Just lastV -> do
          sq <- square_ lastV
          go (Array.snoc acc sq) (i - 1)
