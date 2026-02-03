-- | IPA (Inner Product Argument) verification circuits.
-- |
-- | This module provides in-circuit implementations for verifying IPA opening proofs
-- | as used in the Kimchi/Pickles proving system.
-- |
-- | The key operations are:
-- | - Challenge extraction from L/R commitment pairs via Fiat-Shamir
-- | - bPoly: The challenge polynomial from the IPA protocol
-- | - computeB: Combines bPoly evaluations at zeta and zeta*omega
-- | - Verification that b = bPoly(challenges, zeta) + evalscale * bPoly(challenges, zetaOmega)
-- |
-- | Reference: wrap_verifier.ml in mina/src/lib/pickles
module Pickles.IPA
  ( -- Types
    LrPair
  , BPolyInput
  , ComputeBInput
  , BCorrectInput
  , BulletReduceInput
  -- Challenge polynomial
  , bPoly
  , bPolyCircuit
  -- Combined b evaluation
  , computeB
  , computeBCircuit
  -- Challenge extraction (returns 128-bit scalar challenges)
  , extractScalarChallenges
  -- Bullet reduce (lr_prod computation)
  , bulletReduce
  , bulletReduceCircuit
  -- Verification
  , bCorrect
  , bCorrectCircuit
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (fold, foldM, product)
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Pickles.Sponge (SpongeM, absorbPoint, squeezeScalarChallenge)
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, equals_, if_)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.EndoMul (endo, endoInv)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class PrimeField, class WeierstrassCurve, endoScalar, fromAffine, pow, scalarMul)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.SizedF (SizedF, coerceViaBits)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | A pair of L and R commitment points from an IPA round.
-- | These are curve points on the commitment curve (the "other" curve in the 2-cycle).
type LrPair f = { l :: AffinePoint f, r :: AffinePoint f }

-- | Input type for bPoly circuit tests.
type BPolyInput d f = { challenges :: Vector d f, x :: f }

-- | Input type for computeB and related circuits.
-- | Open row type to allow extension (e.g., adding expectedB for bCorrect).
type ComputeBInput d f r =
  { challenges :: Vector d f
  , zeta :: f
  , zetaOmega :: f
  , evalscale :: f
  | r
  }

-- | Input type for bCorrect / bCorrectCircuit.
-- | Extends ComputeBInput with the expected b value for verification.
type BCorrectInput n f = ComputeBInput n f (expectedB :: f)

-- | Input type for bulletReduce.
-- | Contains L/R pairs and the 128-bit scalar challenges.
type BulletReduceInput n f =
  { pairs :: Vector n (LrPair f)
  , challenges :: Vector n (SizedF 128 f)
  }

-------------------------------------------------------------------------------
-- | Challenge Polynomial (b_poly)
-------------------------------------------------------------------------------

-- | The challenge polynomial from the IPA protocol.
-- |
-- | Computes: b_poly(chals, x) = prod_{i=0}^{k-1} (1 + chals[i] * x^{2^{k-1-i}})
-- |
-- | This is "step 8: Define the univariate polynomial" of appendix A.2 of
-- | https://eprint.iacr.org/2020/499
-- |
-- | The `d` parameter is the number of IPA rounds (= domain log2), which equals
-- | the length of the challenges vector.
bPoly :: forall d f. Reflectable d Int => PrimeField f => Vector d f -> f -> f
bPoly chals x =
  let
    -- powTwos[i] = x^{2^i}
    powTwos :: Vector d f
    powTwos = Vector.generate \i ->
      pow x (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt (getFinite i)))

    -- Reverse to get [x^{2^{d-1}}, ..., x^4, x^2, x]
    -- Then zip with chals to compute (1 + chal * pow) for each pair
    terms :: Vector d f
    terms = Vector.zipWith (\c p -> one + c * p) chals (Vector.reverse powTwos)
  in
    product terms

-- | Circuit version of bPoly using iterative squaring (O(k) multiplications).
-- |
-- | For recursive verification where each multiplication is a constraint.
-- | Computes in a single pass over reversed challenges - no intermediate arrays.
bPolyCircuit
  :: forall d f c t m
   . Reflectable d Int
  => PrimeField f
  => CircuitM f c t m
  => BPolyInput d (FVar f)
  -> Snarky c t m (FVar f)
bPolyCircuit { challenges: chals, x } = do
  -- Iterate over reversed challenges: [c_{k-1}, ..., c_1, c_0]
  -- Powers naturally go x, x², x⁴, ... as we square each iteration
  -- term_i = 1 + c_{k-1-i} * x^{2^i}
  { product: prod } <- foldM
    ( \{ product: p, currPower } c -> do
        -- term = 1 + c * currPower
        cp <- pure c * pure currPower
        let term = CVar.add_ (CVar.const_ one) cp
        -- product *= term
        newProduct <- pure p * pure term
        -- currPower = currPower²
        newPower <- pure currPower * pure currPower
        pure { product: newProduct, currPower: newPower }
    )
    { product: CVar.const_ one, currPower: x }
    (Vector.reverse chals)

  pure prod

-------------------------------------------------------------------------------
-- | Combined b evaluation
-------------------------------------------------------------------------------

-- | Compute the combined b value at two evaluation points.
-- |
-- | This combines bPoly evaluations: b(zeta) + evalscale * b(zeta*omega)
-- |
-- | Corresponds to lines 201-210 of poly-commitment/src/ipa.rs in SRS::verify.
computeB
  :: forall d f
   . Reflectable d Int
  => PrimeField f
  => Vector d f
  -> { zeta :: f, zetaOmega :: f, evalscale :: f }
  -> f
computeB chals { zeta, zetaOmega, evalscale } =
  bPoly chals zeta + evalscale * bPoly chals zetaOmega

-- | Circuit version of computeB.
-- |
-- | Combines bPolyCircuit evaluations: b(zeta) + evalscale * b(zeta*omega)
computeBCircuit
  :: forall d f c t m r
   . Reflectable d Int
  => PrimeField f
  => CircuitM f c t m
  => ComputeBInput d (FVar f) r
  -> Snarky c t m (FVar f)
computeBCircuit { challenges, zeta, zetaOmega, evalscale } = do
  bZeta <- bPolyCircuit { challenges, x: zeta }
  bZetaOmega <- bPolyCircuit { challenges, x: zetaOmega }
  scaledB <- pure evalscale * pure bZetaOmega
  pure $ CVar.add_ bZeta scaledB

-------------------------------------------------------------------------------
-- | Challenge Extraction (In-Circuit)
-------------------------------------------------------------------------------

-- | Extract all 128-bit scalar challenges from a vector of L/R pairs.
-- |
-- | This processes all IPA rounds sequentially, building up the
-- | scalar challenge vector. The endo mapping to full field elements
-- | happens separately, outside this function.
-- |
-- | The number of rounds `n` equals the SRS log size (e.g., 16 for 2^16 SRS).
extractScalarChallenges
  :: forall n f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector n (LrPair (FVar f))
  -> SpongeM f (KimchiConstraint f) t m (Vector n (SizedF 128 (FVar f)))
extractScalarChallenges pairs = for pairs \{ l, r } -> do
  -- Absorb L and R points into the sponge
  absorbPoint l
  absorbPoint r
  -- | The result is a 128-bit scalar challenge, NOT a full field element.
  -- | In pickles, the endo mapping to full field happens separately when needed.
  -- | This matches the OCaml `squeeze_scalar` + `Bulletproof_challenge.unpack`.
  squeezeScalarChallenge

-------------------------------------------------------------------------------
-- | Verification
-------------------------------------------------------------------------------

-- | Pure version of b correctness check.
-- |
-- | Verifies: b == bPoly(challenges, zeta) + evalscale * bPoly(challenges, zetaOmega)
-- |
-- | This is the "b_correct" check from wrap_verifier.ml.
bCorrect
  :: forall n f
   . Reflectable n Int
  => PrimeField f
  => BCorrectInput n f
  -> Boolean
bCorrect input@{ expectedB } =
  let
    computedB = computeB input.challenges { zeta: input.zeta, zetaOmega: input.zetaOmega, evalscale: input.evalscale }
  in
    computedB == expectedB

-- | Circuit version of b correctness check.
-- |
-- | Computes b = bPoly(challenges, zeta) + evalscale * bPoly(challenges, zetaOmega)
-- | and returns a boolean constraint for equality with expected value.
-- |
-- | This is the in-circuit version of the "b_correct" check.
bCorrectCircuit
  :: forall n f c t m
   . Reflectable n Int
  => PrimeField f
  => CircuitM f c t m
  => BCorrectInput n (FVar f)
  -> Snarky c t m (BoolVar f)
bCorrectCircuit input@{ expectedB } = do
  computedB <- computeBCircuit input
  computedB `equals_` expectedB

-------------------------------------------------------------------------------
-- | Bullet Reduce (lr_prod computation)
-------------------------------------------------------------------------------

-- | Pure version of bullet reduce.
-- |
-- | Computes: lr_prod = Σ_i [endoInv(L_i, u_i) + endo(R_i, u_i)]
-- |
-- | Where u_i are 128-bit scalar challenges and endo/endoInv apply the
-- | endomorphism-based scalar multiplication.
-- |
-- | This corresponds to `bullet_reduce` in wrap_verifier.ml / step_verifier.ml.
bulletReduce
  :: forall n f f' g _l
   . Reflectable n Int
  => Add 1 _l n
  => FieldSizeInBits f' 255
  => FieldSizeInBits f 255
  => HasEndo f f'
  => FrModule f' g
  => WeierstrassCurve f g
  => BulletReduceInput n f
  -> g
bulletReduce { pairs, challenges } =
  let
    -- Convert 128-bit challenge to full field element using endo coefficient
    toFullChallenge :: SizedF 128 f -> f'
    toFullChallenge raw128 = unwrap $ toFieldPure (coerceViaBits raw128) (endoScalar @f @f')

    -- Compute one term: endoInv(L, u) + endo(R, u)
    -- where u is the full field challenge
    computeTerm :: LrPair f -> SizedF 128 f -> g
    computeTerm { l, r } raw128 =
      let
        fullChal = toFullChallenge raw128
        fullChalInv = recip fullChal
        -- L * chal_inv
        lPoint = fromAffine @f @g l
        lScaled = scalarMul fullChalInv lPoint
        -- R * chal
        rPoint = fromAffine @f @g r
        rScaled = scalarMul fullChal rPoint
      in
        lScaled <> rScaled

    -- Compute all terms and sum them
    terms = Vector.zipWith computeTerm pairs challenges
  in
    fold terms

-- | Circuit version of bullet reduce.
-- |
-- | Computes: lr_prod = Σ_i [endoInv(L_i, u_i) + endo(R_i, u_i)]
-- |
-- | Uses the efficient endo/endoInv circuits for scalar multiplication.
bulletReduceCircuit
  :: forall n @f f' @g t m _l
   . Reflectable n Int
  => Add 1 _l n
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => HasEndo f f'
  => FrModule f' g
  => WeierstrassCurve f g
  => CircuitM f (KimchiConstraint f) t m
  => Compare 128 255 LT
  => BulletReduceInput n (FVar f)
  -> Snarky (KimchiConstraint f) t m { p :: AffinePoint (FVar f), isInfinity :: BoolVar f }
bulletReduceCircuit { pairs, challenges } = do
  -- Process each (L, R, u) triple to compute endoInv(L, u) + endo(R, u)
  terms <- for (Vector.zip pairs challenges) \(Tuple { l, r } u) -> do
    -- endoInv(L, u) = L * (1 / toField(u, endo))
    lScaled <- endoInv @f @f' @g l u
    -- endo(R, u) = R * toField(u, endo)
    rScaled <- endo r u
    -- Sum: endoInv(L, u) + endo(R, u)
    addComplete lScaled rScaled
  let
    { head, tail } = Vector.uncons terms
  -- Sum all terms using addComplete
  foldM
    ( \p q -> do
        elseBranch <- if_ q.isInfinity p =<< addComplete p.p q.p
        if_ p.isInfinity q elseBranch
    )
    head
    tail