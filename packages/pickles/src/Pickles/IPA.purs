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
-- | - ipaFinalCheck: The full IPA verification equation (c*Q + delta = z1*(sg + b*u) + z2*H)
-- |
-- | Reference: wrap_verifier.ml in mina/src/lib/pickles
module Pickles.IPA
  ( -- Types
    LrPair
  , BPolyInput
  , ComputeBInput
  , BCorrectInput
  , BulletReduceInput
  , IpaFinalCheckInput
  , IpaFinalCheckResult
  , IpaScalarOps
  , CheckBulletproofInput
  -- Challenge polynomial
  , bPoly
  , bPolyCircuit
  -- Combined b evaluation
  , computeB
  , computeBCircuit
  -- Challenge extraction (returns 128-bit scalar challenges)
  , extractScalarChallenges
  , extractScalarChallengesPure
  -- Bullet reduce (lr_prod computation)
  , bulletReduce
  , bulletReduceCircuit
  -- Verification
  , bCorrect
  , bCorrectCircuit
  -- Combined polynomial commitment
  , combinePolynomials
  -- IPA final check
  , ipaFinalCheckCircuit
  -- Full bulletproof check
  , checkBulletproof
  -- Scalar ops helpers
  , type1ScalarOps
  , type2ScalarOps
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (fold, foldM, for_, product)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Pickles.Sponge (PureSpongeM, SpongeM, absorb, absorbPoint, liftSnarky, squeeze, squeezeScalarChallenge, squeezeScalarChallengePure)
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, add_, and_, const_, equals_, if_)
import Snarky.Circuit.Kimchi (GroupMapParams, Type1(..), Type2(..), addComplete, endo, endoInv, expandToEndoScalar, groupMapCircuit, scaleFast1, scaleFast2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve, fromAffine, pow, scalarMul)
import Snarky.Data.EllipticCurve (AffinePoint)

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
        let term = add_ (const_ one) cp
        -- product *= term
        newProduct <- pure p * pure term
        -- currPower = currPower²
        newPower <- pure currPower * pure currPower
        pure { product: newProduct, currPower: newPower }
    )
    { product: const_ one, currPower: x }
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
  pure $ add_ bZeta scaledB

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
  -- The result is a 128-bit scalar challenge, NOT a full field element.
  -- In pickles, the endo mapping to full field happens separately when needed.
  -- This matches the OCaml `squeeze_scalar` + `Bulletproof_challenge.unpack`.
  squeezeScalarChallenge

-- | Pure version of extractScalarChallenges for testing.
-- | Extracts 128-bit scalar challenges from L/R pairs using pure sponge.
extractScalarChallengesPure
  :: forall n f
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => Vector n (LrPair f)
  -> PureSpongeM f (Vector n (SizedF 128 f))
extractScalarChallengesPure pairs = for pairs \{ l, r } -> do
  absorb l.x
  absorb l.y
  absorb r.x
  absorb r.y
  squeezeScalarChallengePure

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
  :: forall n @f f' @g _l
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
    -- Compute one term: endoInv(L, u) + endo(R, u)
    -- where u is the full field challenge
    computeTerm :: LrPair f -> SizedF 128 f -> g
    computeTerm { l, r } raw128 =
      let
        fullChal = expandToEndoScalar raw128 :: f'
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

-------------------------------------------------------------------------------
-- | IPA Final Check Circuit
-------------------------------------------------------------------------------

-- | Operations for working with shifted scalar values in the IPA circuit.
-- |
-- | This record bundles operations that depend on the specific shifted type
-- | (Type1 for Vesta scalars in Pallas circuits, Type2 for Pallas scalars in Vesta circuits).
-- |
-- | Parameters:
-- | - `f`: base field type (Pallas.BaseField or Vesta.BaseField)
-- | - `c`: constraint type
-- | - `t`: tag type
-- | - `m`: underlying monad
-- | - `sf`: shifted scalar type (Type1 (FVar f) or Type2 (FVar f) (BoolVar f))
type IpaScalarOps f c t m sf =
  { -- | Scale a curve point by a shifted scalar value.
    -- | This corresponds to `scale_fast` in wrap_verifier.ml.
    scaleByShifted ::
      AffinePoint (FVar f)
      -> sf
      -> Snarky c t m (AffinePoint (FVar f))
  , -- | Get the field elements to absorb for a shifted scalar.
    -- | For Type1: returns [t] (single field element)
    -- | For Type2: returns [sDiv2, if sOdd then 1 else 0] (two elements)
    shiftedToAbsorbFields ::
      sf
      -> Array (FVar f)
  }

-- | Input for IPA final verification.
-- |
-- | The verification equation is: c*Q + delta = z1*(sg + b*u) + z2*H
-- | where:
-- | - Q = combinedPolynomial + combinedInnerProduct*u + lr_prod
-- | - u = groupMap(squeeze(sponge)) after absorbing combinedInnerProduct
-- | - challenges = extracted from L/R pairs via sponge
-- | - c = squeeze(sponge) after absorbing delta
-- | - b = bPoly(challenges, zeta) + evalscale * bPoly(challenges, zetaOmega)
-- | - lr_prod = Σ_i [chal_inv_i * L_i + chal_i * R_i]
-- |
-- | The circuit field is `f`, the commitment curve is `g` with base field `f`.
-- | Scalars like z1, z2 are in the commitment curve's scalar field,
-- | represented via the shifted type `sf` in the circuit field.
type IpaFinalCheckInput n f sf =
  { -- Opening proof fields (coordinates in f = commitment curve base field)
    delta :: AffinePoint f
  , sg :: AffinePoint f -- challenge_polynomial_commitment
  , lr :: Vector n (LrPair f)
  -- Scalars from opening proof (shifted representation)
  , z1 :: sf
  , z2 :: sf
  -- Combined polynomial commitment (from verifier index + xi)
  , combinedPolynomial :: AffinePoint f
  -- Combined inner product (shifted representation)
  , combinedInnerProduct :: sf
  -- b value (shifted representation, verified separately via bCorrectCircuit)
  , b :: sf
  -- Blinding generator H (from SRS, constant)
  , blindingGenerator :: AffinePoint f
  }

-- | Result of IPA final check, including the success boolean and
-- | the extracted 128-bit scalar challenges (bulletproof challenges).
type IpaFinalCheckResult n f =
  { success :: BoolVar f
  , challenges :: Vector n (SizedF 128 (FVar f))
  }

-- | In-circuit IPA final verification.
-- |
-- | This circuit implements the IPA verification equation:
-- |   c*Q + delta = z1*(sg + b*u) + z2*H
-- |
-- | It derives u, challenges, and c from the sponge (Fiat-Shamir), verifying
-- | compatibility with proofs generated by Kimchi.
-- |
-- | This circuit stays in `SpongeM` so the caller can manage the sponge lifecycle.
-- | The sponge should be in the state ready to squeeze for u (i.e., after absorbing
-- | combined_inner_product).
-- |
-- | NOTE: This circuit operates over the commitment curve's base field (circuit field f).
-- | For Pallas circuits (Fp), the commitment curve is Vesta, use Type1 for sf.
-- | For Vesta circuits (Fq), the commitment curve is Pallas, use Type2 for sf.
ipaFinalCheckCircuit
  :: forall n @f f' @g sf t m _l
   . Reflectable n Int
  => Add 1 _l n
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => IpaScalarOps f (KimchiConstraint f) t m sf
  -> GroupMapParams f
  -> IpaFinalCheckInput n (FVar f) sf
  -> SpongeM f (KimchiConstraint f) t m (IpaFinalCheckResult n f)
ipaFinalCheckCircuit scalarOps groupMapParams input = do
  -- 1. Derive u via group_map
  -- NOTE: combined_inner_product should already be absorbed by caller
  u <- do
    t <- squeeze
    liftSnarky $ groupMapCircuit groupMapParams t

  -- 2. Extract 128-bit scalar challenges from L/R pairs
  scalarChallenges <- extractScalarChallenges input.lr

  -- 3. Absorb delta point
  absorbPoint input.delta

  -- 4. Derive c via squeeze (as 128-bit scalar challenge)
  c <- squeezeScalarChallenge

  success <- liftSnarky $ do
    -- 5. Compute lr_prod from L/R pairs and challenges
    { p: lrProd } <- bulletReduceCircuit @f @g
      { pairs: input.lr
      , challenges: scalarChallenges
      }

    -- 6. Compute Q = combinedPolynomial + combinedInnerProduct*u + lr_prod
    cipU <- scalarOps.scaleByShifted u input.combinedInnerProduct
    { p: pPrime } <- addComplete input.combinedPolynomial cipU
    { p: q } <- addComplete pPrime lrProd

    -- 7. Compute LHS: c*Q + delta = endo(Q, c) + delta
    cQ <- endo q c
    { p: lhs } <- addComplete cQ input.delta

    -- 8. Compute RHS: z1*(sg + b*u) + z2*H
    -- Note: b is provided as input and verified separately via bCorrectCircuit
    bU <- scalarOps.scaleByShifted u input.b
    { p: sgPlusBU } <- addComplete input.sg bU
    z1Term <- scalarOps.scaleByShifted sgPlusBU input.z1
    z2Term <- scalarOps.scaleByShifted input.blindingGenerator input.z2
    { p: rhs } <- addComplete z1Term z2Term

    -- 9. Check LHS == RHS
    xEqual <- equals_ lhs.x rhs.x
    yEqual <- equals_ lhs.y rhs.y
    xEqual `and_` yEqual

  pure { success, challenges: scalarChallenges }

-------------------------------------------------------------------------------
-- | Scalar Ops Implementations
-------------------------------------------------------------------------------

-- | Type1 scalar ops for circuits where scalar field < circuit field.
-- |
-- | Used for Pallas circuits (Fp) with Vesta commitment curve.
-- | Vesta scalar field = Fq < Fp, so scalars fit in Type1.
-- |
-- | For a 255-bit field, nChunks = 51 (since 5 * 51 = 255).
type1ScalarOps
  :: forall f t m
   . FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => IpaScalarOps f (KimchiConstraint f) t m (Type1 (FVar f))
type1ScalarOps =
  { scaleByShifted: \p t -> scaleFast1 @51 p t
  , shiftedToAbsorbFields: \(Type1 t) -> [ t ]
  }

-------------------------------------------------------------------------------
-- | Combined Polynomial Commitment
-------------------------------------------------------------------------------

-- | Combine polynomial commitments using Horner's method with endo scalar multiplication.
-- |
-- | Computes: Q = C_0 + xi*(C_1 + xi*(C_2 + ... + xi*C_{n-1}))
-- | where xi is a 128-bit scalar challenge (polyscale).
-- |
-- | All bases are constants (from VK/proof). The xi challenge is a circuit variable.
-- |
-- | Reference: Pcs_batch.combine_split_commitments in OCaml
combinePolynomials
  :: forall n f f' t m _l
   . Add 1 _l n
  => FieldSizeInBits f 255
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => Compare 128 255 LT
  => Vector n (AffinePoint (F f))
  -> SizedF 128 (FVar f)
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
combinePolynomials bases xi = do
  let
    constPt { x: F x', y: F y' } = { x: const_ x', y: const_ y' }
    reversed = Vector.reverse bases
    { head: h, tail: t } = Vector.uncons reversed
  foldM
    ( \acc base -> do
        xiAcc <- endo acc xi
        { p } <- addComplete (constPt base) xiAcc
        pure p
    )
    (constPt h)
    t

-------------------------------------------------------------------------------
-- | Full Bulletproof Check
-------------------------------------------------------------------------------

-- | Input for the full bulletproof verification circuit.
-- | Contains all proof data needed after the Fq-sponge transcript.
type CheckBulletproofInput n f sf =
  { -- Polyscale challenge (128-bit, from Fr-sponge)
    xi :: SizedF 128 f
  -- Opening proof fields
  , delta :: AffinePoint f
  , sg :: AffinePoint f
  , lr :: Vector n (LrPair f)
  , z1 :: sf
  , z2 :: sf
  -- Advice (from deferred values)
  , combinedInnerProduct :: sf
  , b :: sf
  -- Constant
  , blindingGenerator :: AffinePoint f
  }

-- | Full bulletproof verification circuit.
-- |
-- | Corresponds to OCaml check_bulletproof (step_verifier.ml:232-334).
-- | Absorbs CIP, computes combined polynomial, and runs IPA final check.
-- | Returns success boolean and extracted bulletproof challenges.
-- |
-- | The sponge should be in sponge_before_evaluations state (after Fq-transcript).
-- | Commitment bases are constant points from the verifier index / proof,
-- | passed separately from the circuit input.
checkBulletproof
  :: forall numBases n @f f' @g sf t m _l _l2
   . Reflectable n Int
  => Add 1 _l n
  => Add 1 _l2 numBases
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Compare 128 255 LT
  => IpaScalarOps f (KimchiConstraint f) t m sf
  -> GroupMapParams f
  -> Vector numBases (AffinePoint (F f))
  -> CheckBulletproofInput n (FVar f) sf
  -> SpongeM f (KimchiConstraint f) t m (IpaFinalCheckResult n f)
checkBulletproof scalarOps groupMapParams commitmentBases input = do
  -- 1. Absorb shift_scalar(CIP) into sponge
  let cipFields = scalarOps.shiftedToAbsorbFields input.combinedInnerProduct
  for_ cipFields absorb

  -- 2. Compute combined polynomial via Horner
  combinedPolynomial <- liftSnarky $
    combinePolynomials commitmentBases input.xi

  -- 3. Delegate to ipaFinalCheckCircuit
  ipaFinalCheckCircuit @f @g scalarOps groupMapParams
    { delta: input.delta
    , sg: input.sg
    , lr: input.lr
    , z1: input.z1
    , z2: input.z2
    , combinedPolynomial
    , combinedInnerProduct: input.combinedInnerProduct
    , b: input.b
    , blindingGenerator: input.blindingGenerator
    }

-- | Type2 scalar ops for circuits where scalar field > circuit field.
-- |
-- | Used for Vesta circuits (Fq) with Pallas commitment curve.
-- | Pallas scalar field = Fp > Fq, so scalars need Type2 split representation.
-- |
-- | For a 255-bit field, nChunks = 51 (since 5 * 51 = 255).
type2ScalarOps
  :: forall f t m
   . FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => IpaScalarOps f (KimchiConstraint f) t m (Type2 (FVar f) (BoolVar f))
type2ScalarOps =
  { scaleByShifted: \p t -> scaleFast2 @51 p t
  , shiftedToAbsorbFields: \(Type2 { sDiv2, sOdd }) -> [ sDiv2, coerce sOdd ]
  }