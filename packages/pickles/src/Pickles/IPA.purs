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
  , CheckBulletproofInput
  -- Challenge polynomial
  , bPoly
  , bPolyCircuit
  -- Combined b evaluation
  , computeB
  , computeBCircuit
  -- Challenge extraction (returns 128-bit scalar challenges)
  , extractScalarChallenges
  -- Bullet reduce (lr_prod computation)
  , bulletReduceCircuit
  -- Verification
  , bCorrectCircuit
  -- Combined polynomial commitment
  , combinePolynomials
  -- IPA final check
  , ipaFinalCheckCircuit
  -- Full bulletproof check
  , checkBulletproof
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (foldM, for_, product)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import JS.BigInt as BigInt
import Pickles.ShiftOps (IpaScalarOps)
import Pickles.Sponge (SpongeM, absorb, absorbPoint, getSponge, labelM, liftSnarky, squeeze, squeezeScalar)
import Pickles.Trace as Trace
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, SizedF, Snarky, add_, and_, const_, equals_, if_, label)
import Snarky.Circuit.DSL (exists, readCVar) as SDSL
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (GroupMapParams, addComplete, endo, endoInv, groupMapCircuit)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve, pow)
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

-- | Circuit version of bPoly using two-phase approach matching OCaml.
-- |
-- | Phase 1: Build pow_two_pows = [pt, pt^2, pt^4, ..., pt^(2^(k-1))] via k-1 squarings
-- | Phase 2: Compute product = ∏ (1 + chals[i] * powTwoPows[k-1-i]) with k-1 accumulations
-- |
-- | This matches OCaml's challenge_polynomial (wrap_verifier.ml:35-57) exactly,
-- | producing the same constraint ordering.
bPolyCircuit
  :: forall d f c t m
   . Add 1 _ d
  => Reflectable d Int
  => PrimeField f
  => CircuitM f c t m
  => BPolyInput d (FVar f)
  -> Snarky c t m (FVar f)
bPolyCircuit { challenges: chals, x: pt } = label "b-poly" do
  -- Phase 1: Build pow_two_pows via k-1 squarings
  let { tail: chalsTail } = Vector.uncons chals
  Tuple squaredPowers _ <- mapAccumM
    ( \prev _ -> do
        sq <- pure prev * pure prev
        pure (Tuple sq sq)
    )
    pt
    chalsTail
  let powTwoPows = Vector.append (pt :< Vector.nil) squaredPowers

  -- Phase 2: Product = ∏_{i=0}^{k-1} (1 + chals[i] * powTwoPows[k-1-i])
  let
    paired = Vector.zipWith Tuple chals (Vector.reverse powTwoPows)
    { head: Tuple c0 pw0, tail: rest } = Vector.uncons paired
  cp0 <- pure c0 * pure pw0
  let initProd = add_ (const_ one) cp0
  foldM
    ( \acc (Tuple c pw) -> do
        cp <- pure c * pure pw
        let term = add_ (const_ one) cp
        pure term * pure acc
    )
    initProd
    rest

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
-- |
-- | Evaluation order matches OCaml's right-to-left argument evaluation:
-- | bPoly(zetaOmega), then evalscale * result, then bPoly(zeta).
computeBCircuit
  :: forall d f c t m r
   . Add 1 _ d
  => Reflectable d Int
  => PrimeField f
  => CircuitM f c t m
  => ComputeBInput d (FVar f) r
  -> Snarky c t m (FVar f)
computeBCircuit { challenges, zeta, zetaOmega, evalscale } = label "compute-b" do
  -- OCaml evaluates: challenge_poly zeta + (r * challenge_poly zetaw)
  -- Right-to-left: zetaw first, then r * result, then zeta
  bZetaOmega <- bPolyCircuit { challenges, x: zetaOmega }
  scaledB <- pure evalscale * pure bZetaOmega
  bZeta <- bPolyCircuit { challenges, x: zeta }
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
-- | The number of rounds `n` equals the SRS log size
extractScalarChallenges
  :: forall n f t m r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => { endo :: FVar f | r }
  -> Vector n (LrPair (FVar f))
  -> SpongeM f (KimchiConstraint f) t m (Vector n (SizedF 128 (FVar f)))
extractScalarChallenges params pairs = for pairs \{ l, r } -> do
  -- Absorb L and R points into the sponge
  absorbPoint l
  absorbPoint r
  -- squeeze_scalar with constrain_low_bits:false (matches OCaml's squeeze_scalar)
  squeezeScalar params

-------------------------------------------------------------------------------
-- | Verification
-------------------------------------------------------------------------------

-- | Circuit version of b correctness check.
-- |
-- | Computes b = bPoly(challenges, zeta) + evalscale * bPoly(challenges, zetaOmega)
-- | and returns a boolean constraint for equality with expected value.
-- |
-- | This is the in-circuit version of the "b_correct" check.
bCorrectCircuit
  :: forall n f c t m
   . Add 1 _ n
  => Reflectable n Int
  => PrimeField f
  => CircuitM f c t m
  => BCorrectInput n (FVar f)
  -> Snarky c t m (BoolVar f)
bCorrectCircuit input@{ expectedB } = label "b-correct" do
  computedB <- computeBCircuit input
  expectedB `equals_` computedB

-------------------------------------------------------------------------------
-- | Bullet Reduce (lr_prod computation)
-------------------------------------------------------------------------------

-- | Circuit version of bullet reduce.
-- |
-- | Computes: lr_prod = Σ_i [endoInv(L_i, u_i) + endo(R_i, u_i)]
-- |
-- | Uses the efficient endo/endoInv circuits for scalar multiplication.
bulletReduceCircuit
  :: forall n @f f' @g t m
   . Reflectable n Int
  => Add 1 _ n
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => HasEndo f f'
  => FrModule f' g
  => WeierstrassCurve f g
  => CircuitM f (KimchiConstraint f) t m
  => BulletReduceInput n (FVar f)
  -> Snarky (KimchiConstraint f) t m { p :: AffinePoint (FVar f), isInfinity :: BoolVar f }
bulletReduceCircuit { pairs, challenges } = label "bullet-reduce" do
  -- Process each (L, R, u) triple to compute endoInv(L, u) + endo(R, u)
  -- OCaml let-binding order: endo_inv(L) first, then endo(R), then add_fast
  terms <- for (Vector.zip pairs challenges) \(Tuple { l, r } u) -> do
    lScaled <- endoInv @f @f' @g l u
    rScaled <- endo r u
    addComplete lScaled rScaled
  let
    { head, tail } = Vector.uncons terms
  -- Sum all terms using add_fast without infinity check, matching OCaml's
  -- Array.reduce_exn ~f:(Ops.add_fast ?check_finite:None)
  -- (default check_finite=true means inf=Field.zero, a constant)
  result <- foldM
    (\acc q -> _.p <$> addComplete acc q.p)
    head.p
    tail
  pure { p: result, isInfinity: head.isInfinity }

-------------------------------------------------------------------------------
-- | IPA Final Check Circuit
-------------------------------------------------------------------------------

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
  -- u = group_map(squeeze(sponge)) — derived by caller before combine_poly
  , u :: AffinePoint f
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
  :: forall n @f f' @g sf t m r
   . Reflectable n Int
  => Add 1 _ n
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => IpaScalarOps f t m sf
  -> { endo :: FVar f, groupMapParams :: GroupMapParams f | r }
  -> IpaFinalCheckInput n (FVar f) sf
  -> SpongeM f (KimchiConstraint f) t m (IpaFinalCheckResult n f)
ipaFinalCheckCircuit scalarOps params input = do
  let
    -- Local copy of Pickles.Verify.ivpTrace — can't import from Verify
    -- due to cycle (Verify imports IPA). Semantics identical.
    ivpTrace labelStr v = do
      _ <- SDSL.exists do
        val <- SDSL.readCVar v
        let _ = unsafePerformEffect (Trace.fieldF labelStr val)
        pure val
      pure unit
  -- DIAG: dump IPA inputs at solve time. These are the values the wrap
  -- circuit reads from the step proof's opening via Req.Openings_proof
  -- + deferredValues — if any differs from OCaml, localizes the bug.
  liftSnarky do
    ivpTrace "ipa.dbg.sg.x" input.sg.x
    ivpTrace "ipa.dbg.sg.y" input.sg.y
    ivpTrace "ipa.dbg.delta.x" input.delta.x
    ivpTrace "ipa.dbg.delta.y" input.delta.y
    ivpTrace "ipa.dbg.cp.x" input.combinedPolynomial.x
    ivpTrace "ipa.dbg.cp.y" input.combinedPolynomial.y
    ivpTrace "ipa.dbg.u.x" input.u.x
    ivpTrace "ipa.dbg.u.y" input.u.y

  -- 1. Extract 128-bit scalar challenges from L/R pairs
  -- OCaml: bullet_reduce starts with Array.map gammas ~f:(absorb + squeeze_scalar)
  scalarChallenges <- labelM "ipa_extract_challenges" $
    extractScalarChallenges params input.lr

  -- 2. Compute lr_prod from L/R pairs and challenges
  -- OCaml: bullet_reduce does curve ops (endo_inv/endo/add_fast) AFTER all absorptions
  lrProd <- liftSnarky $ label "ipa_bullet_reduce" $ do
    { p } <- bulletReduceCircuit @f @g
      { pairs: input.lr
      , challenges: scalarChallenges
      }
    pure p

  -- 3. Build p_prime = combinedPolynomial + scale(u, CIP)
  -- OCaml: let uc = scale_fast u advice.combined_inner_product in
  --        combined_polynomial + uc
  -- Right-to-left: uc first, then add
  pPrime <- liftSnarky $ label "ipa_scale_cip" do
    cipU <- label "ipa_scale_cip_scale" $ scalarOps.scaleByShifted input.u input.combinedInnerProduct
    { p } <- label "ipa_scale_cip_add" $ addComplete input.combinedPolynomial cipU
    pure p

  -- 4. Build q = p_prime + lr_prod
  q <- liftSnarky $ label "ipa_q" do
    { p } <- addComplete pPrime lrProd
    pure p

  -- 5. Absorb delta point + squeeze c
  -- OCaml: absorb sponge PC delta ; let c = squeeze_scalar sponge
  -- This happens AFTER bullet_reduce and q computation in OCaml
  c <- labelM "ipa_squeeze_c" $ do
    absorbPoint input.delta
    squeezeScalar params

  -- DIAG: dump Q + c at this point
  liftSnarky do
    ivpTrace "ipa.dbg.q.x" q.x
    ivpTrace "ipa.dbg.q.y" q.y
    ivpTrace "ipa.dbg.c" (SizedF.toField c)

  success <- liftSnarky $ label "ipa_final_eq" $ do
    -- 7. Compute LHS: c*Q + delta = endo(Q, c) + delta
    cQ <- label "ipa_endo_q" $ endo q c
    { p: lhs } <- label "ipa_lhs_add" $ addComplete cQ input.delta

    -- 8. Compute RHS: z1*(sg + b*u) + z2*H
    -- Note: b is provided as input and verified separately via bCorrectCircuit
    bU <- label "ipa_scale_b" $ scalarOps.scaleByShifted input.u input.b
    { p: sgPlusBU } <- label "ipa_sg_add" $ addComplete input.sg bU
    z1Term <- label "ipa_scale_z1" $ scalarOps.scaleByShifted sgPlusBU input.z1
    z2Term <- label "ipa_scale_z2" $ scalarOps.scaleByShifted input.blindingGenerator input.z2
    { p: rhs } <- label "ipa_rhs_add" $ addComplete z1Term z2Term

    -- DIAG: dump LHS + RHS at the final equation
    ivpTrace "ipa.dbg.lhs.x" lhs.x
    ivpTrace "ipa.dbg.lhs.y" lhs.y
    ivpTrace "ipa.dbg.rhs.x" rhs.x
    ivpTrace "ipa.dbg.rhs.y" rhs.y

    -- 9. Check LHS == RHS
    xEqual <- equals_ lhs.x rhs.x
    yEqual <- equals_ lhs.y rhs.y
    xEqual `and_` yEqual

  pure { success, challenges: scalarChallenges }

-------------------------------------------------------------------------------
-- | Combined Polynomial Commitment
-------------------------------------------------------------------------------

-- | Combine polynomial commitments using Horner's method with endo scalar multiplication.
-- |
-- | Computes: Q = C_0 + xi*(C_1 + xi*(C_2 + ... + xi*C_{n-1}))
-- | where xi is a 128-bit scalar challenge (polyscale).
-- |
-- | Bases can be constants or circuit variables.
-- |
-- | Reference: Pcs_batch.combine_split_commitments in OCaml
-- | Combine polynomial commitments using Horner's method with endo scalar multiplication.
-- |
-- | `masks` provides optional keep flags per base (from actual_proofs_verified_mask for sg_old).
-- | When Just keep, OCaml's combine_split_commitments generates:
-- |   if_ keep ~then_:point ~else_:acc.point
-- | matching Opt.Maybe handling. When Nothing, the entry is unconditional (Opt.Just).
combinePolynomials
  :: forall n f f' t m
   . Add 1 _ n
  => FieldSizeInBits f 255
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => Vector n (AffinePoint (FVar f))
  -> Vector n (Maybe (BoolVar f)) -- per-base keep mask (Nothing = unconditional)
  -> SizedF 128 (FVar f)
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
combinePolynomials bases masks xi = label "combine-polynomials" do
  let
    paired = Vector.zip bases masks
    reversed = Vector.reverse paired
    { head: Tuple h _, tail: t } = Vector.uncons reversed
  foldM
    ( \acc (Tuple base mKeep) -> do
        xiAcc <- endo acc xi
        { p } <- addComplete base xiAcc
        -- OCaml: if_ keep ~then_:point ~else_:acc.point (for Opt.Maybe entries)
        case mKeep of
          Nothing -> pure p
          Just keep -> if_ keep p acc
    )
    h
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
  :: forall numBases n @f f' @g sf t m r
   . Reflectable n Int
  => Add 1 _ n
  => Add 1 _ numBases
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => IpaScalarOps f t m sf
  -> { endo :: FVar f, groupMapParams :: GroupMapParams f | r }
  -> Vector numBases (AffinePoint (FVar f))
  -> Vector numBases (Maybe (BoolVar f)) -- per-base keep mask (Nothing = unconditional)
  -> CheckBulletproofInput n (FVar f) sf
  -> SpongeM f (KimchiConstraint f) t m (IpaFinalCheckResult n f)
checkBulletproof scalarOps params commitmentBases baseMasks input = do
  let
    ivpTrace' labelStr v = do
      _ <- SDSL.exists do
        val <- SDSL.readCVar v
        let _ = unsafePerformEffect (Trace.fieldF labelStr val)
        pure val
      pure unit
  -- Dump the sponge STATE entering check_bulletproof (pre-CIP-absorb).
  pre <- getSponge
  liftSnarky do
    ivpTrace' "ipa.dbg.wrap_sponge_pre.s0" (Vector.index pre.state (unsafeFinite @3 0))
    ivpTrace' "ipa.dbg.wrap_sponge_pre.s1" (Vector.index pre.state (unsafeFinite @3 1))
    ivpTrace' "ipa.dbg.wrap_sponge_pre.s2" (Vector.index pre.state (unsafeFinite @3 2))

  -- 1. Absorb shift_scalar(CIP) into sponge
  -- OCaml: Other_field.Packed.absorb_shifted sponge advice.combined_inner_product
  labelM "bp_absorb_cip" $ do
    let cipFields = scalarOps.shiftedToAbsorbFields input.combinedInnerProduct
    for_ cipFields absorb

  -- Dump sponge state after CIP absorb.
  post <- getSponge
  liftSnarky do
    ivpTrace' "ipa.dbg.wrap_sponge_post.s0" (Vector.index post.state (unsafeFinite @3 0))
    ivpTrace' "ipa.dbg.wrap_sponge_post.s1" (Vector.index post.state (unsafeFinite @3 1))
    ivpTrace' "ipa.dbg.wrap_sponge_post.s2" (Vector.index post.state (unsafeFinite @3 2))

  -- 2. Derive u via group_map (squeeze BEFORE combine_poly, matching OCaml)
  -- OCaml: let u = let t = Sponge.squeeze_field sponge in group_map t
  u <- labelM "ipa_group_map" $ do
    t <- squeeze
    liftSnarky $ groupMapCircuit params.groupMapParams t

  -- 3. Compute combined polynomial via Horner (AFTER u, matching OCaml)
  -- OCaml: let combined_polynomial = Split_commitments.combine ...
  combinedPolynomial <- labelM "bp_combine_poly" $ liftSnarky $
    combinePolynomials commitmentBases baseMasks input.xi

  -- 4. Delegate to ipaFinalCheckCircuit (u already computed)
  labelM "bp_ipa_check" $ ipaFinalCheckCircuit @f @g scalarOps params
    { delta: input.delta
    , sg: input.sg
    , lr: input.lr
    , z1: input.z1
    , z2: input.z2
    , u
    , combinedPolynomial
    , combinedInnerProduct: input.combinedInnerProduct
    , b: input.b
    , blindingGenerator: input.blindingGenerator
    }

