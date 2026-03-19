-- | Deterministic dummy values for Pickles recursion bootstrapping.
-- |
-- | Mirrors OCaml's `mina/src/lib/pickles/dummy.ml`, `ro.ml`, `unfinalized.ml`.
-- |
-- | Reference: mina/src/lib/pickles/dummy.ml, mina/src/lib/pickles/ro.ml,
-- |            mina/src/lib/pickles/unfinalized.ml
-- | Fixture: packages/pickles/test/fixtures/dummy_values.txt
-- | Generator: mina/src/lib/crypto/pickles/dump_dummy/dump_dummy.ml
module Pickles.Dummy
  ( DummySgValues
  , computeDummySgValues
  , dummyIpaChallenges
  , wrapDummyUnfinalizedProof
  , stepDummyUnfinalizedProof
  , stepDummyFopProofState
  , dummyProofWitness
  , dummyStepAdvice
  , dummyFinalizeOtherProofParams
  , Ro
  , mkRo
  , tick
  ) where

import Prelude

import Control.Monad.State (State, evalState, get, put)
import Data.Array as Array
import Data.Blake2s (blake2s256Bits)
import Data.Foldable (foldl)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (sequence)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (bPoly, computeB)
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval, domainGenerator, domainShifts, unnormalizedLagrangeBasis)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.Linearization.Types (mkLinearizationPoly)
import Pickles.PlonkChecks (AllEvals)
import Pickles.PlonkChecks.FtEval (ftEval0)
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint)
import Pickles.PlonkChecks.Permutation (permContribution, permScalar)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, frSpongeChallengesPure)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Sponge (initialSponge)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofParams)
import Pickles.Types (StepField, StepIPARounds, WrapField, WrapIPARounds)
import Pickles.Verify.Types (UnfinalizedProof)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import RandomOracle.Sponge as PureSponge
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), SizedF, coerceViaBits, fromBits)
import Snarky.Circuit.DSL.SizedF (fromField, toField, wrapF) as SizedF
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, EndoScalar(..), endoScalar, fromBigInt, generator, pow, toAffine) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (class Shifted, SplitField, Type1, Type2(..), toShifted)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Ro state and monad
-------------------------------------------------------------------------------

type Ro =
  { tockCounter :: Int
  , tickCounter :: Int
  , chalCounter :: Int
  }

mkRo :: Ro
mkRo = { tockCounter: 0, tickCounter: 0, chalCounter: 0 }

type RoM = State Ro

bitsToBigInt :: Array Boolean -> BigInt.BigInt
bitsToBigInt = Array.foldr
  (\bit acc -> acc * BigInt.fromInt 2 + (if bit then BigInt.fromInt 1 else BigInt.fromInt 0))
  (BigInt.fromInt 0)

bitsRandomOracle :: Int -> String -> Array Boolean
bitsRandomOracle length s = Array.take length (blake2s256Bits s)

tock :: RoM WrapField
tock = do
  ro <- get
  let next = ro.tockCounter + 1
  put $ ro { tockCounter = next }
  pure $ Curves.fromBigInt (bitsToBigInt (bitsRandomOracle 255 ("fq_" <> show next)))

tick :: RoM StepField
tick = do
  ro <- get
  let next = ro.tickCounter + 1
  put $ ro { tickCounter = next }
  pure $ Curves.fromBigInt (bitsToBigInt (bitsRandomOracle 255 ("fp_" <> show next)))

chal :: forall @f. Curves.FieldSizeInBits f 255 => Curves.PrimeField f => RoM (SizedF 128 f)
chal = do
  ro <- get
  let next = ro.chalCounter + 1
  put $ ro { chalCounter = next }
  pure $ fromBits $ unsafePartial fromJust $ Vector.toVector @128 $ bitsRandomOracle 128 ("chal_" <> show next)

scalarChal :: forall @f. Curves.FieldSizeInBits f 255 => Curves.PrimeField f => RoM (SizedF 128 f)
scalarChal = chal

-- | Generate n challenges, reversed to match OCaml's right-to-left Vector.init evaluation.
-- |
-- | OCaml pitfall: `Vector.init n ~f:(fun _ -> Ro.scalar_chal())` evaluates
-- | the side-effecting function right-to-left — index n-1 gets chal counter 1,
-- | index 0 gets counter n. PureScript's `sequence` evaluates left-to-right,
-- | so we reverse after generation to match OCaml's index→counter mapping.
replicateChal
  :: forall @n f
   . Compare 128 255 LT
  => Curves.FieldSizeInBits f 255
  => Curves.PrimeField f
  => Reflectable n Int
  => RoM (Vector n (SizedF 128 f))
replicateChal = do
  let n = reflectType (Proxy @n)
  arr <- sequence (Array.replicate n (chal :: RoM (SizedF 128 f)))
  pure $ unsafePartial fromJust $ Vector.toVector @n (Array.reverse arr)

-------------------------------------------------------------------------------
-- | Shared Ro computation
-- |
-- | OCaml's Ro module uses globally mutable state. All dummy values in
-- | `dummy.ml` and `unfinalized.ml` draw from a single shared counter sequence.
-- | Here we mirror that by running the full Ro sequence exactly once and
-- | sharing the result across computeDummySgValues, dummyIpaChallenges, and
-- | wrapDummyUnfinalizedProof. Any change to the sequence affects all three.
-------------------------------------------------------------------------------

type RoComputeResult =
  { wrapChalRaw :: Vector WrapIPARounds (SizedF 128 WrapField)
  , stepChalRaw :: Vector StepIPARounds (SizedF 128 StepField)
  , alpha :: SizedF 128 WrapField
  , beta :: SizedF 128 WrapField
  , gamma :: SizedF 128 WrapField
  , zeta :: SizedF 128 WrapField
  -- Dummy.evals (tock 1-89): the Wrap-side polynomial evaluations
  , wrapDummyEvals :: AllEvals WrapField
  , cipRaw :: WrapField
  , bRaw :: WrapField
  -- z1/z2 from proof.ml:dummy openings (tock 92-93)
  , proofZ1 :: WrapField
  , proofZ2 :: WrapField
  -- Step dummy plonk challenges from proof.ml:dummy.
  -- OCaml right-to-left evaluation: zeta first, then gamma, beta, alpha.
  , stepDummyZeta :: SizedF 128 StepField
  , stepDummyGamma :: SizedF 128 StepField
  , stepDummyBeta :: SizedF 128 StepField
  , stepDummyAlpha :: SizedF 128 StepField
  -- Step dummy prev_evals from tick() in OCaml's right-to-left record order.
  , stepDummyPrevEvals :: AllEvals StepField
  }

-- | Run the complete Ro sequence once (matching OCaml's global Ro state).
-- |
-- | Chal sequence (35 calls):
-- |   chal 1–15:  Dummy.Ipa.Wrap.challenges (WrapIPARounds = 15)
-- |   chal 16–31: Dummy.Ipa.Step.challenges (StepIPARounds = 16)
-- |   chal 32–35: Unfinalized.Constant.dummy plonk (alpha, beta, gamma, zeta)
-- |
-- | Tock sequence (93 calls):
-- |   tock 1–89: Dummy.evals
-- |     15 w evals            x 2 = 30
-- |     15 coeff evals        x 2 = 30
-- |      1 z eval             x 2 =  2
-- |      6 sigma evals        x 2 = 12
-- |      6 selector evals     x 2 = 12  (generic, poseidon, completeAdd, mul, emul, endomulScalar)
-- |      1 publicInput        x 2 =  2
-- |      1 ft_eval1           x 1 =  1
-- |                                  89
-- |   tock 90: b  (evaluated before CIP in OCaml record construction)
-- |   tock 91: cipRaw
-- |   tock 92–93: proof.ml:dummy openings z2, z1 (right-to-left)
-- |
-- | Chal sequence continued (4 more calls):
-- |   chal 36–39: proof.ml:dummy plonk (zeta, gamma, beta, alpha — right-to-left)
-- |
-- | Tick sequence (89 calls, independent counter):
-- |   tick 1–89: proof.ml:dummy prev_evals (see stepDummyPrevEvals)
roComputeResult :: RoComputeResult
roComputeResult = flip evalState mkRo do
  -- Phase 1: IPA challenges (chal counters 1–31)
  wrapChalRaw <- replicateChal @WrapIPARounds :: RoM (Vector WrapIPARounds (SizedF 128 WrapField))
  stepChalRaw <- replicateChal @StepIPARounds :: RoM (Vector StepIPARounds (SizedF 128 StepField))

  -- Phase 2: Unfinalized.Constant.dummy plonk challenges (chal counters 32–35)
  alpha <- scalarChal :: RoM (SizedF 128 WrapField)
  beta <- chal :: RoM (SizedF 128 WrapField)
  gamma <- chal :: RoM (SizedF 128 WrapField)
  zeta <- scalarChal :: RoM (SizedF 128 WrapField)

  -- Phase 3: Dummy.evals tock calls (tock 1–89, see header comment for count)
  -- Same right-to-left record + right-to-left :: eval order as the tick-based prev_evals.
  let
    tockPointEval :: RoM { zeta :: WrapField, omegaTimesZeta :: WrapField }
    tockPointEval = do
      oz <- tock -- right tuple element first (OCaml right-to-left)
      z <- tock
      pure { zeta: z, omegaTimesZeta: oz }

    tockPointEvalVec :: forall @n. Reflectable n Int => RoM (Vector n { zeta :: WrapField, omegaTimesZeta :: WrapField })
    tockPointEvalVec = do
      v <- Vector.generateA (const tockPointEval)
      pure (Vector.reverse v) -- OCaml Vector.map :: right-to-left side effects
  -- Evals record right-to-left: selectors first, then s, z, coefficients, w
  idxEndomulScalar <- tockPointEval
  idxEmul <- tockPointEval
  idxMul <- tockPointEval
  idxCompleteAdd <- tockPointEval
  idxPoseidon <- tockPointEval
  idxGeneric <- tockPointEval
  let
    wrapIndexEvals = unsafePartial fromJust $ Vector.toVector @6
      [ idxGeneric, idxPoseidon, idxCompleteAdd, idxMul, idxEmul, idxEndomulScalar ]
  wrapSigmaEvals <- tockPointEvalVec @6
  wrapZEvals <- tockPointEval
  wrapCoeffEvals <- tockPointEvalVec @15
  wrapWitnessEvals <- tockPointEvalVec @15
  wrapPublicEvals <- tockPointEval
  wrapFtEval1 <- tock
  let
    wrapDummyEvals =
      { ftEval1: wrapFtEval1
      , publicEvals: wrapPublicEvals
      , zEvals: wrapZEvals
      , indexEvals: wrapIndexEvals
      , witnessEvals: wrapWitnessEvals
      , coeffEvals: wrapCoeffEvals
      , sigmaEvals: wrapSigmaEvals
      }

  -- Phase 4: b and combinedInnerProduct (OCaml record: b evaluated before CIP)
  bRaw <- tock -- tock 90
  cipRaw <- tock -- tock 91

  -- Phase 4b: proof.ml:dummy openings z1/z2 (right-to-left: z2 first)
  proofZ2 <- tock -- tock 92
  proofZ1 <- tock -- tock 93

  -- Phase 5: Step dummy plonk challenges from proof.ml:dummy.
  -- OCaml evaluates record fields right-to-left, so within
  --   plonk = { alpha = scalar_chal(); beta = chal(); gamma = chal(); zeta = scalar_chal() }
  -- zeta is evaluated first (last field), then gamma, beta, alpha.
  stepDummyZeta <- scalarChal :: RoM (SizedF 128 StepField)
  stepDummyGamma <- chal :: RoM (SizedF 128 StepField)
  stepDummyBeta <- chal :: RoM (SizedF 128 StepField)
  stepDummyAlpha <- scalarChal :: RoM (SizedF 128 StepField)

  -- Phase 6: Step dummy prev_evals from tick().
  -- OCaml proof.ml:dummy constructs prev_evals with tick() calls.
  -- Record fields evaluate right-to-left; vectors evaluate left-to-right (Vector.map).
  -- Each eval pair: (tick_arr 1, tick_arr 1) → right tuple element first (omega_zeta).
  let
    tickPointEval :: RoM { zeta :: StepField, omegaTimesZeta :: StepField }
    tickPointEval = do
      oz <- tick -- OCaml right-to-left tuple: omega_zeta first
      z <- tick
      pure { zeta: z, omegaTimesZeta: oz }

    -- OCaml's Vector.map (list-based) evaluates side effects right-to-left
    -- (due to `::` right-to-left eval), so last element gets tick values first.
    -- Generate in reverse, then reverse back to get correct index→value mapping.
    tickPointEvalVec :: forall @n. Reflectable n Int => RoM (Vector n { zeta :: StepField, omegaTimesZeta :: StepField })
    tickPointEvalVec = do
      v <- Vector.generateA (const tickPointEval)
      pure (Vector.reverse v)
  -- Evals record right-to-left: selectors first, then s, z, coefficients, w
  stepIdxEndomulScalar <- tickPointEval
  stepIdxEmul <- tickPointEval
  stepIdxMul <- tickPointEval
  stepIdxCompleteAdd <- tickPointEval
  stepIdxPoseidon <- tickPointEval
  stepIdxGeneric <- tickPointEval
  let
    indexEvals = unsafePartial fromJust $ Vector.toVector @6
      [ stepIdxGeneric, stepIdxPoseidon, stepIdxCompleteAdd, stepIdxMul, stepIdxEmul, stepIdxEndomulScalar ]
  sigmaEvals <- tickPointEvalVec @6
  zEvals <- tickPointEval
  coeffEvals <- tickPointEvalVec @15
  witnessEvals <- tickPointEvalVec @15
  -- public_input: right tuple element first
  publicEvals <- tickPointEval
  -- ft_eval1: last tick call
  stepDummyFtEval1 <- tick
  let
    stepDummyPrevEvals =
      { ftEval1: stepDummyFtEval1
      , publicEvals
      , zEvals
      , indexEvals
      , witnessEvals
      , coeffEvals
      , sigmaEvals
      }

  pure
    { wrapChalRaw
    , stepChalRaw
    , alpha
    , beta
    , gamma
    , zeta
    , wrapDummyEvals
    , cipRaw
    , bRaw
    , proofZ1
    , proofZ2
    , stepDummyZeta
    , stepDummyGamma
    , stepDummyBeta
    , stepDummyAlpha
    , stepDummyPrevEvals
    }

-------------------------------------------------------------------------------
-- | DummyValues
-------------------------------------------------------------------------------

type DummySgValues =
  { ipa ::
      { wrap ::
          { challengesRaw :: Vector WrapIPARounds (SizedF 128 WrapField)
          , challengesExpanded :: Vector WrapIPARounds WrapField
          , sg :: AffinePoint StepField
          }
      , step ::
          { challengesRaw :: Vector StepIPARounds (SizedF 128 StepField)
          , challengesExpanded :: Vector StepIPARounds StepField
          , sg :: AffinePoint WrapField
          }
      }
  , unfinalized ::
      { -- Raw scalar challenges from Ro (SizedF 128 in Fq, before expansion)
        alphaRaw :: SizedF 128 WrapField
      , betaRaw :: SizedF 128 WrapField
      , gammaRaw :: SizedF 128 WrapField
      , zetaRaw :: SizedF 128 WrapField
      -- xi = Scalar_challenge.create(Challenge.Constant.dummy) = [1L,1L] as SizedF 128
      , xiRaw :: SizedF 128 WrapField
      -- Expanded versions (after endo_to_field / to_tock_field)
      , zetaExpanded :: WrapField
      , alphaExpanded :: WrapField
      , plonk ::
          { perm :: Type2 (F WrapField)
          , zetaToSrsLength :: Type2 (F WrapField)
          , zetaToDomainSize :: Type2 (F WrapField)
          }
      , combinedInnerProduct :: WrapField
      , b :: WrapField
      , spongeDigest :: WrapField
      }
  }

-- | Compute all dummy values.
computeDummySgValues :: CRS Pallas.G -> CRS Vesta.G -> DummySgValues
computeDummySgValues pallasSrs vestaSrs =
  let
    -- Expand challenges using shared Ro result
    wrapChalExpanded = map (\c -> toFieldPure c wrapEndo) roComputeResult.wrapChalRaw
    stepChalExpanded = map (\c -> toFieldPure c stepEndo) roComputeResult.stepChalRaw

    -- Expand plonk challenges to Fq (unfinalized.ml:36-39)
    -- alpha/zeta use endo expansion; beta/gamma use raw bit packing (no endo).
    alphaFq = toFieldPure roComputeResult.alpha wrapEndo
    zetaFq = toFieldPure roComputeResult.zeta wrapEndo

    -- Compute sg from SRS
    wrapSgCoords = PallasImpl.pallasSrsBPolyCommitment pallasSrs
      (Vector.toUnfoldable wrapChalExpanded)
    wrapSg = { x: unsafeIdx wrapSgCoords 0, y: unsafeIdx wrapSgCoords 1 }
    stepSgCoords = VestaImpl.vestaSrsBPolyCommitment vestaSrs
      (Vector.toUnfoldable stepChalExpanded)
    stepSg = { x: unsafeIdx stepSgCoords 0, y: unsafeIdx stepSgCoords 1 }

    -- Domain: wrap_domains ~proofs_verified:2 = Pow_2_roots_of_unity 15
    -- For Wrap: srs_length_log2 = Tock.Rounds.n = WrapIPARounds = domain_log2 = 15
    -- So zetaToSrsLength = zetaToDomainSize = zeta^(2^15)
    wrapDomainLog2 = reflectType (Proxy :: Proxy WrapIPARounds)
    zetaPow = Curves.pow zetaFq (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt wrapDomainLog2))

    -- Digest.Constant.dummy = [1L, 1L, 1L, 1L] → 1 + 2^64 + 2^128 + 2^192
    digestDummy = Curves.fromBigInt
      ( BigInt.fromInt 1
          + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 64)
          + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)
          + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 192)
      )
  in
    { ipa:
        { wrap:
            { challengesRaw: roComputeResult.wrapChalRaw
            , challengesExpanded: wrapChalExpanded
            , sg: wrapSg
            }
        , step:
            { challengesRaw: roComputeResult.stepChalRaw
            , challengesExpanded: stepChalExpanded
            , sg: stepSg
            }
        }
    , unfinalized:
        { alphaRaw: roComputeResult.alpha
        , betaRaw: roComputeResult.beta
        , gammaRaw: roComputeResult.gamma
        , zetaRaw: roComputeResult.zeta
        -- xi = Scalar_challenge.create(Challenge.Constant.dummy)
        -- Challenge.Constant.dummy = [1L, 1L] → 1 + 2^64 as a 128-bit field element
        , xiRaw: unsafePartial fromJust $ SizedF.fromField @128
            (Curves.fromBigInt (BigInt.fromInt 1 + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 64)) :: WrapField)
        , zetaExpanded: zetaFq
        , alphaExpanded: alphaFq
        , plonk:
            { perm: wrapDummyUnfinalizedProof.deferredValues.plonk.perm
            , zetaToSrsLength: toShifted (F zetaPow)
            , zetaToDomainSize: toShifted (F zetaPow)
            }
        , combinedInnerProduct: roComputeResult.cipRaw
        , b: roComputeResult.bRaw
        , spongeDigest: digestDummy
        }
    }

unsafeIdx :: forall a. Array a -> Int -> a
unsafeIdx arr i = unsafePartial fromJust (Array.index arr i)

-------------------------------------------------------------------------------
-- | Convenience re-exports
-------------------------------------------------------------------------------
dummyIpaChallenges
  :: { wrapRaw :: Vector WrapIPARounds (SizedF 128 WrapField)
     , wrapExpanded :: Vector WrapIPARounds WrapField
     , stepRaw :: Vector StepIPARounds (SizedF 128 StepField)
     , stepExpanded :: Vector StepIPARounds StepField
     }
dummyIpaChallenges =
  let
    wrapRaw = roComputeResult.wrapChalRaw
    stepRaw = roComputeResult.stepChalRaw
    wrapExpanded = map (\c -> toFieldPure c wrapEndo) wrapRaw
    stepExpanded = map (\c -> toFieldPure c stepEndo) stepRaw
  in
    { wrapRaw, wrapExpanded, stepRaw, stepExpanded }

-- | Correct dummy unfinalized proof matching OCaml's Unfinalized.Constant.dummy.
-- |
-- | Uses Ro-derived challenges, NOT zeros. Derives from the same shared Ro
-- | computation as computeDummyValues and defaultChallenges — mirrors OCaml's
-- | globally mutable Ro state.
-- |
-- | Key: OCaml's `Shifted_value(tock())` stores the raw tock value directly
-- | (NOT tock - shift). So combinedInnerProduct and b use Type2 (F raw) directly,
-- | unlike zetaToSrsLength/zetaToDomainSize which use `of_field` (= value - shift).
-- |
-- | Reference: mina/src/lib/crypto/pickles/unfinalized.ml:25-104
wrapDummyUnfinalizedProof :: UnfinalizedProof WrapIPARounds (F WrapField) (Type2 (F WrapField)) Boolean
wrapDummyUnfinalizedProof =
  let
    r = roComputeResult
    evals = r.wrapDummyEvals
    Curves.EndoScalar wEndo = (Curves.endoScalar :: Curves.EndoScalar Pallas.ScalarField)

    -- Expand plonk challenges in WrapField
    alphaExpanded = toFieldPure r.alpha wEndo
    betaExpanded = SizedF.toField r.beta :: WrapField
    gammaExpanded = SizedF.toField r.gamma :: WrapField
    zetaExpanded = toFieldPure r.zeta wEndo

    -- Domain: wrap_domains ~proofs_verified:2 = Pow_2_roots_of_unity 15
    -- srs_length_log2 = Tock.Rounds.n = WrapIPARounds = 15
    wrapDomainLog2 = 15
    zkRows = 3
    omega = (domainGenerator wrapDomainLog2 :: WrapField)
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt wrapDomainLog2)
    zetaToNMinus1 = Curves.pow zetaExpanded n - one
    omegaM1 = recip omega
    omegaM2 = omegaM1 * omegaM1
    omegaM3 = omegaM2 * omegaM1
    zkPoly = (zetaExpanded - omegaM1) * (zetaExpanded - omegaM2) * (zetaExpanded - omegaM3)
    omegaToMinusZkRows = Curves.pow omega (n - BigInt.fromInt zkRows)

    -- Compute perm via permScalar (same as Step side but in WrapField)
    permInput =
      { w: map _.zeta (Vector.take @7 evals.witnessEvals)
      , sigma: map _.zeta evals.sigmaEvals
      , z: evals.zEvals
      , shifts: (domainShifts wrapDomainLog2 :: Vector 7 WrapField)
      , alpha: alphaExpanded
      , beta: betaExpanded
      , gamma: gammaExpanded
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: zetaExpanded
      }
    perm = permScalar permInput

    -- zetaToSrsLength = zeta^(2^srs_length_log2)
    -- For Wrap: srs_length_log2 = Tock.Rounds.n = WrapIPARounds = 15
    -- domain_log2 = 15 → zetaToDomainSize = zeta^(2^15) = same
    zetaPow = Curves.pow zetaExpanded (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt wrapDomainLog2))

    -- Digest.Constant.dummy = [1L, 1L, 1L, 1L] → 1 + 2^64 + 2^128 + 2^192
    digestDummy = Curves.fromBigInt
      ( BigInt.fromInt 1
          + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 64)
          + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)
          + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 192)
      )

    -- xi = Scalar_challenge.create(Challenge.Constant.dummy) = [1L, 1L] packed
    xi :: SizedF 128 (F WrapField)
    xi = SizedF.wrapF $ unsafePartial fromJust $ SizedF.fromField @128
      (Curves.fromBigInt (BigInt.fromInt 1 + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 64)) :: WrapField)
  in
    { deferredValues:
        { plonk:
            { alpha: SizedF.wrapF r.alpha
            , beta: SizedF.wrapF r.beta
            , gamma: SizedF.wrapF r.gamma
            , zeta: SizedF.wrapF r.zeta
            , perm: toShifted (F perm)
            , zetaToSrsLength: toShifted (F zetaPow)
            , zetaToDomainSize: toShifted (F zetaPow)
            }
        -- OCaml: `Shifted_value(tock())` stores raw tock value directly (NOT tock - shift).
        -- Type2 (F raw) is the correct representation here, NOT toShifted (F raw).
        , combinedInnerProduct: Type2 (F r.cipRaw)
        , xi
        , bulletproofChallenges: map SizedF.wrapF r.wrapChalRaw
        , b: Type2 (F r.bRaw)
        }
    , shouldFinalize: false
    , spongeDigestBeforeEvaluations: F digestDummy
    }

-- | Shared computation for Step dummy unfinalized proofs.
-- | The `d` parameter and bp challenges vary between:
-- | - Public input side (WrapIPARounds = 15, Wrap IPA challenges)
-- | - FOP side (StepIPARounds = 16, Step IPA challenges)
-- | All other fields (plonk, cip, b, xi, spongeDigest) are identical.
stepDummyUnfinalizedProofWith
  :: forall d sf
   . Shifted (F StepField) sf
  => Vector d (SizedF 128 (F StepField))
  -> UnfinalizedProof d (F StepField) sf Boolean
stepDummyUnfinalizedProofWith bpChals =
  let
    r = roComputeResult
    evals = r.stepDummyPrevEvals
    Curves.EndoScalar stepEndo = (Curves.endoScalar :: Curves.EndoScalar Vesta.ScalarField)

    -- Expand plonk challenges
    alphaExpanded = toFieldPure r.stepDummyAlpha stepEndo
    betaExpanded = SizedF.toField r.stepDummyBeta :: StepField
    gammaExpanded = SizedF.toField r.stepDummyGamma :: StepField
    zetaExpanded = toFieldPure r.stepDummyZeta stepEndo

    -- Domain parameters (domain_log2 = 15 from proof.ml:dummy ~domain_log2:15)
    domainLog2 = 15
    zkRows = 3
    omega = (domainGenerator domainLog2 :: StepField)
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt domainLog2)
    zetaw = zetaExpanded * omega
    zetaToNMinus1 = Curves.pow zetaExpanded n - one
    omegaM1 = recip omega
    omegaM2 = omegaM1 * omegaM1
    omegaM3 = omegaM2 * omegaM1
    zkPoly = (zetaExpanded - omegaM1) * (zetaExpanded - omegaM2) * (zetaExpanded - omegaM3)
    omegaToMinusZkRows = Curves.pow omega (n - BigInt.fromInt zkRows)

    -- 1. Fr-sponge → xi, evalscale
    -- challenges_digest from expanded old_bulletproof_challenges
    -- OCaml uses 2 copies of Dummy.Ipa.Step.challenges (= stepChalRaw expanded)
    expandedBpChals :: Vector StepIPARounds StepField
    expandedBpChals = map (\c -> toFieldPure c stepEndo) (map coerceViaBits r.stepChalRaw)

    challengesDigest :: StepField
    challengesDigest =
      let
        sponge = foldl (\s c -> PureSponge.absorb c s) (initialSponge :: PureSponge.Sponge StepField) expandedBpChals
        -- 2 copies (MaxProofsVerified=2): absorb same challenges twice
        sponge2 = foldl (\s c -> PureSponge.absorb c s) sponge expandedBpChals
      in
        (PureSponge.squeeze sponge2).result

    frInput :: FrSpongeInput StepField
    frInput =
      { fqDigest: zero -- sponge_digest_before_evaluations = 0 for dummy
      , prevChallengeDigest: challengesDigest
      , ftEval1: evals.ftEval1
      , publicEvals: evals.publicEvals
      , zEvals: evals.zEvals
      , indexEvals: evals.indexEvals
      , witnessEvals: evals.witnessEvals
      , coeffEvals: evals.coeffEvals
      , sigmaEvals: evals.sigmaEvals
      , endo: stepEndo
      }
    frResult = frSpongeChallengesPure frInput

    -- 2. Permutation scalar
    permInput =
      { w: map _.zeta (Vector.take @7 evals.witnessEvals)
      , sigma: map _.zeta evals.sigmaEvals
      , z: evals.zEvals
      , shifts: (domainShifts domainLog2 :: Vector 7 StepField)
      , alpha: alphaExpanded
      , beta: betaExpanded
      , gamma: gammaExpanded
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: zetaExpanded
      }
    perm = permScalar permInput

    -- 3. ftEval0
    permContrib = permContribution permInput
    vanishesOnZk = one :: StepField -- No lookups → vanishes = 1
    lagrangeFalse0 = unnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: zetaExpanded }
    lagrangeTrue1 = unnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: zetaExpanded }
    evalPoint = buildEvalPoint
      { witnessEvals: evals.witnessEvals
      , coeffEvals: map _.zeta evals.coeffEvals
      , indexEvals: evals.indexEvals
      , defaultVal: zero
      }
    challenges_ = buildChallenges
      { alpha: alphaExpanded
      , beta: betaExpanded
      , gamma: gammaExpanded
      , jointCombiner: zero
      , vanishesOnZk
      , lagrangeFalse0
      , lagrangeTrue1
      }
    env = fieldEnv evalPoint challenges_
    gateConstraints = evaluate PallasTokens.constantTermTokens env
    ftEval0Value = ftEval0
      { permContribution: permContrib
      , publicEval: negate evals.publicEvals.zeta
      , gateConstraints
      }

    -- 4. CIP
    ftPointEval :: PointEval StepField
    ftPointEval = { zeta: ftEval0Value, omegaTimesZeta: evals.ftEval1 }

    allEvals45 :: Vector 45 (PointEval StepField)
    allEvals45 =
      (evals.publicEvals :< ftPointEval :< evals.zEvals :< Vector.nil)
        `Vector.append` evals.indexEvals
        `Vector.append` evals.witnessEvals
        `Vector.append` evals.coeffEvals
        `Vector.append` evals.sigmaEvals

    -- sg evals from bPoly on 2 copies of expanded bp challenges
    sgPointEval :: PointEval StepField
    sgPointEval = { zeta: bPoly expandedBpChals zetaExpanded, omegaTimesZeta: bPoly expandedBpChals zetaw }
    cipAllEvals = [ sgPointEval, sgPointEval ] <> Array.fromFoldable allEvals45
    cipStep { result, scale } eval =
      let
        term = eval.zeta + frResult.evalscale * eval.omegaTimesZeta
      in
        { result: result + scale * term, scale: scale * frResult.xi }
    cip = (Array.foldl cipStep { result: zero, scale: one } cipAllEvals).result

    -- 5. b
    b = computeB expandedBpChals { zeta: zetaExpanded, zetaOmega: zetaw, evalscale: frResult.evalscale }

    -- 6. zetaToSrsLength, zetaToDomainSize
    srsLengthLog2 = reflectType (Proxy :: Proxy StepIPARounds)
    zetaToSrsLength = Curves.pow zetaExpanded (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt srsLengthLog2))
    zetaToDomainSize = Curves.pow zetaExpanded n
  in
    { deferredValues:
        { plonk:
            { alpha: SizedF.wrapF r.stepDummyAlpha
            , beta: SizedF.wrapF r.stepDummyBeta
            , gamma: SizedF.wrapF r.stepDummyGamma
            , zeta: SizedF.wrapF r.stepDummyZeta
            , perm: toShifted (F perm)
            , zetaToSrsLength: toShifted (F zetaToSrsLength)
            , zetaToDomainSize: toShifted (F zetaToDomainSize)
            }
        , combinedInnerProduct: toShifted (F cip)
        , xi: SizedF.wrapF (coerceViaBits frResult.rawXi)
        , bulletproofChallenges: bpChals
        , b: toShifted (F b)
        }
    , shouldFinalize: false
    , spongeDigestBeforeEvaluations: F (zero :: StepField)
    }

-- | Dummy unfinalized proof for the Step circuit's FOP (Step verifying a Wrap proof).
-- |
-- | Computes expand_deferred on tick()-derived proof evaluations, matching OCaml's
-- | Wrap_deferred_values.expand_deferred applied to proof.ml:dummy.
-- |
-- | Uses WrapIPARounds (15) bp challenges from the Wrap IPA, matching the public
-- | input's unfinalized proof structure.
-- |
-- | Reference: mina/src/lib/crypto/pickles/wrap_deferred_values.ml (expand_deferred)
-- | Verified against fixture: packages/pickles-circuit-diffs/test/fixtures/dummy_values.txt
stepDummyUnfinalizedProof
  :: forall sf
   . Shifted (F StepField) sf
  => UnfinalizedProof WrapIPARounds (F StepField) sf Boolean
stepDummyUnfinalizedProof =
  let
    -- Bulletproof challenges (WrapIPARounds = 15)
    -- Raw 128-bit scalar challenges coerced from WrapField to StepField
    bpChals :: Vector WrapIPARounds (SizedF 128 (F StepField))
    bpChals = map (SizedF.wrapF <<< coerceViaBits) roComputeResult.wrapChalRaw
  in
    stepDummyUnfinalizedProofWith bpChals

-- | Dummy FOP proof state with StepIPARounds (16) bp challenges.
-- |
-- | Same deferred values as stepDummyUnfinalizedProof but with Step IPA challenges
-- | (N16) instead of Wrap IPA challenges (N15). Used for the FOP proof states in
-- | the advisory monad and prevChallenges vector.
stepDummyFopProofState
  :: forall sf
   . Shifted (F StepField) sf
  => UnfinalizedProof StepIPARounds (F StepField) sf Boolean
stepDummyFopProofState =
  let
    -- Bulletproof challenges (StepIPARounds = 16)
    -- Raw 128-bit scalar challenges coerced from StepField
    bpChals :: Vector StepIPARounds (SizedF 128 (F StepField))
    bpChals = map SizedF.wrapF roComputeResult.stepChalRaw
  in
    stepDummyUnfinalizedProofWith bpChals

-- | Dummy Step advice for base case (n=1 previous proof slot, all dummy).
-- |
-- | Uses deterministic values from OCaml's proof.ml:dummy:
-- | - Messages: all Pallas generator (Tock.Curve.one)
-- | - Opening proof: generator for delta/sg/lr, Ro.tock() for z1/z2
-- | - FOP proof state: stepDummyFopProofState (from expand_deferred, N16 bp challenges)
-- | - Evals: dummyProofWitness (all zeros)
-- | - Prev challenges: all zeros (base case)
-- |
-- | Reference: mina/src/lib/crypto/pickles/proof.ml:dummy
dummyStepAdvice
  :: { stepInputFields :: Array (F StepField)
     , evals :: Vector 1 (ProofWitness (F StepField))
     , prevChallenges :: Vector 1 (Vector StepIPARounds (F StepField))
     , messages :: Vector 1 { wComm :: Vector 15 (AffinePoint (F StepField)), zComm :: AffinePoint (F StepField), tComm :: Vector 7 (AffinePoint (F StepField)) }
     , openingProofs :: Vector 1 { delta :: AffinePoint (F StepField), sg :: AffinePoint (F StepField), lr :: Vector WrapIPARounds { l :: AffinePoint (F StepField), r :: AffinePoint (F StepField) }, z1 :: Type2 (SplitField (F StepField) Boolean), z2 :: Type2 (SplitField (F StepField) Boolean) }
     , fopProofStates :: Vector 1 (UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean)
     , messagesForNextWrapProof :: Vector 1 (F StepField)
     , wrapVerifierIndex :: { sigmaCommLast :: AffinePoint (F StepField), columnComms :: { index :: Vector 6 (AffinePoint (F StepField)), coeff :: Vector 15 (AffinePoint (F StepField)), sigma :: Vector 6 (AffinePoint (F StepField)) } }
     , sgOld :: Vector 1 (AffinePoint (F StepField))
     }
dummyStepAdvice =
  let
    -- Pallas generator point (= OCaml's Tock.Curve.one)
    g0 :: AffinePoint (F StepField)
    g0 = coerce (unsafePartial fromJust $ Curves.toAffine (Curves.generator :: Pallas.G) :: AffinePoint StepField)

    -- z1/z2 from proof.ml:dummy openings (Ro.tock values wrapped as Type2 SplitField)
    r = roComputeResult

    z1 :: Type2 (SplitField (F StepField) Boolean)
    z1 = toShifted (F r.proofZ1)

    z2 :: Type2 (SplitField (F StepField) Boolean)
    z2 = toShifted (F r.proofZ2)
  in
    { stepInputFields: []
    , evals: dummyProofWitness :< Vector.nil
    , prevChallenges: (Vector.generate \_ -> F zero) :< Vector.nil
    , messages:
        { wComm: Vector.generate \_ -> g0
        , zComm: g0
        , tComm: Vector.generate \_ -> g0
        } :< Vector.nil
    , openingProofs:
        { delta: g0
        , sg: g0
        , lr: Vector.generate \_ -> { l: g0, r: g0 }
        , z1
        , z2
        } :< Vector.nil
    , fopProofStates: stepDummyFopProofState :< Vector.nil
    , messagesForNextWrapProof: F zero :< Vector.nil
    , wrapVerifierIndex:
        { sigmaCommLast: g0
        , columnComms:
            { index: Vector.generate \_ -> g0
            , coeff: Vector.generate \_ -> g0
            , sigma: Vector.generate \_ -> g0
            }
        }
    , sgOld: g0 :< Vector.nil
    }

-- | Zero-valued proof witness for use in base case bootstrapping.
-- |
-- | The evals are zero because the FOP circuit skips evaluation checks
-- | when shouldFinalize = false. Using zero avoids any field-arithmetic
-- | degenerate cases that random values might trigger.
dummyProofWitness :: forall f. Curves.PrimeField f => ProofWitness f
dummyProofWitness =
  { allEvals:
      { ftEval1: zero
      , publicEvals: { zeta: zero, omegaTimesZeta: zero }
      , zEvals: { zeta: zero, omegaTimesZeta: zero }
      , indexEvals: Vector.generate \_ -> { zeta: zero, omegaTimesZeta: zero }
      , witnessEvals: Vector.generate \_ -> { zeta: zero, omegaTimesZeta: zero }
      , coeffEvals: Vector.generate \_ -> { zeta: zero, omegaTimesZeta: zero }
      , sigmaEvals: Vector.generate \_ -> { zeta: zero, omegaTimesZeta: zero }
      }
  }

-- | Stub FinalizeOtherProof params for base case bootstrapping.
-- |
-- | Domain/endo/linearization values are placeholders — the FOP circuit uses
-- | these as compile-time constants but the actual verification is skipped when
-- | shouldFinalize = false.
dummyFinalizeOtherProofParams :: forall f. Curves.PrimeField f => FinalizeOtherProofParams f ()
dummyFinalizeOtherProofParams =
  { domain:
      { generator: one
      , shifts: Vector.generate \_ -> one
      }
  , domainLog2: 0
  , srsLengthLog2: 0
  , endo: zero
  , linearizationPoly: mkLinearizationPoly []
  }

-------------------------------------------------------------------------------
-- | Internal
-------------------------------------------------------------------------------

wrapEndo :: WrapField
wrapEndo = let Curves.EndoScalar e = Curves.endoScalar @Pallas.BaseField @Pallas.ScalarField in e

stepEndo :: StepField
stepEndo = let Curves.EndoScalar e = Curves.endoScalar @Vesta.BaseField @Vesta.ScalarField in e
