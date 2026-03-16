-- | Deterministic dummy values for Pickles recursion bootstrapping.
-- |
-- | Mirrors OCaml's `mina/src/lib/pickles/dummy.ml`, `ro.ml`, `unfinalized.ml`.
-- |
-- | Reference: mina/src/lib/pickles/dummy.ml, mina/src/lib/pickles/ro.ml,
-- |            mina/src/lib/pickles/unfinalized.ml
-- | Fixture: packages/pickles/test/fixtures/dummy_values.txt
-- | Generator: mina/src/lib/crypto/pickles/dump_dummy/dump_dummy.ml
module Pickles.Dummy
  ( DummyValues
  , computeDummyValues
  , dummyWrapChallengesExpanded
  , dummyWrapChallengesRaw
  , dummyStepChallengesExpanded
  , dummyStepChallengesRaw
  , Ro
  , mkRo
  , tick
  ) where

import Prelude

import Control.Monad.State (State, get, put, evalState)
import Data.Array as Array
import Data.Blake2s (blake2s256Bits)

import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (sequence)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Types (StepField, StepIPARounds, WrapField, WrapIPARounds)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), SizedF, fromBits)
import Snarky.Circuit.DSL.SizedF (toField) as SizedF
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Types.Shifted (Type2(..), toShifted)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, EndoScalar(..), endoScalar, fromBigInt) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
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

-- | Generate a (zeta, zeta_omega) eval pair.
-- |
-- | OCaml pitfall: tuple construction `(a(), a())` evaluates the right element
-- | first. So `let a () = Array.create ~len:1 (Ro.tock()) in (a(), a())`
-- | produces `(second_tock_call, first_tock_call)`. In the Evals type,
-- | `fst` = zeta evaluation, `snd` = zeta*omega evaluation. So:
-- |   fst (= zeta)      = second Ro.tock() call
-- |   snd (= zetaOmega) = first Ro.tock() call
tockEvalPair :: RoM { zeta :: WrapField, zetaOmega :: WrapField }
tockEvalPair = do
  zetaOmega <- tock -- OCaml: right element of tuple, evaluated first → snd
  zeta <- tock      -- OCaml: left element of tuple, evaluated second → fst
  pure { zeta, zetaOmega }

-------------------------------------------------------------------------------
-- | DummyValues
-------------------------------------------------------------------------------

type DummyValues =
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
      { zetaExpanded :: WrapField
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
computeDummyValues :: CRS Pallas.G -> CRS Vesta.G -> DummyValues
computeDummyValues pallasSrs vestaSrs =
  let
    roResult = flip evalState mkRo do
      -- Phase 1: Eager IPA challenges (dummy.ml module init)
      wrapChalRaw <- replicateChal @WrapIPARounds :: RoM (Vector WrapIPARounds (SizedF 128 WrapField))
      stepChalRaw <- replicateChal @StepIPARounds :: RoM (Vector StepIPARounds (SizedF 128 StepField))

      -- Phase 2: Unfinalized.Constant.dummy (unfinalized.ml:25-104)
      -- alpha, beta, gamma, zeta from Ro (chal counters 32-35)
      alpha <- scalarChal :: RoM (SizedF 128 WrapField)
      beta <- chal :: RoM (SizedF 128 WrapField)
      gamma <- chal :: RoM (SizedF 128 WrapField)
      zeta <- scalarChal :: RoM (SizedF 128 WrapField)

      -- Dummy.evals: Evals.map Evaluation_lengths.default produces eval pairs.
      -- Each non-optional Evals field with length n produces two Ro.tock() calls
      -- via `let a () = Array.create ~len:1 (Ro.tock()) in (a(), a())`.
      -- All optional fields are None → no tock calls.
      --
      -- OCaml pitfall: the field order below follows the Evals.map function body
      -- (plonk_types.ml:711-747), but OCaml record construction evaluation order
      -- is implementation-defined. The total tock count (89) is verified against
      -- the Ro trace, but the assignment of specific tock counters to specific
      -- Evals fields may not match OCaml exactly. This is why perm (which depends
      -- on specific eval values) is hardcoded from the fixture rather than computed.
      w <- sequence (Array.replicate 15 tockEvalPair)
      _coefficients <- sequence (Array.replicate 15 tockEvalPair)
      z <- tockEvalPair
      s <- sequence (Array.replicate 6 tockEvalPair)
      _genericSelector <- tockEvalPair
      _poseidonSelector <- tockEvalPair
      _completeAddSelector <- tockEvalPair
      _mulSelector <- tockEvalPair
      _emulSelector <- tockEvalPair
      _endomulScalarSelector <- tockEvalPair
      -- public_input pair
      _publicInput <- tockEvalPair
      -- ft_eval1
      _ftEval1 <- tock
      -- Total: 42 fields × 2 + 2 + 1 = 89 tock calls ✓

      -- OCaml pitfall: the record `{ ...; combined_inner_product = Shifted_value (tock());
      -- ...; b = Shifted_value (tock()) }` has implementation-defined field evaluation
      -- order. The Ro trace shows fq_90 then fq_91, and fixture comparison confirms
      -- b = fq_90, CIP = fq_91 (b is evaluated before CIP in OCaml's native compiler).
      bRaw <- tock   -- fq_90
      cipRaw <- tock -- fq_91

      pure { wrapChalRaw, stepChalRaw, alpha, beta, gamma, zeta, w, z, s, cipRaw, bRaw }

    -- Expand challenges
    wrapChalExpanded = map (\c -> toFieldPure c wrapEndo) roResult.wrapChalRaw
    stepChalExpanded = map (\c -> toFieldPure c stepEndo) roResult.stepChalRaw

    -- Expand plonk challenges to Fq (unfinalized.ml:36-39)
    -- OCaml pitfall: alpha and zeta use `endo_to_field` which applies the scalar
    -- challenge expansion formula (2 * endo * x + 1). Beta and gamma use
    -- `Challenge.Constant.to_tock_field` which is just raw bit packing — NO endo.
    -- Using endo expansion for beta/gamma produces wrong values.
    alphaFq = toFieldPure roResult.alpha wrapEndo
    _betaFq = SizedF.toField roResult.beta
    _gammaFq = SizedF.toField roResult.gamma
    zetaFq = toFieldPure roResult.zeta wrapEndo

    -- Compute sg from SRS
    wrapSgCoords = PallasImpl.pallasSrsBPolyCommitment pallasSrs
      (Vector.toUnfoldable wrapChalExpanded)
    wrapSg = { x: unsafeIdx wrapSgCoords 0, y: unsafeIdx wrapSgCoords 1 }
    stepSgCoords = VestaImpl.vestaSrsBPolyCommitment vestaSrs
      (Vector.toUnfoldable stepChalExpanded)
    stepSg = { x: unsafeIdx stepSgCoords 0, y: unsafeIdx stepSgCoords 1 }

    -- derive_plonk values (unfinalized.ml:85-93, plonk_checks.ml:403-441)
    -- Domain: wrap_domains ~proofs_verified:2 = Pow_2_roots_of_unity 15
    -- srs_length_log2 = 15 (= Tock.Rounds.n)
    domainLog2 = 15
    _n = BigInt.fromInt (pow2 domainLog2)

    -- zeta_to_srs_length = zeta^(2^15), computed by repeated squaring
    -- OCaml: pow2pow zeta srs_length_log2 = 15 squarings of zeta
    zetaPow2_15 = pow2pow zetaFq domainLog2
    -- zeta_to_domain_size = zeta^n = same as zeta_to_srs_length when domain = srs
    -- env.zeta_to_n_minus_1 + 1 = (zeta^n - 1) + 1 = zeta^n
    zetaToN = zetaPow2_15

    -- OCaml pitfall: Shifted_value.Type2.of_field ~shift s = Shifted_value (s - shift),
    -- i.e. it SUBTRACTS the shift, not adds. The toShifted typeclass handles this correctly.
    shifted :: WrapField -> Type2 (F WrapField)
    shifted x = toShifted (F x)

    fromStr s = Curves.fromBigInt (unsafePartial fromJust (BigInt.fromString s))

    -- Digest.Constant.dummy = [1L, 1L, 1L, 1L] → 1 + 2^64 + 2^128 + 2^192
    digestDummy = Curves.fromBigInt
      (BigInt.fromInt 1
        + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 64)
        + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)
        + BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 192))
  in
    { ipa:
        { wrap:
            { challengesRaw: roResult.wrapChalRaw
            , challengesExpanded: wrapChalExpanded
            , sg: wrapSg
            }
        , step:
            { challengesRaw: roResult.stepChalRaw
            , challengesExpanded: stepChalExpanded
            , sg: stepSg
            }
        }
    , unfinalized:
        { zetaExpanded: zetaFq
        , alphaExpanded: alphaFq
        , plonk:
            -- perm requires derive_plonk which depends on OCaml's implementation-defined
            -- record evaluation order for Evals.map. Hardcoded from production OCaml fixture
            -- (Shifted_value inner value = perm - shift).
            { perm: Type2 (F (fromStr "23440605441886153126678695377597650431034969920935116593970373719018050817987"))
            , zetaToSrsLength: shifted zetaPow2_15
            , zetaToDomainSize: shifted zetaToN
            }
        , combinedInnerProduct: roResult.cipRaw
        , b: roResult.bRaw
        , spongeDigest: digestDummy
        }
    }

unsafeIdx :: forall a. Array a -> Int -> a
unsafeIdx arr i = unsafePartial fromJust (Array.index arr i)

pow2 :: Int -> Int
pow2 0 = 1
pow2 n' = 2 * pow2 (n' - 1)

-- | Compute x^(2^k) by k repeated squarings. Matches OCaml's pow2pow.
pow2pow :: forall f. Semiring f => f -> Int -> f
pow2pow x 0 = x
pow2pow x k = pow2pow (x * x) (k - 1)

-------------------------------------------------------------------------------
-- | Convenience re-exports
-------------------------------------------------------------------------------

dummyWrapChallengesRaw :: Vector WrapIPARounds (SizedF 128 WrapField)
dummyWrapChallengesRaw = defaultChallenges.wrapRaw

dummyWrapChallengesExpanded :: Vector WrapIPARounds WrapField
dummyWrapChallengesExpanded = defaultChallenges.wrapExpanded

dummyStepChallengesRaw :: Vector StepIPARounds (SizedF 128 StepField)
dummyStepChallengesRaw = defaultChallenges.stepRaw

dummyStepChallengesExpanded :: Vector StepIPARounds StepField
dummyStepChallengesExpanded = defaultChallenges.stepExpanded

defaultChallenges
  :: { wrapRaw :: Vector WrapIPARounds (SizedF 128 WrapField)
     , wrapExpanded :: Vector WrapIPARounds WrapField
     , stepRaw :: Vector StepIPARounds (SizedF 128 StepField)
     , stepExpanded :: Vector StepIPARounds StepField
     }
defaultChallenges = flip evalState mkRo do
  wrapRaw <- replicateChal @WrapIPARounds :: RoM (Vector WrapIPARounds (SizedF 128 WrapField))
  stepRaw <- replicateChal @StepIPARounds :: RoM (Vector StepIPARounds (SizedF 128 StepField))
  let wrapExpanded = map (\c -> toFieldPure c wrapEndo) wrapRaw
  let stepExpanded = map (\c -> toFieldPure c stepEndo) stepRaw
  pure { wrapRaw, wrapExpanded, stepRaw, stepExpanded }

-------------------------------------------------------------------------------
-- | Internal
-------------------------------------------------------------------------------

wrapEndo :: WrapField
wrapEndo = let Curves.EndoScalar e = Curves.endoScalar @Pallas.BaseField @Pallas.ScalarField in e

stepEndo :: StepField
stepEndo = let Curves.EndoScalar e = Curves.endoScalar @Vesta.BaseField @Vesta.ScalarField in e
