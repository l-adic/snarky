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
import Snarky.Circuit.DSL (SizedF, fromBits)
import Snarky.Circuit.Kimchi (toFieldPure)
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
-- | OCaml: `Vector.init n ~f:(fun _ -> Ro.scalar_chal ())` evaluates the side effect
-- | for index n-1 first (chal counter 1), then n-2 (counter 2), ..., index 0 (counter n).
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
-- | DummyValues
-------------------------------------------------------------------------------

type DummyValues =
  { ipa ::
      { wrap ::
          { challengesRaw :: Vector WrapIPARounds (SizedF 128 WrapField)
          , challengesExpanded :: Vector WrapIPARounds WrapField
          , sg :: AffinePoint StepField -- Fp coords (Pallas point)
          }
      , step ::
          { challengesRaw :: Vector StepIPARounds (SizedF 128 StepField)
          , challengesExpanded :: Vector StepIPARounds StepField
          , sg :: AffinePoint WrapField -- Fq coords (Vesta point)
          }
      }
  , unfinalized ::
      { plonk ::
          { perm :: WrapField
          , zetaToSrsLength :: WrapField
          , zetaToDomainSize :: WrapField
          }
      , combinedInnerProduct :: WrapField
      , b :: WrapField
      , spongeDigest :: WrapField
      }
  }

-- | Compute all dummy values. Takes the two SRS as arguments (for sg computation).
-- |
-- | OCaml evaluation order:
-- | 1. Dummy.Ipa.Wrap.challenges (eager, chal 1..15)
-- | 2. Dummy.Ipa.Step.challenges (eager, chal 16..31)
-- | 3. Unfinalized.Constant.dummy (lazy, forces Dummy.evals → tock 1..87, then tock 88..89)
computeDummyValues :: CRS Pallas.G -> CRS Vesta.G -> DummyValues
computeDummyValues pallasSrs vestaSrs =
  let
    roResult = flip evalState mkRo do
      -- Phase 1: Eager IPA challenges (dummy.ml module init)
      wrapChalRaw <- replicateChal @WrapIPARounds :: RoM (Vector WrapIPARounds (SizedF 128 WrapField))
      stepChalRaw <- replicateChal @StepIPARounds :: RoM (Vector StepIPARounds (SizedF 128 StepField))

      -- Phase 2: Unfinalized.Constant.dummy (unfinalized.ml:25-104)
      _alpha <- scalarChal :: RoM (SizedF 128 WrapField) -- chal 32
      _beta <- chal :: RoM (SizedF 128 WrapField)        -- chal 33
      _gamma <- chal :: RoM (SizedF 128 WrapField)       -- chal 34
      _zeta <- scalarChal :: RoM (SizedF 128 WrapField)  -- chal 35

      -- Forces Dummy.evals_combined → Dummy.evals
      -- Ro trace shows fq_1 through fq_89 for evals, then fq_90 and fq_91
      -- Total: 89 tock calls for evals, then 2 more for CIP/b
      _evals <- sequence (Array.replicate 89 tock)

      -- fq_90 = b, fq_91 = CIP (verified against fixture)
      bRaw <- tock   -- fq_90
      cipRaw <- tock -- fq_91

      pure { wrapChalRaw, stepChalRaw, cipRaw, bRaw }

    -- Expand challenges
    wrapChalExpanded = map (\c -> toFieldPure c wrapEndo) roResult.wrapChalRaw
    stepChalExpanded = map (\c -> toFieldPure c stepEndo) roResult.stepChalRaw

    -- Compute sg from SRS (OCaml: Ipa.Wrap.compute_sg / Ipa.Step.compute_sg)
    wrapSgCoords = PallasImpl.pallasSrsBPolyCommitment pallasSrs
      (Vector.toUnfoldable wrapChalExpanded)
    wrapSg = { x: unsafeIdx wrapSgCoords 0, y: unsafeIdx wrapSgCoords 1 }

    stepSgCoords = VestaImpl.vestaSrsBPolyCommitment vestaSrs
      (Vector.toUnfoldable stepChalExpanded)
    stepSg = { x: unsafeIdx stepSgCoords 0, y: unsafeIdx stepSgCoords 1 }

    -- Unfinalized plonk values from derive_plonk (hardcoded from OCaml fixture
    -- until we implement Plonk_checks.derive_plonk in PureScript).
    -- Generated by: mina/src/lib/crypto/pickles/dump_dummy/dump_dummy.ml
    fromStr s = Curves.fromBigInt (unsafePartial fromJust (BigInt.fromString s))
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
        { plonk:
            { perm: fromStr "23440605441886153126678695377597650431034969920935116593970373719018050817987"
            , zetaToSrsLength: fromStr "15652644783914055060033111610913539832973880787986945288311229297183530634989"
            , zetaToDomainSize: fromStr "15652644783914055060033111610913539832973880787986945288311229297183530634989"
            }
        , combinedInnerProduct: roResult.cipRaw
        , b: roResult.bRaw
        , spongeDigest: fromStr "6277101735386680764176071790128604879584176795969512275969"
        }
    }

unsafeIdx :: forall a. Array a -> Int -> a
unsafeIdx arr i = unsafePartial fromJust (Array.index arr i)

-------------------------------------------------------------------------------
-- | Convenience re-exports (use default SRS — caller provides)
-------------------------------------------------------------------------------

dummyWrapChallengesRaw :: Vector WrapIPARounds (SizedF 128 WrapField)
dummyWrapChallengesRaw = defaultChallenges.wrapRaw

dummyWrapChallengesExpanded :: Vector WrapIPARounds WrapField
dummyWrapChallengesExpanded = defaultChallenges.wrapExpanded

dummyStepChallengesRaw :: Vector StepIPARounds (SizedF 128 StepField)
dummyStepChallengesRaw = defaultChallenges.stepRaw

dummyStepChallengesExpanded :: Vector StepIPARounds StepField
dummyStepChallengesExpanded = defaultChallenges.stepExpanded

-- | Challenge values only (no SRS needed, computed purely from Ro).
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
