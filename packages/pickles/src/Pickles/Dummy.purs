-- | Deterministic randomness infrastructure used by Pickles for
-- | recursion bootstrapping (the Ro monad) plus the shared
-- | `dummyIpaChallenges` constant consumed by both step- and wrap-side
-- | circuits.
-- |
-- | Step-side dummy assembly (`BaseCaseDummies`, `dummyEvals`,
-- | `wrapDummyUnfinalizedProof`, `computeDummySgValues`, etc.) lives in
-- | `Pickles.Step.Dummy`.
-- |
-- | Reference: mina/src/lib/pickles/ro.ml, dummy.ml's IPA challenges.
module Pickles.Dummy
  ( -- * Ro monad
    Ro
  , RoM
  , mkRo
  , initialRo
  , tick
  , tock
  , chal
  , scalarChal
  , replicateChal
  -- * Internal helpers re-used by Pickles.Step.Dummy
  , pow2
  , wrapEndo
  , stepEndo
  -- * IPA challenge generators
  , dummyIpaWrapChallenges
  , dummyIpaStepChallenges
  -- * Shared `Dummy.Ipa.{Step,Wrap}.challenges` constant
  , dummyIpaChallenges
  ) where

import Prelude

import Control.Monad.State (State, evalState, get, put)
import Data.Array as Array
import Data.Blake2s (blake2s256Bits)
import Data.Foldable (class Foldable, foldr)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Step.Types as Step
import Pickles.Types (StepIPARounds, WrapIPARounds)
import Pickles.Wrap.Types as Wrap
import Prim.Int (class Add)
import Snarky.Circuit.DSL (SizedF, fromBits)
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, EndoScalar(..), endoScalar, fromBigInt) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
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

-- | Canonical "start" Ro state. Alias of `mkRo`, renamed to surface the
-- | intent at callsites (e.g. test setups pass `initialRo` into
-- | `evalStateT` at the top of a `StateT Ro m` block).
initialRo :: Ro
initialRo = mkRo

type RoM = State Ro

bitsToBigInt :: forall f. Foldable f => f Boolean -> BigInt.BigInt
bitsToBigInt = foldr
  (\bit acc -> acc * BigInt.fromInt 2 + (if bit then BigInt.fromInt 1 else BigInt.fromInt 0))
  (BigInt.fromInt 0)

-- | `2^k` as a BigInt. Reduces BigInt.{fromInt,pow} noise at usage sites.
pow2 :: Int -> BigInt.BigInt
pow2 k = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt k)

-- | Blake2s yields 256 bits; `@n` < 257 selects a prefix as a sized vector.
bitsRandomOracle
  :: forall @n nComplement
   . Reflectable n Int
  => Add n nComplement 256
  => String
  -> Vector n Boolean
bitsRandomOracle s =
  let
    n = reflectType (Proxy @n)
  in
    unsafePartial $ fromJust $ Vector.toVector @n (Array.take n (blake2s256Bits s))

tock :: RoM Wrap.Field
tock = do
  ro <- get
  let next = ro.tockCounter + 1
  put $ ro { tockCounter = next }
  pure $ Curves.fromBigInt (bitsToBigInt (bitsRandomOracle @255 ("fq_" <> show next)))

tick :: RoM Step.Field
tick = do
  ro <- get
  let next = ro.tickCounter + 1
  put $ ro { tickCounter = next }
  pure $ Curves.fromBigInt (bitsToBigInt (bitsRandomOracle @255 ("fp_" <> show next)))

chal :: forall @f. Curves.FieldSizeInBits f 255 => Curves.PrimeField f => RoM (SizedF 128 f)
chal = do
  ro <- get
  let next = ro.chalCounter + 1
  put $ ro { chalCounter = next }
  pure $ fromBits $ bitsRandomOracle @128 ("chal_" <> show next)

scalarChal :: forall @f. Curves.FieldSizeInBits f 255 => Curves.PrimeField f => RoM (SizedF 128 f)
scalarChal = chal

-- | Generate n challenges, reversed to match OCaml's right-to-left
-- | Vector.init evaluation.
-- |
-- | OCaml pitfall: `Vector.init n ~f:(fun _ -> Ro.scalar_chal())` evaluates
-- | the side-effecting function right-to-left — index n-1 gets chal counter 1,
-- | index 0 gets counter n. We reverse the generated vector so the stored
-- | values match OCaml's index→counter mapping. (The effect order differs,
-- | but only the chal counter is touched, so the end state is identical.)
replicateChal
  :: forall @n f
   . Curves.FieldSizeInBits f 255
  => Curves.PrimeField f
  => Reflectable n Int
  => RoM (Vector n (SizedF 128 f))
replicateChal = Vector.reverse <$> Vector.generateA @n (\_ -> chal)

-------------------------------------------------------------------------------
-- | IPA challenge generators
-------------------------------------------------------------------------------

-- | 15 chals — OCaml `Dummy.Ipa.Wrap.challenges` (dummy.ml:28-33),
-- | eager module init.
dummyIpaWrapChallenges :: RoM (Vector WrapIPARounds (SizedF 128 Wrap.Field))
dummyIpaWrapChallenges = replicateChal @WrapIPARounds

-- | 16 chals — OCaml `Dummy.Ipa.Step.challenges` (dummy.ml:44-48),
-- | eager module init.
dummyIpaStepChallenges :: RoM (Vector StepIPARounds (SizedF 128 Step.Field))
dummyIpaStepChallenges = replicateChal @StepIPARounds

-- | IPA challenges are force-order-invariant — `Dummy.Ipa.Wrap.challenges`
-- | and `Dummy.Ipa.Step.challenges` in OCaml are eager module-init values
-- | drawn at fixed Ro positions regardless of which circuit is compiled.
-- | We mirror that with a module-level constant so circuit-building code
-- | that only needs IPA challenges (e.g. wrap main's dummy challenge /
-- | padding sponge states) doesn't have to thread `BaseCaseDummies`.
dummyIpaChallenges
  :: { wrapRaw :: Vector WrapIPARounds (SizedF 128 Wrap.Field)
     , wrapExpanded :: Vector WrapIPARounds Wrap.Field
     , stepRaw :: Vector StepIPARounds (SizedF 128 Step.Field)
     , stepExpanded :: Vector StepIPARounds Step.Field
     }
dummyIpaChallenges =
  let
    wrapRaw = evalState dummyIpaWrapChallenges initialRo
    stepRaw = evalState (dummyIpaWrapChallenges *> dummyIpaStepChallenges) initialRo
    wrapExpanded = map (\c -> toFieldPure c wrapEndo) wrapRaw
    stepExpanded = map (\c -> toFieldPure c stepEndo) stepRaw
  in
    { wrapRaw, wrapExpanded, stepRaw, stepExpanded }

-------------------------------------------------------------------------------
-- | Endo coefficients (re-used by Pickles.Step.Dummy)
-------------------------------------------------------------------------------

wrapEndo :: Wrap.Field
wrapEndo = let Curves.EndoScalar e = Curves.endoScalar @Pallas.BaseField @Pallas.ScalarField in e

stepEndo :: Step.Field
stepEndo = let Curves.EndoScalar e = Curves.endoScalar @Vesta.BaseField @Vesta.ScalarField in e
