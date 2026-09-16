-- | Deterministic randomness for recursion bootstrapping: the `RoM`
-- | monad, whose draws come from a blake2s stream indexed by a
-- | per-kind counter, and `dummyIpaChallenges`, the IPA challenges both
-- | the step and the wrap circuits use.
-- |
-- | The step-side dummy assembly built on these lives in
-- | `Pickles.Step.Dummy`.
module Pickles.Dummy
  ( -- * Ro monad
    Ro
  , RoM
  , evalRoM
  , mkRo
  , initialRo
  , tick
  , tock
  , chal
  , scalarChal
  , replicateChal
  -- * Helpers shared with `Pickles.Step.Dummy`
  , pow2
  , wrapEndo
  , stepEndo
  -- * IPA challenge generators
  , dummyIpaWrapChallenges
  , dummyIpaStepChallenges
  -- * The shared IPA challenge constant
  , dummyIpaChallenges
  ) where

import Prelude

import Data.Array as Array
import Data.Blake2s (blake2s256Bits)
import Data.Foldable (class Foldable, foldr)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Field (StepField, WrapField)
import Pickles.Types (StepIPARounds, WrapIPARounds)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (SizedF, fromBits)
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, EndoScalar(..), endoScalar, fromBigInt) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- Ro state and monad
-------------------------------------------------------------------------------

type Ro =
  { tockCounter :: Int
  , tickCounter :: Int
  , chalCounter :: Int
  }

mkRo :: Ro
mkRo = { tockCounter: 0, tickCounter: 0, chalCounter: 0 }

-- | The starting `Ro` state: an alias of `mkRo` that reads better at a
-- | call site.
initialRo :: Ro
initialRo = mkRo

-- | A pure state monad over `Ro`.
newtype RoM a = RoM (Ro -> Tuple a Ro)

instance Functor RoM where
  map f (RoM g) = RoM \s -> let Tuple a s' = g s in Tuple (f a) s'

instance Apply RoM where
  apply = ap

instance Applicative RoM where
  pure a = RoM \s -> Tuple a s

instance Bind RoM where
  bind (RoM g) f = RoM \s -> let Tuple a s' = g s in case f a of RoM h -> h s'

instance Monad RoM

evalRoM :: forall a. RoM a -> Ro -> a
evalRoM (RoM f) = fst <<< f

bitsToBigInt :: forall f. Foldable f => f Boolean -> BigInt.BigInt
bitsToBigInt = foldr
  (\bit acc -> acc * BigInt.fromInt 2 + (if bit then BigInt.fromInt 1 else BigInt.fromInt 0))
  (BigInt.fromInt 0)

-- | `2^k` as a `BigInt`.
pow2 :: Int -> BigInt.BigInt
pow2 k = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt k)

-- | Blake2s yields 256 bits; `@n` selects a prefix of them as a sized
-- | vector.
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

tock :: RoM WrapField
tock = RoM \ro ->
  let
    next = ro.tockCounter + 1
  in
    Tuple (tockVal next) (ro { tockCounter = next })
  where
  tockVal next = Curves.fromBigInt (bitsToBigInt (bitsRandomOracle @255 ("fq_" <> show next)))

tick :: RoM StepField
tick = RoM \ro ->
  let
    next = ro.tickCounter + 1
  in
    Tuple (tickVal next) (ro { tickCounter = next })
  where
  tickVal next = Curves.fromBigInt (bitsToBigInt (bitsRandomOracle @255 ("fp_" <> show next)))

chal :: forall @f. Curves.FieldSizeInBits f 255 => Curves.PrimeField f => RoM (SizedF 128 f)
chal = RoM \ro ->
  let
    next = ro.chalCounter + 1
  in
    Tuple (fromBits $ bitsRandomOracle @128 ("chal_" <> show next)) (ro { chalCounter = next })

scalarChal :: forall @f. Curves.FieldSizeInBits f 255 => Curves.PrimeField f => RoM (SizedF 128 f)
scalarChal = chal

-- | `n` challenges, indexed against the draw order: index `n-1` holds
-- | counter 1 and index 0 holds counter `n`, so the drawn vector is
-- | reversed. A draw moves nothing but the counter, so the end `Ro`
-- | state is the same either way.
replicateChal
  :: forall @n f
   . Curves.FieldSizeInBits f 255
  => Curves.PrimeField f
  => Reflectable n Int
  => RoM (Vector n (SizedF 128 f))
replicateChal = Vector.reverse <$> Vector.generateA @n (\_ -> chal)

-------------------------------------------------------------------------------
-- IPA challenge generators
-------------------------------------------------------------------------------

-- | The 15 wrap-side IPA challenges.
dummyIpaWrapChallenges :: RoM (Vector WrapIPARounds (SizedF 128 WrapField))
dummyIpaWrapChallenges = replicateChal @WrapIPARounds

-- | The 16 step-side IPA challenges.
dummyIpaStepChallenges :: RoM (Vector StepIPARounds (SizedF 128 StepField))
dummyIpaStepChallenges = replicateChal @StepIPARounds

-- | The IPA challenges, raw and endo-expanded, for both sides.
-- |
-- | They sit at fixed `Ro` positions — the 15 wrap challenges first,
-- | then the 16 step ones — whatever circuit is being compiled, so they
-- | can be a module-level constant and code needing only these does not
-- | have to thread a `BaseCaseDummies` through.
dummyIpaChallenges
  :: { wrapRaw :: Vector WrapIPARounds (SizedF 128 WrapField)
     , wrapExpanded :: Vector WrapIPARounds WrapField
     , stepRaw :: Vector StepIPARounds (SizedF 128 StepField)
     , stepExpanded :: Vector StepIPARounds StepField
     }
dummyIpaChallenges =
  let
    wrapRaw = evalRoM dummyIpaWrapChallenges initialRo
    stepRaw = evalRoM (dummyIpaWrapChallenges *> dummyIpaStepChallenges) initialRo
    wrapExpanded = map (\c -> toFieldPure c wrapEndo) wrapRaw
    stepExpanded = map (\c -> toFieldPure c stepEndo) stepRaw
  in
    { wrapRaw, wrapExpanded, stepRaw, stepExpanded }

-------------------------------------------------------------------------------
-- Endo coefficients
-------------------------------------------------------------------------------

wrapEndo :: WrapField
wrapEndo = let Curves.EndoScalar e = Curves.endoScalar @Pallas.BaseField @Pallas.ScalarField in e

stepEndo :: StepField
stepEndo = let Curves.EndoScalar e = Curves.endoScalar @Vesta.BaseField @Vesta.ScalarField in e
