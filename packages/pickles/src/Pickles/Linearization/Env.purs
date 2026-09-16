-- | The operations and values a linearization token stream is
-- | evaluated against, in a plain-field form (`Env`) and a
-- | constraint-emitting one (`EnvM`).
module Pickles.Linearization.Env
  ( Env
  , EnvM
  , module ReExports
  , EvalPoint
  , Challenges
  , AlphaPowersLen
  , buildCircuitEnvM
  , fieldEnv
  , lookupCell
  , lookupMds
  , precomputeAlphaPowers
  ) where

import Prelude

import Data.Fin (Finite, unsafeFinite)
import Data.Int (pow) as Int
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import JS.BigInt (fromInt)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization.Types (Column(..), CurrOrNext(..), FeatureFlag(..), GateType(..), LookupPattern(..)) as ReExports
import Pickles.Linearization.Types (Column(..), CurrOrNext, FeatureFlag, GateType)
import Poseidon (class PoseidonField, getMdsMatrix)
import Snarky.Circuit.DSL (class BasicSystem, FVar, Snarky, add_, const_, div_, label, pow_, sub_)
import Snarky.Circuit.DSL (mul_) as Circuit
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Curves.Class (class HasEndo, class PrimeField, EndoBase(..), endoBase, fromBigInt, pow)
import Type.Proxy (Proxy(..))

-- | Parse a hex string into a field element. The linearization tables
-- | (`Pickles.Linearization.{Pallas,Vesta}`) carry their constants as hex
-- | literals, and this is the only place they are read.
parseHex :: forall f. Partial => PrimeField f => String -> f
parseHex hex = case fromBigInt <$> BigInt.fromString hex of
  Nothing -> unsafeThrow $ "Failed to parse Hex to BigInt: " <> hex
  Just a -> a

-- | The size of the `alphaPowers` vector, `α^0 .. α^70`, which the
-- | linearization interpreter and both `finalize_other_proof` circuits
-- | index into.
type AlphaPowersLen = 71

-- | Evaluation over values of type `a`. Arithmetic is carried as
-- | fields rather than taken from a `Semiring` instance, to keep
-- | dictionary lookups out of the token loop.
type Env a =
  { add :: a -> a -> a
  , sub :: a -> a -> a
  , mul :: a -> a -> a
  , pow :: a -> Int -> a
  , var :: Column -> CurrOrNext -> a
  , cell :: a -> a
  , alphaPow :: Int -> a
  , mds :: { row :: Int, col :: Int } -> a
  , endoCoefficient :: a
  , field :: String -> a
  , vanishesOnZeroKnowledgeAndPreviousRows :: a
  , unnormalizedLagrangeBasis :: { zkRows :: Boolean, offset :: Int } -> a
  , jointCombiner :: a
  , beta :: a
  , gamma :: a
  , ifFeature :: forall b. { flag :: FeatureFlag, onTrue :: Unit -> b, onFalse :: Unit -> b } -> b
  }

-- | The proof's polynomial evaluations, indexed the way the token
-- | stream addresses them.
type EvalPoint a =
  { witness :: CurrOrNext -> Finite 15 -> a
  , coefficient :: Finite 15 -> a
  , index :: CurrOrNext -> GateType -> a
  , lookupAggreg :: CurrOrNext -> a
  , lookupSorted :: CurrOrNext -> Int -> a
  , lookupTable :: CurrOrNext -> a
  , lookupRuntimeTable :: CurrOrNext -> a
  , lookupRuntimeSelector :: CurrOrNext -> a
  , lookupKindIndex :: Int -> a
  }

-- | The transcript-derived values an `Env` reads.
type Challenges a =
  { alpha :: a
  , beta :: a
  , gamma :: a
  , jointCombiner :: a
  , vanishesOnZeroKnowledgeAndPreviousRows :: a
  , unnormalizedLagrangeBasis :: { zkRows :: Boolean, offset :: Int } -> a
  }

-- | An `Env` over plain field elements. `endoBase` is the endomorphism
-- | constant in `f` itself; `f'` is only the field `HasEndo` pairs
-- | with it.
fieldEnv
  :: forall f f'
   . PoseidonField f
  => HasEndo f f'
  => EvalPoint f
  -> Challenges f
  -> Env f
fieldEnv evalPoint challenges =
  { add: (+)
  , sub: (-)
  , mul: (*)
  , pow: \x n -> pow x (fromInt n)
  , var: \col row -> lookupCell evalPoint col row
  , cell: identity
  , alphaPow: \n -> pow challenges.alpha (fromInt n)
  , mds: \{ row, col } -> lookupMds (Proxy) row col
  , endoCoefficient:
      let
        EndoBase eb = endoBase @f @f'
      in
        eb
  , field: unsafePartial parseHex
  , vanishesOnZeroKnowledgeAndPreviousRows: challenges.vanishesOnZeroKnowledgeAndPreviousRows
  , unnormalizedLagrangeBasis: challenges.unnormalizedLagrangeBasis
  , jointCombiner: challenges.jointCombiner
  , beta: challenges.beta
  , gamma: challenges.gamma
  -- Every feature flag reads as disabled, which for a `SkipIfNot`
  -- pair means taking the `onFalse` branch.
  , ifFeature: \{ onFalse } -> onFalse unit
  }

-- | An `Env` over circuit variables. The fields that cost constraints
-- | — `mul`, `pow`, `computeZetaToNMinus1`, `lagrangeBasis` — return
-- | in `n`; the rest are plain `FVar` arithmetic.
type EnvM f n =
  { add :: FVar f -> FVar f -> FVar f
  , sub :: FVar f -> FVar f -> FVar f
  , mul :: FVar f -> FVar f -> n (FVar f)
  , pow :: FVar f -> Int -> n (FVar f)
  , var :: Column -> CurrOrNext -> FVar f
  , cell :: FVar f -> FVar f
  , alphaPow :: Int -> FVar f
  , mds :: { row :: Int, col :: Int } -> FVar f
  , endoCoefficient :: FVar f
  , field :: String -> FVar f
  , vanishesOnZeroKnowledgeAndPreviousRows :: FVar f
  , computeZetaToNMinus1 :: n (FVar f) -- ^ zeta^n - 1; the interpreter forces this at most once
  , lagrangeBasis :: FVar f -> { zkRows :: Boolean, offset :: Int } -> n (FVar f) -- ^ (zeta^n - 1) / (zeta - omega^i)
  , jointCombiner :: FVar f
  , beta :: FVar f
  , gamma :: FVar f
  , ifFeature :: forall b. { flag :: FeatureFlag, onTrue :: Unit -> b, onFalse :: Unit -> b } -> b
  }

-- | `α^0 .. α^70`, at a cost of 69 multiplication constraints; `α^0`
-- | and `α^1` need none.
precomputeAlphaPowers
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f -- ^ alpha
  -> Snarky f c r (Vector AlphaPowersLen (FVar f))
precomputeAlphaPowers alpha = label "precompute-alpha-powers" do
  Tuple rest _ <- mapAccumM
    ( \prev (_ :: Finite 69) -> do
        next <- Circuit.mul_ alpha prev
        pure (Tuple next next)
    )
    alpha
    (Vector.generate identity :: Vector 69 _)
  pure (Vector.append (const_ one :< alpha :< Vector.nil) rest)

-- | An `EnvM` for in-circuit evaluation. `computeZetaToNMinus1` is
-- | left as an action so its constraints land at the first Lagrange
-- | basis term, not before it.
buildCircuitEnvM
  :: forall f f' c r
   . PrimeField f
  => BasicSystem f c
  => PoseidonField f
  => HasEndo f f'
  => Vector AlphaPowersLen (FVar f) -- ^ precomputed alpha powers α^0..α^70
  -> FVar f -- ^ zeta
  -> Int -- ^ domainLog2
  -> ({ zkRows :: Boolean, offset :: Int } -> FVar f) -- ^ omega power for the lagrange basis
  -> EvalPoint (FVar f)
  -> FVar f -- ^ vanishesOnZeroKnowledgeAndPreviousRows
  -> FVar f -- ^ beta
  -> FVar f -- ^ gamma
  -> FVar f -- ^ jointCombiner
  -> EnvM f (Snarky f c r)
buildCircuitEnvM alphaPowers zeta domainLog2 omegaForLagrange evalPoint vanishesOnZk beta gamma jointCombiner =
  { add: add_
  , sub: sub_
  , mul: Circuit.mul_
  , pow: pow_
  , var: \col row -> lookupCell evalPoint col row
  , cell: identity
  , alphaPow: \n -> Vector.index alphaPowers (unsafeFinite @AlphaPowersLen n)
  , mds: \{ row, col } -> const_ $ lookupMds (Proxy) row col
  , endoCoefficient:
      let
        EndoBase eb = endoBase @f @f'
      in
        const_ eb
  , field: \hex -> const_ $ unsafePartial parseHex hex
  , vanishesOnZeroKnowledgeAndPreviousRows: vanishesOnZk
  , computeZetaToNMinus1: do
      zetaToN <- pow_ zeta (Int.pow 2 domainLog2)
      pure (zetaToN `sub_` const_ one)
  , lagrangeBasis: \zetaToNMinus1 args ->
      div_ zetaToNMinus1 (zeta `sub_` omegaForLagrange args)
  , jointCombiner
  , beta
  , gamma
  , ifFeature: \{ onFalse } -> onFalse unit
  }

lookupMds :: forall f. PoseidonField f => Proxy f -> Int -> Int -> f
lookupMds p row col =
  let
    matrix = getMdsMatrix p
  in
    Vector.index (Vector.index matrix (unsafeFinite @3 row)) (unsafeFinite @3 col)

lookupCell :: forall a. EvalPoint a -> Column -> CurrOrNext -> a
lookupCell ep col row = case col of
  Witness i -> ep.witness row (unsafeFinite @15 i)
  Coefficient i -> ep.coefficient (unsafeFinite @15 i)
  Index g -> ep.index row g
  LookupAggreg -> ep.lookupAggreg row
  LookupSorted i -> ep.lookupSorted row i
  LookupTable -> ep.lookupTable row
  LookupRuntimeTable -> ep.lookupRuntimeTable row
  LookupRuntimeSelector -> ep.lookupRuntimeSelector row
  LookupKindIndex i -> ep.lookupKindIndex i
