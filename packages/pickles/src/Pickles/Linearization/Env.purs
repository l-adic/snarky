-- | Environment for evaluating Kimchi constraint linearization polynomials.
-- | This record provides all operations and values needed to evaluate
-- | the Polish notation expressions in the linearization.
module Pickles.Linearization.Env
  ( Env
  , EnvM
  , module ReExports
  , EvalPoint
  , Challenges
  , circuitEnv
  , buildCircuitEnvM
  , fieldEnv
  , lookupCell
  , lookupMds
  , precomputeAlphaPowers
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (Finite, unsafeFinite)
import Data.Int (pow) as Int
import Data.Maybe (fromJust)
import Data.Vector as Vector
import JS.BigInt (fromInt)
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization.Types (Column(..), CurrOrNext(..), FeatureFlag(..), GateType(..), LookupPattern(..)) as ReExports
import Pickles.Linearization.Types (Column(..), CurrOrNext, FeatureFlag, GateType)
import Poseidon (class PoseidonField, getMdsMatrix)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, add_, const_, div_, pow_, sub_)
import Snarky.Circuit.DSL (mul_) as Circuit
import Snarky.Curves.Class (class HasEndo, EndoBase(..), endoBase, pow)
import Type.Proxy (Proxy(..))

-- | Environment providing operations for polynomial evaluation.
-- | The type parameter 'a' is the field type being used.
-- | Note: add/sub/mul are passed explicitly to avoid typeclass dictionary overhead
-- | in large generated expressions.
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

-- | Evaluation point containing polynomial evaluations at zeta and zeta*omega
-- | Type parameter 'a' is the value type (e.g., `f` for direct field values, `FVar f` for circuit variables)
type EvalPoint a =
  { witness :: CurrOrNext -> Finite 15 -> a
  , coefficient :: Finite 15 -> a
  , index :: CurrOrNext -> GateType -> a -- Takes row for Curr/Next evaluation
  , lookupAggreg :: CurrOrNext -> a
  , lookupSorted :: CurrOrNext -> Int -> a
  , lookupTable :: CurrOrNext -> a
  , lookupRuntimeTable :: CurrOrNext -> a
  , lookupRuntimeSelector :: CurrOrNext -> a
  , lookupKindIndex :: Int -> a
  }

-- | Challenge values from the protocol transcript
-- | Type parameter 'a' is the value type (e.g., `f` for direct field values, `FVar f` for circuit variables)
type Challenges a =
  { alpha :: a
  , beta :: a
  , gamma :: a
  , jointCombiner :: a
  , vanishesOnZeroKnowledgeAndPreviousRows :: a
  , unnormalizedLagrangeBasis :: { zkRows :: Boolean, offset :: Int } -> a
  }

-- | Construct a field environment for direct evaluation of linearization polynomials
-- | Note: HasEndo f f' constraint means f is our working field and endoBase gives us
-- | the endo coefficient in that field (e.g., for Pallas base field, we get Pallas endo base)
fieldEnv
  :: forall f f'
   . PoseidonField f
  => HasEndo f f'
  => EvalPoint f
  -> Challenges f
  -> (String -> f) -- field literal parser
  -> Env f
fieldEnv evalPoint challenges parseField =
  { add: (+)
  , sub: (-)
  , mul: (*)
  , pow: \x n -> pow x (fromInt n)
  , var: \col row -> lookupCell evalPoint col row
  , cell: identity
  , alphaPow: \n -> pow challenges.alpha (fromInt n)
  , mds: \{ row, col } -> lookupMds (Proxy :: Proxy f) row col
  , endoCoefficient:
      let
        EndoBase eb = endoBase @f @f'
      in
        eb
  , field: parseField
  , vanishesOnZeroKnowledgeAndPreviousRows: challenges.vanishesOnZeroKnowledgeAndPreviousRows
  , unnormalizedLagrangeBasis: challenges.unnormalizedLagrangeBasis
  , jointCombiner: challenges.jointCombiner
  , beta: challenges.beta
  , gamma: challenges.gamma
  -- All features are treated as disabled for testing, matching Rust behavior.
  -- SkipIfNot(feat): skip when feature disabled → use onFalse (push zero)
  -- SkipIf(feat): don't skip when feature disabled → use onTrue (evaluated)
  , ifFeature: \{ onFalse } -> onFalse unit
  }

-- | Construct a circuit environment for evaluating linearization polynomials
circuitEnv
  :: forall f f' c t m
   . CircuitM f c t m
  => PoseidonField f
  => HasEndo f f'
  => EvalPoint (FVar f)
  -> Challenges (FVar f)
  -> (String -> f) -- field literal parser
  -> Env (Snarky c t m (FVar f))
circuitEnv evalPoint challenges parseField =
  { add: \x y -> add_ <$> x <*> y
  , sub: \x y -> sub_ <$> x <*> y
  , mul: \x y -> join (Circuit.mul_ <$> x <*> y)
  , pow: \x n -> x >>= \v -> pow_ v n
  , var: \col row -> pure $ lookupCell evalPoint col row
  , cell: identity -- cell is identity since var already returns the value
  , alphaPow: \n -> pow_ challenges.alpha n
  , mds: \{ row, col } -> pure $ const_ $ lookupMds (Proxy :: Proxy f) row col
  , endoCoefficient:
      let
        EndoBase eb = endoBase @f @f'
      in
        pure $ const_ eb
  , field: \hex -> pure $ const_ $ parseField hex
  , vanishesOnZeroKnowledgeAndPreviousRows: pure challenges.vanishesOnZeroKnowledgeAndPreviousRows
  , unnormalizedLagrangeBasis: \args -> pure $ challenges.unnormalizedLagrangeBasis args
  , jointCombiner: pure challenges.jointCombiner
  , beta: pure challenges.beta
  , gamma: pure challenges.gamma
  -- All features are treated as disabled for testing, matching Rust behavior.
  -- SkipIfNot(feat): skip when feature disabled → use onFalse (push zero)
  -- SkipIf(feat): don't skip when feature disabled → use onTrue (evaluated)
  , ifFeature: \{ onFalse } -> onFalse unit
  }

-- | Monadic environment for direct-in-Snarky evaluation of linearization.
-- | Pure operations (add, sub, var, cell, alphaPow, constants) return FVar directly.
-- | Monadic operations (mul, pow, unnormalizedLagrangeBasis) run in monad n and create constraints.
-- | The type parameter 'n' is the monad (e.g., Snarky c t m).
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
  , computeZetaToNMinus1 :: n (FVar f) -- ^ Compute zeta^n - 1 (called at most once, memoized by interpreter)
  , lagrangeBasis :: FVar f -> { zkRows :: Boolean, offset :: Int } -> n (FVar f) -- ^ div_ zetaToNMinus1 / (zeta - omega^i)
  , jointCombiner :: FVar f
  , beta :: FVar f
  , gamma :: FVar f
  , ifFeature :: forall b. { flag :: FeatureFlag, onTrue :: Unit -> b, onFalse :: Unit -> b } -> b
  }

-- | Precompute alpha^0..alpha^n via successive multiplication.
-- | alpha^0 = 1 (constant), alpha^1 = alpha (given), alpha^i = alpha * alpha^(i-1).
-- | Returns array of n+1 elements. Cost: (n-1) R1CS constraints.
precomputeAlphaPowers
  :: forall f c t m
   . CircuitM f c t m
  => Int -- ^ max power (inclusive)
  -> FVar f -- ^ alpha
  -> Snarky c t m (Array (FVar f))
precomputeAlphaPowers maxPow alpha = go 2 [ const_ one, alpha ]
  where
  go i acc
    | i > maxPow = pure acc
    | otherwise = do
        let prev = unsafePartial $ fromJust $ Array.last acc
        next <- Circuit.mul_ alpha prev
        go (i + 1) (Array.snoc acc next)

-- | Construct a monadic circuit environment for evaluating linearization polynomials.
-- | Unlike `circuitEnv`, this environment operates directly on `FVar f` values,
-- | avoiding re-computation when stored values are loaded.
-- | The `computeZetaToNMinus1` field defers the zeta^n-1 computation to match
-- | OCaml's lazy binding (plonk_checks.ml:280), which is forced mid-evaluation
-- | at the first UnnormalizedLagrangeBasis token.
buildCircuitEnvM
  :: forall f f' c t m
   . CircuitM f c t m
  => PoseidonField f
  => HasEndo f f'
  => Array (FVar f) -- ^ precomputed alpha powers (alpha^0 .. alpha^n)
  -> FVar f -- ^ zeta
  -> Int -- ^ domainLog2 (for computing zeta^n - 1)
  -> ({ zkRows :: Boolean, offset :: Int } -> f) -- ^ omega constant for lagrange basis call
  -> EvalPoint (FVar f)
  -> FVar f -- ^ vanishesOnZeroKnowledgeAndPreviousRows
  -> FVar f -- ^ beta
  -> FVar f -- ^ gamma
  -> FVar f -- ^ jointCombiner
  -> (String -> f) -- ^ field literal parser
  -> EnvM f (Snarky c t m)
buildCircuitEnvM alphaPowers zeta domainLog2 omegaForLagrange evalPoint vanishesOnZk beta gamma jointCombiner parseField =
  { add: add_
  , sub: sub_
  , mul: Circuit.mul_
  , pow: pow_
  , var: \col row -> lookupCell evalPoint col row
  , cell: identity
  , alphaPow: \n -> unsafePartial $ fromJust $ Array.index alphaPowers n
  , mds: \{ row, col } -> const_ $ lookupMds (Proxy :: Proxy f) row col
  , endoCoefficient:
      let
        EndoBase eb = endoBase @f @f'
      in
        const_ eb
  , field: \hex -> const_ $ parseField hex
  , vanishesOnZeroKnowledgeAndPreviousRows: vanishesOnZk
  , computeZetaToNMinus1: do
      zetaToN <- pow_ zeta (Int.pow 2 domainLog2)
      pure (zetaToN `sub_` const_ one)
  , lagrangeBasis: \zetaToNMinus1 args ->
      div_ zetaToNMinus1 (zeta `sub_` const_ (omegaForLagrange args))
  , jointCombiner
  , beta
  , gamma
  , ifFeature: \{ onFalse } -> onFalse unit
  }

-- | Look up MDS matrix element
lookupMds :: forall f. PoseidonField f => Proxy f -> Int -> Int -> f
lookupMds p row col =
  let
    matrix = getMdsMatrix p
  in
    Vector.index (Vector.index matrix (unsafeFinite row)) (unsafeFinite col)

-- | Look up a cell value from the evaluation point
lookupCell :: forall a. EvalPoint a -> Column -> CurrOrNext -> a
lookupCell ep col row = case col of
  Witness i -> ep.witness row (unsafeFinite i)
  Coefficient i -> ep.coefficient (unsafeFinite i)
  Index g -> ep.index row g -- Pass row to handle Curr/Next evaluation
  LookupAggreg -> ep.lookupAggreg row
  LookupSorted i -> ep.lookupSorted row i
  LookupTable -> ep.lookupTable row
  LookupRuntimeTable -> ep.lookupRuntimeTable row
  LookupRuntimeSelector -> ep.lookupRuntimeSelector row
  LookupKindIndex i -> ep.lookupKindIndex i
