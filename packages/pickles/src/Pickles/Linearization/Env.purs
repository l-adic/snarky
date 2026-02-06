-- | Environment for evaluating Kimchi constraint linearization polynomials.
-- | This record provides all operations and values needed to evaluate
-- | the Polish notation expressions in the linearization.
module Pickles.Linearization.Env
  ( Env
  , module ReExports
  , EvalPoint
  , Challenges
  , circuitEnv
  , fieldEnv
  ) where

import Prelude

import Data.Fin (Finite, unsafeFinite)
import Data.Vector as Vector
import JS.BigInt (fromInt)
import Pickles.Linearization.Types (Column(..), CurrOrNext(..), FeatureFlag(..), GateType(..), LookupPattern(..)) as ReExports
import Pickles.Linearization.Types (Column(..), CurrOrNext, FeatureFlag, GateType)
import Poseidon.Class (class PoseidonField, getMdsMatrix)
import Snarky.Circuit.CVar (CVar(..))
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, Snarky, pow_)
import Snarky.Circuit.DSL (mul_) as Circuit
import Snarky.Circuit.Types (FVar)
import Snarky.Curves.Class (class HasEndo, endoBase, pow)
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
  , endoCoefficient: endoBase
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
  { add: \x y -> CVar.add_ <$> x <*> y
  , sub: \x y -> CVar.sub_ <$> x <*> y
  , mul: \x y -> join (Circuit.mul_ <$> x <*> y)
  , pow: \x n -> x >>= \v -> pow_ v n
  , var: \col row -> pure $ lookupCell evalPoint col row
  , cell: identity -- cell is identity since var already returns the value
  , alphaPow: \n -> pow_ challenges.alpha n
  , mds: \{ row, col } -> pure $ Const $ lookupMds (Proxy :: Proxy f) row col
  , endoCoefficient: pure $ Const (endoBase :: f)
  , field: \hex -> pure $ Const $ parseField hex
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
