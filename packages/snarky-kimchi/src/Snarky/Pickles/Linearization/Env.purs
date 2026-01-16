-- | Environment for evaluating Kimchi constraint linearization polynomials.
-- | This record provides all operations and values needed to evaluate
-- | the Polish notation expressions in the linearization.
module Snarky.Pickles.Linearization.Env
  ( Env
  , Column(..)
  , CurrOrNext(..)
  , GateType(..)
  , LookupPattern(..)
  , FeatureFlag(..)
  , EvalPoint
  , Challenges
  , circuitEnv
  , fieldEnv
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Vector as Vector
import JS.BigInt (fromInt)
import Poseidon.Class (class PoseidonField, getMdsMatrix)
import Snarky.Circuit.CVar (CVar(..))
import Snarky.Circuit.DSL.Field (pow_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky)
import Snarky.Circuit.Types (FVar)
import Snarky.Curves.Class (class HasEndo, endoScalar, pow)
import Type.Proxy (Proxy(..))

-- | Gate types used in Index columns
data GateType
  = CompleteAdd
  | EndoMul
  | EndoMulScalar
  | ForeignFieldAdd
  | ForeignFieldMul
  | Generic
  | Poseidon
  | RangeCheck0
  | RangeCheck1
  | Rot64
  | VarBaseMul
  | Xor16

derive instance Eq GateType
derive instance Ord GateType

-- | Lookup pattern types
data LookupPattern
  = LookupPatternXor
  | LookupPatternLookup
  | LookupPatternRangeCheck
  | LookupPatternForeignFieldMul

derive instance Eq LookupPattern
derive instance Ord LookupPattern

-- | Feature flags for conditional gate inclusion
data FeatureFlag
  = FeatureForeignFieldAdd
  | FeatureForeignFieldMul
  | FeatureLookupTables
  | FeatureRangeCheck0
  | FeatureRangeCheck1
  | FeatureRot
  | FeatureRuntimeLookupTables
  | FeatureXor
  | FeatureLookupPattern LookupPattern
  | FeatureLookupsPerRow Int
  | FeatureTableWidth Int

derive instance Eq FeatureFlag
derive instance Ord FeatureFlag

-- | Column types in the constraint system
data Column
  = Witness Int
  | Coefficient Int
  | Index GateType
  | LookupAggreg
  | LookupKindIndex Int
  | LookupRuntimeSelector
  | LookupRuntimeTable
  | LookupSorted Int
  | LookupTable

derive instance Eq Column
derive instance Ord Column

-- | Row offset (current or next)
data CurrOrNext = Curr | Next

derive instance Eq CurrOrNext
derive instance Ord CurrOrNext

-- | Environment providing operations for polynomial evaluation.
-- | The type parameter 'a' is the field type being used.
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
  { witness :: CurrOrNext -> Int -> a
  , coefficient :: Int -> a
  , index :: GateType -> a
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
fieldEnv
  :: forall f
   . PoseidonField f
  => HasEndo f f
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
  , endoCoefficient: endoScalar
  , field: parseField
  , vanishesOnZeroKnowledgeAndPreviousRows: challenges.vanishesOnZeroKnowledgeAndPreviousRows
  , unnormalizedLagrangeBasis: challenges.unnormalizedLagrangeBasis
  , jointCombiner: challenges.jointCombiner
  , beta: challenges.beta
  , gamma: challenges.gamma
  , ifFeature: \{ onTrue } -> onTrue unit
  }

-- | Construct a circuit environment for evaluating linearization polynomials
circuitEnv
  :: forall f c t m
   . CircuitM f c t m
  => PoseidonField f
  => HasEndo f f
  => EvalPoint (FVar f)
  -> Challenges (FVar f)
  -> (String -> f) -- field literal parser
  -> Env (Snarky c t m (FVar f))
circuitEnv evalPoint challenges parseField =
  { add: \x y -> x + y
  , sub: \x y -> x - y
  , mul: \x y -> x * y
  , pow: \x n -> x >>= \v -> pow_ v n
  , var: \col row -> pure $ lookupCell evalPoint col row
  , cell: identity -- cell is identity since var already returns the value
  , alphaPow: \n -> pow_ challenges.alpha n
  , mds: \{ row, col } -> pure $ Const $ lookupMds (Proxy :: Proxy f) row col
  , endoCoefficient: pure $ Const (endoScalar :: f)
  , field: \hex -> pure $ Const $ parseField hex
  , vanishesOnZeroKnowledgeAndPreviousRows: pure challenges.vanishesOnZeroKnowledgeAndPreviousRows
  , unnormalizedLagrangeBasis: \args -> pure $ challenges.unnormalizedLagrangeBasis args
  , jointCombiner: pure challenges.jointCombiner
  , beta: pure challenges.beta
  , gamma: pure challenges.gamma
  , ifFeature: \{ onTrue } -> onTrue unit -- TODO: proper feature flag handling
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
  Witness i -> ep.witness row i
  Coefficient i -> ep.coefficient i
  Index g -> ep.index g
  LookupAggreg -> ep.lookupAggreg row
  LookupSorted i -> ep.lookupSorted row i
  LookupTable -> ep.lookupTable row
  LookupRuntimeTable -> ep.lookupRuntimeTable row
  LookupRuntimeSelector -> ep.lookupRuntimeSelector row
  LookupKindIndex i -> ep.lookupKindIndex i
