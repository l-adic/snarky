-- | Environment for evaluating Kimchi constraint linearization polynomials.
-- | This record provides all operations and values needed to evaluate
-- | the Polish notation expressions in the linearization.
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

import Control.Monad.State (StateT, evalStateT, get, put)
import Control.Monad.Trans.Class (lift)
import Data.Fin (Finite, unsafeFinite)
import Data.Int (pow) as Int
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import JS.BigInt (fromInt)
import Partial.Unsafe (unsafePartial)
import Pickles.Hex (parseHex)
import Pickles.Linearization.Types (Column(..), CurrOrNext(..), FeatureFlag(..), GateType(..), LookupPattern(..)) as ReExports
import Pickles.Linearization.Types (Column(..), CurrOrNext, FeatureFlag, GateType)
import Poseidon (class PoseidonField, getMdsMatrix)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, add_, const_, div_, label, pow_, sub_)
import Snarky.Circuit.DSL (mul_) as Circuit
import Snarky.Curves.Class (class HasEndo, EndoBase(..), endoBase, pow)
import Type.Proxy (Proxy(..))

-- | Number of precomputed powers of α: `α^0 .. α^70`. Drives the size
-- | of the `alphaPowers` vector consumed by
-- | `Pickles.Linearization.Interpreter` + the two
-- | `FinalizeOtherProof` circuits. Matches OCaml
-- | `Plonk_checks.scalars_env`'s max alpha exponent.
type AlphaPowersLen = 71

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
  -> Env f
fieldEnv evalPoint challenges =
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
  , field: unsafePartial parseHex
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

-- | Precompute α^0..α^70 via successive multiplication, producing a
-- | `Vector AlphaPowersLen (FVar f)` (71 entries). Cost: 69 R1CS
-- | constraints.
-- |
-- | Internals: seed with `[α^0, α^1] = [1, α]`, then generate α^2..α^70
-- | via a StateT-threaded monadic scan (`Vector.generateA` carrying the
-- | previous power). Each step emits one `Circuit.mul_` constraint.
-- | Type-level `Vector.append` glues the seed and the generated tail
-- | into the final `Vector 71` — no runtime length check needed.
precomputeAlphaPowers
  :: forall f c t m
   . CircuitM f c t m
  => FVar f -- ^ alpha
  -> Snarky c t m (Vector AlphaPowersLen (FVar f))
precomputeAlphaPowers alpha = label "precompute-alpha-powers" do
  let
    step :: Finite 69 -> StateT (FVar f) (Snarky c t m) (FVar f)
    step _ = do
      prev <- get
      next <- lift (Circuit.mul_ alpha prev)
      put next
      pure next
  rest <- evalStateT (Vector.generateA @69 step) alpha
  pure (Vector.append (const_ one :< alpha :< Vector.nil) rest)

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
  => Vector AlphaPowersLen (FVar f) -- ^ precomputed alpha powers α^0..α^70
  -> FVar f -- ^ zeta
  -> Int -- ^ domainLog2 (for computing zeta^n - 1)
  -> ({ zkRows :: Boolean, offset :: Int } -> FVar f) -- ^ omega power for lagrange basis (may be circuit variable)
  -> EvalPoint (FVar f)
  -> FVar f -- ^ vanishesOnZeroKnowledgeAndPreviousRows
  -> FVar f -- ^ beta
  -> FVar f -- ^ gamma
  -> FVar f -- ^ jointCombiner
  -> EnvM f (Snarky c t m)
buildCircuitEnvM alphaPowers zeta domainLog2 omegaForLagrange evalPoint vanishesOnZk beta gamma jointCombiner =
  { add: add_
  , sub: sub_
  , mul: Circuit.mul_
  , pow: pow_
  , var: \col row -> lookupCell evalPoint col row
  , cell: identity
  , alphaPow: \n -> Vector.index alphaPowers (unsafeFinite @AlphaPowersLen n)
  , mds: \{ row, col } -> const_ $ lookupMds (Proxy :: Proxy f) row col
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

-- | Look up MDS matrix element
lookupMds :: forall f. PoseidonField f => Proxy f -> Int -> Int -> f
lookupMds p row col =
  let
    matrix = getMdsMatrix p
  in
    Vector.index (Vector.index matrix (unsafeFinite @3 row)) (unsafeFinite @3 col)

-- | Look up a cell value from the evaluation point
lookupCell :: forall a. EvalPoint a -> Column -> CurrOrNext -> a
lookupCell ep col row = case col of
  Witness i -> ep.witness row (unsafeFinite @15 i)
  Coefficient i -> ep.coefficient (unsafeFinite @15 i)
  Index g -> ep.index row g -- Pass row to handle Curr/Next evaluation
  LookupAggreg -> ep.lookupAggreg row
  LookupSorted i -> ep.lookupSorted row i
  LookupTable -> ep.lookupTable row
  LookupRuntimeTable -> ep.lookupRuntimeTable row
  LookupRuntimeSelector -> ep.lookupRuntimeSelector row
  LookupKindIndex i -> ep.lookupKindIndex i
