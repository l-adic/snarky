module Snarky.Circuit.R1CS.Backend.Compile where

--( 
----Checker
----, Solver
----, SolverT
----, compilePure
-- -- compile
----, makeSolver
----, runSolver
----, runSolverT
--) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (Except, ExceptT, lift, runExceptT)
import Data.Array (zip)
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (for_)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (replicateA)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.Backend.Builder (CircuitBuilderState, emptyCircuitBuilderState, runCircuitBuilderT, setPublicInputVars)
import Snarky.Circuit.Backend.Compile as Snarky.Circuit.Backend.Compile
import Snarky.Circuit.Backend.Prover (emptyProverState, getAssignments, runProverT, setAssignments, throwProverError)
import Snarky.Circuit.CVar (CVar(..), EvaluationError, Variable)
import Snarky.Circuit.DSL.Assert (assertEqual_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, fresh, read, runAsProverT, runSnarky)
import Snarky.Circuit.Types (class CircuitType, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Constraint.R1CS (Gates, R1CS, makeGates)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

--compilePure
--  :: forall f c a b avar bvar
--   . PrimeField f
--  => CircuitType f a avar
--  => CircuitType f b bvar
--  => BasicSystem f c
--  => Proxy a
--  -> Proxy b
--  -> (forall t. CircuitM f c t Identity => avar -> Snarky t Identity bvar)
--  -> CircuitBuilderState c
--compilePure pa pb circuit = un Identity $ compile pa pb circuit

newtype Circuit f i o = Circuit ({ inputs :: i, outputs :: o } -> Gates f)

compile
  :: forall f m a b avar bvar
   . PrimeField f
  => CircuitType f a avar
  => CircuitType f b bvar
  => Monad m
  => Proxy a
  -> Proxy b
  -> (forall t. CircuitM f (R1CS f) t m => avar -> Snarky t m bvar)
  -> m (Circuit f a b)
compile pa pb circuit = do
  { constraints, publicInputs } <- Snarky.Circuit.Backend.Compile.compile pa pb circuit
  let gates = makeGates { constraints, nPublicInputs: Array.length publicInputs }
  unsafeCrashWith ""

--makeSolver
--  :: forall f a b c m avar bvar
--   . PrimeField f
--  => CircuitType f a avar
--  => CircuitType f b bvar
--  => Monad m
--  => BasicSystem f c
--  => Proxy c
--  -> (forall t. CircuitM f c t m => avar -> Snarky t m bvar)
--  -> SolverT f c m a b
--makeSolver _ circuit = \inputs -> do
--  eres <- lift $ flip runProverT emptyProverState do
--    let n = sizeInFields (Proxy @f) (Proxy @a)
--    let m = sizeInFields (Proxy @f) (Proxy @b)
--    vars <- replicateA (n + m) fresh
--    let { before: avars, after: bvars } = Array.splitAt n vars
--    setAssignments $ zip avars (valueToFields inputs)
--    outVar <- runSnarky $ circuit (fieldsToVar @f @a (map Var avars))
--    eres <- getAssignments >>= runAsProverT (read outVar)
--    either throwProverError
--      ( \output -> do
--          setAssignments $ (zip bvars (valueToFields output))
--          pure output
--      )
--      eres
--  case eres of
--    Tuple (Left e) _ -> throwError e
--    Tuple (Right c) { assignments } -> pure $ Tuple c assignments
--
--type SolverResult f a =
--  { result :: a
--  , assignments :: Map Variable f
--  }
--
--type SolverT :: Type -> Type -> (Type -> Type) -> Type -> Type -> Type
--type SolverT f c m a b = a -> ExceptT (EvaluationError f) m (Tuple b (Map Variable f))
--
--runSolverT :: forall f c m a b. SolverT f c m a b -> a -> m (Either (EvaluationError f) (Tuple b (Map Variable f)))
--runSolverT f a = runExceptT (f a)
--
--type Solver f c a b = SolverT f c Identity a b
--
--runSolver :: forall f c a b. Solver f c a b -> a -> Either (EvaluationError f) (Tuple b (Map Variable f))
--runSolver c a = un Identity $ runSolverT c a
--
--type Checker f c =
--  (Variable -> Except (EvaluationError f) f)
--  -> c
--  -> Except (EvaluationError f) Boolean