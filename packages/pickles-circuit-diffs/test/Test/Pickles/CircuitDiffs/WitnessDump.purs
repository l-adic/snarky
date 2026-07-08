-- | Witness generation for the circuit-diff harness: run the solver on a concrete input
-- | and package the solved 15-column witness as a `WitnessExport` (all field elements
-- | LE-hex, the encoding the fields' `WriteForeign` instances use).
module Test.Pickles.CircuitDiffs.WitnessDump
  ( buildWitnessExport
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Partial.Unsafe (unsafeCrashWith)
import Pickles.CircuitDiffs.Types (WitnessExport)
import Snarky.Backend.Compile (Solver, runSolver)
import Snarky.Backend.Kimchi (makeWitness)
import Snarky.Circuit.DSL (Variable)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, class SerdeHex, toHexLe)

-- | Solve the circuit on `input` and package the witness columns and public inputs.
-- | The per-row variable layout and public inputs come from the caller's one
-- | `makeGateData`/`compile` — this function only does witness generation.
buildWitnessExport
  :: forall f a b
   . PrimeField f
  => SerdeHex f
  => { constraints :: Array (Vector 15 (Maybe Variable))
     , publicInputs :: Array Variable
     }
  -> Solver f (KimchiConstraint f) a b
  -> a
  -> Effect WitnessExport
buildWitnessExport { constraints, publicInputs } solver input =
  runSolver solver input >>= case _ of
    Left e -> unsafeCrashWith ("witness export: solver failed: " <> show e)
    Right (Tuple _out assignments) -> do
      let
        solved = makeWitness { assignments, constraints, publicInputs }
      pure
        { witness: map (map toHexLe) (Vector.toUnfoldable solved.witness :: Array (Array f))
        , publicInputs: map toHexLe solved.publicInputs
        }
