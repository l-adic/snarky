-- | Pickles-specific type aliases for the Pasta 2-cycle.
-- |
-- | Centralizes field types, IPA round counts, commitment curve aliases,
-- | and Step circuit I/O types used throughout the Pickles modules and tests.
-- |
-- | Reference: mina/src/lib/pickles/common/nat.ml, kimchi_pasta_basic.ml
module Pickles.Types
  ( StepField
  , WrapField
  , StepIPARounds
  , WrapIPARounds
  , StepCommitmentCurve
  , WrapCommitmentCurve
  , StepInput
  , StepStatement
  ) where

import Data.Vector (Vector)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Step circuit field (Fp = Vesta.ScalarField = Pallas.BaseField).
type StepField = Vesta.ScalarField

-- | Wrap circuit field (Fq = Pallas.ScalarField = Vesta.BaseField).
type WrapField = Pallas.ScalarField

-- | IPA rounds in a Step proof (= log2 of Vesta SRS size = Rounds.Step = 16).
type StepIPARounds = 16

-- | IPA rounds in a Step proof (= log2 of Vesta SRS size = Rounds.Step = 16).
-- NOTE: This should be 15, but the circuit is unoptimized
type WrapIPARounds = 16

-- | Step proofs commit on Vesta (scalar field = Fp = StepField).
type StepCommitmentCurve = Vesta.G

-- | Wrap proofs commit on Pallas (scalar field = Fq = WrapField).
type WrapCommitmentCurve = Pallas.G

-------------------------------------------------------------------------------
-- | Step Circuit I/O Types
-------------------------------------------------------------------------------

-- | Input to the Step circuit combinator.
-- |
-- | Bundles the application input with the proof witness data.
-- |
-- | Parameters:
-- | - `n`: Number of previous proofs to verify
-- | - `input`: Application-specific input type
-- | - `prevInput`: Previous proof public input type
-- | - `ds`: Step IPA rounds (phantom, carried for type bookkeeping)
-- | - `dw`: Wrap IPA rounds (used: previous Wrap proofs have dw bulletproof challenges)
-- | - `f`: Field element type
-- | - `sf`: Shifted scalar type
-- | - `b`: Boolean type
type StepInput :: Int -> Type -> Type -> Int -> Int -> Type -> Type -> Type -> Type
type StepInput n input prevInput ds dw f sf b =
  { appInput :: input
  , previousProofInputs :: Vector n prevInput
  , unfinalizedProofs :: Vector n (UnfinalizedProof dw f sf b)
  , prevChallengeDigests :: Vector n f
  }

-- | The Step circuit's output statement.
-- |
-- | This becomes part of the public input for the Wrap circuit to verify.
-- |
-- | The `fv` parameter is the field variable type (e.g., `FVar f` in circuits).
-- | The `sf` parameter is the shifted value type (e.g., `Type1 (FVar f)`).
-- | The `b` parameter is the boolean type (e.g., `BoolVar f`).
-- |
-- | Reference: step_main.ml:587-594 `Types.Step.Statement`
type StepStatement :: Int -> Int -> Int -> Type -> Type -> Type -> Type
type StepStatement n ds dw fv sf b =
  { proofState ::
      { unfinalizedProofs :: Vector n (UnfinalizedProof dw fv sf b)
      , messagesForNextStepProof :: fv
      }
  , messagesForNextWrapProof :: Vector n fv
  }
