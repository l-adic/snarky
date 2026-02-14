-- | Pickles-specific type aliases for the Pasta 2-cycle.
-- |
-- | Centralizes field types, IPA round counts, and commitment curve aliases
-- | used throughout the Pickles Step/Wrap circuit modules and tests.
-- |
-- | Reference: mina/src/lib/pickles/common/nat.ml, kimchi_pasta_basic.ml
module Pickles.Types
  ( StepField
  , WrapField
  , StepIPARounds
  , WrapIPARounds
  , StepCommitmentCurve
  , WrapCommitmentCurve
  ) where

import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Step circuit field (Fp = Vesta.ScalarField = Pallas.BaseField).
type StepField = Vesta.ScalarField

-- | Wrap circuit field (Fq = Pallas.ScalarField = Vesta.BaseField).
type WrapField = Pallas.ScalarField

-- | IPA rounds in a Step proof (= log2 of Vesta SRS size = Rounds.Step = 16).
type StepIPARounds = 16

-- | IPA rounds in a Wrap proof (= log2 of Pallas SRS size = Rounds.Wrap = 15).
-- | Requires a 2^15 Pallas SRS (created via crsCreate, not loaded from cache).
type WrapIPARounds = 15

-- | Step proofs commit on Vesta (scalar field = Fp = StepField).
type StepCommitmentCurve = Vesta.G

-- | Wrap proofs commit on Pallas (scalar field = Fq = WrapField).
type WrapCommitmentCurve = Pallas.G
