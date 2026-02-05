-- | Core types for the Pickles Step circuit.
-- |
-- | The Step circuit combines an application circuit with verification of
-- | previous Wrap proofs. These types define the deferred values and unfinalized
-- | proof structures used in this verification.
-- |
-- | Key sizes (Pasta curves):
-- | - 16 IPA rounds (bulletproof challenges)
-- | - 128-bit scalar challenges
-- | - 255-bit field elements
-- |
-- | Step circuit runs on Vesta.ScalarField (= Pallas.BaseField = Fp).
-- | It verifies Wrap proofs which run on Pallas.ScalarField (= Vesta.BaseField = Fq).
-- | Since |Fq| < |Fp|, we use Type1 shifted values.
-- |
-- | Reference: mina/src/lib/pickles/unfinalized.ml, composition_types.ml
module Pickles.Step.Types
  ( -- * Bulletproof Challenges
    BulletproofChallenges
  , ScalarChallenge
  -- * Plonk Deferred Values
  , PlonkMinimal
  , PlonkExpanded
  , expandPlonkMinimal
  , expandPlonkMinimalCircuit
  -- * Full Deferred Values
  , DeferredValues
  -- * Unfinalized Proof
  , UnfinalizedProof
  ) where

import Prelude

import Data.Newtype (unwrap)
import Data.Vector (Vector)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.EndoScalar (toField, toFieldPure)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.SizedF (SizedF)

-------------------------------------------------------------------------------
-- | Scalar Challenge (128-bit)
-------------------------------------------------------------------------------

-- | A 128-bit scalar challenge, as squeezed from the sponge.
-- |
-- | These are NOT full field elements - they're 128-bit values that get
-- | converted to full field elements via the endo coefficient when needed.
-- |
-- | Reference: step_verifier.ml:1054 `compute_challenges ~scalar`
type ScalarChallenge f = SizedF 128 f

-------------------------------------------------------------------------------
-- | Bulletproof Challenges
-------------------------------------------------------------------------------

-- | Vector of 16 scalar challenges from IPA rounds.
-- |
-- | For Pasta curves, we have 16 IPA rounds (domain size up to 2^16).
-- | Each challenge is a 128-bit value derived from absorbing L/R pairs.
-- |
-- | Reference: unfinalized.ml:99 `bulletproof_challenges = Dummy.Ipa.Wrap.challenges`
type BulletproofChallenges f = Vector 16 (ScalarChallenge f)

-------------------------------------------------------------------------------
-- | Plonk Minimal Values
-------------------------------------------------------------------------------

-- | Minimal PLONK challenges needed to derive all verification values.
-- |
-- | These are the challenges from the PLONK IOP, plus the evaluations in the
-- | proof, are all that's needed to derive the full In_circuit values.
-- |
-- | Reference: composition_types.ml:36-50 `Plonk.Minimal`
type PlonkMinimal f =
  { alpha :: ScalarChallenge f
  , beta :: f -- Note: beta/gamma are full challenges, not scalar
  , gamma :: f
  , zeta :: ScalarChallenge f
  -- jointCombiner omitted (None for now, used for lookups)
  }

-------------------------------------------------------------------------------
-- | Plonk Expanded Values
-------------------------------------------------------------------------------

-- | PLONK challenges with scalar challenges expanded to full field elements.
-- |
-- | This is the "In_circuit" representation where alpha and zeta have been
-- | converted from 128-bit scalar challenges to full field elements via
-- | the endo coefficient.
-- |
-- | Reference: composition_types.ml In_circuit.map_challenges ~scalar
type PlonkExpanded f =
  { alpha :: f -- expanded from ScalarChallenge
  , beta :: f
  , gamma :: f
  , zeta :: f -- expanded from ScalarChallenge
  }

-- | Expand PlonkMinimal scalar challenges to full field values.
-- |
-- | Converts alpha and zeta from 128-bit scalar challenges to full field
-- | elements using: expanded = a * endo + b
-- | where (a, b) is the decomposition of the 128-bit challenge.
-- |
-- | Reference: step_verifier.ml:857-859 map_challenges ~scalar
expandPlonkMinimal
  :: forall f
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => f -- endo coefficient
  -> PlonkMinimal (F f)
  -> PlonkExpanded f
expandPlonkMinimal endo plonk =
  { alpha: unwrap $ toFieldPure plonk.alpha (F endo)
  , beta: unwrap plonk.beta
  , gamma: unwrap plonk.gamma
  , zeta: unwrap $ toFieldPure plonk.zeta (F endo)
  }

-- | Expand PlonkMinimal scalar challenges to full field values in-circuit.
-- |
-- | Circuit version of expandPlonkMinimal that generates the appropriate
-- | constraints for endo expansion.
expandPlonkMinimalCircuit
  :: forall f t m
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => FVar f -- endo coefficient
  -> PlonkMinimal (FVar f)
  -> Snarky (KimchiConstraint f) t m (PlonkExpanded (FVar f))
expandPlonkMinimalCircuit endo plonk = do
  alpha <- toField plonk.alpha endo
  zeta <- toField plonk.zeta endo
  pure
    { alpha
    , beta: plonk.beta
    , gamma: plonk.gamma
    , zeta
    }

-------------------------------------------------------------------------------
-- | Deferred Values
-------------------------------------------------------------------------------

-- | Deferred scalar-field values that need to be finalized by the next circuit.
-- |
-- | When a circuit partially verifies a proof, it exposes these values in its
-- | public input so the next circuit can finalize verification.
-- |
-- | The `sf` parameter is the shifted value type:
-- | - Type1 for Step verifying Wrap (Wrap scalars < Step field)
-- | - Type2 for Wrap verifying Step (Step scalars > Wrap field)
-- |
-- | Reference: unfinalized.ml:95-101, composition_types.ml Deferred_values
type DeferredValues f sf =
  { plonk :: PlonkMinimal f
  , combinedInnerProduct :: sf
  , xi :: ScalarChallenge f
  , bulletproofChallenges :: BulletproofChallenges f
  , b :: sf
  , perm :: sf -- Permutation argument scalar (shifted)
  }

-------------------------------------------------------------------------------
-- | Unfinalized Proof
-------------------------------------------------------------------------------

-- | An unfinalized proof with a flag indicating whether it should be verified.
-- |
-- | This enables bootstrapping: dummy proofs have `shouldFinalize = false`,
-- | which makes the assertion `finalized || not shouldFinalize` pass regardless
-- | of whether the dummy actually verifies.
-- |
-- | The `b` parameter is the boolean type:
-- | - `Boolean` for constant/value types
-- | - `BoolVar f` for circuit variable types
-- |
-- | Reference: unfinalized.ml:9-12 (comment), wrap_main.ml:431 (assertion)
type UnfinalizedProof f sf b =
  { deferredValues :: DeferredValues f sf
  , shouldFinalize :: b
  , spongeDigestBeforeEvaluations :: f
  }
