-- | Core types for Pickles proof verification.
-- |
-- | These types are shared between Step and Wrap circuits. They define the
-- | deferred values and unfinalized proof structures used in verification.
-- |
-- | Key sizes (Pasta curves):
-- | - 128-bit scalar challenges
-- | - 255-bit field elements
-- |
-- | Reference: mina/src/lib/pickles/unfinalized.ml, composition_types.ml
module Pickles.Verify.Types
  ( -- * Bulletproof Challenges
    BulletproofChallenges
  , ScalarChallenge
  -- * Plonk Deferred Values
  , PlonkMinimal
  , PlonkInCircuit
  , toPlonkMinimal
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
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, SizedF, Snarky)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (toField, toFieldPure)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)

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

-- | Vector of scalar challenges from IPA rounds.
-- |
-- | The `d` parameter is the number of IPA rounds. 
-- | Each challenge is a 128-bit value derived
-- | from absorbing L/R pairs.
-- |
-- | Reference: unfinalized.ml:99 `bulletproof_challenges = Dummy.Ipa.Wrap.challenges`
type BulletproofChallenges d f = Vector d (ScalarChallenge f)

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
  , beta :: ScalarChallenge f
  , gamma :: ScalarChallenge f
  , zeta :: ScalarChallenge f
  -- jointCombiner omitted (None for now, used for lookups)
  }

-- | PLONK In_circuit values: minimal challenges plus shifted scalars.
-- |
-- | This extends PlonkMinimal with the shifted scalar values (perm, zeta powers)
-- | that are computed from the plonk challenges. These are stored together in
-- | the deferred values, matching OCaml's `Plonk.In_circuit`.
-- |
-- | Reference: composition_types.ml Plonk.In_circuit
type PlonkInCircuit f sf =
  { alpha :: ScalarChallenge f
  , beta :: ScalarChallenge f
  , gamma :: ScalarChallenge f
  , zeta :: ScalarChallenge f
  , perm :: sf
  , zetaToSrsLength :: sf
  , zetaToDomainSize :: sf
  }

-- | Extract the minimal challenges from PlonkInCircuit.
toPlonkMinimal :: forall f sf. PlonkInCircuit f sf -> PlonkMinimal f
toPlonkMinimal p = { alpha: p.alpha, beta: p.beta, gamma: p.gamma, zeta: p.zeta }

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
  , beta: unwrap $ SizedF.toField plonk.beta
  , gamma: unwrap $ SizedF.toField plonk.gamma
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
  alpha <- toField @8 plonk.alpha endo
  zeta <- toField @8 plonk.zeta endo
  pure
    { alpha
    , beta: SizedF.toField plonk.beta
    , gamma: SizedF.toField plonk.gamma
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
type DeferredValues d f sf =
  { plonk :: PlonkInCircuit f sf
  , combinedInnerProduct :: sf
  , xi :: ScalarChallenge f
  , bulletproofChallenges :: BulletproofChallenges d f
  , b :: sf
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
type UnfinalizedProof d f sf b =
  { deferredValues :: DeferredValues d f sf
  , shouldFinalize :: b
  , spongeDigestBeforeEvaluations :: f
  }
