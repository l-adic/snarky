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
  -- * Step Deferred Values & Unfinalized Proof
  , DeferredValues
  , UnfinalizedProof
  -- * Wrap Deferred Values
  , BranchData
  , WrapDeferredValues
  ) where

import Prelude

import Data.Newtype (unwrap)
import Data.Vector (Vector)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (F(..), SizedF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (toFieldPure)
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

-------------------------------------------------------------------------------
-- | Wrap Deferred Values
-------------------------------------------------------------------------------

-- | Branch data: encodes which step branch was verified.
-- |
-- | In OCaml: Branch_data.Checked.Step.t = { domain_log2, proofs_verified_mask }
-- | Packed as: branch_data = 4*domain_log2 + mask[0] + 2*mask[1]
-- |
-- | Reference: composition_types.ml line 211, branch_data.ml
type BranchData f b =
  { domainLog2 :: f
  , proofsVerifiedMask :: Vector 2 b
  }

-- | Wrap deferred values: Step deferred values + branch_data.
-- |
-- | This is what step_verifier.finalize_other_proof receives in OCaml.
-- | The Step FOP uses branch_data for domain selection and proofs-verified masking.
-- |
-- | Note: OCaml's Wrap.Plonk.In_circuit also has feature_flags and joint_combiner,
-- | but these are all constant false/None for vanilla Mina and are omitted here.
-- |
-- | Reference: Wrap.Proof_state.Deferred_values.In_circuit.t (composition_types.ml:185-213)
type WrapDeferredValues d f sf b =
  { plonk :: PlonkInCircuit f sf
  , combinedInnerProduct :: sf
  , xi :: ScalarChallenge f
  , bulletproofChallenges :: BulletproofChallenges d f
  , b :: sf
  , branchData :: BranchData f b
  }

