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
    BulletproofChallenges(..)
  , ScalarChallenge
  -- * Plonk Deferred Values
  , PlonkMinimal(..)
  -- * Full Deferred Values
  , DeferredValues(..)
  -- * Unfinalized Proof
  , UnfinalizedProof(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Show.Generic (genericShow)
import Data.Vector (Vector)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, BoolVar, F, FVar, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.SizedF (SizedF)
import Snarky.Types.Shifted (Type1)

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
newtype BulletproofChallenges f = BulletproofChallenges (Vector 16 (ScalarChallenge f))

derive instance Newtype (BulletproofChallenges f) _
derive instance Eq f => Eq (BulletproofChallenges f)
derive instance Generic (BulletproofChallenges f) _

instance Show f => Show (BulletproofChallenges f) where
  show = genericShow

instance
  ( PrimeField f
  , FieldSizeInBits f 255
  ) =>
  CircuitType f (BulletproofChallenges (F f)) (BulletproofChallenges (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(BulletproofChallenges (F f))
  fieldsToVar = genericFieldsToVar @(BulletproofChallenges (F f))

instance
  ( PrimeField f
  , FieldSizeInBits f 255
  , BasicSystem f c
  ) =>
  CheckedType f c (BulletproofChallenges (FVar f)) where
  check = genericCheck

-------------------------------------------------------------------------------
-- | Plonk Minimal Values
-------------------------------------------------------------------------------

-- | Minimal PLONK challenges needed to derive all verification values.
-- |
-- | These are the challenges from the PLONK IOP, plus the evaluations in the
-- | proof, are all that's needed to derive the full In_circuit values.
-- |
-- | Reference: composition_types.ml:36-50 `Plonk.Minimal`
newtype PlonkMinimal f = PlonkMinimal
  { alpha :: ScalarChallenge f
  , beta :: f -- Note: beta/gamma are full challenges, not scalar
  , gamma :: f
  , zeta :: ScalarChallenge f
  -- jointCombiner omitted (None for now, used for lookups)
  }

derive instance Newtype (PlonkMinimal f) _
derive instance Eq f => Eq (PlonkMinimal f)
derive instance Generic (PlonkMinimal f) _

instance Show f => Show (PlonkMinimal f) where
  show = genericShow

instance
  ( PrimeField f
  , FieldSizeInBits f 255
  ) =>
  CircuitType f (PlonkMinimal (F f)) (PlonkMinimal (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(PlonkMinimal (F f))
  fieldsToVar = genericFieldsToVar @(PlonkMinimal (F f))

instance
  ( PrimeField f
  , FieldSizeInBits f 255
  , BasicSystem f c
  ) =>
  CheckedType f c (PlonkMinimal (FVar f)) where
  check = genericCheck

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
newtype DeferredValues f sf = DeferredValues
  { plonk :: PlonkMinimal f
  , combinedInnerProduct :: sf
  , xi :: ScalarChallenge f
  , bulletproofChallenges :: BulletproofChallenges f
  , b :: sf
  }

derive instance Newtype (DeferredValues f sf) _
derive instance (Eq f, Eq sf) => Eq (DeferredValues f sf)
derive instance Generic (DeferredValues f sf) _

instance (Show f, Show sf) => Show (DeferredValues f sf) where
  show = genericShow

-- CircuitType instance for Step verifying Wrap (Type1 shifted values)
instance
  ( PrimeField f
  , FieldSizeInBits f 255
  ) =>
  CircuitType f
    (DeferredValues (F f) (Type1 (F f)))
    (DeferredValues (FVar f) (Type1 (FVar f))) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(DeferredValues (F f) (Type1 (F f)))
  fieldsToVar = genericFieldsToVar @(DeferredValues (F f) (Type1 (F f)))

instance
  ( PrimeField f
  , FieldSizeInBits f 255
  , BasicSystem f c
  , CheckedType f c (Type1 (FVar f))
  ) =>
  CheckedType f c (DeferredValues (FVar f) (Type1 (FVar f))) where
  check = genericCheck

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
newtype UnfinalizedProof f sf b = UnfinalizedProof
  { deferredValues :: DeferredValues f sf
  , shouldFinalize :: b
  , spongeDigestBeforeEvaluations :: f
  }

derive instance Newtype (UnfinalizedProof f sf b) _
derive instance (Eq f, Eq sf, Eq b) => Eq (UnfinalizedProof f sf b)
derive instance Generic (UnfinalizedProof f sf b) _

instance (Show f, Show sf, Show b) => Show (UnfinalizedProof f sf b) where
  show = genericShow

-- CircuitType instance for Step verifying Wrap (Type1 shifted values)
instance
  ( PrimeField f
  , FieldSizeInBits f 255
  ) =>
  CircuitType f
    (UnfinalizedProof (F f) (Type1 (F f)) Boolean)
    (UnfinalizedProof (FVar f) (Type1 (FVar f)) (BoolVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(UnfinalizedProof (F f) (Type1 (F f)) Boolean)
  fieldsToVar = genericFieldsToVar @(UnfinalizedProof (F f) (Type1 (F f)) Boolean)

instance
  ( PrimeField f
  , FieldSizeInBits f 255
  , BasicSystem f c
  , CheckedType f c (Type1 (FVar f))
  ) =>
  CheckedType f c (UnfinalizedProof (FVar f) (Type1 (FVar f)) (BoolVar f)) where
  check = genericCheck
