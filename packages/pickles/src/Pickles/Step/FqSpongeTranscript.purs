-- | Sponge transcript for proof verification.
-- |
-- | Replays the Fiat-Shamir transcript by absorbing commitments and squeezing
-- | challenges, matching the sequence from kimchi/src/verifier.rs:
-- |   1. absorb VK digest
-- |   2. absorb prev_challenges commitments (empty for base case)
-- |   3. absorb public_comm point
-- |   4. absorb w_comm[0..14] points
-- |   5. squeeze beta
-- |   6. squeeze gamma
-- |   7. absorb z_comm point
-- |   8. squeeze alpha
-- |   9. absorb t_comm points
-- |  10. squeeze zeta
-- |  11. digest (full squeeze)
-- |
-- | Field-polymorphic: works on whichever field the circuit is native to.
-- |
-- | Two versions are provided:
-- | - `spongeTranscriptCircuit`: In-circuit version using Kimchi constraints
-- | - `spongeTranscriptPure`: Pure reference implementation for testing
module Pickles.Step.FqSpongeTranscript
  ( FqSpongeInput
  , FqSpongeOutput
  , spongeTranscriptCircuit
  , spongeTranscriptPure
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Vector (Vector)
import Pickles.Sponge (evalPureSpongeM, evalSpongeM, initialSponge, initialSpongeCircuit, squeezeScalarChallenge, squeezeScalarChallengePure)
import Pickles.Sponge as Sponge
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, FVar, SizedF, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

-------------------------------------------------------------------------------
-- | Statically-sized circuit input for the sponge transcript.
-- | `chunks` is the number of t_comm chunks (= 7 * ceil(domain_size / max_poly_size)).
-------------------------------------------------------------------------------

type FqSpongeInput chunks f =
  { indexDigest :: f
  , publicComm :: AffinePoint f
  , wComm :: Vector 15 (AffinePoint f)
  , zComm :: AffinePoint f
  , tComm :: Vector chunks (AffinePoint f)
  }

type FqSpongeOutput f =
  { beta :: SizedF 128 f
  , gamma :: SizedF 128 f
  , alphaChal :: SizedF 128 f
  , zetaChal :: SizedF 128 f
  , digest :: f
  }

-------------------------------------------------------------------------------
-- | Circuit version
-------------------------------------------------------------------------------

-- | Sponge transcript as a Kimchi circuit.
spongeTranscriptCircuit
  :: forall f chunks t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => FqSpongeInput chunks (FVar f)
  -> Snarky (KimchiConstraint f) t m (FqSpongeOutput (FVar f))
spongeTranscriptCircuit input = evalSpongeM initialSpongeCircuit do
  Sponge.absorb input.indexDigest
  Sponge.absorbPoint input.publicComm
  for_ input.wComm Sponge.absorbPoint
  beta <- squeezeScalarChallenge
  gamma <- squeezeScalarChallenge
  Sponge.absorbPoint input.zComm
  alphaChal <- squeezeScalarChallenge
  for_ input.tComm Sponge.absorbPoint
  zetaChal <- squeezeScalarChallenge
  digest <- Sponge.squeeze
  pure { beta, gamma, alphaChal, zetaChal, digest }

-------------------------------------------------------------------------------
-- | Pure reference implementation
-------------------------------------------------------------------------------

spongeTranscriptPure
  :: forall f chunks
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => FqSpongeInput chunks f
  -> FqSpongeOutput f
spongeTranscriptPure input = evalPureSpongeM initialSponge do
  Sponge.absorb input.indexDigest
  Sponge.absorbPoint input.publicComm
  for_ input.wComm Sponge.absorbPoint
  beta <- squeezeScalarChallengePure
  gamma <- squeezeScalarChallengePure
  Sponge.absorbPoint input.zComm
  alphaChal <- squeezeScalarChallengePure
  for_ input.tComm Sponge.absorbPoint
  zetaChal <- squeezeScalarChallengePure
  digest <- Sponge.squeeze
  pure { beta, gamma, alphaChal, zetaChal, digest }
