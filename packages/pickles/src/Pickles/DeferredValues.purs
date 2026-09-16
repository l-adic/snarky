-- | The deferred values a proof carries, and the unfinalized-proof
-- | structures built on them.
-- |
-- | Deferred values are the quantities a proof's verifier must check
-- | but whose checking falls to the next circuit in the chain: the
-- | PLONK IOP challenges, the inner-product argument's outputs, and —
-- | in a wrap statement — `branchData`, which tells the step circuit
-- | which domain to run the other checks against.
-- |
-- | Shared vocabulary, not verifier-private: both
-- | `Pickles.Step.FinalizeOtherProof` and
-- | `Pickles.Wrap.FinalizeOtherProof` consume it,
-- | `Pickles.IncrementallyVerifyProof` takes it as input, the step and
-- | wrap statements carry it, and the out-of-circuit `Pickles.Verify`
-- | reads it last.
module Pickles.DeferredValues
  ( -- * Bulletproof Challenges
    BulletproofChallenges
  , ScalarChallenge
  -- * Plonk Deferred Values
  , PlonkChallenges
  , PlonkMinimal
  , PlonkInCircuit
  , toPlonkMinimal
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

-- | A 128-bit scalar challenge, as squeezed from the sponge. Not a full
-- | field element; the endo coefficient turns it into one where one is
-- | needed.
type ScalarChallenge f = SizedF 128 f

-- | One scalar challenge per IPA round, each derived from absorbing
-- | that round's L/R pair. `d` is the round count.
type BulletproofChallenges d f = Vector d (ScalarChallenge f)

-- | The four PLONK IOP challenges, parameterised by how they are
-- | carried: `PlonkMinimal` holds them as 128-bit scalar challenges,
-- | `expandPlonkMinimal` returns them endo-expanded to full field
-- | elements. Together with the proof's evaluations they determine
-- | every other deferred value.
-- |
-- | `jointCombiner` is absent — it is `None` until lookups.
type PlonkChallenges a =
  { alpha :: a
  , beta :: a
  , gamma :: a
  , zeta :: a
  }

type PlonkMinimal f = PlonkChallenges (ScalarChallenge f)

-- | `PlonkMinimal` plus the shifted scalars derived from it — `perm`
-- | and the two powers of `zeta` — as the deferred values carry them.
type PlonkInCircuit f sf =
  { alpha :: ScalarChallenge f
  , beta :: ScalarChallenge f
  , gamma :: ScalarChallenge f
  , zeta :: ScalarChallenge f
  , perm :: sf
  , zetaToSrsLength :: sf
  , zetaToDomainSize :: sf
  }

toPlonkMinimal :: forall f sf. PlonkInCircuit f sf -> PlonkMinimal f
toPlonkMinimal p = { alpha: p.alpha, beta: p.beta, gamma: p.gamma, zeta: p.zeta }

-- | The four challenges as full field elements. `alpha` and `zeta` are
-- | endo-expanded — `a * endo + b`, for `(a, b)` the decomposition of
-- | the 128-bit challenge — while `beta` and `gamma` are injected
-- | directly.
expandPlonkMinimal
  :: forall f
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => f -- endo coefficient
  -> PlonkMinimal (F f)
  -> PlonkChallenges f
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

-- | Deferred values plus the flag saying whether they must check out.
-- |
-- | The flag is what bootstraps the chain: a dummy proof carries
-- | `shouldFinalize = false`, so the assertion
-- | `finalized || not shouldFinalize` holds whether or not the dummy
-- | verifies.
type UnfinalizedProof d f sf b =
  { deferredValues :: DeferredValues d f sf
  , shouldFinalize :: b
  , spongeDigestBeforeEvaluations :: f
  }

-- | Which step branch was verified: its domain log2 and its
-- | proofs-verified mask. The packing into a single statement field is
-- | fixed at `4*domainLog2 + mask[0] + 2*mask[1]`.
type BranchData f b =
  { domainLog2 :: f
  , proofsVerifiedMask :: Vector 2 b
  }

-- | `DeferredValues` plus `branchData`, the form
-- | `Pickles.Step.FinalizeOtherProof` receives: it selects the domain
-- | and the proofs-verified mask from `branchData`.
-- |
-- | Feature flags and a joint combiner are not carried — they are
-- | constant `false`/`None` for vanilla Mina.
type WrapDeferredValues d f sf b =
  { plonk :: PlonkInCircuit f sf
  , combinedInnerProduct :: sf
  , xi :: ScalarChallenge f
  , bulletproofChallenges :: BulletproofChallenges d f
  , b :: sf
  , branchData :: BranchData f b
  }

