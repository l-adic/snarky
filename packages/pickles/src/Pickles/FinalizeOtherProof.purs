-- | Shared types for the `finalize_other_proof` circuit, used on both
-- | the step side (`Pickles.Step.FinalizeOtherProof`) and wrap side
-- | (`Pickles.Wrap.FinalizeOtherProof`).
-- |
-- | Both circuits take the same compile-time `Params` (VK-derived
-- | data: domains, shifts, srs size, endo coefficient, linearization
-- | polynomial, domain-resolution mode) and produce the same `Output`
-- | shape (per-check booleans + bulletproof challenges).
-- |
-- | Each side keeps its own input record (`Pickles.Step.FinalizeOtherProof.Input`
-- | vs `Pickles.Wrap.FinalizeOtherProof.Input`) because the
-- | shifted-scalar representation differs between sides.
-- |
-- | Reference: OCaml `step_verifier.ml`, `wrap_verifier.ml`'s
-- | `finalize_other_proof`.
module Pickles.FinalizeOtherProof
  ( Params
  , Output
  , DomainMode(..)
  ) where

import Data.Vector (Vector)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.Verify.Types (BulletproofChallenges)
import Snarky.Circuit.DSL (BoolVar, FVar)

-- | Domain-resolution mode for `finalize_other_proof`.
-- |
-- | * `KnownDomainsMode` — compiled-rule path. `params.domains` is
-- |   the compile-time `unique_domains` Vector (typically `Vector 1`
-- |   for single-rule, larger for multi-branch self prevs). Vanishing
-- |   polynomial uses `pow2_pows` + `Pseudo.mask`.
-- | * `SideLoadedMode` — side-loaded prev. The candidate-log2
-- |   universe `Vector 17` (log2s ∈ [0..16]) is synthesized
-- |   internally from `input.domainLog2Var`; `params.domains` is
-- |   ignored. The FOP body emits 17 `equals_` gates +
-- |   `Boolean.Assert.any` for the one-hot mask and uses iterative
-- |   `if_(mask[i], square, …)` for the vanishing polynomial.
-- |
-- | Reference: OCaml `step_verifier.ml`'s `finalize_other_proof` +
-- | `side_loaded_domain`.
data DomainMode
  = KnownDomainsMode
  | SideLoadedMode

-- | Compile-time parameters for finalizing another proof.
-- |
-- | These come from the verification key / are known at circuit compile time.
-- |
-- | - `domains`: Per-branch `{ generator, log2 }` over the `nd` possible
-- |   step-domain sizes the prev proof could have. For single-rule
-- |   callers `nd = 1`. Multi-rule (e.g. TwoPhaseChain Self prev)
-- |   passes the deduped Vector of all possible per-branch step domains.
-- |   Mirrors OCaml `domain_for_compiled`'s `unique_domains`.
-- | - `shifts`: kimchi permutation argument shifts. Single Vector
-- |   because OCaml's `Pseudo.Domain.shifts` asserts shifts are
-- |   identical across all unique domains
-- |   (`disabled_not_the_same`).
-- | - `srsLengthLog2`: Log2 of SRS length (e.g. 16)
-- | - `endo`: Endomorphism coefficient for scalar challenge conversion
-- | - `linearizationPoly`: The linearization polynomial for gate constraints
-- | - `domainMode`: Whether the prev proof's domain is compile-time
-- |   known (`KnownDomainsMode`) or side-loaded (`SideLoadedMode`).
type Params :: Int -> Type -> Row Type -> Type
type Params nd f r =
  { domains :: Vector nd { generator :: FVar f, log2 :: Int }
  , shifts :: Vector 7 (FVar f)
  , srsLengthLog2 :: Int
  , endo :: f -- ^ EndoScalar coefficient
  , linearizationPoly :: LinearizationPoly f
  , domainMode :: DomainMode
  | r
  }

-- | Output from finalizing another proof.
-- |
-- | - `finalized`: Boolean indicating whether all checks passed
-- | - `challenges`: The raw bulletproof challenges (128-bit scalar challenges)
-- | - `expandedChallenges`: The expanded bulletproof challenges (full field via endo)
type Output d f =
  { finalized :: BoolVar f
  , xiCorrect :: BoolVar f
  , bCorrect :: BoolVar f
  , cipCorrect :: BoolVar f
  , plonkOk :: BoolVar f
  , challenges :: BulletproofChallenges d (FVar f)
  , expandedChallenges :: Vector d (FVar f)
  }
