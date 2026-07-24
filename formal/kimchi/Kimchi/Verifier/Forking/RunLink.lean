import Kimchi.Verifier.Forking.OracleRun
import Kimchi.Verifier.Reflect

/-!
# W2 · Run-level faithfulness

The bridges in `Forking.OracleRun` land at `fqOracles` / `frOracles`. The soundness layer consumes
the *run-level* oracles `runOracles` / `runVU` (`Kimchi.Verifier.Reflect`) — those same functions
specialized to the run's own public commitment. These two corollaries make the connection explicit:
reading the sponge-as-oracle at the transcript prefixes reproduces the exact `(β, γ, α, ζ)` and
`(v, u)` the guards read. This is the seam W3 builds on when it bounds those challenges against the
`soundBad*` / `badXi`/`badR` sets.
-/

namespace Kimchi.Verifier.Forking

open Bulletproof

variable {C : Ipa.CommitmentCurve} {nc : ℕ}

/-- The fq challenges the soundness guards read (`runOracles`) are exactly the sponge-as-oracle
reads at the four fq prefixes, taken at the run's own public commitment. -/
theorem oracleChallenges_runOracles (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    oracleChallenges poseidonO cvk cp (publicCommitment C σ cvk pub)
      = ((runOracles C σ cvk cp pub).beta, (runOracles C σ cvk cp pub).gamma,
         (runOracles C σ cvk cp pub).alpha, (runOracles C σ cvk cp pub).zeta) := by
  simp only [oracleChallenges_poseidonO, runOracles]

/-- The batch challenges the soundness guards read (`runVU`) are exactly the fr-oracle reads at the
`v`/`u` prefixes, taken at the run's own fq digest and public evaluations. -/
theorem oracleVU_runVU (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    oracleVU poseidonOFr cp (runOracles C σ cvk cp pub).digest (runPubEvals C σ cvk cp pub)
      = runVU C σ cvk cp pub := by
  simp only [oracleVU_poseidonOFr, runVU]

end Kimchi.Verifier.Forking
