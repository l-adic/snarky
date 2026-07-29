import Kimchi.Verifier.Forking.OracleRun
import Kimchi.Verifier.Reflect

/-!
# Run-level faithfulness

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

end Kimchi.Verifier.Forking
