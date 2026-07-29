import Pasta.Shifted
import Kimchi.Gate.Generic
import Kimchi.Gate.AddComplete
import Kimchi.Gate.VarBaseMul
import Kimchi.Gate.EndoScalar
import Kimchi.Gate.EndoMul
import Kimchi.Gate.Poseidon
import Kimchi.Gate.Semantics.Generic
import Kimchi.Gate.Semantics.AddComplete
import Kimchi.Gate.Semantics.VarBaseMul
import Kimchi.Gate.Semantics.EndoScalar
import Kimchi.Gate.Semantics.EndoMul
import Kimchi.Gate.Semantics.Poseidon
import Bulletproof.Protocol
import Bulletproof.Soundness
import Kimchi.Lift
import Kimchi.Permutation.Copy
import Kimchi.Index.Basic
import Kimchi.Index.Satisfies
import Kimchi.Index.Aggregate
import Kimchi.Index.Degree
import Kimchi.Index.CopySoundness
import Kimchi.Permutation.Wiring
import Kimchi.Permutation.Permutation
import Kimchi.GrandProduct
import Bulletproof.Wire
-- Side A — the polynomial protocol (PCS-free) and its soundness
import Kimchi.Protocol.Accepts
import Kimchi.Protocol.Linearization
import Kimchi.Protocol.Equation
-- Side B — the PCS reduction and the concrete wire verifier
import Bulletproof.Reflection
import Kimchi.Verifier.Reduction.Correspond
import Kimchi.Verifier.Reduction.Binding
import Kimchi.Verifier.Reduction.Soundness
import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Reflect
import Kimchi.Verifier.Wire
import Kimchi.Verifier.Capstone.Algebraic
import Kimchi.Verifier.Capstone.Reflection

-- The Fiat–Shamir random-oracle model (fq + fr) and its run-level faithfulness
import Kimchi.Verifier.Forking.RunLink
-- Knowledge soundness of the deployed verifier, over the IPA forking extractor
import Kimchi.Verifier.KnowledgeSoundness
-- The honest family (anti-vacuity) and the bridge to the deployed verifier
import Kimchi.Verifier.Forking.Honest
import Kimchi.Verifier.Forking.Bridge

/-!
# Kimchi — the kimchi proof system over the Pasta curves

Root module of the `Kimchi` library. The development runs bottom-up, from a single gate row
to knowledge soundness of the executable verifier:

- `Kimchi/Gate/` — each modelled gate as a constraint predicate over a witness structure
  (`Holds` / `ok` / `ok_iff`), proved faithful to Mathlib's elliptic-curve group law.
- `Kimchi/Gate/Semantics/` — the multi-row development: ladders, GLV accumulation, and the
  per-curve deployed entry points (`pallas_endoMul`, `varBaseMul_scaleFast2`, and the rest).
- `Kimchi/Index/`, `Kimchi/Permutation/`, `Kimchi/Lift.lean`, and the vanishing-argument
  modules `Domain`, `GrandProduct`, `SchwartzZippel`, `Aggregate` — the arithmetization: the
  index, satisfiability as divisibility, and the linearization.
- `Kimchi/Protocol/` — the ideal polynomial protocol, PCS-free, and its soundness.
- `Kimchi/Verifier/` — the executable verifier, its reflection, the reduction to the IPA
  commitment of the `Bulletproof` package, and the forking development.

The headline is per-curve knowledge soundness of the *deployed* verifier,
`Kimchi.Verifier.KnowledgeSoundness.{vesta,pallas}_kimchi_knowledge_sound`.

**The modelled fragment excludes lookups, optional gates, recursion, and the sub-SRS
regime.** The canonical statement of that scope is the preamble of
`Kimchi/Verifier/KnowledgeSoundness.lean`. The package declares no axioms: every endpoint
reduces to the standard logical axioms plus the Pasta trust base, which
`scripts/check_axioms.sh` enforces.
-/
