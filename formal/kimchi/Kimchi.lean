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
import Kimchi.Lift
import Kimchi.GrandProduct
import Kimchi.SchwartzZippel
import Kimchi.Permutation.Copy
import Kimchi.Index.Basic
import Kimchi.Index.Satisfies
import Kimchi.Index.CopySoundness
import Kimchi.Index.Aggregate
import Kimchi.Permutation.Wiring
import Kimchi.Permutation.Permutation
import Bulletproof.Wire
-- The verifier's scalar side in closed form
import Kimchi.Protocol.Linearization
-- The executable verifier, its run functions, and the serde wire boundary
import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Reflect
import Kimchi.Verifier.Wire

/-!
# Kimchi — the kimchi proof system over the Pasta curves

Root module of the `Kimchi` library. The development runs bottom-up, from a single gate row
to the executable verifier:

- `Kimchi/Gate/` — each modelled gate as a constraint predicate over a witness structure
  (`Holds` / `ok` / `ok_iff`), proved faithful to Mathlib's elliptic-curve group law.
- `Kimchi/Gate/Semantics/` — the multi-row development: ladders, GLV accumulation, and the
  per-curve deployed entry points (`pallas_endoMul`, `varBaseMul_scaleFast2`, and the rest).
- `Kimchi/Index/`, `Kimchi/Permutation/`, `Kimchi/Lift.lean`, `Kimchi/Domain.lean` — the
  arithmetization as MODELLING: the index as data, what it means for a witness table to
  satisfy it (`Index.Satisfies`), the wiring and σ-columns, and the polynomial lift
  (`Lift.Argument.bridge` — a gate's constraints hold at every row iff its lift is divisible
  by `Z_H`), which is what the verifier's commitments commit to.
- `Kimchi/Protocol/Linearization.lean` — the verifier's scalar side in closed form
  (`ftEval0`, `permScalar`, `zkpmEval`) over the gate constraint families.
- `Kimchi/Verifier/` — the executable verifier transcribed from proof-systems
  (`Verifier/Kimchi.lean`), every intermediate of its body as a named closed form
  (`Verifier/Reflect.lean`), and the serde wire boundary with its parse
  (`Verifier/Wire.lean`).

The headline object is `Kimchi.Verifier.kimchiVerify`: the deployed kimchi verifier, as a
total executable function of the checked records. It is a **specification** — the
transcription proof-systems' `kimchi/src/verifier.rs` is measured against, and the anchor
downstream circuit implementations are proved faithful to. It is not accompanied by a
soundness claim: the probabilistic soundness development this package once carried was
retired (see the module preamble of `Kimchi/Verifier/Kimchi.lean` for what the verifier
does and does not model, and `git log` for the retired tree).

**The modelled fragment excludes lookups, optional gates, recursion, and the sub-SRS
regime.** The canonical statement of that scope, with every declared deviation from
`verifier.rs`, is the `## Scope` section of `Kimchi/Verifier/Kimchi.lean`'s preamble. The
package declares no axioms: every rooted result reduces to the standard logical axioms plus
the Pasta trust base, which `scripts/check_axioms.sh` enforces.
-/
