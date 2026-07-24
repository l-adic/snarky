import Kimchi.Verifier.Forking.OracleRun

/-!
# W2 · The random-oracle model and its trust boundary (fq + fr sides)

## What is proved, and what is assumed

`Forking.Transcript` and `Forking.OracleRun` are *fully verified* — no new axiom. They define
the fq-side transcript domain, interpret a prefix through the deployed Poseidon sponge
(`poseidonO`), and prove (`oracleChallenges_poseidonO`) that reading `poseidonO` at the four
prefixes reproduces the verifier's `(β, γ, α, ζ)` exactly. So the abstract oracle game below
provably *specializes to the real verifier* at `O := poseidonO`.

## The one modeling assumption (documented, not a kernel axiom)

The soundness bound is proved for a **uniform** oracle `O : List (KimchiTranscriptElt C) →
C.ScalarField`. Transporting it to the deployed verifier rests on a single assumption:

> **Poseidon-as-random-oracle.** The deployed Poseidon fq-sponge, read at the transcript
> prefixes — i.e. `poseidonO` — is distributed as a uniform random function over its query
> domain. Equivalently: the sponge's challenge outputs at distinct transcript points are
> jointly indistinguishable from independent uniform field elements.

This is **not** introduced as a Lean `axiom`. The deployed sponge is a deterministic function;
asserting its uniformity inside the kernel would be a false-as-stated proposition (an unconditioned
distribution claim, the shape the statement audit flagged as M3). Instead — following
`zcash/ironwood`'s `Forking.Oracle` — every probabilistic theorem is stated *within* the uniform
model, and this paragraph is the named boundary at which the model meets Blake2b/Poseidon reality.
`#print axioms` on the W4 roots will therefore show **no** oracle axiom; the assumption is
auditable here and in `roots.txt`, by reading, exactly as prominent as an axiom would be.

Two conversions are idealized inside the same boundary and carry no separate accounting: the
128-bit prechallenge cast (`β`, `γ`) and the endomorphism expansion (`α`, `ζ`) are treated as
landing uniformly in `C.ScalarField`. Their deviation from uniform is negligible; a strengthening
that discharges the `endoExpand` half from the GLV short-basis bounds is recorded for later.

## Layer boundary

This module frames the game shape (`fsWins`-style: an acceptance predicate evaluated at the
oracle-read challenges) and records faithfulness. The probability measure over uniform oracles,
the per-challenge freshness bounds against the `soundBad*` sets, and the forking reduction consume
`zcash/ironwood` and land in W3/W4; nothing here imports `Zcash` yet.
-/

namespace Kimchi.Verifier.Forking

open Bulletproof

variable {C : Ipa.CommitmentCurve} {nc k : ℕ}

/-- The Fiat–Shamir game event, in `ironwood`'s `fsWins` shape: an acceptance predicate on the
challenge tuple, evaluated at the challenges *read from the oracle* `O` at the four fq-side
prefixes. W3 instantiates `accept` with the deployed verifier's guard conditions (the
`RunGuardImp` antecedents avoiding the `soundBad*` sets); the soundness bound then measures
`{O | GuardEvent accept O …}` over a uniform `O`. -/
def GuardEvent (accept : C.ScalarField × C.ScalarField × C.ScalarField × C.ScalarField → Prop)
    (O : List (KimchiTranscriptElt C) → C.ScalarField)
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) (publicComm : Vector C.Point nc) : Prop :=
  accept (oracleChallenges O cvk cp publicComm)

/-- **The game specializes to the real verifier.** For any acceptance predicate, the game event
at `O := poseidonO` is exactly acceptance at the deployed verifier's own `(β, γ, α, ζ)`. This is
the bridge that lets a uniform-oracle bound on `GuardEvent` become a bound on the real verifier,
under the modeling assumption above. -/
theorem guardEvent_poseidonO
    (accept : C.ScalarField × C.ScalarField × C.ScalarField × C.ScalarField → Prop)
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) (publicComm : Vector C.Point nc) :
    GuardEvent accept poseidonO cvk cp publicComm
      ↔ accept ((fqOracles C cvk cp publicComm).beta, (fqOracles C cvk cp publicComm).gamma,
                (fqOracles C cvk cp publicComm).alpha, (fqOracles C cvk cp publicComm).zeta) := by
  rw [GuardEvent, oracleChallenges_poseidonO]

/-- The fr-side game event: an acceptance predicate on the `(v, u)` batch-challenge pair,
evaluated at the challenges read from the fr-oracle `O` at the two prefixes. W3 instantiates
`accept` with the batch-opening guard conditions (the `badXi`/`badR` avoidance). -/
def GuardEventVU (accept : C.ScalarField × C.ScalarField → Prop)
    (O : List (FrTranscriptElt C) → C.ScalarField) (cp : KimchiProof C nc k)
    (fqDig : C.ScalarField) (pubEvals : PointEvaluations (Vector C.ScalarField nc)) : Prop :=
  accept (oracleVU O cp fqDig pubEvals)

/-- **The fr game specializes to the real verifier.** At `O := poseidonOFr`, the fr game event
is exactly acceptance at the deployed verifier's own `(v, u)`. -/
theorem guardEventVU_poseidonOFr (accept : C.ScalarField × C.ScalarField → Prop)
    (cp : KimchiProof C nc k) (fqDig : C.ScalarField)
    (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    GuardEventVU accept poseidonOFr cp fqDig pubEvals ↔ accept (frOracles C cp fqDig pubEvals) := by
  rw [GuardEventVU, oracleVU_poseidonOFr]

end Kimchi.Verifier.Forking
