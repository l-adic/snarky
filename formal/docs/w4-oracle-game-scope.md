# W4 scope — the oracle game and the probabilistic capstones

**Status: STAGING.** Child of `ironwood-refoundation-plan.md` §5/W4; successor to W2 (#273,
merged: the oracle model + run-level faithfulness) and W3 (#275, merged: the challenge-vector
escape bounds). This document pins the machinery against verified signatures, resolves the
finite-domain problem, and — importantly — isolates **one modeling decision that needs your
sign-off** before the capstone statement can be written (§4).

---

## 1. Verified machinery inventory

### Ours (landed)
| Fact | Where | Why W4 needs it |
|---|---|---|
| `oracleChallenges_runOracles`, `oracleVU_runVU` | `Forking/RunLink.lean` | the O-reads at the prefixes *are* the guards' challenges |
| `preBeta_ne_preGamma`, … (6 + `preV_ne_preU`) | `Forking/Transcript.lean` | discharges `fresh_read_bound`'s `hφ : Injective φ` |
| `runGuardsFailFq_measure_le`, `runVUFail_measure_le` | `Forking/GuardEscape.lean` | supplies `fresh_read_bound`'s `S` / `hS` |
| **`RunBounds` is challenge-independent** | `Capstone/Reflection.lean:991` | every clause is `∀ β…`-quantified, so the card bounds the terminal root *concludes* hold at **every** challenge value — this is what makes a probabilistic argument over uniform challenges legitimate, and it is exactly what the C1 named-sets refactor bought |
| `Fintype (SWPoint E)` | CompElliptic `ShortWeierstrass.lean:447` | `Finite` for our transcript alphabet |

### Ironwood's (available, unused so far)
| Item | Signature sketch | Role |
|---|---|---|
| `OracleComp T F α` | `pure`/`query t k`, `run O`, `QueryBound A Q` | the adaptive Q-query adversary |
| `fsWins` / `fsWinsFull` | `accept (A.run O) (fun j => O (prefixes (A.run O) j))` | the attack event: challenges read at the **output's own** prefixes |
| `uniformOfFintype_fresh_read_bound` | `φ` injective, `S : X → Set (ι → F)`, `hS` ⟹ table bound ≤ β | **the transport** vector-bound → table-bound |
| `escapesDuringC_measure_le'` | `hQ : QueryBound A Q` ⟹ `≤ Q · ε` | the adaptive query loss |
| `completing` | appends the extra read of the output's own prefix | makes "the challenge the verifier uses" a counted query |
| `BTranscript F G L` + `Finite`/`Fintype` instances | `{l : List (TranscriptElt F G) // l.length ≤ L}` | **the finite-domain pattern** |
| `fsWinsFull_restrictSum_le`, `DomainReduction` | split/restrict the domain | alternatives to length-bounding |

## 2. The finite-domain problem — solved, with one asymmetry

`fresh_read_bound` and every table measure require **`Fintype T`**; our transcript domains are
`List (KimchiTranscriptElt C)` / `List (FrTranscriptElt C)`, both infinite. Ironwood hit the same
wall and solved it by *bounding transcript length*: `BTranscript F G L` with `Finite` by injection
into `Fin L → Option elt`, then `Fintype.ofFinite`. We mirror it:

- **fq side — clean.** `KimchiTranscriptElt C` is list-free (`fqPoint C.Point`, `fqBase
  C.BaseField`, `fqCast`, `fqEndo`), so `Finite` follows from `Fintype (SWPoint E)` +
  `Fintype (ZMod C.base)` by injection into `C.Point ⊕ C.BaseField ⊕ Bool`. Then
  `BKimchiTranscript C L := {l : List (KimchiTranscriptElt C) // l.length ≤ L}` is `Fintype`.
- **fr side — genuine obstruction.** `FrTranscriptElt.frAbsorb : List C.ScalarField → _` carries an
  *unbounded list*, so the element type itself is infinite and no length bound on the transcript
  fixes it. Options: (a) a bounded-absorb variant `frAbsorb : {l // l.length ≤ M} → _` for the W4
  domain (the real absorbs are singletons or `nc`-chunk vectors, so `M := max 1 nc` suffices and is
  *provably* respected by `preVAbsorbs`); (b) re-index `frAbsorb` by `Vector C.ScalarField m`.
  **(a) is recommended** — it leaves the W2/W3 fr statements untouched and adds a domain-only type.

The length bound `L` is not a limitation of substance: a `Q`-query adversary reaches only finitely
many points anyway (ironwood's `reachSet`/`restrictTo` formalize exactly that), and every prefix our
verifier reads has a statically known length. `L` is a parameter of the capstone.

## 3. The proof chain (what composes with what)

For a fixed adversary output (proof, key, public input) with the algebraic side data:

1. **Terminal root** (`kimchi{Vesta,Pallas}_run_sound_algebraic_ft`, untouched) — from a genuine
   acceptance + `hrep`/`hTC`/`hvk`/`hbind`/`hξ`/`hr`: `RunBounds ∧ RunGuardImp`.
2. **`RunGuardImp`** is literally *guards ⟹ `Satisfies`*. Contrapositive: **`¬Satisfies` ⟹ some
   guard antecedent fails**.
3. **`RunBounds`** (challenge-independent, §1) feeds W3's `runGuardsFailFq_measure_le` /
   `runVUFail_measure_le`: over a **uniform challenge vector**, guard failure has measure
   `≤ (7(n−zk) + 7(n−zk) + n(K−1) + (9n+2))/|F|` and `≤ (2(m−1)+1)/|F|`.
4. **`fresh_read_bound`** transports (3) from the vector to the **oracle table** over the finite
   domain of §2, along `φ :=` the four/two transcript prefixes — injective by W2's distinctness
   lemmas, with the adversary's other reads absorbed into `choice`.
5. **W2's `RunLink`** identifies the transported coordinates with `runOracles`/`runVU` — the very
   challenges the guards in (2) test.

Steps 3–5 are mechanical given what is landed. **Step 1↔4 is where the modeling decision lives.**

## 4. THE DECISION — what "the verifier accepts" means in the oracle world

The terminal root is a statement about the **deployed, deterministic** verifier: `hacc :
kimchiVerify … = true`, with `RunGuardImp`'s antecedents about `runOracles` — the *real Poseidon
sponge* challenges. The probabilistic statement wants acceptance and challenges to be relative to a
**uniform** `O`. Reconciling them is the crux, and there are two honest options:

**Option A′ — the conditional capstone (recommended).** State W4 as: *for an adversary output the
deployed verifier accepts (so `RunBounds` is in hand via the terminal root), the measure of oracles
on which the guard antecedents fail at the transcript-prefix reads is ≤ ε; hence outside that set,
`Satisfies` holds.* This is fully provable with what exists, changes no frozen file, and its
honest reading is: *"conditioned on a genuine acceptance, and modeling the sponge's challenge reads
as a uniform oracle (the Option-A boundary from W2's `Model.lean`), soundness fails with
probability ≤ ε."* The residual gap — that acceptance itself is evaluated under the real sponge
rather than under `O` — is precisely the Poseidon-as-RO boundary we already documented, not a new
one. **`#print axioms` stays at the terminal roots' existing closure; no new axiom.**

**Option B′ — the O-parameterized verifier (full game).** Define `kimchiVerifyO O …` (challenges
sourced from `O` rather than the sponge), prove `kimchiVerifyO poseidonO = kimchiVerify` (W2's
bridges give the challenge equality; the rest is the body), and **re-derive the terminal chain over
an abstract challenge source** so `RunBounds ∧ RunGuardImp` holds for the O-run. This yields the
unconditional `fsWins`-shaped statement the plan sketches. Cost: the AGM/reflection chain
(`Capstone/{Algebraic,Reflection}.lean`, plus the `kimchi_fiat_shamir_*` seam) is stated over
`runOracles` concretely; abstracting it is major surgery on frozen, audited files, and the FS
axioms would need restating over the O-run. This is a workstream comparable to W3+W4 combined.

**My recommendation: A′ now, B′ only if you want the unconditional form.** A′ delivers the real
mathematical content (the ε bound, the union of all seven guards, the adaptive query loss) and
composes with the existing roots without touching them; B′ mostly buys a cosmetically stronger
*statement* at a large refactor cost, and its extra content is exactly the boundary we already
declare. If you want B′ eventually, A′ is a strict prerequisite anyway — nothing is wasted.

## 5. Deliverables (under Option A′)

| Module | Contents | Est. |
|---|---|---|
| ~~`Forking/Domain.lean`~~ **DONE — proven, 0 sorries** | `Finite (KimchiTranscriptElt)`, `BKimchiTranscript C L` + `Finite`/`Fintype`/`DecidableEq`; `BFrElt C M` (bounded-absorb variant) + `toFrElt` erasure, `BFrTranscript C M L` + instances; and `preZeta_length` — the longest fq prefix is **exactly `5 + 17·nc + |tComm|`** (1 publicComm + 15 wComm columns + 1 zComm chunk-vector, plus the digest and four squeeze markers), which pins the capstone's `L` parameter concretely rather than arbitrarily | ~140 |
| `Forking/Game.lean` | `fresh_read_bound` transport: `guardsFailFqAtOracle_measure_le` and `guardsFailVUAtOracle_measure_le` — table-measure versions of W3's bounds, along the W2 prefixes | ~220 |
| `Forking/Capstone.lean` | the composition with the terminal roots: `kimchi{Vesta,Pallas}_run_sound_ro` — *accepted ⟹ off a measure-≤ε set of oracles, `Satisfies`* | ~160 |
| gates | add the two new roots to `kimchi/roots.txt` and `scripts/check_axioms.lean`'s `roots`; **`allowed` is unchanged** (they inherit the terminal roots' `kimchi_fiat_shamir_*` closure) | — |

Adaptive query loss (`escapesDuringC_measure_le'`, the `+Q/|F|` term) enters in `Game.lean` only if
we model the adversary as an `OracleComp`; under A′ the adversary can stay implicit (the output is
universally quantified), which is simpler and strictly more general. Recommend: start without
`OracleComp`, add it only if a reviewer wants the query-counted form.

## 6. Risks

| Risk | Mitigation |
|---|---|
| fr element type not `Finite` (§2) | domain-only bounded-absorb variant; W2/W3 fr statements untouched |
| `fresh_read_bound`'s `choice`/`S` shape mismatches our events | our events are already `Set (Fin k → F)` *by design* (W3 §2) — the shape was chosen for this |
| Prefix injectivity needs *all* pairs distinct, we proved 6+1 | that is exactly all pairs for 4 (fq) and 2 (fr) coordinates |
| Length bound `L` looks arbitrary | it is a capstone parameter with a proved lower bound from the actual prefix lengths; document it |
| Scope creep into B′ | A′ is severable and is B′'s prerequisite; decide explicitly (§4) |
