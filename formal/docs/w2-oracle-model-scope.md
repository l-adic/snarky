# W2 scope — the oracle model, the bridges, and the Poseidon-RO assumption

**Status: SCOPING ONLY — no code changes.** Child of `ironwood-refoundation-plan.md` §4/W2.
W1 is done (PR #272: ironwood `Zcash` pinned at `83a98f7f`, CompElliptic a shared git pin at
daira `a549e455`). This document fixes the design of W2 precisely enough to implement, and
isolates the one decision that needs user sign-off (§5).

---

## 1. What ironwood actually does (verified against the pinned rev)

The facts below were read off the clone at the pinned commit; they materially shape W2.

**(a) The oracle domain is the transcript-prefix list, with explicit squeeze markers.**
`Zcash/Snark/Verifier/FiatShamir.lean`:

```
inductive TranscriptElt (F G) | point : G → _ | scalar : F → _ | challenge : _
structure FiatShamir (F G) where squeeze : List (TranscriptElt F G) → F
```

`deriveChallenges` builds each challenge as `fs.squeeze (prefix ++ [.challenge])` — the
`.challenge` marker is appended per squeeze and **not** re-absorbed, which is how two
consecutive squeezes from the same absorbed data get distinct oracle points. This solves
the duplex-sponge subtlety (squeezes consume state) *at the domain level*.

**(b) The game.** `Forking/Adversary/OracleComp.lean`: an adversary is a query program
`A : OracleComp T F P`;

```
fsWins A accept prefixes O : Prop := accept (A.run O) (fun j => O (prefixes (A.run O) j))
fsAdvantage A accept prefixes := (PMF.uniformOfFintype (T → F)).toOuterMeasure {O | fsWins …}
```

The challenges the acceptance predicate sees are **oracle reads at prefixes determined by
the adversary's own output** — exactly the commit-then-challenge chronology our C1 named
sets already respect. `[Fintype T]` is required for the uniform measure; infinite
transcript domains are handled by `Adversary/DomainReduction.lean` (`reachSet` /
`restrictTo` / `mapDomain`: restrict to the adversary's finite reachable support).

**(c) There is NO Lean axiom for the random oracle.** This is the decisive discovery for
§5. Ironwood's probabilistic theorems are stated *inside* the RO model (uniform `O`,
`OracleComp` adversaries); the step "Blake2b realizes this oracle" is a **documented
modeling assumption** (`Forking/Oracle.lean` module docstring, `TrustBoundary.lean`
census), not an `axiom` declaration. Two further honest caveats they carry in prose, not
in bounds:
  - **challenge conversion** — halo2's `Challenge255 → Fp` is *assumed exactly uniform*;
    "the real conversion has a negligible, unaccounted reduction bias";
  - **transcript-encoding injectivity** — distinct logical prefixes are assumed to encode
    to distinct oracle points.

**(d) The escape primitive we consume in W3.** `uniformChallenge_badSet`
(`bad.card / |Fp|`), `uniformOfFintype_fresh_read_bound` (a fresh read at an
injectively-embedded point lands in a prefix-determined bad set with measure ≤ β), and
the `escapesDuring` / `fsWins` machinery — all generic in `(T, F)`.

## 2. Our squeeze-site inventory (verified)

Every challenge the C1 guards constrain, with its sponge, its absorbed prefix, and its
conversion out of the 128-bit prechallenge space. All six are `C.ScalarField`-valued.

| # | challenge | sponge | absorbed before the squeeze | conversion | guarded set (card bound) |
|---|---|---|---|---|---|
| 1 | β | fq (base field) | VK digest ‖ publicComm ‖ wComm | 128-bit nat → cast | `soundBadB` (≤ 7(n−zk)) |
| 2 | γ | fq | …same absorb, second squeeze | 128-bit nat → cast | `soundBadG β` (≤ 7(n−zk)) |
| 3 | α | fq | + zComm | 128-bit → `endoExpand λ` | `soundBadA` (≤ n(K−1)) |
| 4 | ζ | fq | + tComm | 128-bit → `endoExpand λ` | `soundBadZ` (≤ 9n) + `{1, ω^(n−zk)}` |
| 5 | v (polyscale) | **fr** (scalar field, own params) | fqDigest ‖ frDigest(init) ‖ ftEval1 ‖ pubEvals ‖ all evals | `challengeNat` → `endoExpand λ` | `badXiOf` (≤ 2(44·nc+1−1)) |
| 6 | u (evalscale) | fr | …same absorb, second squeeze | `challengeNat` → `endoExpand λ` | `badROf` (≤ 1) |

(Sources: `Verifier/Kimchi.lean` `fqOracles`/`frOracles`, `Reflect.lean`
`runOracles`/`runVU`, `Poseidon/FqSponge.lean` `challenge`/`squeezeChallenge`/
`challengeNat`/`endoExpand`.)

**Out of W2/W3 scope (W5 only):** the IPA-interior challenges — `t → uBase = toGroup t`
(`challengeFq`, base-field-valued), the per-round `u_i` (`squeezeChallenge` after
absorbing `L_i, R_i`), and the Schnorr `c`. These matter for *deriving* tree extraction
(W5); the W3 guard discharge does not touch them.

**Chronology check (the load-bearing invariant, already delivered by C1):** each guarded
set is a function only of data absorbed *before* its squeeze — `soundBadB/G` of `runW`
(from `wComm`, row 1's absorb), `soundBadA` additionally of `runZ` (from `zComm`, row 3's
absorb), `soundBadZ` additionally of `ftChunkAssembly … aT` (from `tComm`, row 4's
absorb), `badXiOf/badROf` of `aRef` over the full commitment stream (all absorbed before
the fr squeezes). This is precisely `fsWins`'s `prefixes (A.run O)` shape: nothing needs
reordering.

## 3. Design decisions (with recommendations)

**D1 — Oracle domain `T`.** Mirror ironwood: an inductive transcript-element type +
prefix lists with explicit squeeze markers, but *tagged by sponge*:

```
inductive KimchiTranscriptElt (C : Ipa.CommitmentCurve)
  | fqPoint  : C.Point → _          -- fq-sponge point absorb (chunk-wise)
  | fqScalar : C.BaseField → _      -- fq-sponge field absorb (digest)
  | frScalar : C.ScalarField → _    -- fr-sponge absorb
  | squeeze  : _                    -- squeeze marker (not re-absorbed)
```

with `T := List (KimchiTranscriptElt C)`. The six prefixes are then literal transcriptions
of `fqOracles`/`frOracles`'s absorb order (the fr-sponge prefix embeds `fqDigest`, which
chains the two sponges into one domain). Distinctness of the six points is by list shape
(different lengths/tags) — small decidable lemmas, ironwood's encoding-injectivity
obligation made proof rather than assumption where possible. Alternative considered and
rejected: a bespoke 6-constructor query type (simpler injectivity, but useless for W5's
IPA rounds and it hides the transcript structure the forking argument needs).

**D2 — Oracle codomain `F`.** `F := C.ScalarField`, uniform — i.e. the oracle answers
*post-conversion* challenges directly. This is ironwood's exact idealization
(`uniformChallenge : PMF Fp`), and it absorbs both of our conversions (the 128-bit cast
for β/γ; `endoExpand` for α/ζ/v/u) into the model, with the same documented caveat:
*the conversions' deviation from uniform is negligible and unaccounted in the bounds*.
Alternative (stronger, deferred): oracle answers `Fin 2^128` and we prove the conversions
carry bad-set bounds through — the cast is injective (2¹²⁸ < p) so that side is free;
`endoExpand` injectivity is plausibly provable from the GLV short-basis bounds already in
`Pasta/Endo.lean` (a collision yields a short `λ`-relation), but it is real work and
buys only the removal of a caveat ironwood also carries. Record as a W6+ strengthening,
do not block W2.

**D3 — One model per curve, both sponges in one oracle.** The fq- and fr-sponges have
different states and parameters, but the *model* needs only one uniform
`O : T → C.ScalarField` with sponge-tagged prefixes (D1). Vesta and Pallas instantiate
the same generic development at their curve bundles — no per-curve axioms needed at all
(see §5).

**D4 — The bridge (`runOraclesO`).** New defs, structured as challenge-parametric
versions of the existing readers:

- `oracleChallenges O cvk cp pub : β × γ × α × ζ` and `oracleVU O cvk cp pub : v × u` —
  read `O` at the six §2 prefixes;
- the substitution seam: a challenge-parametric `runOracles`-analogue is **not** a
  rewrite of `fqOracles` (frozen file); it is a *new* def in the Forking tree that
  computes the same downstream data (`runW/runZ` are already challenge-free; the guards
  and `RunGuardImp` take challenges as the `runOracles` projections). Concretely W3 needs
  only: `GuardEvent O := the antecedents of RunGuardImp with runOracles/runVU replaced by
  the O-reads`, plus the definitional bridge
  `poseidonO cvk cp pub : T → C.ScalarField` (evaluate the real sponges along a prefix)
  with `oracleChallenges (poseidonO …) … = (runOracles …).{beta,gamma,alpha,zeta}` and
  `oracleVU (poseidonO …) … = runVU …`. These bridges should be `rfl`-adjacent: the
  prefixes are transcriptions of the very absorb sequences the sponge functions execute.
  (If `rfl` fails, small unfolding lemmas; no statement of the frozen files changes.)

**D5 — Finiteness.** `T` is infinite (field-valued absorbs). For W3's per-site escape
bounds this is handled pointwise (`uniformOfFintype_fresh_read_bound` needs the
*embedded index set* finite, not `T`); for W4's game-level advantage over `T → F`,
reuse ironwood's `DomainReduction` (`reachSet`) as-is. No new finiteness machinery.

## 4. Deliverables, sizes, acceptance

New modules only, under `kimchi/Kimchi/Verifier/Forking/` (per the no-new-package
decision); nothing existing is edited; kimchi's axiom gate grows the second tier only
when W4 adds roots (W2 adds none).

| Module | Contents | Est. |
|---|---|---|
| `Forking/Transcript.lean` | `KimchiTranscriptElt`, the six prefix defs (literal absorb-order transcriptions), pairwise-distinctness lemmas | ~200 lines |
| `Forking/OracleRun.lean` | `poseidonO` (sponge-evaluated oracle), `oracleChallenges`, `oracleVU`, the six bridge identities | ~250 lines |
| `Forking/Model.lean` | the RO-model preamble (trust statement, §5's outcome), `GuardEvent`, the `fsWins` instantiation shape for W4 | ~120 lines |
| docs | trust-surface paragraph in the module preamble + plan W2 checkoff | — |

**Acceptance gates:** (i) `lake build Kimchi` green, no existing statement touched;
(ii) the six bridge identities proved (`rfl` or short unfolding proofs) — this is the
non-negotiable one: it pins the model to the deployed schedule; (iii) prefix-distinctness
lemmas proved; (iv) axiom gate unchanged (W2 declares **no** axiom under the recommended
§5 outcome); (v) style/lint/shake clean.

**Estimated effort:** 1–2 weeks (per plan P2), dominated by the bridge identities.

## 5. THE SIGN-OFF QUESTION — how "Poseidon-as-RO" enters the system

The plan (§4) anticipated "ONE honest RO-realization axiom per curve." Scoping against
ironwood revealed a better-shaped option, and the choice changes the trust surface's
*form*, so it is the user's call. The tension: the deployed sponge is a **deterministic
function** — there is no probability space on the real side — so any Lean `axiom`
connecting it to the uniform oracle is either false as stated (probability-1 shapes: the
M3 mistake again) or not expressible without inventing a distribution over something
(seeds/keys) the protocol does not have.

**Option A (recommended — ironwood parity).** No new Lean axiom. The W4 probabilistic
capstones are stated *in the RO model*: for every `OracleComp` adversary and uniform `O`,
the measure of oracles on which the adversary wins (accepted + extracted table fails
`Satisfies`) is ≤ ε. "The Poseidon sponge realizes this oracle at the deployed
transcript encoding, and the 128-bit-cast/`endoExpand` conversions are uniform enough"
becomes a **named, documented modeling assumption** — stated in the `Forking/Model.lean`
preamble, `roots.txt` prose, and the trust-surface docs with the same prominence as an
axiom, but not a kernel-level declaration. Consequences: the axiom gate's allowlist does
not grow; the four legacy FS axioms remain the only FS-related kernel axioms (consumed
only by the legacy line); the Lean-checkable content is maximal (everything inside the
model is proved); the RO step is exactly as auditable as ironwood's — by reading, not by
`#print axioms`.

**Option B (a kernel axiom, as the plan originally sketched).** Declare, per curve,
an axiom of the least-false expressible form — e.g. an abstract
`PoseidonRO : (T → C.ScalarField)` constant together with
`axiom poseidonRO_uniform : ∀ (E : Set (T → F)), measurable-event bound …` — i.e.
*postulating a distribution-like interface for the sponge*. Consequences: the assumption
is visible to `#print axioms`/the gate (a genuine benefit for our audit discipline), but
the statement is artificial (it asserts uniformity of a specific deterministic function —
strictly false, exactly the shape M3 flagged), and every W3/W4 theorem inherits an axiom
whose falsity-as-stated we would have to scope apologetically. This is the trade: gate
visibility vs. statement honesty.

**Recommendation: Option A**, with one mitigation adopted from our own audit findings:
the modeling assumption gets a single named Lean *definition* (e.g.
`def PoseidonROModelStatement : Prop`-shaped documentation anchor or simply a reserved
docstring section) referenced from every W4 root's docstring and from `roots.txt`, so no
reader can consume a probabilistic root without seeing the model boundary. If you want
the kernel-visible axiom regardless (your prerogative — "this is an axiom in our
system"), Option B is implementable; I would then also add the M3-style scope note to it
on day one.

**Also implicitly signed off with either option:** the D2 conversion idealization
(uniform post-conversion challenges; `endoExpand` bias unaccounted — ironwood-identical
caveat) and the D1 encoding (prefix distinctness proved where possible, assumed injective
where the model requires it).

## 6. Risks

| Risk | Mitigation |
|---|---|
| Bridge identities not `rfl` (sponge threading vs. prefix reading mismatch) | prefixes are transcriptions of the same absorb calls; fall back to unfolding lemmas; worst case restate `poseidonO` per site |
| `endoExpand` bias objection from a reviewer | documented caveat (ironwood-identical); D2 strengthening path recorded (GLV short-basis injectivity proof) |
| `Fintype` friction at the game layer | pointwise bounds for W3 avoid it; `DomainReduction` reused for W4 |
| Ironwood API drift under us | pin already hard (`83a98f7f`); the consumed core is its most stable layer |
| Scope creep into W5 (IPA-interior challenges) | explicitly out: §2 marks them; `Transcript.lean`'s element type already accommodates them so W5 extends, not reworks |

## 7. Where the Poseidon-as-RO trust boundary lives now (2026-07-25)

`kimchi/Kimchi/Verifier/Forking/Model.lean` was deleted, and this section replaces its preamble as
the written statement of the trust boundary. Its four declarations went with it: `GuardEvent` is
`Zcash.Snark.fsWinsFull` at `m = 4` with the prefix indirection inlined, `GuardEventVU` the same at
`m = 2`, and `guardEvent_poseidonO` / `guardEventVU_poseidonOFr` are two-line corollaries of
`oracleChallenges_poseidonO` (`Forking/OracleRun.lean:107`) and `oracleVU_poseidonOFr` (`:188`),
which survive. No content was lost; the faithfulness statements live where the faithfulness proofs
already were.

**The assumption, unchanged.** `Forking/Transcript.lean` and `Forking/OracleRun.lean` are fully
verified — they define the transcript domain, interpret a prefix through the deployed Poseidon
sponge, and prove that reading it at the prefixes reproduces the verifier's own challenges. What is
*assumed*, and only here, is that the deployed sponge read at those prefixes behaves as a uniform
random function on its query domain.

This is deliberately **not** a Lean `axiom`. The sponge is a deterministic function; asserting its
uniformity inside the kernel would be a false-as-stated proposition — an unconditioned distribution
claim, the shape §5 and the statement audit both flagged. Every probabilistic theorem is instead
stated *within* the uniform model, following ironwood's own `Forking.Oracle`, and this paragraph is
the boundary where the model meets Poseidon.

**One correction carried over.** `Model.lean`'s preamble claimed the assumption was "auditable here
and in `roots.txt`". It was not: no declaration under either `Forking/` tree appears in any
`roots.txt` (verified, zero hits), so the axiom gates never saw this layer at all. That gap is why
`bulletproof-pcs/scripts/check_locked_target.sh` and `scripts/check_sorry_census.sh` exist — the
first pins the statement being proved, the second pins the sorry set in both directions, because
`check_axioms.sh` cannot see either.

**One idealisation retired rather than carried.** `Model.lean` also recorded that the 128-bit
prechallenge cast and the endomorphism expansion were "treated as landing uniformly in
`C.ScalarField`", with a strengthening deferred. That deferral is no longer needed on the IPA side:
the locked target (`docs/locked-target.md`) games the **prechallenge** alphabet directly and divides
its error by `2 ^ 128`, with `expandPre`'s injectivity and non-vanishing as theorems. The idealisation
was not merely imprecise — the deleted `Forking/GuardEscape.lean` divided by
`Fintype.card C.ScalarField ≈ 2 ^ 254` for challenges carrying 128 bits, understating the per-round
cost by about `2 ^ 126`. Restating kimchi's plonk-phase guards over the prechallenge alphabet is
open work, tracked as the `m = 6` instantiation; until it lands, kimchi has **no** plonk-guard escape
bound, correct or otherwise. That is a debt, not progress.
