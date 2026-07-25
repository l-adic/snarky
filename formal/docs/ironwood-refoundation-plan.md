# Refounding the soundness line on ironwood's forking primitives — plan

**Status: PLAN ONLY — nothing here is enacted.** Companion to
`statement-audit-report.md` (this plan is the follow-up for finding **M3** and the
"deferred forking/density model" scope note carried by the run-level roots after the
C1 fix, PR #269).

## 0. Goal and constraints

**Goal.** Discharge the undischarged guards of the terminal run-level roots — the
run-oracle avoidance conditions (`runOracles ∉ Protocol.soundBad*`, `hξ`/`hr`) — as
*negligible-probability events with an explicit knowledge error*, by taking
[`zcash/ironwood`](https://github.com/zcash/ironwood) as a **direct lake dependency**
and building a probabilistic capstone layer on its forking/random-oracle machinery.
End state: run-level soundness statements of the form

> for any `Q`-query adversary producing an accepted `(cvk, cp, pub)` with AGM
> representations, the measure (over the random oracle) of transcripts on which the
> extracted table fails `Satisfies` is `≤ ε(n, Q)/|F|`-shaped, explicitly,

with a trust surface of: **Poseidon-realizes-a-random-oracle (axiom, accepted), DL-relation
hardness (`hbind`, hypothesis as today), the point-count/`native_decide` certificate base
(as today)**.

**Constraints (binding):**

1. **Poseidon-as-RO is an accepted axiom.** We are not treating the Blake2b→Poseidon
   substitution as a risk to engineer around. The refoundation states ONE honest
   RO-realization axiom per curve (§4) and builds everything above it as theorems.
2. **No declared root is thrown away.** Every entry in `kimchi/roots.txt` (and the
   bulletproof-pcs manifest) keeps its name and its current statement. The four existing
   FS axioms stay declared (the legacy deterministic line keeps compiling and keeps its
   gate). The refoundation is **additive**: new roots alongside the old, old ones
   eventually *scoped* in prose as the deterministic core the probabilistic layer wraps —
   never deleted, never restated destructively.
3. Ironwood is consumed as a **pinned git dependency** (`[[require]]`), not a vendored
   copy. We track a pinned rev and bump deliberately.

**Non-goals.** No unconditional soundness (does not exist). No change to the executable
verifier, the wire boundary, the gate layer, or the fixtures. No porting of ironwood's
Orchard/halo2 protocol content (their `Circuits/`, `Snark/Verifier/*` deployed material,
lookup arguments) — only the generic forking/probability core is consumed.

## 1. What we have and what is open (recap)

After PR #269 (C1), the terminal roots `kimchi{Vesta,Pallas}_run_sound_algebraic_ft`
conclude `RunBounds ∧ RunGuardImp` over the *named* exclusion sets
`Protocol.soundBad{B,G,A,Z}` at the run's assembled `runW`/`runZ` and the explicit table
`runWTab`. The statements are non-vacuous; what remains open, per the audit:

- **The avoidance guards are hypotheses.** Nothing bounds the probability that the run's
  own Poseidon-derived challenges land inside the (card-bounded) exclusion sets, nor that
  `polyscale/evalscale` avoid `badXiOf`/`badROf`. (The "forking/density model".)
- **The four FS axioms** (`poseidon_fiat_shamir_*`, `kimchi_fiat_shamir_*`) assert
  probability-1, adversary-unbounded transcript-tree extraction over every SRS — audit
  finding M3 (over-strong as stated; in-principle refutable at degenerate SRS).
- **M5**: the standard-model `kimchi{Vesta,Pallas}_run_sound` still have the pre-C1
  existential shape.

This plan addresses the first item fully, the second by *narrowing what the trust surface
needs to assume* (the tree-extraction content becomes provable, W5), and the third
incidentally (W6).

## 2. What ironwood provides (verified against a clone, main @ 2026-07-23)

Repo: `zcash/ironwood`, Lean 4 **v4.30.0**, Mathlib pin **v4.30.0** — *identical to
ours* — dual-licensed MIT/Apache-2.0, package name `Zcash`. Requires
`daira/CompElliptic` (our vendored fork's upstream) and `Verified-zkEVM/clean` (used by
their `Circuits/`, NOT by the forking core). No `sorry`; free axioms limited to
`pallas_natCard` (a point count, same trust class as our CompElliptic certificates);
axiom hygiene enforced by their `Zcash/Meta/AxiomCheck.lean` census
(`assert_axioms`/`assert_computable`), a mechanism worth adopting alongside our own gate.

The reusable core, with import closures checked:

| Module (`Zcash/Snark/Soundness/…`) | Contents | Deps |
| --- | --- | --- |
| `Forking/Tree.lean` | transcript-tree combinatorics | Mathlib only |
| `Forking/Probability.lean` | measure theory on `PMF.uniformOfFintype`: **`uniformOfFintype_fresh_read_bound`** (a fresh oracle read lands in a prefix-determined bad set with measure ≤ β), `forking_measure_bound`, `extractable_of_prob`, rectangle/fiber bounds | Mathlib + `Oracle`, `Tree` |
| `Forking/KnowledgeError.lean` | `kerr N d = 3·d·N^(d−1)` — the (3, d)-special-soundness knowledge error, `kerr_div_card` | `Tree` |
| `Forking/Adversary/OracleComp.lean` (~1.3 kLOC) | the query monad `OracleComp T F α`: `run`, `queries`, `history`, `escapesDuring(C)`, `dedup`, `forkIdx`, `fsWins`, `fsAdvantage` — **generic in the oracle domain `T` and field `F`** | `Rewind` |
| `Forking/Adversary/{Adaptive,DomainReduction,ExpectedRuns,ExpectedRunsPoly,Recursive,PreIpa,Provenance,Algebraic}.lean` | adaptive-adversary reductions, domain restriction, expected-runtime rewinding, the algebraic (AGM) adversary | above |
| `Forking/{Oracle,Rewind,Extractor,Assembly,Ordering}.lean` | oracle model, rewinding schedule, extractor assembly | ⚠ `Rewind` imports their `Soundness.Main`; `Oracle` imports their `Verifier.FiatShamir`, `Core.Field` — **Orchard-entangled** (§5, W5) |
| `AGM/{Capstone,Peel,Prover,Probability*}.lean` | AGM extractor: `deployedAlgebraicRelationFinder`, `relationOfRun_isSome_of_mismatch` — a forking mismatch *produces a DL relation* | above |
| `KnowledgeSoundness.lean` | `knowledge_sound` (proved conditional core), `soundness_error` (SZ count → probability over `scalarFieldOrder`) | — |

**Field identity (important):** their `Fp := ZMod scalarFieldOrder` with
`scalarFieldOrder := CompElliptic.Fields.Pasta.PALLAS_BASE_CARD` — *definitionally our
`Fp`* (Vesta scalar = Pallas base), built from the same CompElliptic constants we vendor.
Concrete-field lemmas transfer to our Vesta side with no transport; the generic lemmas
are field-polymorphic and cover the Pallas side.

**Two-layer split to respect:** `Tree`/`Probability`/`KnowledgeError`/`OracleComp` +
the `Adversary/*` reductions are protocol-agnostic (consume directly);
`Oracle`/`Rewind`/`Extractor`/`Main` are Orchard-specific (treat as *templates* to
re-derive over our `Ipa.verify`, not as imports — except where the generic parts can be
factored, see W5 risk).

## 3. Dependency engineering (W1)

**STATUS: DONE — PR #272.** Ironwood (`Zcash`) is wired into `formal/lakefile.toml` and
`formal/kimchi/lakefile.toml`, pinned at ironwood main HEAD
`83a98f7fb3bcd8f87ddf0a459dcab96a782d91d8`. A workspace-level `path` require of
`CompElliptic` (`vendor/CompElliptic`) makes ironwood's transitive
`daira/CompElliptic @ a549e455` resolve to our vendored submodule — the diamond collapsed
to one source (manifest: `CompElliptic :: path`), mathlib unchanged. Verified: full
workspace builds green, and `lake build Zcash.Snark.Soundness.Forking.Tree` builds — ironwood
is usable from our workspace. Nothing imports `Zcash.*` yet, so CI fetches but does not
compile it. Items 1–3 below are the design record; item 4 (the `forking/` package) was
superseded by the "no new package" decision — the layer lives under
`kimchi/Kimchi/Verifier/Forking/`.

1. **Require pin.** In `formal/lakefile.toml` (workspace) and the consuming package
   lakefiles: `[[require]] name = "Zcash" git = "https://github.com/zcash/ironwood" rev
   = "83a98f7fb3bcd8f87ddf0a459dcab96a782d91d8"`. Pin + bump policy in the lakefile comment.
   Toolchain and Mathlib pins already agree (v4.30.0/v4.30.0), so no second Mathlib is built.
2. **The CompElliptic diamond — RESOLVED BY SWITCHING TO UPSTREAM** (verified
   2026-07-23 against a fetch of `daira/CompElliptic @ a549e455`, ironwood's exact pin).
   Divergence audit: our fork carries exactly two substantive local patches, and both
   have cheap exits —
   (a) *the `Fp`/`Fq` rename* (`0392940`): upstream has the four role aliases
   (`PallasBaseField`, …), our tree consumes bare `Fp`/`Fq` via
   `open CompElliptic.Fields.Pasta` in **12 files across 5 packages**. Fix: a two-line
   shim in our `pasta` package (`namespace CompElliptic.Fields.Pasta` +
   `abbrev Fp/Fq := ZMod *_CARD`, defeq to upstream's aliases) — zero churn to the 12
   consumers. (Optionally PR the rename upstream later; ironwood itself defines
   `Fp := ZMod PALLAS_BASE_CARD` privately, so upstream demand exists.)
   (b) *the `SWPoint ↔ Affine.Point` card bridge* (`e31413f`:
   `SWPoint.equivPoint`, `SWPoint.card_eq_point`, `valid_ofPt`, `toPt_ofPt`, ~49 lines):
   consumed at exactly **two sites** (`pasta/Pasta/Basic.lean:41,47`); its substrate
   (`toW`/`toPt`/`ofPt`) exists upstream unchanged. Fix: relocate the four declarations
   into the `pasta` package (or PR upstream — a clean complement to their new computable
   `instFintypeSWPoint`).
   The switch also *gains* upstream's `TrustBoundary.lean` + `Meta/AxiomCheck.lean`
   (`assert_axioms`/`assert_computable` — the very hygiene machinery W1.5 wants) and the
   computable `Fintype (SWPoint E)`. Lakefile change: the `path`-require on
   `vendor/CompElliptic` becomes a git require pinned at `a549e455` (or the vendored
   checkout is reset to that rev) — one CompElliptic in the workspace, byte-identical to
   ironwood's pin, no name-resolution question at all. Remaining W1 obligation: a full
   `lake build` + all axiom gates against upstream (the trusted-`native_decide` prefixes
   `CompElliptic.*` and the `pallasBase`/`vestaBase` certificate names are unchanged, so
   gates are expected green — but this is asserted from API diff, not yet from a build).
3. **`Clean` footprint.** Lake will *fetch* `Verified-zkEVM/clean` (transitive
   requirement) but only the imported closure is *built*; the forking core does not
   import it. Accept the fetch; document it.
4. **Placement: inside the `kimchi` package — no new package.** The probabilistic layer
   lives in a new subtree `kimchi/Kimchi/Verifier/Forking/` (oracle model, bridges, guard
   discharge, probabilistic capstones). `kimchi/lakefile.toml` gains the `Zcash` require
   (and the workspace aggregator mirrors it). All additions are **new modules only**:
   nothing existing under `kimchi/` or `bulletproof-pcs/` is edited except additive
   `roots.txt` entries and (if separately approved) one-sentence docstring pointers.
   Existing declarations, statements, and proofs stay byte-identical.
5. **Gates — tiered, so legacy closures are *enforced* unchanged.** The new roots join
   `kimchi/roots.txt` (additive) and `kimchi/scripts/check_axioms.lean` grows a **second
   tier**: the existing root list keeps the existing allowlist verbatim (so any leakage
   of the new axioms into a legacy root's closure FAILS the gate — constraint 2 becomes
   machine-checked, not convention); the new `Forking` roots get an extended allowlist =
   existing tier + ironwood's `pallas_natCard` + the new Poseidon-RO axiom(s) (§4).
   CI (`lean.yml`): build/lint/shake/kernel-replay pick the new modules up via the
   existing kimchi package wiring; extend `scripts/deadcode.sh` roots via the updated
   manifest. Evaluate adopting ironwood's `assert_axioms`/`assert_computable` attributes
   inside the `Forking/` subtree for per-declaration hygiene.

**Gate to W2:** ironwood's forking closure builds green inside our workspace against
upstream CompElliptic, and a trivial smoke theorem under `Kimchi/Verifier/Forking/` consuming
`uniformOfFintype_fresh_read_bound` passes our axiom gate.

## 4. The oracle model and the ONE new axiom (W2)

**Model.** Adopt ironwood's shape: an oracle is a function `O : T → F` drawn from
`PMF.uniformOfFintype (T → F)`; an adversary is an `OracleComp T F` program. Our oracle
domain `T` is the **transcript-prefix type** of the deployed schedule: a query point is
the full absorb history at a squeeze (the `fqOracles` β/γ/α/ζ squeezes, the `frOracles`
v/u squeezes, and the IPA round/`c` squeezes of `Ipa.verifyFrom` — one constructor per
squeeze site, indexed by the absorbed data). This is a reflection of
`Verifier/Kimchi.lean`'s existing schedule, not a new protocol description; W2's
deliverable is the definitional bridge

> `runOraclesO O cvk cp pub` — the challenges of the run when the sponge squeezes are
> read from `O` — together with `runOraclesO poseidonO = runOracles` where `poseidonO`
> is the sponge-defined oracle,

with the same bridge for `runVU` (polyscale/evalscale) and the IPA finish.

**The axiom (per curve).**

```
axiom poseidon_random_oracle_vesta :
  ∀ {α} (A : OracleComp TranscriptPrefix Fp α) (E : Set α),
    -- the behaviour of A against the Poseidon-sponge oracle is that of A against a
    -- uniformly random oracle:
    (A.run poseidonO ∈ E) ↔ᵖ …   -- (final form: an equality of the induced measures,
                                  --  or the standard "no distinguisher" formulation)
```

Final formulation to be settled in W2 (candidates: (a) measure-transport — the pushforward
of `uniformOfFintype` along `A.run` is the distribution of `A.run poseidonO` under the
sponge's seed, (b) per-event bound — for every event, its sponge-probability is ≤ its
RO-probability + 0, i.e. exact emulation, which is the user-accepted reading). Design
requirements, learned from finding M3: the axiom must be (i) stated **only** about the
sponge-vs-uniform substitution — no tree, no extraction, no acceptance content; (ii)
quantified over the *deployed* sponge parameters (not arbitrary SRS — there is no SRS in
it at all); (iii) accompanied by the same candid scope note style `hbind` carries.
This is deliberately **much weaker** than the current FS axioms: everything those axioms
smuggle (tree existence, de-blinding, the scalar-equation↔tree correspondence) becomes
theorem material (W3/W5).

**Existing axioms untouched.** `poseidon_fiat_shamir_*`/`kimchi_fiat_shamir_*` remain
declared and the legacy roots remain gated over them (constraint 2). Their docstrings
gain one sentence pointing at the probabilistic line. (A later, separate decision may
restrict their `σ`-quantification per M3; out of scope here.)

**Gate to W3:** the bridge identities (`runOraclesO poseidonO = runOracles` etc.) proved
definitionally; the axiom statement reviewed by the user (this is the trust surface —
human sign-off, not CI).

## 5. Workstreams over the machinery

### W3 — Escape-probability discharge of the guards

For each undischarged guard, package the exclusion set as a *prefix-determined* bad set
and apply `uniformOfFintype_fresh_read_bound` + our existing card bounds:

| Guard (challenge) | Exclusion set | Determined by (absorbed BEFORE the squeeze) | Card bound (have) |
| --- | --- | --- | --- |
| β | `soundBadB idx runW` | witness commitments (`wComm`) | `≤ 7(n − zkRows)` |
| γ | `soundBadG idx runW β` | `wComm`, β | `≤ 7(n − zkRows)` |
| α | `soundBadA … runZ β γ` | `wComm`, `zComm`, β, γ | `≤ n(K − 1)` |
| ζ | `soundBadZ … (ftChunkAssembly …)` | + `tComm` | `≤ degreeBound n = 9n` |
| ζ boundary | `{1, ω^(n−zkRows)}` | — | `= 2` |
| polyscale v | `badXiOf σ aRef …` | the full commitment stream | `≤ 2(44·nc+1−1)` |
| evalscale u | `badROf σ aRef … v` | + v | `≤ 1` |

The chronology column is the crux, and it is already sound: each named set is a function
of data the deployed schedule absorbs *before* the corresponding squeeze (this is what
the C1 named-sets refactor bought us — the sets are explicit functions of prefix data,
so ironwood's `φ`-injection fresh-read setup applies literally). The adversary is
adaptive (chooses `cp` interactively); that is exactly what `OracleComp` +
`Adversary/Adaptive.lean` (`fsWinsFull`, `completing`) handle — the standard
commit-then-challenge measurability, formalized.

Deliverable: `runGuards_whp` — the measure of oracles on which any antecedent of
`RunGuardImp` (plus `hξ`/`hr`) fails is `≤ (7(n−zk)+7(n−zk)+n(K−1)+9n+2+2(44·nc)+1)/|F|`
(explicit union bound; number is illustrative pending the exact per-guard counts).

### W4 — The probabilistic run-level capstones (new roots)

Compose W3 with the **existing, untouched** terminal roots: `RunGuardImp` is precisely
"guards ⟹ Satisfies", so

> `kimchi{Vesta,Pallas}_run_sound_ro` (names TBD): for a `Q`-query `OracleComp`
> adversary emitting `(cvk, cp, pub, aRef, ρRef, aT, ρT)` with
> `kimchiVerify … = true`, `hrep`/`hTC`, `cvk.Corresponds σ idx`, `hbind`: the measure
> of oracles on which `Satisfies idx (pubView idx pub) runWTab` fails is ≤ ε(n, nc, Q)/|F|.

Consumes: the Poseidon-RO axiom + W3 + `kimchi{Vesta,Pallas}_run_sound_algebraic_ft`
(as-is) + (for the FS-tree hypothesis, until W5 lands) the existing kimchi FS axiom.
Added to `kimchi/roots.txt` as **new** roots (second gate tier, §3.5); the old roots stay. The AGM
representations and `hbind` remain hypotheses — the declared trust surface is unchanged
in kind.

### W5 — Deriving tree extraction (retiring the FS axioms' content) — stretch

The remaining assumed content is `FiatShamirTreeB` (accepted run ⟹ de-blinded accepting
3-ary tree). Ironwood *proves* this shape: `Forking/Rewind` + `Adversary/ExpectedRuns` +
`KnowledgeError` (`kerr N d`) + `AGM/Capstone` derive tree extraction from a `Q`-query
accepting adversary, with the mismatch case emitting a DL relation. Port strategy: their
`Rewind`/`Extractor` are Orchard-entangled (import their `Soundness.Main`), so this is a
**re-derivation over our `Ipa.verifyFrom`** using their generic
`OracleComp`/`ExpectedRuns`/`KnowledgeError` layers — the probabilistic heavy lifting is
generic; the protocol wiring (our IPA round structure, `k` rounds, 3 challenges per
node) is ours. Endpoint: a *theorem*
`fiat_shamir_tree_whp : … measure(no tree | accepted) ≤ kerr(|F|, 3^k-ish)/|F| + DL-advantage`,
after which the probabilistic capstones consume no FS axiom at all — trust =
Poseidon-RO + `hbind` + certificates. The legacy axioms remain declared for the legacy
line (constraint 2) but nothing in the new line consumes them.

This is the largest and most uncertain workstream; it is severable — W1–W4 deliver the
guard discharge (the audit's deferred item) without it.

### W6 — M5 cleanup (opportunistic)

Restate `kimchi{Vesta,Pallas}_run_sound` (Standard.lean) in the C1 named-set vocabulary
(same fix as PR #269, sibling shape), so the probabilistic layer can wrap the
standard-model line too. Additive/statement-strengthening only; names preserved.

### W7 — Documentation and trust-surface truth

- `roots.txt` (forking + kimchi): the new roots' prose, with the explicit ε.
- The audit report gains an addendum: M3 status → "narrowed: new line consumes only the
  RO-realization axiom"; the deferred-forking register row → discharged (W3/W4) /
  remaining (W5 if unfinished).
- `formal/CLAUDE.md` package table + trust-surface section (also fixes audit M9 for the
  new layer).
- A `Kimchi/Verifier/Forking/` module preamble stating, in external-reviewer language, exactly what the
  probability is taken over and what `Q` bounds.

## 6. Risk register

| Risk | Likelihood | Mitigation |
| --- | --- | --- |
| CompElliptic switch-to-upstream breaks something the API diff missed | low | W1.2 verified the only two fork patches + their exits; full build + gates before merging; the fork stays recoverable in git if the build disagrees |
| Ironwood API churn (active pre-NU6.3 development) | high over months | hard pin + deliberate bumps; the consumed core (`Tree`/`Probability`/`OracleComp`/`KnowledgeError`) is the most stable layer |
| Axiom-formulation subtlety in §4 (an RO axiom accidentally too strong — M3 repeat) | medium | the axiom mentions ONLY sponge-vs-uniform; adversarial review of the statement (re-run the D3 panel discipline on it); user sign-off gate |
| Adaptive-adversary bridging (our reflection is deterministic; `OracleComp` is a program) | medium | W2 bridge theorems are definitional (`runOraclesO poseidonO = runOracles`); keep the adversary abstract, instantiate at "the program that outputs the fixed `(cvk,cp,…)`" first, generalize after |
| W5 scale (re-deriving rewinding over our IPA) | high | severable; W1–W4 stand alone; scope W5 only after W4 lands |
| Build-time/CI cost | low | same Mathlib pin — no duplicate Mathlib; forking closure is small; fixtures untouched |
| License | none | MIT/Apache-2.0 dual — compatible; attribute in the lakefile comment |

## 7. Phasing and acceptance

| Phase | Content | Acceptance gate |
| --- | --- | --- |
| P1 (days) | W1 dependency + gates + smoke theorem | workspace builds; smoke root passes axiom gate |
| P2 (1–2 wk) | W2 oracle model + bridge + axiom statement | bridge identities proved; axiom text signed off by user |
| P3 (2–4 wk) | W3 guard discharge (`runGuards_whp`) | per-guard escape lemmas + union bound, axiom-gated |
| P4 (1–2 wk) | W4 probabilistic capstones + W7 docs | new roots green in CI; legacy roots byte-identical; audit addendum |
| P5 (unscoped) | W5 tree-extraction derivation; W6 M5 | separate SoW after P4 review |

Every phase preserves: all existing roots byte-identical in statement, all existing gates
green (the legacy tier of the kimchi gate enforcing unchanged closures, §3.5). All edits
under `kimchi/` are additive: new modules under `Kimchi/Verifier/Forking/`, new
`roots.txt` entries, the lakefile require — plus (P4/W6) additive docstring sentences and
the M5 restatement if approved. `bulletproof-pcs/` is untouched.

## 8. Explicit non-commitments

- No claim of unconditional soundness; the endpoint trust surface is
  {Poseidon-as-RO axiom, `hbind`, `Lean.ofReduceBool` + point-count certificates}
  (+ the legacy FS axioms, consumed only by the legacy line, until/unless W5 retires
  their use).
- No deletion or restatement of `poseidon_fiat_shamir_*` / `kimchi_fiat_shamir_*`.
- No new workspace package: the probabilistic layer lives in `kimchi/` under
  `Kimchi/Verifier/Forking/` (the `kimchi` package gains the ironwood require;
  `bulletproof-pcs` does not). No existing module in either package is modified.
