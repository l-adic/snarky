# Scope: the AGM prover model for bulletproof-pcs, by reusing ironwood

**Constraint:** use as much of `zcash/ironwood` as possible without redefining or rebinding.

The survey below changes the shape of the job. I previously scoped this as "build an AGM prover
model for bulletproof-pcs". That is wrong: **ironwood's AGM layer is fully generic and already
complete**, and separately, **our single-opening core is a re-derivation of ironwood's IPA
soundness layer**. The work is almost entirely *deletion and re-pointing*, not construction.

---

## 1. What ironwood already has (nothing to build)

The whole AGM + forking + DL-reduction stack is parameterized over an arbitrary finite basis
`basis : ι → G` with `[Fintype ι]`. Nothing is halo2-specific or curve-specific.

| Need | Ironwood provides | Where |
|---|---|---|
| AGM representation | `GroupRepresentation`, `AlgebraicPoint`, `representationEval` | `AGM/Adapter.lean:44-56` |
| Relation as data | `AlgebraicRelationWitness` (`coeffs ≠ 0`, eval `= 0`) | `AGM/Adapter.lean:85` |
| DL relation on a URS | `NontrivialDLRelation`, `.ofCollision`, `.ofIpaOpenings` | `CommitFold.lean:115-137` |
| Algebraic prover | `AlgebraicProver`, `.toProver` | `AGM/Prover.lean:19-27` |
| Algebraic fork cert | `AlgebraicDForkCert`, `.toDForkCert` | `AGM/Prover.lean:35-44` |
| Plain prover + accept | `Prover`, `proverAccept`, `proverAccept_forkValid` | `Forking/Extractor.lean:212-226` |
| Fork validity | `DForkCert`, `DeployedForkValid`, `produceDeployed` | `Forking/Extractor.lean:110-141` |
| **Data-valued extractor** | `ipa_extractV` (a `def` into `Σ'`) | `IpaSoundness.lean:164` |
| Deployed peel → break | `NontrivialRelation.ofDeployedTree`, `ofFoldedGens`, `ofLeafPeel` | `Deployed/IpaPeel.lean:53-92` |
| Relation → discrete log | `discreteLogOfBasis_of_relation`, `DLChallengeGame`, `solveFromRelation` | `AGM/Adapter.lean:211-269` |
| Augmented basis plumbing | `AugmentedIndex`, `augmentedBasis`, `ursOfAugmentedBasis` | `AGM/Adapter.lean:315-336` |
| Top-level dichotomy | `deployedAlgebraicForkingRelation` | `AGM/Capstone.lean:30` |
| Slot-loss probability | `AGM/Probability.lean`, `.ProbabilityVesta` | — |

**Nothing in this table needs to be written.** Two items deserve emphasis:

- `ipa_extractV` is the data-valued extractor I claimed last message we would have to build. It
  exists, as a `def`, and `ipa_soundV` is merely its existential projection.
- `NontrivialDLRelation (urs : URS G)` is *exactly* the structure I proposed to define under that
  same name. Defining it would have been a direct violation of the reuse constraint.

## 2. What we duplicate (delete and re-point)

`Bulletproof/Soundness/SingleOpening.lean` and parts of `Protocol.lean` re-derive ironwood's IPA
layer declaration-for-declaration. Ours is the weaker copy in every case where they differ.

| ours | ironwood | note |
|---|---|---|
| `commitGen` | `commitGen` | character-identical |
| `innerProduct`, `evalVector` | `innerProduct`, `evalVector` | identical |
| `SRS` (`k, g, h, U`) | `URS` (`k, g, w, u`) | same structure, field-for-field |
| `commitGen_{add_left,smul_left,add_gen,smul_gen,sub}` (private) | same names, public | ours private ⇒ re-proved a 3rd time in `Forking/Triviality.lean` |
| `vandermonde3` | `vandermonde3` | **theirs returns `Σ'` (data); ours is a `theorem`** |
| `ipa_round_commit_with_coeffs` | same name | identical statement |
| `loHalf`, `hiHalf`, `append` | same names | identical |
| `foldHalves` | `foldGens` | **convention differs — see §3.1** |
| `loHalf_append`, `hiHalf_append`, `commitGen_split`, `commitGen_append` | same names | identical |
| `IpaTreeV`, `IpaAcceptV` | same names | same shape, modulo §3.1 |
| `ipa_soundV` (private, `Prop`) | `ipa_extractV` (`def`) + `ipa_soundV` | **theirs is strictly stronger** |
| `openingRelation`, `openingRelationB` | `IpaRelation` | ours splits blinded/unblinded |
| `CommitmentBinding`, `DLRelation`, `commitmentBinding_iff_no_relation` | `NontrivialDLRelation` + `.ofCollision` | ours asserts, theirs computes |
| `ipaRelation_unique` | `NontrivialDLRelation.ofIpaOpenings` | ours needs `hbind`; theirs returns the break |
| `FiatShamirTree` + the 2 declared axioms | `Prover` / `proverAccept` / `DForkCert` | ours assumed, theirs computed |
| `Forking/Extraction.lean`: `Strategy`, `stratAccept` | `Prover`, `proverAccept` | **I reinvented these last session — delete** |
| `Forking/Extraction.lean`: `ipaTreeV_of_extractable` | `proverAccept_forkValid`, `deployed_forking_tree` | same |

The `Strategy`/`stratAccept` pair I wrote is a duplicate of `Prover`/`proverAccept` down to the
constructor shape. It goes.

## 3. The three genuine mismatches

These are the only places real work is required.

### 3.1 The fold convention is inverted — **the one correctness risk**

```lean
-- ours
def foldHalves (v) (u) := loHalf v + u  • hiHalf v
-- ironwood
def foldGens   (g) (u) := loHalf g + u⁻¹ • hiHalf g
```

Both `IpaAcceptV`s update the commitment identically (`P + u⁻¹ • L + u • R`), so this is **not**
a naming difference: our accept predicate is genuinely not theirs.

Working it out, substituting `u = v⁻¹` into ours gives generators folded by `v⁻¹` and `P` updated
by `v • L + v⁻¹ • R`. So:

> our tree at challenges `uᵢ` ≡ their tree at challenges `uᵢ⁻¹` **with `L` and `R` swapped**.

That is an isomorphism of tree data, so it bridges cleanly — but it must be written and proved,
not assumed. **This is the item that would silently corrupt a naive "just use theirs" port**, and
it is the first thing to settle, because everything downstream inherits it.

Open question to resolve first: which convention does kimchi's deployed verifier actually use?
Our side is fixture-validated against kimchi (`verify_reflects`, `check_ipa_fixture.sh`), so if
kimchi folds by `u`, we keep our convention and carry the bridge; if by `u⁻¹`, we should re-point
onto `foldGens` and delete ours. Decide by reading `Wire.lean`'s fold against the fixture before
writing anything.

### 3.2 Blinded vs unblinded commitment

Ours: `commit σ a r = commitGen σ.g a + r • σ.h` (blinder is an argument).
Ironwood: `commit urs a = commitGen urs.g a`, with blinding carried in the `w` slot of the
deployed layer.

Not a blocker — ironwood already has `ipaRelation_unblind` and `ipaRelation_unblind_value`
(`InnerProduct.lean:104,114`) for exactly this. But our `openingRelationB` carries `ρ` in the
relation itself, so the adapter has to choose: keep our blinded relation and unblind at the
boundary, or move to their `w`-slot treatment. The `w`-slot treatment is what the AGM reduction
expects (`augmentedBasis g U W`), so moving is the reuse-maximal choice.

### 3.3 What is genuinely ours, and stays

Ironwood's deployed layer is halo2-shaped; ours is kimchi-shaped. Keep:

- the chunked/batched layer — `chunkCoeffs`, `assemblePoly`, `chunkedCombinedCommitment`,
  `combinedB`, `bPoly`, `BatchAccepts`, `chunked_ipa_soundness`, `chunked_batch_soundness`;
- the executable wire verifier — `Wire.lean`, `verifyWith` / `verifyFrom`, `verify_reflects`,
  and the fixture check;
- the Poseidon Fiat–Shamir instantiation and the W2–W4 oracle-model work.

Ironwood has no counterpart to the chunking, and its `Deployed/*` will not fit kimchi's verifier
equation. This is the part of bulletproof-pcs that earns its keep.

## 4. Plan

Staged so each step is independently checkable, ordered by risk.

**Stage 0 — settle the fold convention (§3.1). DONE**, in
`Bulletproof/Forking/Convention.lean`.

Kimchi's convention is **ours**. Ground truth is the verifier's `sg = ⟨bPolyCoefficients chal, g⟩`
check (`Wire.lean`): `bPolyCoefficients chal m = ∏ j, if testBit m j then chal (Fin.rev j) else 1`
is precisely the coefficient vector produced by folding with the high half scaled by `u`. At
`k = 2` that is `g₀ + chal₁·g₁ + chal₀·g₂ + chal₀chal₁·g₃`, which `foldHalves` reproduces exactly
and `foldGens` does not (it yields the inverted challenges). `Protocol.lean` records the same
asymmetry independently: `bPoly = ∏ (1 + u · X ^ 2 ^ i)`, the linear form.

So we keep `foldHalves` and carry the transport. Delivered:

- `toZcash` — invert every challenge, exchange `L`/`R` and `Lv`/`Rv`;
- `foldGens_inv : Zcash.Snark.foldGens v u⁻¹ = foldHalves v u` (`rfl` after `inv_inv`; their
  `loHalf`/`hiHalf` are definitionally ours);
- `zcash_ipaAcceptV_toZcash` — our accept implies theirs after transport;
- `ipaExtract` — ironwood's `ipa_extractV` run on kimchi transcripts, returning `Σ'` data.

Their `commitGen` unified with ours definitionally, so no adapter was needed for it.

**Stage 1 — adapter. DONE**, in `Bulletproof/Forking/Adapter.lean`. Additive only; the 7 roots and
the axiom gate stayed green.

- `ursOf` / `srsOf`, with both round-trips `rfl` (structure eta);
- `commit_eq_zcash : commit σ a r = Zcash.Snark.commit (ursOf σ) a + r • σ.h`, also `rfl`;
- `openingRelationB_iff_zcash` — our blinded relation is theirs at the de-blinded commitment
  `P - ρ • σ.h`, settling §3.2;
- `openingOfAcceptV` — the composite: a kimchi accepting tree yields a witness for **our own**
  `openingRelationB`, as data, with no extraction reproved on our side.

Also delivered (was flagged as a Stage-3 need): `Convention.ipaAcceptV_of_zcash` gives the reverse
transport, hence `ipaAcceptV_iff_zcash` and `Forking.decIpaAcceptV` — our accept is decidable by
transport onto ironwood's `decIpaAcceptV` rather than a hand-written instance. The peel needs that
decidability to locate a failing subtree.

`check_extractor_computes.sh` now covers both the unblinded extraction and the blinded composite.

**Stage 3 — the capstone. DONE** (reordered before Stage 2's deletions by user directive:
nothing is deleted until the capstone exists), in `Bulletproof/Forking/{Schnorr,Capstone}.lean`.

The survey's Stage-3 plan was over-scoped: reading `produceDeployed`/`deployed_forking_tree`
showed ironwood recovers the deployed tree's decorations by **Vandermonde interpolation of the
sibling recursions**, so no per-node AGM representations are needed — the plain `DForkCert`
suffices, and the AGM surface shrinks to a single root representation `P = ⟨pg, g⟩ + pw•H`
(exactly kimchi's Pedersen shape; `U` is transcript-derived after `P`, so no `U` slot).

- `schnorr_fork_eq` — the one extraction step ironwood lacks: kimchi's Schnorr wrapper is
  2-special-sound, with the extraction formulas inline (difference quotients);
- `KimchiForkCert` / `KimchiForkValid` — the `(3,…,3)` wire fork, in kimchi's fold convention,
  leaves carrying two Schnorr transcripts;
- `toDFork` + `KimchiForkValid.toDFork` — transport into ironwood's certificate and validity
  (`Pwhole = P + v•U`, `z = 1`, `W = H`);
- `kimchiOpeningOrBreak` — the dichotomy: `(Σ' a ρ, openingRelationB σ P b v a ρ) ⊕'
  AlgebraicRelationWitness (augmentedBasis σ.g σ.U σ.h)`, composing
  `deployed_forking_tree` → `deployedToAcceptVWitnessCore` → `ipa_extractV`, de-blinded by
  `ρ := pw`. No extraction reproved; no `hbind`.

`check_extractor_computes.sh` runs the full capstone on an honest depth-0 Schnorr 2-fork over
`ZMod 7` and recovers the witness (`some (4, 1)`). Standard axioms only.

Still open on the way to retiring the axioms:

- ~~the s-vector bridge~~ **DONE**, `Bulletproof/Forking/SVector.lean`: `bPolyCoefficients`
  satisfies `sFun`'s doubling recursion in kimchi's convention (`bPolyCoefficients_succ`), one
  commitment step is one `foldHalves` (`commitGen_bPolyCoefficients_step`, module-generic), and
  `bPoly_eq_innerProduct` / `combinedB_eq_innerProduct` close the wire's `sg`/`b0` forms onto
  the folded leaves;
- ~~Stage 4 wiring~~ **DONE**, `Bulletproof/Forking/Prover.lean`: `KimchiProver` (the
  prefix-determined strategy; the Schnorr layer is one extra challenge round),
  `kimchiProverAccept_forkValid` (Extractable acceptance → valid certificate, mirroring
  ironwood's `proverAccept_forkValid`), faithfulness
  `kimchiProverAccept_iff_verifierAcceptsAt` (acceptance along any branch IS
  `VerifierAcceptsAt` at the assembled proof), and the headline
  `kimchi_opening_or_break_of_extractable`;
- **Stage 5a — the uniform-challenge game. DONE**, `Bulletproof/Forking/Knowledge.lean`:
  `kimchi_knowledge_soundness` — success probability above `kerr |F| (k+1) / |F|^(k+1)` over
  uniform challenge vectors yields opening-or-break, by `extractable_of_prob` into the Stage-4
  chain, with the decidability instance the accepting-set count needs. Self-audited per the
  vacuity discipline: `kimchi_knowledge_soundness_conclusion_free_at_1dim` proves the
  `Prop`-level disjunction is free at a 1-dimensional group (the deployed Pasta case), so the
  theorem's content at deployed parameters lives in the data-valued chain, exactly as the W5
  scope doc's §1.1 predicted for any `Prop` conclusion over this group.

- **D3 (challenge domain) — RESOLVED, `Bulletproof/Forking/EndoChallenge.lean`.** The forking
  game runs over the **prechallenge** domain (`Fintype.card ≤ 2¹²⁸`), not the scalar field, so
  the counting hypothesis is satisfiable (the W5 doc's B3 option (a)). Both facts that transport
  needs are proved per curve: `endoExpand_{vesta,pallas}_injOn` (injective on `[0, 2¹²⁸)`) and
  `endoExpand_{vesta,pallas}_ne_zero` (never zero — so the fork tree's nonzero side conditions
  hold for *every* prechallenge, needing nothing from `Extractable`). A collision or a vanishing
  value is a short GLV relation among the bounded integer accumulators, refuted by the
  certificate-backed `{vesta,pallas}_glv_no_short_relation`. Closure: standard trio, plus
  CompElliptic's point-count `native_decide` axiom via `{vesta,pallas}_card` (allowed).

- **Stage 5b — the computed fork. DONE**, `Bulletproof/Forking/Game.lean` (1877 lines, 0 sorries,
  standard axioms). `kimchiExtract_failure_measure_le`: an algebraic bounded-query adversary that
  convinces the deployed verifier yields an opening witness or a computed DL break, except on
  oracle tables of measure `≤ (Q + k + 1)·3/|Pre|` over the 2¹²⁸ prechallenge domain. No `hbind`,
  no FS axiom. Supporting: `DecodesFromPrefixes` (commit-then-challenge — without it the game is
  false, recorded as the proved `verifierAcceptsAt_of_deferred_delta`), `kimchiExtract` (a plain
  computable `def`), `honest_wins_everywhere` (anti-vacuity companion).

  *Why the escape layer is ours rather than instantiated:* `RecursiveForkReached` needs no
  arithmetic — its body truncates the answer list and looks up a coin-tree node — but carries
  `[Field F]` from its section's `variable` line; ironwood `omit`s those instances on the very
  next theorem and nowhere else in 1425 lines. That part was avoidable upstream. The certificate
  layer *is* genuinely field-coupled (`AlgebraicDForkCert` consumes challenges as `u⁻¹`).
  Everything below the escape layer is imported and called from `Zcash.Snark.*`.

- **Remaining to actually shrink the gate.** The theorem exists; the axioms are not yet retired.
  That needs the abstract game instantiated at the deployed transcript type (`T`, `Pre`, and a
  `PrefixDecode` proved from `Forking/Transcript.lean`'s prefix lengths), then
  `ipa{Vesta,Pallas}_sound` and the four kimchi consumers re-plumbed onto it, then
  `poseidon_fiat_shamir_*` deleted and `roots.txt` updated.

- ~~Stage 5b (was: remaining)~~ The end-to-end content at Pasta needs the
  certificate *computed* from a sponge-driven adversary: ironwood's Route B
  (`Forking/Adversary/{OracleComp,Recursive}.lean` — the bounded-query oracle machine, rewinding
  with explicit coins, `recursiveAlgebraicFork` + failure-measure bounds). Genericity survey:
  `OracleComp` is fully generic in `(T, F)`; `Recursive`'s engine is generic
  (`{T F G P ι}, [Field F]`) with only its `FpValidity` section and halo2 endpoints `Fp`-locked;
  `Adaptive`/`DomainReduction`/`ExpectedRuns(Poly)` are generic. The seam to rebuild against our
  verifier is `algebraicForkCertAttempt_valid`-shaped, targeting `kimchiProverAccept` (already
  pinned to the wire by `kimchiProverAccept_iff_verifierAcceptsAt`) over the transcript domain
  of `Bulletproof/Forking/Transcript.lean`. This is the W5 scope doc's Shape B, with its listed
  costs; per that doc's §7 it is gated on repo-owner decisions (notably D3 challenge domain,
  D4 fixed-claim scope, D7 AGM acceptance, D8 worth-it) before proving begins. Note D1/D2/D6
  and the anti-triviality prerequisite (§3.0) have been resolved by the work above; the root
  representation `(pg, pw)` already in `kimchiOpeningOrBreak` is the AGM-lite piece of D7.
  Only after 5b can `poseidon_fiat_shamir_*` retire with content (in either shape, removing
  two kernel axioms without adding any — ironwood declares no RO axiom and neither does W2).

**Stage 2 — delete the duplicated core.** Remove our `commitGen`, `loHalf`/`hiHalf`/`append`,
`vandermonde3`, `ipa_round_commit_with_coeffs`, `IpaTreeV`/`IpaAcceptV`/`ipa_soundV`,
`CommitmentBinding`/`DLRelation`, and the private bilinearity helpers (including the third copy in
`Forking/Triviality.lean`); re-point every consumer at `Zcash.Snark.*`. Delete `Strategy` /
`stratAccept` / `ipaTreeV_of_extractable` from `Forking/Extraction.lean`.

Expected: a large net deletion, and `Triviality.lean`'s local re-proofs disappear because
ironwood's versions are public.

**Stage 3 — instantiate the AGM stack.** Build our `AlgebraicProver` / `AlgebraicDForkCert` at
`augmentedBasis σ.g σ.U σ.h`, and land the dichotomy by *calling*
`deployedAlgebraicForkingRelation` — not reproving it:

```lean
def ipa_openingOrBreak (σ : SRS G) … :
    (Σ' a, IpaRelation (ursOf σ) P b v a) ⊕' AlgebraicRelationWitness (augmentedBasis σ.g σ.U σ.h)
```

**Stage 4 — retire `hbind` and the two FS axioms.** Replace the `hbind` hypothesis in
`chunked_ipa_soundness` / `chunked_batch_soundness` with the break branch, and re-point
`ipaVesta_sound` / `ipaPallas_sound` at the dichotomy. Update `roots.txt`; the two
`poseidon_fiat_shamir_*` axioms and the `hbind` parameter both go.

## 5. Acceptance gates

- `lake build` clean, 0 `sorry`.
- `#print axioms` on the new capstone: standard three only.
- **The extractor must compute.** A `Σ'` conjured by choice is the vacuous version wearing a
  `Type`, so the data-valued form needs a gate — but *not* the "no `Classical.choice`" one I first
  wrote here. Mathlib's `Field` hierarchy drags `Classical.choice` into everything, including
  ironwood's own `ipa_extractV`, so the axiom list cannot discriminate. The gate that does:
  the extractor is a plain compilable `def` (Lean's compiler rejects it otherwise, forcing
  `noncomputable`) **and it `#eval`s on a fixture**. Demonstrated for `Forking.Convention.ipaExtract`
  over `ZMod 7`: a depth-1 honest transcript extracts back to the original witness `(4, 6)` with
  both opening equations `true`.
- `bulletproof-pcs/scripts/check_axioms.sh` — roots reduce with **no** `poseidon_fiat_shamir_*`.
- `check_ipa_fixture.sh` still passes (guards against a Stage-0 convention error).
- `shake` / deadcode gates green after the Stage-2 deletions.

## 6. Risks

1. **Fold convention (§3.1)** — the only correctness risk. Mitigated by making Stage 0 a hard gate
   and keeping the fixture check in CI.
2. **Ironwood churn** — we pin `83a98f7f`. Deleting our copies makes us dependent on their API;
   acceptable given the pin, but bumps become real work.
3. **`Fp` specialization** — ironwood's IPA core (`InnerProduct`, `IpaSoundness`, `CommitFold`,
   `AGM/Adapter`, `AGM/Prover`) is generic in `F`; only the upper layers (`KnowledgeSoundness`,
   `Main`, `Vesta`) fix `Fp`. Our reuse is confined to the generic layers, so this is fine — but
   `AGM/Capstone` is stated over `Module Fp G`, so Stage 3 must check whether we can instantiate
   it at Pasta directly or need the generic sub-lemmas underneath it.
4. **Scale** — Stage 2 touches every consumer in the package. Mechanical, but wide.
