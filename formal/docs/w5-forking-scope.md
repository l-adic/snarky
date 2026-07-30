# W5 scope — deriving IPA tree extraction (the forking instantiation)

**Status: SCOPING ONLY — no code changes. Contains a finding that changes what W5 should be
(§1.1); read that before costing anything else.**

**W5's goal has SINCE BEEN ACHIEVED.** The two `poseidon_fiat_shamir_{vesta,pallas}` axioms are
retired: `grep -c '^axiom'` over the five packages is 0, and the names survive only in
retrospective prose. `Bulletproof/Forking/Game.lean:1930` records the removal, and the live
endpoints are `ipa{Vesta,Pallas}_knowledge_sound` (`Forking/KnowledgeSoundness.lean:902,920`).
Read this document as the design record for that result.

Child of `ironwood-refoundation-plan.md`
§5/W5. Predecessors: W2 (the kimchi-side oracle model, PR #273), W3 (the guard-escape engine,
PR #275), and — on this branch — the IPA-side oracle model, `4e303379..c5ebc11c`
(`Bulletproof/Forking/Transcript.lean`).

---

## 1. Goal

W5 is the last workstream of the refoundation: retire the *content* of the two declared
Fiat–Shamir axioms `Bulletproof.poseidon_fiat_shamir_{vesta,pallas}`
(`bulletproof-pcs/Bulletproof/Reflection.lean:192,202`) — "an accepted run admits a de-blinded
accepting 3-ary transcript tree" — by instantiating `zcash/ironwood`'s forking machinery
(`Zcash/Snark/Soundness/Forking/{Tree,Probability,KnowledgeError,Extractor}.lean`, plus the
adversary tower under `Forking/Adversary/`) at *our* IPA, rather than assuming it. The input
side is already built and pinned to the deployed protocol: `Bulletproof/Forking/Transcript.lean`
gives the transcript-prefix oracle domain (`IpaTranscriptElt`, `preT`/`preU`/`preC`), the two
sponge oracles (`spongeOBase`/`spongeOScalar`), the three bridge theorems tying them to
`Ipa.transcriptFrom`, the challenge-source abstraction (`structure FiatShamir`, `verifyOracle`),
and the headline `verifyOracle_spongeFS : verifyOracle (spongeFS C) σ inp = Ipa.verify C σ inp`
(`:404`) — a `Bool`-level equality, so a forking argument run against `verifyOracle` over a
random source recovers the deployed verifier as a *theorem*. The intended endpoint was the plan's
`fiat_shamir_tree_whp`: the measure of oracles on which an accepting adversary yields no tree is
bounded by the fork-tree knowledge error plus a DL term, after which the probabilistic line
consumes no FS axiom at all.

### 1.1 The finding that reframes the goal

**The conclusion of those axioms is almost certainly satisfiable at the deployed instantiation by
linear algebra alone, with no cryptography.** Two steps:

1. `FiatShamirTreeB σ P b v A` (`Soundness.lean:124`) is an implication into
   `∃ ρ t, IpaAcceptV σ.g b (P - ρ • σ.h) v t`. Every field of the tree — `L, R, Lv, Rv`, the
   three node challenges, the leaf scalars — is existentially bound and constrained by nothing
   in the wire proof. So from any opening witness `(a, ρ)` the tree can be *synthesised* by
   honest folding (at a node `L := ⟨a_hi, g_lo⟩`, `R := ⟨a_lo, g_hi⟩`, `Lv := ⟨a_hi, b_lo⟩`,
   `Rv := ⟨a_lo, b_hi⟩`, child witness `a_lo + u⁻¹ a_hi` — all independent of `u`, so one node
   serves all three branches, and `1, 2, 3` supply three distinct nonzero challenges). Downstream
   nothing ever inspects the tree: `ipa_soundnessA` (`Soundness.lean:135`) destructures it and
   immediately discards it via `ipaRelation_of_acceptV` (`SingleOpening.lean:376`). Hence
   `FiatShamirTreeB` ⟺ `∃ a ρ, openingRelationB σ P b v a ρ`.
2. At the deployed instantiation `G = SWPoint Vesta.curve` is a **1-dimensional `Fp`-vector
   space**: `Pasta.vestaPointModule` (`pasta/Pasta/Basic.lean:126`) is `AddCommGroup.zmodModule`
   at the prime point count (`Vesta.card_eq`). So `commit σ a ρ = P ∧ ⟨a, b⟩ = v` is two linear
   equations in `2^k + 1` unknowns: pick `i₀` with `b i₀ ≠ 0`, set `a i₀ := v / b i₀` and the
   rest `0`, then solve for `ρ` — possible whenever `σ.h ≠ 0`.

This is the same phenomenon the package already concedes for binding: `Soundness.lean:104-108`
says `hbind` "is information-theoretically false for a real single-curve SRS … so the theorem is
vacuous at real parameters; it is meaningful only as the computational assumption, discharged
elsewhere." The FS axioms sit on the same side of that line, and nobody had noticed.

Consequences, stated plainly:

* **The stated W5 goal is probably reachable in ~50 lines of linear algebra** — and that is
  exactly why achieving it would be worthless. It would delete two entries from
  `bulletproof-pcs/scripts/check_axioms.lean:33` while proving nothing about Fiat–Shamir.
* **No Prop-level `∃`/`∨` conclusion over the deployed Pasta group can carry content.** This
  kills the obvious repair as well: a hypothesis-free disjunction `opening ∨ ValueBaseRelation σ P`
  is *also* trivially true there (take `μ := 1`; every `P - σ.U` lies in the span of `σ.g, σ.h`).
  Content requires the conclusion to be either **AGM-relative** (the extracted witness must be
  the adversary's *own declared* coefficient vector, or we output a relation among the declared
  coefficients — ironwood's `AlgebraicRelationWitness`, `AGM/Adapter.lean:85`) or **data-valued**
  (a named computable extractor returning `Σ'`/`⊕'`, ironwood's `deployed_forking_tree`,
  `Forking/Extractor.lean:179`). Ironwood does both, and neither is an accident.
* **W5 therefore splits into two different projects** with very different costs and payoffs
  (§3.6, §7/D1–D2), and the first deliverable is the anti-triviality lemma itself, because it is
  cheap and it decides which project we are in.

**Uncertainty, stated rather than papered over:** neither step above has been machine-checked.
Step 1 needs an `IpaAcceptV`-completeness lemma, which **does not exist in this repo** (grep for
`complete`/`of_witness` in `Soundness/SingleOpening.lean` and `Soundness.lean` returns nothing);
ironwood has the analogue, `deployedIpaAcceptV_of_witness` (`Deployed/Ipa.lean:104`, generic in
`F`/`G`). Step 2 needs "a nonzero point spans the group over `Fp`", which follows from
`Vesta.card_eq` + cyclicity but which I did not locate as an existing lemma. Both are short.
If either fails, the *reason* it fails is precisely the non-degeneracy content W5 would be
adding — so the lemma is informative in both directions.

---

## 2. Verified inventory

**Provenance note.** The "ours" rows were read off the working tree on branch
`w2-oracle-model` at `c5ebc11c` while writing this document. The "ironwood" rows are as reported
by the machinery survey against the pinned rev `83a98f7fb3bcd8f87ddf0a459dcab96a782d91d8`; I
spot-checked `kerr`, `Extractable`, `extractable_of_kerr_lt` (`Forking/Tree.lean:21,26,171`) and
`kerr_div_card` (`Forking/KnowledgeError.lean:48`) verbatim, and confirmed every cited file
exists at its path. The survey's build/co-import probes (ironwood's Route-A closure builds in
this workspace; `Zcash.Snark.commitGen = Bulletproof.commitGen` by `rfl`; instances resolve at
`IpaVesta.curve.{ScalarField,Point}`) were **not** re-run here.

### 2.1 What ironwood provides

| Declaration | file:line | Shape / note |
|---|---|---|
| `Zcash.Snark.kerr` | `Forking/Tree.lean:21` | `kerr N 0 = 0`, `kerr N (d+1) = 3·N^d + N·kerr N d` |
| `Zcash.Snark.Extractable` | `Forking/Tree.lean:26` | Prop-recursion on `(Fin d → α) → Prop`; ternary, 3 pairwise-distinct **nonzero** challenges per node. Only `[Zero α]` |
| `extractable_of_kerr_lt` | `Forking/Tree.lean:171` | Pure ℕ counting: `kerr (card α) d < #(univ.filter acc) → Extractable acc`. No `Nonempty`, no measure |
| `extractable_of_prob` | `Forking/Probability.lean:354` | Measure wrapper (12 lines) over the above, at `PMF.uniformOfFintype (Fin d → α)` |
| `kerr_div_card` | `Forking/KnowledgeError.lean:48` | `(kerr (card α) d)/card (Fin d → α) = 3·d/card α` |
| `LadderEscape`, `ladderEscapeSet`, `ladderEscapeSet_subset_triple`, `ladderEscapeSet_congr` | `Forking/Tree.lean:40,104,145,113` | The adaptivity-safe route: per-round bad set ⊆ a 3-element set, measurable w.r.t. earlier challenges only |
| `uniformOfFintype_toOuterMeasure_{finset,set}` | `Forking/Probability.lean:30,86` | counting ↔ measure bridges |
| `uniformOfFintype_map_precomp_injective` | `Forking/Probability.lean:70` | RO bridge: reading a uniform table at **distinct** points ⇒ uniform vector |
| `uniformOfFintype_fresh_read_bound` | `Forking/Probability.lean:156` | adaptive version (bad set chosen from unread coordinates) |
| `uniformOfFintype_point_mem_blind_le` | `Forking/Probability.lean:305` | per-query loss for an answer-blind bad set |
| `uniformOfFintype_toOuterMeasure_triple_le` | `Forking/Probability.lean:339` | the `3/N` per-round escape |
| `forking_measure_bound` | `Forking/Probability.lean:454` | classical local `ε² ≤ Pr[fork] + ε/|F|` over a `Ψ × F` split. **Not** on the path to `Extractable` |
| `DForkCert`, `DeployedForkValid`, `produceDeployed` | `Forking/Extractor.lean:110,130,141` | the certificate datatype, its validity predicate, and the bottom-up recovery (computable, `Σ'`-valued) |
| `fold_inj`, `vandermonde3_recover{,_group}` | `Forking/Extractor.lean:43,80,20` | why arity is 3: the fold is a Laurent window `{u⁻¹, 1, u}` |
| `deployed_forking_tree` | `Forking/Extractor.lean:179` | endpoint: accepting tree `⊕'` `NontrivialRelation g U W` |
| `Prover`, `proverAccept`, `proverAccept_forkValid` | `Forking/Extractor.lean:212,217,226` | prefix-determined strategy; `Extractable acc → ∃ cert, DeployedForkValid …` |
| `DForkCert.treeRuns_eq` | `Forking/Extractor.lean:123` | the certificate has exactly `3^d` leaves |
| `deployedIpaAcceptV_of_witness` | `Deployed/Ipa.lean:104` | **tree completeness** — the lemma we lack (§1.1 step 1) |
| `NontrivialRelation` | `Zcash/Common/DiscreteLogRelation.lean:25` | the break, as **data** (`a ≠ 0 ∨ α ≠ 0 ∨ β ≠ 0`, `Σ a i • g i + α•U + β•W = 0`) |
| `flatAccept`, `invProver`, `proverAccept_iff_flatAccept`, `proverAccept_measure_eq_flatAccept` | `Forking/Rewind.lean:241,250,264,280` | the fold-convention reconciliation (`u ↦ u⁻¹`, `L ↔ R`) + its measure transfer. **Specialized to `Fp`** |
| `deployedVerifierEq_iff_flatAccept` | `Forking/Rewind.lean:445` | halo2's verifier-equation ↔ fold bridge — the shape of the thing we must rebuild |
| `OracleComp`, `QueryBound`, `escapesDuringC`, `completing`, `escapesDuringC_measure_le'` | `Forking/Adversary/OracleComp.lean:16,42,140,280,728` | the adversary/query model and the **only** probability primitive (union bound under per-point blindness) |
| `fsWinsFull`, `fsAdvantageFull_zero_slice_le`, `BTranscript`, `PrefixDecode`, `FullDecode` | `Forking/Adversary/Adaptive.lean:30,37,118,15,102` | the FS game; the `z = 0` slice priced at `(Q+1)/|F|`; the finite domain; the decode contract |
| `recursiveAlgebraicFork{,From}`, `_isSome_of_not_escape`, `_realizes`, `recursiveForkFailure_measure_le`, `_runs_le` | `Forking/Adversary/Recursive.lean:562,507,1362,796,1396,665` | the executable rewinding extractor; success, correctness, failure `≤ (Q+k)·3/|F|`, unconditional cost `(2|F|+1)^k` |
| `AlgebraicForkRealizes.deployedForkValid` | `Forking/Adversary/Recursive.lean:1014` | the seam, abstract half |
| `algebraicForkCertAttempt_valid` | `Forking/Adversary/Algebraic.lean:403` | the seam, concrete half (~130 lines; the model for ours) |
| `knowledgeSoundness_under_DL`, `DiscreteLogRelationHardFor`, `ReductionEfficient` | `Forking/Adversary/Algebraic.lean:1464,1456,1407` | the endpoint: `(Q+k)·3/|F| + (Q+1)/|F| + \|basis\|·ε`, DL stated **per family** |
| `AlgebraicPoint`, `AlgebraicRelationWitness` | `AGM/Adapter.lean:55,85` | the AGM interface |
| `ForkSpread`, `..._of_forkSpread` | `Forking/Adversary/ExpectedRuns.lean:583,902` | **do not copy** — see gap C1 |

Ironwood's whole `Forking/` tree contains **zero `axiom` declarations and no `sorry`**; the RO
assumption lives in the statement shape (quantify over a uniform table), exactly as our
`Kimchi/Verifier/Forking/Model.lean` (W2 Option A) already frames it.

### 2.2 What we provide

| Declaration | file:line | Note |
|---|---|---|
| `Bulletproof.poseidon_fiat_shamir_{vesta,pallas}` | `Bulletproof/Reflection.lean:192,202` | the discharge targets; `∀ σ`, `∀ m p`, `∀ inp`, total implication, no ε |
| `FiatShamirTreeB` | `Bulletproof/Soundness.lean:124` | `accepts → ∃ ρ t, IpaAcceptV σ.g b (P - ρ•σ.h) v t` |
| `IpaTreeV`, `IpaAcceptV` | `Soundness/SingleOpening.lean:226,236` | character-for-character ironwood's, except the fold |
| `loHalf`, `hiHalf`, `foldHalves` | `SingleOpening.lean:165,170,184` | **all `private`** — blocks stating any cross-library lemma |
| `ipa_soundnessA` | `Soundness.lean:135` | the only consumer of a tree: modus ponens, destructure, discard |
| `ipaRelation_of_acceptV` | `SingleOpening.lean:376` | tree ⇒ `∃ a, commitGen σ.g a = P ∧ v = ⟨a,b⟩` |
| `openingRelationB` | `Bulletproof/Protocol.lean:244` | `commit σ a ρ = P ∧ v = ⟨a, b⟩` — the real target |
| `batch_soundnessA`, `chunked_batch_soundness` | `Soundness.lean:225,405` | grid consumers; both thread `hbind` separately |
| `ipa{Vesta,Pallas}_sound` | `Reflection.lean:277,310` | headline; one axiom instance per grid node, `(∑ nc) × p` of them |
| `verify_reflects` | `Reflection.lean:158` | the only executable→abstract bridge; a declared root **consumed by nothing**; carries `hsmul` |
| `Ipa.Proof.toOpening` | `Reflection.lean:56` | **`private`** |
| `Ipa.verifyWith` / `verifyFrom` / `verify` | `Bulletproof/Wire.lean:262,283,290` | algebra / derivation / cold start. `σ.U` never read |
| `bPoly`, `bPolyCoefficients`, `combinedB`, `evalVector`, `combinedEvalVector`, `innerProduct` | `Protocol.lean:70,76,225,64,235,59` | **no lemma anywhere relates `bPoly` to `innerProduct (bPolyCoefficients …) (evalVector …)`** (verified by grep) |
| `IpaTranscriptElt`, `stepState`, `preT`, `roundBlock`, `preU`, `preC` | `Forking/Transcript.lean:44,58,70,74,79,83` | domain + prefixes; lengths 2, 3i+5, 3k+4 |
| `spongeOBase`, `spongeOScalar` | `Forking/Transcript.lean:99,103` | hard-code `FqSponge.init` ⇒ **cold start only** |
| `toGroup_spongeOBase_preT`, `spongeOScalar_preU`, `spongeOScalar_preC` | `Forking/Transcript.lean:114,268,318` | the three bridges; axiom-clean |
| `structure FiatShamir`, `transcriptOf`, `verifyOracle`, `spongeFS`, `verifyOracle_spongeFS` | `Forking/Transcript.lean:376,384,392,398,404` | the abstraction point + the `Bool`-level equality |
| `escape_coord`, `escape2`, `escape4` | `kimchi/Kimchi/Verifier/Forking/Escape.lean:34,58,78` | W3's measure engine over `Fin k → F`, reusable verbatim |
| `Pasta.{vesta,pallas}PointModule`, `{vesta,pallas}_smul_val` | `pasta/Pasta/Basic.lean:126,132,139,143` | the module instance (1-dimensional!) and `z • P = z.val • P` by `rfl` |
| `FqSponge.challengeFq`, `squeezeChallenge`, `endoExpand`, `challengeNat` | `poseidon/Poseidon/FqSponge.lean:91,132,120` | scalar challenges are `endoExpand λ` of a **128-bit** prechallenge |

### 2.3 What neither side provides

* An `IpaAcceptV` completeness lemma on our side (ironwood has `deployedIpaAcceptV_of_witness`).
* The `combinedB`/`bPoly`/`sg` ↔ `combinedEvalVector` correspondence — currently *carried by the
  axiom itself* (`Soundness.lean:99-102`: "the equation is never exercised here, since
  `ipa_soundnessA` holds for any `b0`").
* Anything about a Schnorr proof-of-knowledge layer. Our `Ipa.Proof` hides the final scalar and
  the blinder behind `z1, z2` (`Wire.lean:116`); halo2 sends `ipaC`, `ipaF` in the clear, so
  ironwood's leaf just reads them off. This is a whole extra extraction level with arity 2.
* Anything about a map-to-curve `U` base. Ironwood's `params.u` is a fixed URS generator; ours is
  `C.toGroup (squeezeBase (preT inp))` (SvdW), and `preT` is adversary-controlled.

---

## 3. Proposed statements

Layered, cheapest first. Every hypothesis is justified inline. Names are proposals.

### 3.0 The anti-triviality companion (write this FIRST — it decides W5)

```lean
/-- Tree completeness: an opening witness synthesises an accepting tree by honest folding. -/
theorem ipaAcceptV_of_opening (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (a : Fin (2 ^ σ.k) → F)
    (hF : 3 < Fintype.card F) :
    ∃ t : IpaTreeV F G σ.k, IpaAcceptV σ.g b (commitGen σ.g a) (innerProduct a b) t

/-- Therefore the tree is not content: `FiatShamirTreeB` is exactly the opening relation. -/
theorem fiatShamirTreeB_iff_opening (σ : SRS G) (P : G) (b) (v) {A : Prop}
    (hF : 3 < Fintype.card F) :
    FiatShamirTreeB σ P b v A ↔ (A → ∃ a ρ, openingRelationB σ P b v a ρ)

/-- And over a one-dimensional module the opening relation is unconditional. -/
theorem exists_openingB_of_cyclic (σ : SRS G) (P : G) (b) (v)
    (hspan : ∀ X Y : G, Y ≠ 0 → ∃ c : F, X = c • Y)   -- G is 1-dimensional
    (hh : σ.h ≠ 0) (hb : b ≠ 0) :
    ∃ a ρ, openingRelationB σ P b v a ρ

/-- **The two declared axioms are dischargeable without cryptography.** -/
theorem poseidon_fiat_shamir_vesta' (σ : SRS IpaVesta.Point) (hh : σ.h ≠ 0) {m p : ℕ}
    (inp : IpaVesta.Input σ.k m p) (hb : combinedEvalVector (2 ^ σ.k) inp.evalscale
      inp.pointFn ≠ 0) :
    FiatShamirTreeB σ (combinedCommitment inp.polyscale inp.commitmentFn)
      (combinedEvalVector (2 ^ σ.k) inp.evalscale inp.pointFn) (cipOf inp)
      (Ipa.verify IpaVesta.curve σ inp = true)
```

*Hypotheses.* `hF` gives three distinct nonzero challenges (`1, 2, 3` at char ≠ 2, 3 — Pasta
qualifies); it is what `IpaAcceptV`'s node side conditions demand. `hspan` is the
1-dimensionality of `SWPoint Vesta.curve` over `Fp`, from `Pasta.vestaPointModule` +
`Vesta.card_eq`. `hh`, `hb` are the only non-degeneracies the linear solve needs.

This is not a deliverable of W5 so much as its *precondition*: it must be a declared root, with a
docstring that says what it means, so that no future reader mistakes tree existence for content.
Template for `ipaAcceptV_of_opening`: ironwood's `deployedIpaAcceptV_of_witness`
(`Deployed/Ipa.lean:104`).

### 3.1 The `b0` correspondence (owed regardless of which W5 we do)

```lean
theorem bPoly_eq_innerProduct {k : ℕ} (chal : Fin k → F) (x : F) :
    bPoly chal x = innerProduct (bPolyCoefficients chal) (evalVector (2 ^ k) x)

theorem combinedB_eq_innerProduct {k m : ℕ} (chal : Fin k → F) (r : F) (x : Fin m → F) :
    combinedB chal r x = innerProduct (bPolyCoefficients chal) (combinedEvalVector (2 ^ k) r x)
```

*Justification.* The verifier checks a **scalar** slot `b0 := combinedB chal evalscale pointFn`
(`Wire.lean:265`) and pins `sg` to `commitGen σ.g (bPolyCoefficients chal)` (`:275`); the tree and
every consumer speak about `combinedEvalVector`. The axiom silently carries the bridge. Without
these two lemmas any W5 result is a correct theorem about a `b` the verifier never checked — the
axiom would *move*, not retire. Risk: the index convention (`bPolyCoefficients` uses `Fin.rev`
and `Nat.testBit`; the fold is a top-bit split) — spot-checked consistent at `k = 1`, unverified
beyond that. No group-side analogue is needed: `commitGen σ.g (bPolyCoefficients u)` *is* the
fully folded generator, and the deployed `sgOk` check pins `sg` to it.

### 3.2 Challenge-parametric acceptance (the composition point with what landed)

```lean
def Ipa.Forking.AcceptsAt (σ : SRS C.Point) (inp : Ipa.Input C σ.k m p)
    (t : C.BaseField) (u : Fin σ.k → C.ScalarField) (c : C.ScalarField) : Prop :=
  Ipa.verifyWith C σ (C.toGroup t) (Vector.ofFn u) c inp = true

theorem acceptsAt_spongeFS (σ : SRS C.Point) (inp : Ipa.Input C σ.k m p) :
    AcceptsAt σ inp (spongeOBase (preT inp)) (fun i => spongeOScalar (preU inp i))
      (spongeOScalar (preC inp)) ↔ Ipa.verify C σ inp = true
```

*Justification.* Immediate from `verifyOracle_spongeFS` (`Transcript.lean:404`) + `transcriptOf`
(`:384`). This is the **only** place W5 touches what landed, and it is why the landed work is not
wasted whichever shape §3.6 takes.

### 3.3 The verifier→fold bridge (the largest single item)

```lean
theorem verifyWith_reflects (hsmul : ∀ (z : C.ScalarField) (P : C.Point), z • P = z.val • P)
    (σ : SRS C.Point) (uBase : C.Point) (chals : Vector C.ScalarField σ.k)
    (c : C.ScalarField) (inp : Ipa.Input C σ.k m p)
    (hv : Ipa.verifyWith C σ uBase chals c inp = true) :
    BatchAccepts { σ with U := uBase } inp.proof.toOpening inp.polyscale inp.evalscale c
      (fun i => chals[i]) inp.commitmentFn inp.pointFn inp.evalFn
```

*Justification.* `verify_reflects` (`Reflection.lean:158`) is exactly this at the deployed
transcript; generalising it off `transcript C inp` de-orphans a declared root (it currently has
zero consumers) and gives the forking layer a `Prop`-level accept predicate. `hsmul` is already
its hypothesis and is `rfl` at both curves (`Pasta.{vesta,pallas}_smul_val`). Two boundaries are
crossed here and nowhere else: `Array.foldl` (`verifyWith`'s `Q`) → `Finset.sum`, and
`ZMod.val • P` (ℕ-smul) → `Module` smul. This is our analogue of ironwood's
`deployedVerifierEq_iff_flatAccept` (`Rewind.lean:445`), and ironwood gives no help with it.

### 3.4 The two forks (independent; this is the structural design win)

```lean
/-- Schnorr fork: two accepting runs at the same round challenges, sharing (lr, delta, sg),
    with distinct final challenges, open the folded commitment. -/
theorem pathOpens_of_two_challenges (σ) (uBase) (u : Fin σ.k → F) (inp₁ inp₂)
    (hshare : inp₁.proof.lr = inp₂.proof.lr ∧ inp₁.proof.delta = inp₂.proof.delta
      ∧ inp₁.proof.sg = inp₂.proof.sg)
    (hc : c₁ ≠ c₂) (h₁ : AcceptsAt σ inp₁ t u c₁) (h₂ : AcceptsAt σ inp₂ t u c₂) :
    PathOpens σ uBase u inp₁          -- ∃ a₀ ρ, Q = a₀ • sg + (a₀ * b0) • uBase + ρ • σ.h

/-- Round fork: a ternary tree of paths, each opening, yields the claim opening. -/
theorem opening_of_extractable (σ) (uBase) (S : Strategy F G σ.k)
    (hext : Zcash.Snark.Extractable (fun χ => PathOpens σ uBase χ (S.pf χ))) :
    (∃ a ρ, openingRelationB σ P b v a ρ) ∨ ValueBaseRelation F σ P uBase
```

*Hypotheses.* `hshare` is forced by our own transcript, not assumed: `preU inp j` already contains
`L₀…L_j, R₀…R_j`, so two runs drawing the same `u_j` agree on those points — our analogue of
ironwood's trunk-rejection gate `prefixes p' j = t`, derivable rather than postulated. `hc` is a
2-transcript special-soundness hypothesis, discharged in the model by the escape layer. The
Schnorr fork needs **no other hypothesis**: `sg = commitGen σ.g (bPolyCoefficients u)` comes free
from the run's own `sgOk` conjunct, and `b0` stays abstract. The round fork needs **no AGM /
representation hypothesis on `L, R`**: carry the invariant
`Q_j = commitGen g_j a_j + ⟨a_j, b_j⟩ • U + ρ_j • σ.h` (value riding on `U`, ironwood-style), and
the Vandermonde combination `Σlᵢuᵢ⁻¹ = 0, Σlᵢ = 1, Σlᵢuᵢ = 0` annihilates `L` and `R` outright.
The value slot is separated from the commitment slot exactly once, at the root — which is where
`ValueBaseRelation σ P U := ∃ a ρ μ, μ ≠ 0 ∧ P = commitGen σ.g a + ρ•σ.h + μ•U` comes from. Note
per §1.1 that this disjunction is **not by itself content-bearing** at Pasta; it is the correct
*shape* (it makes the cost visible at every call site and absorbs degenerate SRS), and it becomes
content-bearing only under §3.6/Shape B.

### 3.5 The escape/measure layer

Reuse W3 verbatim: `escape_coord`/`escape2`/`escape4`
(`kimchi/Kimchi/Verifier/Forking/Escape.lean:34,58,78`) already bound sequential
challenge-vector escapes over `PMF.uniformOfFintype (Fin k → F)`; the per-round bad sets here are
`{0}` ∪ collisions, matching ironwood's `ladderEscapeSet_subset_triple` (`Tree.lean:145`) and
`uniformOfFintype_toOuterMeasure_triple_le` (`Probability.lean:339`). Note W3's deliberate
restaging (measure over challenge *vectors*, not over tables) applies here for the same reason:
`T = List (IpaTranscriptElt C)` is infinite, so `uniformOfFintype (T → F)` does not exist.

### 3.6 The two candidate headlines

**Shape A — generic, Prop-level, ironwood Route A.**

```lean
theorem ipa_opening_whp {F G} [Field F] [AddCommGroup G] [Module F G]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F) (v : F) (U : G)
    (S : Strategy F G σ.k)
    (hprob : (Zcash.Snark.kerr (Fintype.card F) σ.k : ℝ≥0∞) / Fintype.card (Fin σ.k → F)
        < (PMF.uniformOfFintype (Fin σ.k → F)).toOuterMeasure
            {χ | AcceptsAtStrategy σ P b v U S χ}) :
    (∃ a ρ, openingRelationB σ P b v a ρ) ∨ ValueBaseRelation F σ P U
```

Consumes `extractable_of_prob` (`Probability.lean:354`) with the threshold rewritten by
`kerr_div_card` (`KnowledgeError.lean:48`) to `3·σ.k/|F|`; optionally `forking_measure_bound`
(`Probability.lean:454`) to convert accept probability into two-distinct-Schnorr-challenge
probability, giving roughly `ε > √(3(σ.k+1)/|F|)`. Consumes **nothing** from `Extractor`,
`Rewind`, `Ordering`, `Adversary/*`, `ExpectedRuns`, `Provenance`. `Strategy` is a record — `pf :
(Fin σ.k → F) → F → OpeningProof F G σ.k` plus `rounds_prefix`/`final_prefix` chronology fields —
replacing ironwood's `Prover` inductive with two hypotheses.

*Honest assessment.* This is a real theorem about arbitrary `F`-modules and it is **not** vacuous
as a general statement. But by §1.1 its Pasta instance says nothing a linear-algebra lemma does
not already say, and its conclusion is unconditionally true there — so the `hprob` hypothesis is
doing no work at the instantiation. Its value is narrow and should be advertised as exactly that:
*two declared assumptions become theorems of a generic algebraic statement, so the audit gate
shrinks and the remaining trust concentrates in the RO-model boundary and `hbind`, exactly where
`Soundness.lean:104-108` already says it lives.*

**Shape B — AGM / data-valued, ironwood Route B.**

```lean
def ipaFork (basis : ι → G) (k : ℕ) (A : OracleComp T F Pf) … :
    (T → F) → RecursiveForkCoins F k → RecursiveForkAttempt (AlgebraicDForkCert basis k)

theorem ipaFork_failure_measure_le [Fintype T] [Fintype F] [Nonempty F]
    (D : PrefixDecode T k prefixes) (coins) (hcomplete : coins.Complete)
    {Q} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure (ipaForkFailureSet …)
      ≤ (Q + k) * (3 / Fintype.card F)

theorem ipaFork_valid (hout : (ipaFork … O coins).output = some cert) :
    DeployedForkValid urs.g b urs.u urs.h z Pwhole cert.toDForkCert
```

Instantiates `recursiveAlgebraicFork` (`Recursive.lean:562`) + `_isSome_of_not_escape` (`:1362`)
+ `_realizes` (`:796`) + `recursiveForkFailure_measure_le` (`:1396`), with the seam
(`algebraicForkCertAttempt_valid`, `Algebraic.lean:403`) rebuilt against our verifier. This is
the shape that carries content at Pasta, because the extracted opening is tied to the adversary's
own declared representation and the failure branch is `AlgebraicRelationWitness` **as data**.
It also costs: an `AlgebraicWfProof` analogue for `Ipa.Proof`, a finite bounded transcript type,
a `FullDecode` instance, a claim-stability invariant, and a model change for the whole package
from DL-binding to AGM.

---

## 4. Gap table

### Blockers

| # | Gap | Resolution |
|---|---|---|
| B1 | **The conclusion is trivial at the deployed instantiation** (§1.1). Any Prop-level `∃`/`∨` over `SWPoint Vesta.curve` is satisfiable by linear algebra; "discharging the axioms as stated" removes two gate entries and proves nothing. | Write §3.0 first. Then choose Shape A (accept a narrow, honestly-advertised win) or Shape B (content, at Route-B cost). Land §3.0 as a **declared root** either way. |
| B2 | **The axiom's shape has no ironwood counterpart.** `∀ σ` (incl. degenerate), `∀ m p` (incl. 0), `∀ inp`, total implication, no ε, no relation branch. A fixed accepting `inp` is a constant strategy — rewinding it yields no second transcript. | Plan the replacement + consumer re-plumb up front: `fs_tree_chunked` (`Reflection.lean:226`), `ipa{Vesta,Pallas}_sound` (`:277,:310`), `KimchiBatchAcc.nodeFS` (`kimchi/…/Capstone/Standard.lean:115`), `kimchi{Vesta,Pallas}_{sound,run_sound}` (`:166,:214,:275,:355`), `bulletproof-pcs/roots.txt:27-28`, `bulletproof-pcs/scripts/check_axioms.lean:33`, `kimchi/scripts/check_axioms.lean:76`. Per `feedback_formal_no_api_stability` restating is allowed; the manifests must move in the same change. |
| B3 | **Challenge domain.** `squeezeChallenge = endoExpand λ` of a 128-bit prechallenge (`FqSponge.lean:120,132`) ⇒ range ≤ 2¹²⁸, not \|ScalarField\| ≈ 2²⁵⁴. Instantiating ironwood's `α := ScalarField` makes the counting hypothesis **arithmetically unsatisfiable**: `kerr \|F\| d = 3d·2^{254(d−1)}` while the accepting set is supported on ≤ `(2^128)^d` vectors — impossible already at `d = 2`. | Either (a) instantiate `α` at the prechallenge type (`Fintype.card α ≤ 2¹²⁸`, floor `3k/2¹²⁸`), which additionally needs `endoExpand` injectivity on 128-bit inputs (plausible from the GLV short-basis bounds in `Pasta/Endo.lean`) to transport distinctness/nonzero-ness; or (b) carry W2's D2 idealization explicitly and state the caveat in the same paragraph as the ε. Do **not** copy `Deployed/ConcreteBounds.lean`'s numbers. |
| B4 | **We have a Schnorr PoK layer ironwood does not model.** `Ipa.Proof = {lr, delta, z1, z2, sg}` (`Wire.lean:116`) never sends the folded scalar or the blinder; halo2 sends `ipaC`, `ipaF` in the clear. `Extractable`/`DForkCert`/`produceDeployed` are uniform-arity-3, uniform-depth; a Schnorr level is arity 2. | Do **not** bend `Extractable`. Prove §3.4's standalone 2-transcript lemma against `verifyWith`'s equation at the `preC` prefix, price the second fork as an extra escape term, and feed its output as leaf data. |
| B5 | **The cold transcript does not absorb the claim.** `preT inp = [frScalar (shiftScalar (cipOf inp)), sqBase]` (`Transcript.lean:66,70`) — commitments, eval points, `polyscale`, `evalscale` enter no prefix, though all enter the acceptance equation. So there is no analogue of ironwood's `preIpaTranscript_inj` (`PreIpa.lean:546`): a rewound adversary may return a *different claim*, and the fork tree's leaves need not share a root. | Pick one and write it in the module preamble in reviewer language: (a) fixed-claim / non-adaptive model with an explicit `ClaimStable` hypothesis shown satisfiable for constant-claim adversaries; (b) note that kimchi's real usage is the **warm** start where commitments are already absorbed, so the gap is an artifact of the standalone cold verifier — but that start is out of scope (see C4). Escalate; do not pick silently. |
| B6 | **The `b0`/`sg` ↔ `combinedEvalVector` correspondence is unproved** (verified by grep) and is currently carried inside the axiom. | §3.1, as a prerequisite deliverable. |
| B7 | **The verifier→fold bridge does not exist.** Crossing `Array.foldl` → `Finset.sum` and `ZMod.val •` → `Module` smul; our analogue of the deferred 45-row↔`batchC` reconciliation. | §3.3, replacing rather than duplicating `verify_reflects`. Budget as the largest single item. |

### Moderate

| # | Gap | Resolution |
|---|---|---|
| M1 | `loHalf`, `hiHalf`, `foldHalves` (`SingleOpening.lean:165,170,184`) and `Ipa.Proof.toOpening` (`Reflection.lean:56`) are `private`; any cross-library or completeness lemma is unstatable from outside. | Un-private (visibility only) — same norm as W2's `frSpec` and W3's three `Capstone/Algebraic.lean` lemmas. |
| M2 | No `IpaAcceptV` completeness lemma. | Port `deployedIpaAcceptV_of_witness` (`Deployed/Ipa.lean:104`). Needs M1. |
| M3 | Two oracles with different codomains (`squeezeBase : … → BaseField`, `squeezeScalar : … → ScalarField`) vs ironwood's single `squeeze`. A product codomain is unsound (`u ≠ 0`, `u⁻¹` are meaningless on a pair). | Fix `F := ScalarField`; hold the base read in a second, never-reprogrammed table and reduce with `uniformOfFintype_prod_fiber_bound` (already used in `Escape.lean`). Document the extra idealization: the deployed sponge derives both from one state, so two independent tables is *stronger* than ironwood's assumption. |
| M4 | `T = List (IpaTranscriptElt C)` is infinite; `DecidableEq (IpaTranscriptElt C)` is not derived. | `deriving DecidableEq`; a length-bounded subtype at `L = 3k+4` mirroring `BTranscript` (`Adaptive.lean:118`), only if Shape B. Shape A needs neither (W3's restaging). |
| M5 | No prefix distinctness / chronology / `PrefixDecode`. Only `roundBlock_succ` exists, and it is `private` (`Transcript.lean:258`). | Prove `|preT| = 2`, `|preU i| = 3i+5`, `|preC| = 3k+4`, pairwise distinctness (by length alone — holds even if the adversary repeats `(L,R)`), and the chain `preT <+: preU 0 <+: … <+: preC`. Our trunk is *constant* length, so this is strictly easier than ironwood's `PsWellFormed`/`preIpaLen` route. |
| M6 | The headline consumers need a **grid** — `(∑ nc) × p` independent instances (`ipa{Vesta,Pallas}_sound`), and `kimchiProof_sound` needs two full grids. Different `(ξ, r)` ⇒ different `cipOf` ⇒ disjoint prefixes ⇒ separate events. | Plan the union bound explicitly; state the grid-scaled error. Good for independence, but the blindness argument reruns per row. |
| M7 | `bulletproof-pcs/lakefile.toml` does not require `Zcash` (only `kimchi` does). | Add `[[require]] name = "Zcash"` at the same pinned rev `83a98f7f`; `lake update Zcash`; verify the workspace manifest is unchanged; run `formal/scripts/prune-stale-oleans.sh`. Alternative (rejected): host in `kimchi/`, which inverts the dependency direction since the object under study is `Bulletproof.Ipa`. |
| M8 | `Bulletproof/Forking/Transcript.lean` is an **orphan**: built via the lib glob, imported by nothing, in no `roots.txt`, no consumers — invisible to the dead-code pass and the axiom gate. | Add `verifyOracle_spongeFS` + the three bridges to `bulletproof-pcs/roots.txt` and the gate's `roots`. |
| M9 | `Rewind.lean`'s convention lemmas (`invProver`, `proverAccept_iff_flatAccept`, `proverAccept_measure_eq_flatAccept`) are stated at `Fp = ZMod PALLAS_BASE_CARD` — *our Vesta scalar field*, so they apply to the Vesta instance and **not** to Pallas. | Re-prove locally at `{F} [Field F] [Fintype F] [DecidableEq F]` (short), or upstream. Do not silently ship only the Vesta half. |
| M10 | Module-instance diamond: ironwood's `vestaFpModule` (`Soundness/Vesta.lean:60`) vs our `Pasta.vestaPointModule`. Verified **absent** on the Route-A closure (`Core/Field` is only imported by `Deployed/ConcreteBounds`). | Shape A: keep it out of the closure; add a `#synth` regression. Shape B: prove a defeq/rewrite bridge once. |
| M11 | Shape B's entry points (`AlgebraicWfProof.ofStandard`/`ofRepresented`) are `native_decide`-tainted; our gate's `isTrustedNativeDecide` prefix-matches only `CompElliptic.` (`check_axioms.lean:38-41`) and would **reject** them. | Only relevant under Shape B: either widen the allowlist deliberately (a trust decision) or build our own representation constructors. |
| M12 | `U = C.toGroup (squeezeBase (preT inp))` — SvdW, neither surjective nor regular, and `preT` depends only on `cipOf inp`, which the adversary fully controls (it can grind `U`). Ironwood's `params.u` is a fixed generator; it models no map-to-curve. | State as a named modelling assumption alongside Poseidon-as-RO, in `Model.lean`'s wording. Do not attempt to prove it from `toGroup`. If a DL story mentions `U`, charge the `preT` read against the query budget. |

### Cosmetic

| # | Gap | Resolution |
|---|---|---|
| C1 | **Do not copy `ForkSpread`** (`ExpectedRuns.lean:583`): quantified over *all* tables, so it asserts ≥ σ₀ good continuations even on tables where the adversary loses, where the good set is empty ⇒ false for any adversary with success probability < 1. Exactly our audit's C1 shape. | Skip `ExpectedRuns`/`ExpectedRunsPoly` entirely; nothing outside `Zcash/TrustBoundary.lean` consumes them, and the unconditional cost bound already lives at `Recursive.lean:665`. |
| C2 | Extractor cost is `3^k` leaves (`treeRuns_eq`, `Extractor.lean:123`) — ≈1.4×10⁷ at `σ.k = 15` — and the only unconditional adversary-call bound is `(2\|F\|+1)^k`. | State it in the docstring. Under Shape A nothing is executed and the tree is discarded, so it is a non-issue *provided* we never say "efficient extractor". |
| C3 | Ironwood's `33/\|Fp\| ≈ 2⁻²⁴⁹` is Orchard's number at `k = 11` over the full field. | Never quote it; see B3. |
| C4 | **Scope.** These axioms are anchored on the **cold** `Ipa.verify`; the kimchi terminal roots (`kimchi{Vesta,Pallas}_run_sound_algebraic_ft`, `ft_opening_of_reflected_*`) rest on the disjoint **warm** pair `Kimchi.Verifier.kimchi_fiat_shamir_{vesta,pallas}` (`Capstone/Reflection.lean:56,73`). | Say so up front in the module preamble, `roots.txt` prose, and any PR text: W5 improves `ipa{Vesta,Pallas}_sound` and `kimchi{Vesta,Pallas}_{sound,run_sound}` **only**. The terminal trust surface is unchanged. |

---

## 5. Vacuity guards that must appear in the statement

Each row is a property of the *statement*, checkable by reading it, with the failure mode it
prevents. These are the acceptance criteria for §6(a).

| # | Guard | Prevents |
|---|---|---|
| V1 | The anti-triviality lemma (§3.0) is landed **as a declared root** with a docstring saying what it means, before or with the headline. | The whole workstream being read as cryptographic content when §1.1 says it is not. |
| V2 | The conclusion is either AGM-relative (witness = the adversary's declared coefficients) or data-valued (`Σ'`/`⊕'` from a named `def`) — or the statement is advertised as generic-only, with §1.1 cited. | The B1 collapse: a Prop-level `∃`/`∨` over a cyclic group is unconditionally true. |
| V3 | **No `hbind`** anywhere in the forking statement. | Re-importing a hypothesis the package already documents as IT-false (`Soundness.lean:104-108`) while looking stronger than the axiom replaced. |
| V4 | The accept event ranges over a **strategy/adversary** whose round points are functions of earlier challenges (`Strategy` with `rounds_prefix`/`final_prefix`, or `OracleComp`), never over a fixed `Ipa.Proof`. Ship a satisfiability witness (the honest prover accepts with probability 1). | An accept-probability hypothesis at a fixed `inp` is measure ≈ `\|F\|^{-k}` and never exceeds `3k/\|F\|` — an unsatisfiable hypothesis that reads like the real forking lemma. |
| V5 | Bad/escape sets are **named `def`s of prover data**, with cardinality bounds stated for the named def; the `∃` never sits inside a per-run implication. | The literal audit-C1 shape (`statement-audit-report.md:76`): `∃ bad, χ ∉ bad → …` is dischargeable by `bad := {the run's own challenge}`. |
| V6 | If the claim is Fiat–Shamir (rather than interactive), the query count `Q` appears in the statement **and in the bound** — e.g. `(Q + k)·(3/N)`. | Pricing no grinding: a bound of `3k/N` with no `Q` is the honest-verifier interactive statement, not an FS statement. |
| V7 | The bound's `N` is the **true challenge-set cardinality** (see B3), or the idealization is a single named modelling definition cited from the docstring. | Overstating security by ~2¹²⁶ and stating distinctness/nonzero-ness about the wrong set. |
| V8 | Every hypothesis ships a satisfiability lemma at landing (honest prover accepts; the recorded fixture in `bulletproof-pcs/scripts/check_ipa_fixture.sh` inhabits the accept event; constant-claim adversaries satisfy `ClaimStable`; every deployed prefix inhabits the bounded transcript type). | The repo's known failure mode (C1 shipped; M3 flagged): a hypothesis that type-checks, reads like the literature, and is false. |
| V9 | No `[Fintype (List (IpaTranscriptElt C))]` (or any instance hypothesis on an infinite type). | An unsatisfiable instance hypothesis makes everything below it vacuous while type-checking. |
| V10 | If the union bound is used, a **blindness lemma** is stated and consumed (the escape set is a function of the query point and the table off that point — ironwood `recursiveForkEscapeSet_blind`, `Recursive.lean:1133` feeding `escapesDuringC_measure_le'`, `OracleComp.lean:728`). | A bad set chosen after seeing what it must exclude: a circular bound. |
| V11 | The root triple is literally `combinedCommitment inp.polyscale inp.commitmentFn`, `combinedEvalVector … inp.evalscale inp.pointFn`, `cipOf inp`, reached through §3.3's bridge — not restated with fresh variables. | A correct theorem about a claim the deployed verifier never checked. |
| V12 | Fold-convention reconciliation is explicit (ours: `foldHalves g u = lo + u • hi`, node `P + u⁻¹•L + u•R`; ironwood's `foldGens g u = lo + u⁻¹ • hi`), with the measure-transfer lemma if a measure crosses it — plus a fixture cross-check that the accepted IPA fixture satisfies the flat predicate. | A fully-proved theorem about a protocol we do not run. |
| V13 | Claim stability (B5) is an explicit, named hypothesis, shown satisfiable, with the scope note in the preamble. | Silently assuming trunk-determinacy — the easiest place in this workstream to hide an unstated hypothesis. |
| V14 | Prefix injectivity/distinctness is **proved** (M5), never taken as `hφ : Function.Injective φ`. | Assuming the transcript-encoding half of the RO assumption. |

---

## 6. Work breakdown

### (a) Statement is the risk — a human writes and validates it

These are small in lines and large in consequence. None should be handed to an autonomous prover,
because a wrong statement here is provable.

| # | Item | Why it is statement-risk |
|---|---|---|
| a1 | **§3.0 anti-triviality** — `ipaAcceptV_of_opening`, `fiatShamirTreeB_iff_opening`, `exists_openingB_of_cyclic`, and the corollary that the axioms are dischargeable. | This *is* the decision (D1/D8). Also: whether it goes through, and what blocks it if not, is the only real information we have about where content lives. |
| a2 | **The replacement headline** (Shape A vs B, §3.6) and the consumer re-plumb design across the six sites in B2. | B1/B2/V2. Every consumer takes `FiatShamirTreeB` positionally; the ε and the disjunction must thread. |
| a3 | **Challenge-domain decision** (B3) and, if (a), the `endoExpand`-injectivity statement. | Decides satisfiability, not just tightness. Getting it wrong yields an unsatisfiable hypothesis. |
| a4 | **Claim-stability / adaptivity scope note** (B5, V13). | A genuine soundness gap in the standalone cold verifier; the wording is the deliverable. |
| a5 | **`Strategy` (or the `OracleComp` instantiation) + the accept predicate** — the exact shape `Extractable`'s `acc` takes. | V4/V5. Ironwood spends `Prover`/`proverAccept`/`flatAccept`/`invProver` on precisely this and still needs a measure-transfer lemma. |
| a6 | If Shape B: the **seam** (`stable`, `stable_update`, `hdecode`, the common-`Pwhole` calculation), modelled on `algebraicForkCertAttempt_valid` (`Algebraic.lean:403`). | This is where ironwood's hardest 130 lines are, and it is where B5 bites. |
| a7 | Trust-surface prose: `Model.lean`-style preamble (W2 Option A wording), `roots.txt` entries, gate updates, C4 scope note. | The advertised-vs-delivered gap is the standing risk on this workstream. |

### (b) Statement settled, proving is heavy — Archon-able, with source material

Hand these to `archon-lean-prover` **only after** the corresponding statement in (a) is landed
with a `sorry`. Named templates matter: every one of these has a worked analogue.

| # | Obligation | Source material / template |
|---|---|---|
| b1 | `bPoly_eq_innerProduct`, `combinedB_eq_innerProduct` (§3.1) | Defs at `Protocol.lean:70,76,225,64,235`; the standard "product over `(1 + u x^{2^j})` = sum over bit-masks" argument; the `Fin.rev`/`Nat.testBit` convention is the only subtlety. Pure algebra, no dependencies. |
| b2 | Prefix length / distinctness / chronology lemmas (M5) | `Transcript.lean:66-83`; template: ironwood `Ordering.lean` `roundTranscriptFin_length`/`_injective`/`_prefix`/`_take` (`:177,188,247,263`). List arithmetic. |
| b3 | `ipaAcceptV_of_opening` (§3.0, once stated) | Template: `deployedIpaAcceptV_of_witness` (`Deployed/Ipa.lean:104`), generic in `F`/`G`. Needs M1 (un-private). |
| b4 | `IpaAcceptV` ↔ `Zcash.Snark.IpaAcceptV` relabeling (only if we import their extractor) | Template: `invProver` / `proverAccept_iff_flatAccept` (`Rewind.lean:250,264`); closes with `inv_inv` + `abel` per node. The two inductives are otherwise character-identical. |
| b5 | `verifyWith_reflects` (§3.3) | Generalize the existing `verify_reflects` proof body (`Reflection.lean:158-179`) off `transcript C inp`; `hsmul` discharged by `Pasta.{vesta,pallas}_smul_val`. Mechanical but long. |
| b6 | `pathOpens_of_two_challenges` (§3.4 Schnorr fork) | The algebra was worked by hand during scoping and needs no hypothesis beyond `c₁ ≠ c₂` and the three sharing equations: `a₀ = (z1₁−z1₂)/(c₁−c₂)`, `ρ = (z2₁−z2₂)/(c₁−c₂)`; `sg` correctness comes from the run's own `sgOk`. |
| b7 | `opening_of_extractable` (§3.4 round fork) — **the one genuinely hard proof** | Our own `ipa_soundV` (`SingleOpening.lean:253`) is the same recursion shape; ironwood's `produceDeployed` / `fold_inj` / `vandermonde3_recover{,_group}` (`Extractor.lean:141,43,80,20`) is the template for carrying the invariant and identifying the recovered root. |
| b8 | The measure wrappers (§3.5) | Reuse `escape_coord`/`escape2`/`escape4` (`kimchi/…/Forking/Escape.lean:34,58,78`); ironwood's `extractable_of_prob` (`Probability.lean:354`) + `kerr_div_card` (`KnowledgeError.lean:48`) for the threshold rewrite. |
| b9 | `acceptsAt_spongeFS` (§3.2) | One rewrite through `verifyOracle_spongeFS` (`Transcript.lean:404`). Trivial; include for completeness. |

**Suggested order, stopping to re-cost after each of the first two.** (1) a1+b3 — the
anti-triviality lemma, because it is cheap and decides everything. (2) b1+b2 (+M1, M8) — owed
regardless of the outcome, and they retire real assumed content. (3) a2/a3/a4 decisions. (4)
b5/b6, then b7, then b8/b9.

---

## 7. Decision points (repo owner sign-off before proving begins)

| # | Question | Recommendation |
|---|---|---|
| **D1** | Given §1.1, is the goal of W5 **"delete two declared axioms"** or **"gain cryptographic content at the deployed instantiation"**? These are different projects. | Answer *after* a1/b3 lands (days, not weeks). If the trivializing lemma goes through, "delete two axioms" is a ~50-line job and the interesting question becomes whether Shape B is worth its cost. |
| **D2** | Shape A (generic, Prop, ironwood Route A: `Tree` + `Probability` + `KnowledgeError` + the Vandermonde pattern) or Shape B (AGM, data-valued, Route B: `OracleComp` + `Recursive` + `Adversary/*`)? | If D1 = "delete axioms": Shape A, advertised narrowly per §3.6. If D1 = "content": Shape B, and accept M11 + a model change for the package. Do not drift into B by accident — pick before a5. |
| **D3** | Challenge domain: idealize to \|F\| (W2's D2 caveat, ironwood-identical) or instantiate at the true ~2¹²⁸ set (needs `endoExpand` injectivity)? | Instantiate at the true set. Under Shape A this is not merely a tightness question — the naive instantiation makes the counting hypothesis arithmetically unsatisfiable (B3). |
| **D4** | Claim adaptivity (B5): fixed-claim model with an explicit hypothesis, or declare the cold standalone verifier not claim-binding and point at the warm start? | State the fixed-claim scope limit explicitly *and* record that the deployed usage is warm. Do not attempt to close the gap by strengthening the game. |
| **D5** | May W5 change the statements of `ipa{Vesta,Pallas}_sound` and the four kimchi consumers, plus both axiom-gate manifests, in one change? | Yes — `formal/` has no committed API (`feedback_formal_no_api_stability`), but the PR must state which roots' *meanings* changed, and the anti-triviality root must land with them. |
| **D6** | Does `bulletproof-pcs` take the `Zcash` require (manifest churn, second package compiling ironwood's closure in CI), or does the forking layer live in `kimchi/`? | Take the require in `bulletproof-pcs` at the same pin; hosting in `kimchi` inverts the dependency direction. |
| **D7** | Only if D2 = B: is **AGM acceptable for `bulletproof-pcs`** (today it is DL-binding-only; the kimchi terminal already accepts AGM), and do we widen the `native_decide` allowlist (M11)? | Both are trust decisions, not engineering ones. Raise them together. |
| **D8** | Given all of the above — is W5 still worth doing? The plan already calls it "the largest and most uncertain workstream" and **severable**; W1–W4 deliver the audit's deferred guard discharge without it. | My read: (i) do a1/b1/b2 unconditionally — they are cheap, they retire genuinely assumed content (the `b0` correspondence), and a1 is information we do not currently have; (ii) then re-decide. Shape B is a multi-month project whose payoff is real but which leaves the **kimchi terminal roots untouched** (C4) — that qualifier should be weighed before starting. |

**One point in W5's favour that the refoundation plan does not make:** ironwood declares **no**
Lean axiom for its random oracle, and neither does our W2 model. So a successful W5 — in either
shape — *removes* two kernel axioms rather than trading them for a new one. That is a strictly
better trust surface than the plan's original "one honest RO-realization axiom per curve", and
it dissolves the W2 axiom-text sign-off problem for this line entirely.
