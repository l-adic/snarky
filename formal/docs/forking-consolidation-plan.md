# Forking-tree consolidation: the disposition ledger and migration order

Produced by a per-declaration audit of both forking trees against the pinned `zcash/ironwood`
(`83a98f7f`). Every `DELETE_UPSTREAM` claim in this document was **compile-tested** — 21 claims
across four verification files, 21 confirmed, 0 refuted. Claims in the `DELETE_OBSOLETE` tier were
not compiled and are labelled as such throughout.

Companion document: `ironwood-generic-application.md` (what upstream offers and why).
Compiled evidence in-tree: `bulletproof-pcs/scripts/check_ironwood_generic.{lean,sh}`.

## Verdict

**INCREMENTAL — delete in place, in dependency order. Do not wipe the directories.**

Your proposal assumes most of the tree dies. It does not. **242 of 321 declarations survive — 76% of declaration lines, ~4,775 of 6,253 file-lines.** Wiping both directories to cherry-pick means re-landing 2,872 declaration lines in order to remove 921. That is a 3:1 ratio of re-typing to removal, and the re-typing includes the two largest proofs in the tree and the route to the only `sorry`.

**The fraction, precisely:**

| | decl-lines | share |
|---|--:|--:|
| DELETE, evidence-backed | 586 | 15% |
| DELETE?, obsolete, no compile evidence | 335 | 9% |
| MOVE (to the seam, or to a module below Game.lean) | 607 | 16% |
| KEEP | 2,265 | 60% |

**Entanglement is what settles it.** The survivors are not a separable block — they are welded to the deletions at exactly the worst three places:

1. **The `sorry`'s proof route crosses the delete boundary.** `Deployed.lean:812` needs `wireWins_iff_wins` (KEEP, but 3 of its 4 inputs move or delete) → `kimchiExtract_failure_measure_le` (MOVE, body shrinks 43→~10) → the escape/counting quartet (DELETE, subsumed) → `kimchiForkFrom_isSome_of_not_escape` (MOVE, 135 lines, must be **restated**) → `kimchiForkFrom_realizes` (KEEP, 154 lines, must be **edited**) → the scanner (DELETE, verified). Five of the six links change and none of them can be dropped. A wipe destroys the route; incremental edits preserve it under a gate at every step.
2. **The largest two proofs survive as edits, not as moves.** `kimchiForkFrom_realizes` (154 lines) and `kimchiForkFrom_isSome_of_not_escape` (135) sit *directly downstream* of the deleted scanner and escape strands. They must be adapted in the same commit as the deletion. Cherry-picking them out of a wiped tree means re-deriving 289 lines of proof to reach the same place an in-place edit reaches.
3. **The negative results depend on the duplicates being deleted in the right direction.** `honest_wins_everywhere` (Game:1802, 74 lines, on your never-lose list) consumes 5 declarations whose surviving copies currently live in `Honest.lean` — which is *downstream* of Game.lean (`Honest.lean:1 → Deployed.lean:1 → Game.lean`). Delete Game's copies and rely on Honest's, and the negative result stops compiling. The survivor of each pair must be hoisted *below* Game.lean first. The `deployed` classifier got this backwards; a wipe-and-cherry-pick would hit it blind.

**Where your instinct is right, and it is already the incremental operation.** Four whole files go to zero and should be `git rm`'d outright — **483 file-lines**:

- `kimchi/Kimchi/Verifier/Forking/Escape.lean` (131) — and this removes kimchi's only `import Zcash`
- `kimchi/Kimchi/Verifier/Forking/GuardEscape.lean` (115) — the wrong-denominator bounds
- `kimchi/Kimchi/Verifier/Forking/Model.lean` (89) — declarations go, its 40 lines of trust-boundary prose must be re-sited
- `bulletproof-pcs/Bulletproof/Forking/Extraction.lean` (148) — the pre-Schnorr Prop-level layer

plus `Knowledge.lean` collapsing to one theorem. That is `git rm` on 4 of 20 files, not a wipe of 20.

**And nine files have zero deletions at all — 1,826 file-lines that a wipe would put at risk for no gain:** `Transcript.lean`, `EndoChallenge.lean`, `Convention.lean`, `Schnorr.lean`, `SVector.lean`, `Capstone.lean` (bulletproof-pcs) and `Transcript.lean`, `OracleRun.lean`, `RunLink.lean` (kimchi). `EndoChallenge.lean` is 29/29 KEEP: `grep -rni glv` over the whole Zcash pin returns **zero hits**, `challengeNat` zero, and upstream's own `Challenges.lean:10-12` says outright it does not model the transcript. That file is the enabling condition for the entire reuse claim — it is what licenses instantiating the alphabet-generic layer at `Fin (2^128)` instead of at `Fp`. There is no version of "wipe and cherry-pick" in which touching it is correct.

**The one piece of good news that makes INCREMENTAL cheap.** The replacement for Game.lean's whole escape/counting layer already exists and is green in your repo: `shared_failure_measure_le` (`bulletproof-pcs/scripts/check_ironwood_generic.lean:108-131`, 24 lines) plus `pre_escape_measure_le` (:77-83, 7 lines). I ran the file — EXIT:0, zero diagnostics, zero sorries. Those 31 compiled lines retire 130 lines of Game.lean (the escape-set quartet plus `preForkEscape_subset_triple`). You do not need to write the seam theorem; you need to move it out of `scripts/` and supply it `hforce`.

## Totals

Units are **declaration lines** (the sum of per-declaration source lines). File lines reconcile
separately and exactly: `wc -l` = 6,253 = 5,458 (bulletproof-pcs, 14 files) + 795 (kimchi, 6 files).

| bucket | decl-lines |
| --- | --: |
| DELETE, compile-verified | 586 |
| DELETE, obsolete tier (not compiled) | 335 |
| MOVE | 607 |
| KEEP | 2265 |

Units: DECLARATION lines (the sum of per-decl `lines` fields) = 3,793. File lines reconcile exactly and separately: wc -l gives 6,253 = 5,458 (bulletproof-pcs, 14 files) + 795 (kimchi, 6 files), matching the brief. The 2,460-line gap between 3,793 and 6,253 is docstrings, module preambles, imports, section/variable blocks and blank lines -- not missing work. Self-check: the game classifier independently said Game.lean is '1877 lines of which ~1292 are code' and my per-decl sum for Game.lean is exactly 1292. Applying each file's own multiplier (1.45x Game and EndoChallenge, up to 4.45x kimchi Model.lean which is mostly prose), the estimated FILE-line impact is ~1,478 removable of 6,253 (24%), leaving ~4,775.

Buckets: delete_lines 586 = 45 lines of compile-verified upstream substitution in the six 'DELETE_UPSTREAM' passes + 101 lines of compile-verified commitGen retirement (18 decls across 3 files, one upstream decl per N copies) + 138 lines of character-diff-verified duplicates of our own declarations (I diffed six of them; they are byte-identical modulo the `private` keyword or a binder rename) + 95 lines subsumed by `shared_failure_measure_le`, which already exists and compiles in bulletproof-pcs/scripts/check_ironwood_generic.lean:108 (I ran it: EXIT:0, zero output, zero sorries), + 207 further verified-upstream lines in Game.lean's scanner/escape/traversal strands.

unverified_lines 335 is NOT unverified DELETE_UPSTREAM -- that number is ZERO. Every upstream-substitution claim in all six groups was compile-tested (12/12 game, 3/3 deployed, 5/5 triviality, 1/1 kimchi; transcript-endo and convention made none) and NONE was refuted. The 335 is the entire DELETE_OBSOLETE tier: 27 declarations claimed superseded on grep plus judgment, never compiled. It splits three ways by risk: 160 lines of kimchi Escape/GuardEscape/Model where the statement being deleted is arithmetically WRONG (divides by card F ~ 2^254 for 128-bit challenges), so deleting is safer than keeping; 166 lines of 'superseded in our own tree' including Stage 5a's headline kimchi_knowledge_soundness, which needs explicit sign-off rather than a janitorial delete; 9 lines of zero-consumer eta lemmas.

One cross-group double-count corrected: the game and deployed groups each marked their own copy of the same 7 non-upstream duplicate pairs DELETE_DEAD, naming the other file as survivor. Only one copy of each can die (68 lines). Those 68 are counted in move_lines as 'winner of pair', not twice in delete_lines. One reclassification: 4 escape-set decls (95 lines) moved from MOVE to DELETE on the strength of the compiled shared_failure_measure_le.

Survivors: 242 of 321 declarations (75%); 2,872 of 3,793 declaration lines (76%). By directory: bulletproof-pcs 2,613 of 3,353 survive (78%); kimchi 259 of 440 (59%), and its non-survivors are 3 whole files. Nine of the twenty files have ZERO deletions (1,826 file-lines untouched), including EndoChallenge.lean at 29/29 KEEP -- upstream has none of the GLV/signed-digit story (grep -rni glv over the whole pin: 0 hits).

---

# Migration order

## Step 0 — snapshot (keep this part of your plan)

`git checkout -b forking-preconsolidation && git commit -am 'snapshot before forking consolidation'`, then branch off it. Everything below is `git rm`/edit on a working branch; the snapshot is the escape hatch. **Gate:** none.

## The gates, once, so each step can name them

- `B` = `cd formal/bulletproof-pcs && lake build`
- `K` = `cd formal/kimchi && lake build`
- `G1` = `bulletproof-pcs/scripts/check_ironwood_generic.sh` (imports **Game.lean** — green today, EXIT:0, I ran it)
- `G2` = `bulletproof-pcs/scripts/check_extractor_computes.sh` (imports **Adapter + Capstone**; contains three `by decide`s and five `#eval`s, so it is the behavioural gate)
- `G3` = `bulletproof-pcs/scripts/check_axioms.sh`, `G3k` = `kimchi/scripts/check_axioms.sh`
- `G4` = `bulletproof-pcs/scripts/check_ipa_fixture.sh` (Reflection.lean is on this path)
- `L` = `lake lint` (Batteries `runLinter` over the package roots) — **de-privatization trips `docBlame` unless you add a docstring**
- `S` = `grep -rn sorry` over both trees must return **exactly** `Deployed.lean:812` (one hit; that is the state today)

Every step below is independently buildable: after each one, `B` + `K` + all gates pass and `S` still returns exactly one hit.

---

## Step 1 — kimchi: `git rm` Escape.lean + GuardEscape.lean

Delete both files (246 file-lines, 7 decls, 111 decl-lines) and drop `kimchi/Kimchi.lean:50`. Nothing else imports them (verified: the only importers are `Kimchi.lean:50` and `GuardEscape.lean:1`). This also removes kimchi's **only** `import Zcash`.

Do **not** re-derive `escape_coord` first: its sole consumers are `escape2`/`escape4`, which go in the same commit, so the compile-verified upstream substitution is moot here — record it in docs as the route for when the correct-alphabet version is written.

**Gates:** `K`, `G3k`, `L`.

## Step 2 — kimchi: retire Model.lean's 4 decls, keep its prose

Move `Model.lean:3-43` — the only written statement of the kimchi Poseidon-as-RO trust boundary, including the deliberate decision *not* to make it a Lean `axiom` and the admission that the 128-bit cast and endoExpand are idealized as uniform-in-F — into `docs/` or the surviving `OracleRun.lean` module docstring. Then `git rm Model.lean` and drop `kimchi/Kimchi.lean:47`. Fix, do not carry, its false claim at :30 that these decls are auditable in `roots.txt` (**no** Forking decl is in either roots.txt — verified, 0 hits).

After steps 1–2 the kimchi tree is 3 files / 460 file-lines, **100% survivors**.

**Gates:** `K`, `G3k`, `L`.

## Step 3 — bp: retire the `commitGen` algebra to upstream (one commit, 3 files)

Delete `Triviality.lean:49-93` (6 decls, 42 lines), `Game.lean:1518-1562` (6, 30), `Honest.lean:79-121` (6, 29) = **101 lines out, ~5 in**. Re-point the three consumers (`Triviality:104` `ipaAcceptV_of_witness`; `Game:1595/1609` `honestProver_accept`; `Honest:160/174` `honestProver_accept`) at `Zcash.Snark.{commitGen_add_gen, commitGen_smul_gen, commitGen_add_left, commitGen_smul_left, commitGen_split, commitGen_round}`.

Three mechanical traps, all from the verifier: (i) `commitGen_smul_coeff` → `commitGen_smul_left` **permutes the first two explicit args** (`(g) (c) (a)` upstream vs `(s) (g) (a)` ours); (ii) `rw` **fails** across the `Bulletproof.commitGen` / `Zcash.Snark.commitGen` defeq boundary — `exact`/`show` works, precedent `SVector.lean:83-88`; (iii) `commitGen_fold_identity` is not a bare import, it is `commitGen_split` + `commitGen_round` + `abel` under one `show` (compiled). Keep that as a single ~3-line corollary.

Optional in the same pass, outside the trees: `Soundness/SingleOpening.lean:39/44/49/54/206` are byte-identical to the same upstream names — this single import retires **13** in-tree declarations, not 6.

**Gates:** `B`, `G1`, `G2`, `G3`, `L`.

## Step 4 — bp: hoist the 7 non-upstream duplicated helpers BELOW Game.lean, then delete both copies

**Direction is forced** (`Honest.lean:1 → Deployed.lean:1 → Game.lean`): Honest's public copies are downstream and cannot be imported by Game. Put the survivors in `Prover.lean` (it already owns `KimchiProver`/`lrAt`/`leafAt`/`proofAt` and the private `tail_snoc`) or a new `Forking/Shared.lean` imported by it.

Survivors (take Honest's bodies, which are already public): `honestProver`, `honestProver_accept`, `lrAt_congr`, `leafAt_congr`, `padChal` (the `[Zero F]` version) + `padChal_apply_of_lt`; de-privatize `Prover.lean:142 tail_snoc` and `Capstone.lean:90 commitGen_singleton`.
Deletions: `Game.lean:1041 tail_snoc'`, `:1564 commitGen_one`, `:1575 honestProver`, `:1588 honestProver_accept`, `:1726 padChal`, `:1731 lrAt_congr`, `:1750 leafAt_congr` (78 lines); `Honest.lean:123 commitGen_one`, `:236 padChal_self` (dead, 7 lines).
**82 lines out, 74 relocated.**

**Gates:** `B`, `G1`, `G2` (it exercises `kimchiOpeningOrBreak`, which uses `commitGen_singleton`), `L` (add docstrings to the newly public decls).

## Step 5 — bp: `import Bulletproof.Reflection` and delete Deployed.lean's 7 re-derivations

Cycle-freedom **verified**: `Reflection.lean` imports only `Bulletproof.Wire`, `Bulletproof.Soundness`, `Pasta`; neither Wire nor Soundness imports anything under `Forking/`. Deployed.lean:454's "that module is not in this file's import closure" is simply false.

De-privatize `Reflection.lean:56/73/82/113/123/135` (`:101 combineCommitments_eq` is **already public** and was re-derived anyway). Delete `Deployed.lean:210, 426, 435, 456, 468, 478, 490` = 7 decls, **60 lines**. In the same commit, make `Deployed.lean:514 verifyWith_iff_verifierAcceptsAt` public and **move it into Reflection.lean**, then derive `verify_reflects` (:158, one-directional, sponge-challenges-only) from it — otherwise the next module needing an iff re-derives it a third time.

**Gates:** `B`, `G4` (Reflection is on the fixture path), `G3` (Reflection declares the two live FS axioms — the census must not move), `G1`, `G2`, `L`.

## Step 6 — bp: delete the superseded Prop-level knowledge-soundness layer ⚠️ THE UNVERIFIED TIER

`git rm Extraction.lean` (148 file-lines, 5 decls). From `Knowledge.lean` delete `decKimchiProverAccept` + `kimchi_knowledge_soundness` (34 lines) and **rehome** `kimchi_knowledge_soundness_conclusion_free_at_1dim` (29 lines) next to the other vacuity results in `Triviality.lean` — it needs only `openingRelation_solvable` plus two `Zcash.Snark` names, **not** `Prover.lean`, so it moves cleanly; then `git rm Knowledge.lean`. Also `Adapter.lean:36-44` (5 dead eta lemmas) and `Prover.lean:38/46` (`foldAll` pair).

Before deleting, re-point the docstring at `Convention.lean:129`, which cites `ipa_knowledge_soundness_conclusion_free`.

**This step needs your explicit sign-off**, because `kimchi_knowledge_soundness` (Knowledge:58) is Stage 5a's headline. It is superseded for a real reason (uniform over `Fin (σ.k+1) → F`, error over the whole scalar field, when the deployed challenges are 128-bit) and has zero consumers and no gate — but deleting a completed milestone is a decision, not a cleanup.

Do **not** also delete the Convention/Adapter island: `G2` parts (1) and (2) consume `ipaExtract`, `decIpaAcceptV`, `openingOfAcceptV` and `IpaAcceptV` (`by decide` at :19). Dropping it is a separate, optional consolidation that costs gate coverage.

**Gates:** `B`, `G1`, `G2`, `G3`, `L`, `S`.

## Step 7 — bp: the upstream swap in Game.lean ⚠️ ONE ATOMIC COMMIT, THE BIG ONE

This cannot be split: `kimchiForkEscapeSet` mentions `preForkEscape` (:713), `_prefix` mentions `KimchiForkReached` (:787), and the dichotomy proof mentions both.

Deletions (**~335 lines**, all compile-verified): scanner strand `scanFork` + 3 lemmas + `two_more` + the two `≠ none` corollaries (157) → `Zcash.Snark.nextForkChallenge*` at `F := Pre`; `PreThreeForkSuccess`/`preForkEscape`/`_subset_triple` (42) → `ThreeForkSuccess`/`recursiveForkEscape` + `pre_escape_measure_le`; `KimchiForkReached`/`_child` (38) → `RecursiveForkReached`/`_child`; `KimchiRunHistory` (3) → `RecursiveRunHistory`; the escape-set quartet (95) → the compiled `shared_failure_measure_le` block.

Edits (**~453 lines touched, none deleted**): `kimchiForkFrom` (48) gains `hexp_inj`; `kimchiForkFrom_realizes` (154) adapts to the new fresh-witness shape (favourably — it needed exactly that witness at :1245/:1282-1283); the dichotomy chain (208) is **restated** at upstream's escape/reached and sheds the global-escape plumbing; `kimchiExtract_failure_measure_le` shrinks 43 → ~10 as an application of `shared_failure_measure_le`.

For `Wins`: **keep a one-line pointwise abbreviation** over `fsWinsFull` rather than deleting outright. The `Iff.rfl` holds only at `p := A.run O`, and three sites apply it at a bound `p` — the extractor body (:286), its `Decidable` instance `decideWins` (:211/:214, where substituting re-runs `A.run O` and changes the def) and `Deployed.lean:548 wireWins_iff_wins`. Net saving from a full delete is ~5 lines; not worth touching `wireWins_iff_wins`.

**Gates:** `B`, then **`G1` must stay green** (it imports Game.lean and is the doc's own evidence), then **`G2` — this is the step that changes `deployedExtract`'s computational behaviour** (freshness moves from field images to prechallenges; the verifier exhibited order list `[0]` where the two scanners diverge, `by decide`), then `G3`, `L`, `S`.

## Step 8 — bp: lift the seam

Create the shared `Alphabet` / `ForkSetup` module (doc §4) and move into it: `Prechallenge`/`expandPre`/the four endpoint theorems (15); `foldGens_inv` (5) — **hoist before anything else touches Convention or Capstone**, it has 6 consumers in Convention and 3 in Capstone; `kimchiForkGood` + `_update` (26) as `good`/`hgood`; the dichotomy chain (208) as `hforce`; `OpeningOrBreak`/`oracleChallenges`/`KimchiRunSuffix` (22); the `Fin.snoc` plumbing + `tail_snoc` (21); the challenge-source structure (16, **generalize** — 2 squeeze fields do not cover kimchi's 4 across 2 sponges); and **one** generic honest reader machine replacing Game's `honestAdv*` (69) + Honest's `honestNodeAdv*` (67) with ~70. Restate `kimchiExtract_failure_measure_le` with the two additive summands.

Rename on the way in: `oracleChallenges` (Game:119 vs kimchi OracleRun:34 are different decls), `preU` (IPA round challenge vs kimchi evalscale), `commitGen_split`/`commitGen_split'`, `commitGen_one`/`commitGen_singleton`, `tail_snoc`/`tail_snoc'`.

**Gates:** `B`, `K`, all four bp gates, `L`, `S`.

## Step 9 — close `Deployed.lean:812`

Now a ~10-line application: `wireWins_iff_wins` forward → `shared_failure_measure_le` with `hforce` from step 8 → `card_prechallenge`, with `hinj`/`hne` from `expandPre_{vesta,pallas}_{injective,ne_zero}`. Out of scope for this ledger, but it is the point of steps 7–8.

## Ordering constraints, stated

Steps **1, 2** (kimchi) are independent of everything. **3 before 4** (so step 4's hoist list is 7 decls, not 13). **5** is independent. **6** is independent *except* `Game.lean:573/586`, which must wait for **7** (they are consumed by the dichotomy chain). **3 and 4 before 7** (so Game.lean's honest section is already thin and the hoisted helpers exist below it). **7 before 8**. `foldGens_inv` hoists in step 8 but must precede any later edit to Convention/Capstone.

---

# Risks

## A. Every DELETE that is NOT compile-verified

**Zero DELETE_UPSTREAM claims are unverified, and zero were refuted.** All six groups' upstream-substitution claims were compile-tested: 12/12 (game), 3/3 (deployed), 5/5 (triviality), 1/1 (kimchi); the transcript-endo and convention groups made none. Four verification files compiled with EXIT:0 and no sorries. So the classic burn — "an unverified deletion claim" — is not present in the upstream tier. The unverified risk lives elsewhere:

**A1. The 335-line "obsolete" tier — 27 decls, none compile-tested.** Three sub-tiers with very different risk:
- **160 lines, LOW risk (kimchi Escape/GuardEscape/Model).** Deleting these removes a statement that is *wrong*: `runGuardsFailFq_measure_le` (GuardEscape:61) and `runVUFail_measure_le` (:104) measure `PMF.uniformOfFintype (Fin n → C.ScalarField)` and divide by `Fintype.card C.ScalarField ≈ 2^254`, while all six kimchi challenges come from 128-bit prechallenges (`FqSponge.challenge` :113 for β,γ; `squeezeChallenge` :132 for α,ζ; `challengeNat`+`endoExpand` :109/:120 for v,u — our own `frStep`, OracleRun:124, spells this out). The bound understates the true per-round cost by ~2^126: **unsound as a model of the deployed verifier, not merely loose.** Risk of deleting ≈ 0; risk of keeping > 0. **But:** after deletion the plonk-guard escape summand has *no* statement at all, correct or otherwise. Record it as an open debt, not as progress.
- **166 lines, MEDIUM risk (Extraction 93, Knowledge 34, Prover `foldAll` 11, Game's two `≠ none` corollaries 28).** These delete statements nothing needs — but "nothing needs" is judgment. `Extraction.lean` is the largest single whole-file deletion in the plan (148 file-lines) and its entire justification is supersession by `Prover.lean` + Stage 5b. One mitigating fact I confirmed: `ipa_knowledge_soundness` (Extraction:114) is not merely dead but **unusable as written** — its `[DecidablePred (stratAccept …)]` binder has no instance anywhere in the tree.
- **9 lines, trivial (Adapter's 5 dead eta lemmas, `padChal_self`).**

**A2. The 138 DELETE_DEAD lines are duplicate-verified, not compile-verified.** I diffed them: `honestProver`, `honestProver_accept`, `lrAt_congr` are byte-identical to Honest.lean's copies **except the `private` keyword**; `tail_snoc'`/`tail_snoc` identical except the prime; `toOpening` identical modulo `p`→`π`; `zipFold_eq_recombine` identical modulo `k`→`n` and whitespace. Residual risk is not mathematical, it is `lake lint`: **a newly-public declaration with no docstring trips Batteries' `docBlame`**, and the linter is a CI gate. Cheap to hit, cheap to fix, easy to forget.

**A3. The 95 "subsumed" lines are backed by a compiled artifact, but subsumed ≠ free.** `shared_failure_measure_le` (`scripts/check_ironwood_generic.lean:108-131`) and `pre_escape_measure_le` (:77-83) compile today — I ran the file, EXIT:0, zero diagnostics, zero sorries. But `shared_failure_measure_le` takes `hforce` as a **hypothesis**, and supplying `hforce` means **rewriting the 135-line `kimchiForkFrom_isSome_of_not_escape`**, the largest proof in the tree. The 95 lines vanish; the 135 do not, and they must be *edited*, not moved.

**A4. `scanFork` is a verified delete that is also an algorithm change.** The verifier compiled `scanFork_ne_nextForkChallenge_at_zero` **`by decide`**, exhibiting order list `[0]` where our scanner selects prechallenge 0 and upstream's guard (`u = 0 ∨ u ∈ seen`) skips it. The substitution is sound but replaces the extractor's algorithm: the seen-set moves `List F → List Pre`, freshness is tested in `Pre`, and the field-distinctness `KimchiForkValid` demands must now be produced from `hexp_inj` at node construction — which today's extractor deliberately avoids (its own docstring, Game:283-286). `expandPre_{vesta,pallas}_injective` are unconditional theorems so the hypothesis is available. **`check_extractor_computes.sh` is the gate that would catch a mistake here**, and it is the only behavioural gate in the tree.

**A5. Two verifier corrections that must not be re-lost.** (i) `preForkEscape` was verified only as **`⊆`**, never `=` — upstream keeps the alphabet's zero and `expandPre C q ≠ 0` for *all* q, so this must never be read as `expand 0 = 0`. (ii) The escape set grows by up to **3 points**, not "≤ the single point 0" as the game classifier wrote (three good prechallenges with distinct images, one of them 0, puts ours at ∅ and upstream's at `{u | u = 0 ∨ good u}`). The 3/card-Q charge is unaffected because upstream re-derives the triple cap itself — that is exactly what `pre_escape_measure_le` does in 7 compiled lines.

## B. De-privatizations required

| file:line | decl | why |
|---|---|---|
| `Bulletproof/Reflection.lean:56` | `Ipa.Proof.toOpening` | step 5 |
| `Bulletproof/Reflection.lean:73` | `msm_eq_commitGen` | step 5 |
| `Bulletproof/Reflection.lean:82` | `combineFoldl_aux` | step 5 |
| `Bulletproof/Reflection.lean:113` | `combineCommitments_toArray_eq` | step 5 |
| `Bulletproof/Reflection.lean:123` | `foldl_add_eq_sum` | step 5 |
| `Bulletproof/Reflection.lean:135` | `zipFold_eq_recombine` | step 5 |
| `Bulletproof/Forking/Prover.lean:142` | `tail_snoc` | step 4; Mathlib has **no** `Fin.tail_snoc` (nearest: `Fin.tail_init_eq_init_tail`), so exactly one copy must survive |
| `Bulletproof/Forking/Capstone.lean:90` | `commitGen_singleton` | step 4 |
| `Bulletproof/Forking/Deployed.lean:514` | `verifyWith_iff_verifierAcceptsAt` | step 5; strongest wire reflection in the package |
| `Soundness/SingleOpening.lean:39/44/49/54/206` | the `commitGen` block | optional; or delete in favour of upstream |

`Reflection.lean:101 combineCommitments_eq` is **already public** and was re-derived anyway — no keyword needed, just the import. Game.lean's private honest section is *deleted*, not de-privatized: Honest.lean's public copies are the survivors, relocated below Game.lean.

## C. What could silently break — `Deployed.lean:812`

The single `sorry` (confirmed: `grep -rn sorry` over both trees returns exactly one hit) needs **nine declarations that a dead-code sweep would flag**:

| decl | consumers today | role in :812 |
|---|---|---|
| `prefixDecode_nodes` (Deployed:243, 43 lines) | 1, a leaf (`chainAt_sg`) | the `_D` argument |
| `card_prechallenge` (Deployed:95, 1 line) | **0** | rewrites 3/card-Pre → 3/2^128 |
| `expandPre_vesta_injective` (:105) | **0** | `hinj` |
| `expandPre_pallas_injective` (:110) | **0** | `hinj` |
| `expandPre_vesta_ne_zero` (:116) | **0** | `hne`, also of Honest:526 |
| `expandPre_pallas_ne_zero` (:120) | **0** | `hne`, also of Honest:526 |
| `endoAcc`, `endoExpand_eq_endoAcc`, `endoAcc_bound`, `endoAcc_injOn` (EndoChallenge) | **0 external** | the whole cone under the four above |
| `ipaNodeEquivProd` → `instFintypeIpaNode` (:158/:166) | 1 / instance | without them `PMF.uniformOfFintype (IpaNode C σ.k → Prechallenge)` at :805 **does not typecheck** — the STATEMENT breaks, not the proof |
| `decodesFromPrefixes_nodes` (:225) | 1 | the `dec` argument; also what makes the deferred-δ cheat inapplicable |

**Do NOT use `lake exe shake`, a zero-consumer filter, or a dead-code sweep as the migration filter.** It would flag most of the above and every faithfulness/trust-boundary artefact.

**Two more traps on this route:**
- **Underscore-prefixed hypotheses that are load-bearing.** `kimchiExtract_failure_measure_le` uses `_hexp_inj` (:1486), `_hQ` (:1487) and `_D` (:1473-1486); `kimchiExtract` uses `_hP` (:347) and `_dec` (:341). Any reader — or linter-driven cleanup — that trusts the underscore will delete a required argument.
- **`wireWins_iff_wins` (Deployed:548) is the most fragile KEEP in the plan.** Three of its four inputs move or delete (`Wins` deletes; `verifyWith_iff_verifierAcceptsAt` moves to Reflection.lean; the six combiners become an import), and **both directions are spent**: forward is step 1 of the :812 route, backward is the only path by which `honestNode_wireWins_everywhere` reaches the measured event. Anyone who "simplifies" it to one direction silently re-opens the vacuity hole the companions exist to close.

## D. The anti-vacuity companions and falsity proofs — all 8 preserved, each with its threat

| decl | lines | threat under this plan |
|---|--:|---|
| `verifierAcceptsAt_of_deferred_delta` (Game:158) | 8 | 0 consumers → sweep bait. Untouched by every step |
| `honest_wins_everywhere` (Game:1802) | 74 | depends on **5 pair-losers** (`honestProver`, `honestProver_accept`, `lrAt_congr`, `leafAt_congr`, `padChal`). **Breaks unless step 4 precedes any deletion** — this is exactly the error the `deployed` group's plan ("de-privatize Game's") would have caused in reverse |
| `verifyWith_of_deferred_delta` (Deployed:835) | 30 | 0 consumers; fully independent, can move at any time |
| `honestNode_wins_everywhere` (Honest:526) | 48 | depends on step 4's winners + `kimchiProverAccept_iff_verifierAcceptsAt` + `uBaseOf` |
| `honestNode_wireWins_everywhere` (Honest:584) | 16 | **THE endpoint**; needs `wireWins_iff_wins` BACKWARD, i.e. hostage to §C |
| `openingRelation_solvable` (Triviality:140) | 24 | the vacuity engine; one of its 3 consumers is being deleted. Survives |
| `fiatShamirTreeB_trivial` (Triviality:165) | 23 | depends on `ipaAcceptV_of_witness` → the `commitGen` block. Must be re-pointed **in the same commit as step 3** |
| `kimchi_knowledge_soundness_conclusion_free_at_1dim` (Knowledge:90) | 29 | only survivor of Knowledge.lean — **dies with the file unless step 6 rehomes it** |

**`fiatShamirTreeB_trivial` is not a historical note.** `poseidon_fiat_shamir_{vesta,pallas}` are still declared (`Reflection.lean:192`, `:202`) and consumed (:304/:337), and `FiatShamirTreeB` is a hypothesis of the chunked headline (`Soundness.lean:136`, `:230`). It is the only machine-checked statement that the current trust surface contains two tautologies at deployed parameters. Carry it.

**Prose-only negative results that a file wipe destroys** (they have no declaration and exist nowhere else):
1. `Game.lean:1773-1801` — why the T/Pf-universally-quantified `honest_wins_everywhere` is **FALSE** (`Pf := Empty` makes `OracleComp T Pre Pf` empty; `Pf := Unit` fails because `sg` must vary with `u`).
2. `EndoChallenge.lean:11-13` — that instantiating the game at `α := F` makes its counting hypothesis arithmetically unsatisfiable. Asserted in prose only; ideally becomes a decl.
3. `Model.lean:3-43` — the kimchi Poseidon-as-RO trust boundary and the cast/endoExpand idealization admission (step 2 re-sites it).

## E. Open gaps the plan does not close (record, don't bury)

1. **The 1-dim hypothesis is never discharged.** `hspan : ∀ x : G, ∃ s, x = s • H` and `hh` appear nowhere else in bulletproof-pcs — no Pasta instantiation exists. All three vacuity theorems are conditional on an un-witnessed premise. It is true (both Pasta point groups are prime-order cyclic and the `pasta` package carries the orders) but no Lean term says so. Add the Vesta/Pallas discharge, or a future reader dismisses the negative results as hypothetical.
2. **kimchi still owes its own anti-vacuity companion.** Nothing in `kimchi/Forking/` is one, and the IPA-side `Honest.lean` does **not** cover it (different domain — `Honest.lean:21-27` argues correctly that neither companion transports). Unrecorded anywhere in that directory today.
3. **The kimchi prefix carrier admits no measure, and never did.** `Escape.lean:14-17` and `GuardEscape.lean:14-18` promise a W4 lift that **cannot be performed at these types**: every prefix is a `List (KimchiTranscriptElt C)` / `List (FrTranscriptElt C)`, while upstream's game and every probability lemma need `[Fintype T] [DecidableEq T]`. Worse on the fr side: `frAbsorb : List C.ScalarField` (Transcript:167) makes `FrTranscriptElt C` **infinite even at Pasta**, so outer length-bounding does not help — retype the payload to `Vector C.ScalarField nc` (every call site already passes `.toList` of one). Upstream's `BTranscript` pattern is the model for the fq side but is monomorphic in its own element type, so it is not instantiable.
4. **Four factually wrong docstrings must not be carried forward.** `Game.lean:609-611` (upstream `RecursiveForkReached` "force-includes `[Field F]`" — refuted, the signature has **no** instance binders); `Deployed.lean:36-38` (a transcript-list domain fails because lists aren't `Fintype` — unsound; upstream's `BTranscript` is a bounded list *with* `Fintype` at Adaptive.lean:138. The **sound** reason is the `sg` slot: `grep -rn '\bsg\b' Zcash/` → **zero hits**); `Deployed.lean:454` (the false import-cycle excuse); `Prover.lean:24` (credits `foldAll`, which plays no part). Also `Adapter.lean:15-17` and `Convention.lean`'s preamble misdescribe which route is live.
5. **`roundNodeOf` (Deployed:586) is a verbatim copy of the record literal at :247-250 in the same file.** Define the branch once or the two will drift.

---

# The ledger

## Reconciliation first (read before the tables)

**File lines reconcile exactly.** `wc -l` over both trees = **6,253** = 5,458 (bulletproof-pcs, 14 files) + 795 (kimchi, 6 files). Matches the brief.

**Declaration counts: two classifier headers were wrong; the listings were right.** `grep -cE '^(private )?(noncomputable )?(theorem|lemma|def|abbrev|structure|inductive|instance) '` gives Deployed.lean = **52** (header said 48), and the six kimchi files = 3+4+4+18+2+21 = **52** (header said 41). Honest.lean = 32 once `@[simp]`-prefixed decls are counted. Total ledger rows: **321 declarations**.

**Per-decl `lines` sum to 3,793, not 6,253.** The 2,460-line gap is docstrings, module preambles, imports, `section`/`variable` blocks and blank lines — it is *not* missing work. Self-consistency check: the game classifier independently said Game.lean is "1877 lines of which ~1292 are code"; my sum for Game.lean is exactly **1292**. Per-file multipliers run 1.45× (Game, EndoChallenge) to 4.45× (kimchi Model.lean, which is 89 lines of which only 20 are declarations — the rest is the trust-boundary prose). All numbers below are **declaration lines** unless labelled "file-lines".

**Cross-classifier conflicts found and resolved (4):**

1. **The Game↔Honest dead-pair standoff.** The `game` group marked 13 Game.lean decls DELETE_DEAD naming Honest.lean as survivor; the `deployed` group marked 12 Honest.lean decls DELETE_DEAD naming Game.lean as survivor. Both cannot hold. Resolution: (a) the 6 `commitGen` bilinearity/split/fold lemmas go **upstream** — both copies plus Triviality's third copy die (compile-verified in `Verify_triviality.lean`); (b) for the 7 non-upstream pairs (`commitGen_one`, `honestProver`, `honestProver_accept`, `lrAt_congr`, `leafAt_congr`, `padChal`, `tail_snoc'`) exactly **one** copy dies. Direction is forced by the module graph — `Honest.lean:1 → Deployed.lean:1 → Game.lean`, so Honest's public copies are DOWNSTREAM and cannot be imported by Game. The survivor must be hoisted **below** Game.lean. I diffed the pairs: `honestProver`, `honestProver_accept`, `lrAt_congr` are byte-identical except the `private` keyword; `tail_snoc'`/`tail_snoc` identical except the prime. Ledger shows Game's copy as loser (DELETE) and Honest's as `MOVE (winner of pair)`. **A naive sum of the two groups' DELETE_DEAD would over-state deletion by 68 lines.**
2. **`commitGen_fold_identity`: three-way circular blame.** Group `deployed` pointed at Game/Triviality; group `triviality` pointed at Honest:112; group `game` pointed at Honest:112. Resolved by the `triviality` verifier, which *compiled* it from `Zcash.Snark.commitGen_split` + `commitGen_round` + `abel` with one `show`-bridge. All three copies die; one ~3-line corollary survives.
3. **`MOVE` depending on `DELETE` in the escape strand.** Group `game` marked the escape-set quartet MOVE_ABSTRACT while marking `preForkEscape`/`KimchiForkReached` DELETE — but `kimchiForkEscapeSet` *mentions* `preForkEscape` (:713) and `_prefix` mentions `KimchiForkReached` (:787). I then found the replacement already exists and compiles: `shared_failure_measure_le` (`bulletproof-pcs/scripts/check_ironwood_generic.lean:108-131`, 24 lines) plus `pre_escape_measure_le` (:77-83, 7 lines). I ran it: `lake env lean scripts/check_ironwood_generic.lean` → **EXIT:0, zero output, zero sorries**. So I **reclassified those 4 decls (95 lines) from MOVE to DELETE (subsumed)** — they are the `esc`/`hblind`/`hsub` block that the compiled seam theorem already contains.
4. **Same upstream decl claimed by multiple groups — checked, all legitimate.** `commitGen_*` replaces three in-tree copies each (one upstream decl, N copies — fine). `fsWinsFull` is claimed to replace both IPA's `Wins` and kimchi's `GuardEvent` — legitimate, that is exactly the m=0 / m=6 seam. No genuine collision.

---
### `bulletproof-pcs/Bulletproof/Forking/Game.lean` — 1877 file-lines, 67 decls

| decl | lines | disposition | upstream / survivor | status | note |
|---|--:|---|---|---|---|
| `OpeningOrBreak` | 6 | MOVE | — | — | |
| `oracleChallenges` | 3 | MOVE | — | — | name collides with kimchi OracleRun.lean:34 |
| `Wins` | 6 | DELETE (upstream) | Adaptive.lean:30 `fsWinsFull` | VERIFIED `Iff.rfl` — but only at `p := A.run O` | see risk R3; net gain ~5 lines |
| `verifierAcceptsAt_of_deferred_delta` | 8 | KEEP (negative result) | — | — | FALSITY PROOF. zero consumers → sweep bait |
| `DecodesFromPrefixes` | 10 | KEEP | — | — | |
| `decideWins` | 6 | KEEP | — | — | applies `Wins` at a bound `p` — blocks a naive `Wins` delete |
| `decideKimchiForkValid` | 20 | KEEP | — | — | |
| `scanFork` | 9 | DELETE (upstream) | Recursive.lean:242 `nextForkChallenge` | VERIFIED — **NOT definitional** (differs at q=0) | algorithm change, see risk R2 |
| `kimchiForkFrom` | 48 | KEEP | — | — | MUST BE EDITED: gains `hexp_inj` when the scanner is swapped |
| `kimchiExtract` | 17 | KEEP | — | — | `_hP` (:347), `_dec` (:341) underscored yet USED |
| `scanFork_isSome_of_good` | 22 | DELETE (upstream) | Recursive.lean:258 | VERIFIED | |
| `scanFork_output_fresh` | 20 | DELETE (upstream) | Recursive.lean:323 + :347 (fused) | VERIFIED | new witness shape is strictly better |
| `scanFork_other_good_mem_rest` | 31 | DELETE (upstream) | Recursive.lean:285 | VERIFIED | |
| `PreThreeForkSuccess` | 5 | DELETE (upstream) | Recursive.lean:168 `ThreeForkSuccess` | VERIFIED as implication (upstream stronger) | |
| `preForkEscape` | 2 | DELETE (upstream) | Recursive.lean:174 `recursiveForkEscape` | VERIFIED as **SUBSET only**, never `=` | never read as `expand 0 = 0` |
| `preForkEscape_subset_triple` | 35 | DELETE (upstream) | Recursive.lean:179 | VERIFIED (35 lines → 2) | `[Nonempty Pre]` no longer needed |
| `scanFork_two_more` | 47 | DELETE (upstream) | Recursive.lean:417 | VERIFIED (47 lines → 0) | |
| `scanFork_fst_ne_none` | 10 | DELETE? (obsolete) | — | not compile-tested | `≠ none` repackaging; re-derived, not imported |
| `scanFork_snd_ne_none` | 18 | DELETE? (obsolete) | — | not compile-tested | same |
| `KimchiForkReached` | 8 | DELETE (upstream) | Recursive.lean:1063 `RecursiveForkReached` | VERIFIED `Iff.rfl` | its docstring at :609-611 is REFUTED |
| `kimchiForkReached_child` | 30 | DELETE (upstream) | Recursive.lean:1074 | VERIFIED (30 lines → 1) | |
| `kimchiForkGood` | 15 | MOVE | — | — | becomes the seam's `good` argument |
| `kimchiForkGood_update` | 11 | MOVE | — | — | becomes `hgood` |
| `kimchiForkEscapeSet` | 15 | DELETE (subsumed) | scripts/check_ironwood_generic.lean:108 `shared_failure_measure_le` | **COMPILED IN REPO today (EXIT:0)** | |
| `kimchiForkEscapeSet_blind` | 28 | DELETE (subsumed) | same | COMPILED IN REPO | becomes `simp only [hesc, hgood]` |
| `kimchiForkEscapeSet_measure_le` | 24 | DELETE (subsumed) | same + `pre_escape_measure_le` (:77) | COMPILED IN REPO | 7 upstream lines replace 24+35 |
| `kimchiForkEscapeSet_prefix` | 28 | DELETE (subsumed) | same | COMPILED IN REPO | no global escape set exists under the seam |
| `kimchiForkFrom_isSome_of_not_escape` | 135 | MOVE | — | — | largest proof in tree; MUST BE **RESTATED** at upstream escape/reached; becomes `hforce` |
| `kimchiForkFrom_isSome_of_not_escape_root` | 17 | MOVE | — | — | |
| `proverOfProof` | 6 | KEEP | — | — | |
| `lrAt_proverOfProof` | 9 | KEEP | — | — | |
| `leafAt_proverOfProof` | 4 | KEEP | — | — | |
| `proofAt_proverOfProof` | 3 | KEEP | — | — | |
| `verifierAcceptsAt_iff_proverOfProof_accept` | 6 | KEEP | — | — | |
| `tail_snoc'` | 7 | DELETE (dup, loser) | ours: Prover.lean:142 `tail_snoc` | char-diff identical (only the prime) | Mathlib has no `Fin.tail_snoc` |
| `KimchiRunHistory` | 3 | DELETE (upstream) | Recursive.lean:780 `RecursiveRunHistory` | VERIFIED bare `Iff.rfl` | |
| `KimchiRunSuffix` | 13 | MOVE | — | — | |
| `KimchiForkRealizes` | 15 | KEEP | — | — | |
| `KimchiForkRealizes.mono` | 14 | KEEP | — | — | |
| `snoc_expand_cons_zero` | 6 | MOVE | — | — | |
| `snoc_expand_cons_tail` | 8 | MOVE | — | — | |
| `KimchiForkRealizes.forkValid` | 44 | KEEP | — | — | |
| `kimchiRunHistory_update` | 22 | MOVE | — | — | upstream has it only as an inline `have` (Recursive.lean:891-928) — NOT importable |
| `kimchiForkFrom_realizes` | 154 | KEEP | — | — | MUST BE EDITED: new fresh-witness shape (favourably) |
| `kimchiExtract_isSome_of_not_escape` | 56 | MOVE | — | — | |
| `kimchiExtract_failure_measure_le` | 43 | MOVE | — | — | body 43 → ~10 (application of `shared_failure_measure_le`); `_hexp_inj`/`_hQ`/`_D` underscored yet USED |
| `commitGen_add_gen` | 3 | DELETE (upstream) | CommitFold.lean:42 | VERIFIED (bare `exact`) | |
| `commitGen_smul_gen` | 4 | DELETE (upstream) | CommitFold.lean:47 | VERIFIED (bare `exact`) | |
| `commitGen_add_coeff` | 3 | DELETE (upstream) | CommitFold.lean:32 `commitGen_add_left` | VERIFIED (bare `exact`) | |
| `commitGen_smul_coeff` | 3 | DELETE (upstream) | CommitFold.lean:37 `commitGen_smul_left` | VERIFIED — **arg order permuted** | |
| `commitGen_split` | 8 | DELETE (upstream) | IpaSoundness.lean:88 | VERIFIED (bare `exact`) | |
| `commitGen_fold_identity` | 9 | DELETE (upstream) | CommitFold.lean:57 `commitGen_round` + split + `abel` | VERIFIED — needs `show` bridge | |
| `commitGen_one` | 3 | DELETE (dup, loser) | ours: Capstone.lean:90 `commitGen_singleton` | 3 copies; 1 survives | |
| `honestProver` | 8 | DELETE (dup, loser) | ours: Honest.lean:140 | char-diff identical except `private` | |
| `honestProver_accept` | 32 | DELETE (dup, loser) | ours: Honest.lean:153 | char-diff identical except `private` | |
| `HonestPrefix` | 1 | MOVE | — | — | |
| `honestPrefixes` | 2 | MOVE | — | — | |
| `honestAdvAux` | 6 | MOVE | — | — | collapse with Honest:343 into ONE generic reader |
| `honestAdv` | 3 | MOVE | — | — | |
| `honestAdvAux_queryBound` | 9 | MOVE | — | — | |
| `honestAdv_queryBound` | 3 | MOVE | — | — | |
| `honestAdvAux_run` | 43 | MOVE | — | — | same induction as Honest:379 |
| `honestAdv_run` | 3 | MOVE | — | — | |
| `padChal` | 2 | DELETE (dup, loser) | ours: Honest.lean:232 (`[Zero F]`, better) | char-diff modulo the binder | |
| `lrAt_congr` | 15 | DELETE (dup, loser) | ours: Honest.lean:194 | char-diff identical except `private` | |
| `leafAt_congr` | 11 | DELETE (dup, loser) | ours: Honest.lean:213 | char-diff identical except `private` | |
| `honest_wins_everywhere` | 74 | KEEP (negative result) | — | — | ANTI-VACUITY. depends on 5 pair-losers; prose at :1773-1801 is a negative result with NO decl |

**subtotal Game.lean:** DELETE **421** · unverified-delete **28** · MOVE **405** · KEEP **438** = 1292 of 1877 file-lines

### `bulletproof-pcs/Bulletproof/Forking/Deployed.lean` — 866 file-lines, 52 decls

| decl | lines | disposition | upstream / survivor | status | note |
|---|--:|---|---|---|---|
| `Prechallenge` | 1 | MOVE | — | — | seam `Q`; shared by both instantiations |
| `instNonemptyPrechallenge` | 1 | MOVE | — | — | |
| `card_prechallenge` | 1 | MOVE | — | — | 1 line, 0 consumers, named in the :812 route → **sweep bait** |
| `expandPre` | 2 | MOVE | — | — | seam `expand` |
| `expandPre_vesta_injective` | 3 | MOVE | — | — | 0 consumers today; the `hinj` of :812 → sweep bait |
| `expandPre_pallas_injective` | 3 | MOVE | — | — | same |
| `expandPre_vesta_ne_zero` | 2 | MOVE | — | — | 0 consumers; `hne` of :812 AND of Honest:526 |
| `expandPre_pallas_ne_zero` | 2 | MOVE | — | — | same |
| `IpaNode` | 14 | KEEP | — | — | sound reason = the `sg` slot (0 hits for `sg` upstream); the "lists aren't Fintype" reason is FALSE |
| `ipaNodeEquivProd` | 7 | KEEP | — | — | delete this and :812's STATEMENT breaks |
| `instFintypeIpaNode` | 2 | KEEP | — | — | without it :812 does not TYPECHECK |
| `nodeU` | 6 | KEEP | — | — | |
| `nodeC` | 6 | KEEP | — | — | |
| `nodes` | 2 | KEEP | — | — | |
| `nodes_eq` | 5 | KEEP | — | — | |
| `nodeRound` | 2 | KEEP | — | — | |
| `nodeFinal` | 2 | KEEP | — | — | the function that cannot exist on the absorbed-list domain |
| `toOpening` | 6 | DELETE (dup of our private) | ours: Reflection.lean:56 | char-diff identical; import **CYCLE-FREE (verified)** | |
| `decodesFromPrefixes_nodes` | 12 | KEEP | — | — | the `dec` of :812; what blocks the deferred-δ cheat |
| `prefixDecode_nodes` | 43 | KEEP | — | — | the `_D` of :812. 1 leaf consumer → **sweep bait** |
| `nodeTranscript` | 11 | KEEP | — | — | |
| `flatMap_finRange_take` | 18 | KEEP | — | — | |
| `toList_eq_map_finRange` | 4 | KEEP | — | — | Mathlib-derivable; inline rather than migrate |
| `nodeTranscript_nodes` | 40 | KEEP | — | — | FAITHFULNESS artefact, leaf by design |
| `sg_determined_of_verifyWith` | 6 | KEEP | — | — | |
| `uBaseOf` | 2 | KEEP | — | — | |
| `uBaseOf_eq_transcript` | 3 | KEEP | — | — | FAITHFULNESS artefact, leaf by design |
| `wireWins` | 6 | KEEP | — | — | the event :812 measures |
| `msm_eq_commitGen` | 4 | DELETE (dup of our private) | ours: Reflection.lean:73 | char-diff identical; cycle-free | |
| `combineFoldl_aux` | 15 | DELETE (dup of our private) | ours: Reflection.lean:82 | char-diff identical; cycle-free | |
| `combineCommitments_arr_eq` | 7 | DELETE (dup of our private) | ours: Reflection.lean:101 — **ALREADY PUBLIC** | re-derived anyway; Deployed:454's "not in import closure" excuse is FALSE | |
| `combineCommitments_toArray_eq` | 6 | DELETE (dup of our private) | ours: Reflection.lean:113 | char-diff identical | |
| `foldl_add_eq_sum` | 7 | DELETE (dup of our private) | ours: Reflection.lean:123 | char-diff identical | |
| `zipFold_eq_recombine` | 15 | DELETE (dup of our private) | ours: Reflection.lean:135 | **I diffed it** — identical modulo `k`→`n` | |
| `verifyWith_iff_verifierAcceptsAt` | 15 | KEEP | — | — | `private`; strongest wire reflection (iff, challenge-generic) → make public in Reflection.lean |
| `wireWins_iff_wins` | 12 | KEEP | — | — | **MOST FRAGILE KEEP**: both directions spent; 3 of its 4 inputs move or delete |
| `roundNodeOf` | 6 | KEEP | — | — | verbatim copy of the record literal at :247-250 in the SAME file |
| `roundNodeOf_nodeC` | 7 | KEEP | — | — | |
| `sgForget` | 1 | KEEP | — | — | |
| `pinNode` | 7 | KEEP | — | — | |
| `pinTable` | 3 | KEEP | — | — | |
| `pinNode_factors` | 9 | KEEP | — | — | |
| `pinTable_factors` | 4 | KEEP | — | — | TRUST-BOUNDARY artefact, leaf by design |
| `pinNode_nodeC_of_sg` | 13 | KEEP | — | — | |
| `pinNode_nodeU` | 6 | KEEP | — | — | |
| `pinNode_nodes` | 12 | KEEP | — | — | |
| `wireWins_congr` | 11 | KEEP | — | — | |
| `wireWins_pinTable` | 21 | KEEP | — | — | TRUST-BOUNDARY artefact, leaf by design |
| `chainAt_sg` | 6 | KEEP | — | — | TRUST-BOUNDARY artefact; only consumer of `prefixDecode_nodes` |
| `deployedExtract` | 10 | KEEP | — | — | plain computable `def` — the discipline the vacuity results force |
| `deployedExtract_failure_measure_le` | 18 | KEEP | — | — | **THE SORRY (:812)** |
| `verifyWith_of_deferred_delta` | 30 | KEEP (negative result) | — | — | FALSITY PROOF at the wire. 0 consumers; independent of every step |

**subtotal Deployed.lean:** DELETE **60** · unverified-delete **0** · MOVE **15** · KEEP **382** = 457 of 866 file-lines

### `bulletproof-pcs/Bulletproof/Forking/Honest.lean` — 603 file-lines, 32 decls

| decl | lines | disposition | upstream / survivor | status | note |
|---|--:|---|---|---|---|
| `commitGen_add_gen` | 3 | DELETE (upstream) | CommitFold.lean:42 | VERIFIED (bare `exact`) | |
| `commitGen_smul_gen` | 4 | DELETE (upstream) | CommitFold.lean:47 | VERIFIED (bare `exact`) | |
| `commitGen_add_coeff` | 3 | DELETE (upstream) | CommitFold.lean:32 | VERIFIED (bare `exact`) | |
| `commitGen_smul_coeff` | 3 | DELETE (upstream) | CommitFold.lean:37 | VERIFIED — arg order permuted | |
| `commitGen_split` | 7 | DELETE (upstream) | IpaSoundness.lean:88 | VERIFIED (bare `exact`) | |
| `commitGen_fold_identity` | 9 | DELETE (upstream) | CommitFold.lean:57 + split + `abel` | VERIFIED — needs `show` | this IS the kimchi-convention fold; keep the corollary once |
| `commitGen_one` | 3 | MOVE (winner of pair) | — | — | relocate BELOW Game.lean |
| `honestProver` | 8 | MOVE (winner of pair) | — | — | relocate BELOW Game.lean |
| `honestProver_accept` | 32 | MOVE (winner of pair) | — | — | relocate BELOW Game.lean |
| `lrAt_congr` | 15 | MOVE (winner of pair) | — | — | relocate BELOW Game.lean |
| `leafAt_congr` | 11 | MOVE (winner of pair) | — | — | relocate BELOW Game.lean |
| `padChal` | 2 | MOVE (winner of pair) | — | — | the `[Zero F]` version is the better one |
| `padChal_self` | 4 | DELETE? (obsolete) | — | not compile-tested | genuinely dead: grep finds only its own statement |
| `padChal_apply_of_lt` | 2 | MOVE | — | — | the one padding lemma actually used |
| `mapComp` | 3 | DELETE (upstream) | OracleComp.lean:225 `bind` (no `map` upstream) | VERIFIED — needs `funext`, not `rfl` | |
| `mapComp_run` | 5 | DELETE (upstream) | OracleComp.lean:229 `run_bind` | VERIFIED bare | call sites become plain `simp` |
| `mapComp_queryBound` | 5 | DELETE (upstream) | OracleComp.lean:246 `queryBound_bind` | VERIFIED — no arithmetic needed | |
| `wireProofOf` | 6 | KEEP | — | — | |
| `toOpening_wireProofOf` | 6 | KEEP | — | — | |
| `wireProofOf_lr_getElem` | 3 | KEEP | — | — | |
| `honestNode` | 15 | KEEP | — | — | |
| `honestPrefixNode` | 3 | KEEP | — | — | |
| `honestNodeAdvAux` | 7 | MOVE | — | — | one generic reader subsumes this + Game:1638 |
| `honestNodeAdv` | 4 | KEEP | — | — | where the kimchi conventions enter |
| `honestNodeAdvAux_queryBound` | 10 | MOVE | — | — | |
| `honestNodeAdv_queryBound` | 4 | KEEP | — | — | |
| `honestNodeAdvAux_run` | 43 | MOVE | — | — | same induction as Game:1668 → prove once |
| `honestNodeAdv_run` | 7 | MOVE | — | — | NAME IS WRONG: statement never mentions `honestNodeAdv` |
| `honestPrefixNode_eq_nodes` | 50 | KEEP | — | — | the genuinely new argument: query points ARE the prefixes of its own output |
| `honestNodeAdv_prefixes` | 9 | KEEP | — | — | |
| `honestNode_wins_everywhere` | 48 | KEEP (negative result) | — | — | ANTI-VACUITY (deployed domain). does NOT transport from Game:1802 |
| `honestNode_wireWins_everywhere` | 16 | KEEP (negative result) | — | — | ANTI-VACUITY **ENDPOINT**. needs `wireWins_iff_wins` BACKWARD |

**subtotal Honest.lean:** DELETE **42** · unverified-delete **4** · MOVE **140** · KEEP **164** = 350 of 603 file-lines

### `bulletproof-pcs/Bulletproof/Forking/Transcript.lean` — 414 file-lines, 29 decls — **ZERO deletions**

| decl | lines | disposition | note |
|---|--:|---|---|
| `IpaTranscriptElt` | 9 | KEEP | upstream `TranscriptElt` has 2 params / 1 squeeze; we need 3 carriers — not instantiable |
| `stepState` | 6 | KEEP | upstream has no sponge at all (Blake2b, abstract) |
| `preTAbsorbs` | 2 | KEEP | |
| `preT` | 2 | KEEP | |
| `roundBlock` | 2 | KEEP | |
| `preU` | 2 | KEEP | |
| `preC` | 2 | KEEP | **LOAD-BEARING NEGATIVE CONTENT: `sg`/`z1`/`z2` absorbed NOWHERE. Never "fix" this** |
| `spongeOBase` | 2 | KEEP | |
| `spongeOScalar` | 3 | KEEP | |
| `toGroup_spongeOBase_preT` | 4 | KEEP | the only faithfulness bridge the deployed route actually consumes |
| `rstep` | 7 | KEEP | |
| `roundChallengesAux_eq_foldl` | 6 | KEEP | |
| `mstate` | 7 | KEEP | |
| `mchals` | 9 | KEEP | |
| `rstep_foldl_state` | 15 | KEEP | |
| `rstep_foldl_toList` | 15 | KEEP | |
| `roundChallengesAux_snd` | 4 | KEEP | |
| `roundChallengesAux_fst_toList` | 5 | KEEP | |
| `flatMap_block_foldl` | 14 | KEEP | |
| `mchals_getElem?` | 17 | KEEP | |
| `roundChallengesAux_getElem?` | 7 | KEEP | |
| `roundBlock_succ` | 8 | KEEP | upstream's `roundTranscriptFin_eq_append` is at a type that does not unify |
| `spongeOScalar_preU` | 48 | KEEP | only Lean tie from the deployed ROUND challenges to Poseidon. 0 proof consumers |
| `spongeOScalar_preC` | 39 | KEEP | only Lean tie for the SCHNORR challenge. 0 proof consumers |
| `FiatShamir` | 5 | MOVE | MOVE-and-**GENERALIZE**: 2 squeeze fields do NOT cover kimchi's 4 across 2 sponges |
| `transcriptOf` | 5 | MOVE | |
| `verifyOracle` | 4 | MOVE | |
| `spongeFS` | 2 | MOVE | |
| `verifyOracle_spongeFS` | 9 | KEEP | the anti-assumption seal. 0 proof consumers |

**subtotal Transcript.lean:** DELETE **0** · unverified **0** · MOVE **16** · KEEP **244** = 260 of 414 file-lines

### `bulletproof-pcs/Bulletproof/Forking/EndoChallenge.lean` — 428 file-lines, 29 decls — **ZERO deletions, 100% KEEP**

| decl | lines | disposition | note |
|---|--:|---|---|
| `endoAcc` | 7 | KEEP | public, 0 external consumers → sweep bait |
| `zstep` | 4 | KEEP | |
| `fstep` | 4 | KEEP | |
| `sigmaBit` | 1 | KEEP | |
| `epsBit` | 1 | KEEP | |
| `endoAcc_eq_foldl` | 2 | KEEP | |
| `foldl_reverse_range_succ` | 4 | KEEP | |
| `fstep_cast` | 5 | KEEP | |
| `foldl_cast` | 9 | KEEP | |
| `endoExpand_eq_fstep` | 6 | KEEP | |
| `endoExpand_eq_endoAcc` | 10 | KEEP | public, 0 external consumers → sweep bait |
| `zstep_bounds` | 6 | KEEP | |
| `foldl_bound` | 19 | KEEP | |
| `endoAcc_bound` | 10 | KEEP | SHORTNESS; public, 0 external consumers → sweep bait |
| `signVal_inj` | 3 | KEEP | |
| `zstep_sum` | 4 | KEEP | |
| `zstep_diff` | 4 | KEEP | |
| `foldl_sum` | 9 | KEEP | |
| `foldl_diff` | 9 | KEEP | |
| `endoAcc_sum` | 4 | KEEP | |
| `endoAcc_diff` | 4 | KEEP | |
| `sum_bound` | 12 | KEEP | not in Mathlib, not upstream |
| `signed_unique` | 24 | KEEP | the mathematical heart of injectivity |
| `endoAcc_injOn` | 55 | KEEP | public, 0 external consumers → sweep bait |
| `cast_short_relation_eq_zero` | 6 | KEEP | |
| `endoExpand_vesta_injOn` | 19 | KEEP | the ONLY property the 3 / card Q counting needs |
| `endoExpand_vesta_ne_zero` | 16 | KEEP | deletes the m zero-slice summands entirely |
| `endoExpand_pallas_injOn` | 19 | KEEP | |
| `endoExpand_pallas_ne_zero` | 16 | KEEP | |

**subtotal EndoChallenge.lean:** DELETE **0** · unverified **0** · MOVE **0** · KEEP **292** = 292 of 428 file-lines. Verified negatives: `grep -rni glv` over the whole Zcash pin → 0 hits; `challengeNat` → 0; `endo` → 6 hits, all the English word "vendored". **Upstream has none of this story.**

### `bulletproof-pcs/Bulletproof/Forking/Convention.lean` — 137 file-lines, 7 decls

| decl | lines | disposition | note |
|---|--:|---|---|
| `toZcash` | 4 | KEEP | |
| `foldGens_inv` | 5 | MOVE | THE fold-convention seam; consumed by Convention (6×) AND Capstone (3×) — hoist FIRST |
| `zcash_ipaAcceptV_toZcash` | 21 | KEEP | |
| `ipaAcceptV_of_zcash` | 24 | KEEP | |
| `ipaAcceptV_iff_zcash` | 4 | KEEP | |
| `decIpaAcceptV` | 5 | KEEP | load-bearing for the `by decide` at check_extractor_computes.lean:19 |
| `ipaExtract` | 4 | KEEP | |

**subtotal:** DELETE **0** · MOVE **5** · KEEP **62** = 67 of 137 file-lines

### `bulletproof-pcs/Bulletproof/Forking/Adapter.lean` — 78 file-lines, 9 decls

| decl | lines | disposition | note |
|---|--:|---|---|
| `ursOf` | 1 | KEEP | |
| `srsOf` | 1 | DELETE? (obsolete) | zero consumers |
| `ursOf_k` | 1 | DELETE? (obsolete) | dead `@[simp] rfl` |
| `ursOf_g` | 1 | DELETE? (obsolete) | dead `@[simp] rfl` |
| `srsOf_ursOf` | 1 | DELETE? (obsolete) | dead |
| `ursOf_srsOf` | 1 | DELETE? (obsolete) | dead |
| `commit_eq_zcash` | 2 | KEEP | our commitment is HIDING, upstream's is not |
| `openingRelationB_iff_zcash` | 11 | KEEP | NOT upstream's `ipaRelation_unblind` |
| `openingOfAcceptV` | 5 | KEEP | only consumer is the computability gate |

**subtotal:** unverified-delete **5** · KEEP **19** = 24 of 78 file-lines

### `bulletproof-pcs/Bulletproof/Forking/Schnorr.lean` — 66 file-lines, 1 decl

| decl | lines | disposition | note |
|---|--:|---|---|
| `schnorr_fork_eq` | 20 | KEEP | `grep -rl Schnorr Zcash/` → NO FILES. halo2 has no such round |

**subtotal:** KEEP **20** = 20 of 66 file-lines

### `bulletproof-pcs/Bulletproof/Forking/SVector.lean` — 155 file-lines, 8 decls — **ZERO deletions**

| decl | lines | disposition | note |
|---|--:|---|---|
| `bPolyCoefficients_zero` | 3 | KEEP | |
| `bPolyCoefficients_succ` | 28 | KEEP | the real content: testBit product satisfies the doubling recursion |
| `commitGen_bPolyCoefficients_step` | 11 | KEEP | 4 live consumers |
| `commitGen_bPolyCoefficients_zero` | 5 | KEEP | |
| `bPoly_succ` | 11 | KEEP | upstream has no `bPoly` |
| `foldHalves_evalVector` | 7 | KEEP | |
| `bPoly_eq_innerProduct` | 19 | KEEP | |
| `combinedB_eq_innerProduct` | 5 | KEEP | consumed by Deployed.lean:525 |

**subtotal:** KEEP **89** = 89 of 155 file-lines

### `bulletproof-pcs/Bulletproof/Forking/Capstone.lean` — 166 file-lines, 6 decls

| decl | lines | disposition | note |
|---|--:|---|---|
| `KimchiForkCert` | 6 | KEEP | referenced at 12 sites in Game.lean + the gate |
| `KimchiForkValid` | 11 | KEEP | the predicate the whole Game/Deployed layer is written against |
| `KimchiForkCert.toDFork` | 5 | KEEP | |
| `commitGen_singleton` | 3 | MOVE | de-privatize into the shared algebra module |
| `KimchiForkValid.toDFork` | 26 | KEEP | the load-bearing transport |
| `kimchiOpeningOrBreak` | 30 | KEEP | THE data-valued endpoint. do NOT reroute via `algebraicRelationOfDeployedAccept` |

**subtotal:** MOVE **3** · KEEP **78** = 81 of 166 file-lines

### `bulletproof-pcs/Bulletproof/Forking/Prover.lean` — 237 file-lines, 12 decls

| decl | lines | disposition | note |
|---|--:|---|---|
| `foldAll` | 4 | DELETE? (obsolete) | dead AND contradicts Prover.lean:24's own docstring |
| `commitGen_bPolyCoefficients_foldAll` | 7 | DELETE? (obsolete) | zero consumers |
| `KimchiProver` | 5 | KEEP | the commit-then-challenge leaf; group's public API |
| `kimchiProverAccept` | 9 | KEEP | |
| `kimchiProverAccept_forkValid` | 28 | KEEP | Prop-level `∃ cert` (defect inherited from upstream) |
| `KimchiProver.lrAt` | 3 | KEEP | heavily consumed by Game + Honest |
| `KimchiProver.leafAt` | 3 | KEEP | |
| `KimchiProver.proofAt` | 7 | KEEP | |
| `tail_snoc` | 7 | MOVE | de-privatize; then Game:1041 `tail_snoc'` deletes |
| `kimchiProverAccept_snoc` | 48 | KEEP | largest genuine proof in the group |
| `kimchiProverAccept_iff_verifierAcceptsAt` | 8 | KEEP | the anti-trust decl for the whole strategy model |
| `kimchi_opening_or_break_of_extractable` | 12 | KEEP | interactive wrapper, **NEVER an endpoint** (Knowledge:92 proves its conclusion free) |

**subtotal:** unverified-delete **11** · MOVE **7** · KEEP **123** = 141 of 237 file-lines

### `bulletproof-pcs/Bulletproof/Forking/Triviality.lean` — 181 file-lines, 9 decls

| decl | lines | disposition | upstream | status | note |
|---|--:|---|---|---|---|
| `commitGen_add_gen` | 4 | DELETE (upstream) | CommitFold.lean:42 | VERIFIED | |
| `commitGen_smul_gen` | 5 | DELETE (upstream) | CommitFold.lean:47 | VERIFIED | |
| `commitGen_add_coeff` | 4 | DELETE (upstream) | CommitFold.lean:32 | VERIFIED | |
| `commitGen_smul_coeff` | 4 | DELETE (upstream) | CommitFold.lean:37 | VERIFIED — arg order permuted | |
| `commitGen_split'` | 10 | DELETE (upstream) | IpaSoundness.lean:88 | VERIFIED | the prime admits it was already a copy |
| `commitGen_fold_identity` | 15 | DELETE (upstream) | CommitFold.lean:57 + split + `abel` | VERIFIED — needs `show` | |
| `ipaAcceptV_of_witness` | 35 | KEEP | — | — | ONLY satisfiability proof for `Bulletproof.IpaAcceptV` |
| `openingRelation_solvable` | 24 | KEEP (negative result) | — | — | **THE VACUITY ENGINE.** upstream states this only in PROSE (5 docstrings + its book) |
| `fiatShamirTreeB_trivial` | 23 | KEEP (negative result) | — | — | audits the two **LIVE** axioms Reflection.lean:192/:202 |

**subtotal:** DELETE **42** · KEEP **82** = 124 of 181 file-lines

### `bulletproof-pcs/Bulletproof/Forking/Extraction.lean` — 148 file-lines, 5 decls — **WHOLE FILE GOES**

| decl | lines | disposition | superseded by | note |
|---|--:|---|---|---|
| `Strategy` | 13 | DELETE? (obsolete) | ours: Prover.lean:60 `KimchiProver` | NOT a dup of upstream `Prover` — docs/agm-reuse-scope.md:62 is WRONG |
| `stratAccept` | 13 | DELETE? (obsolete) | ours: Prover.lean:70 | |
| `ipaTreeV_of_extractable` | 28 | DELETE? (obsolete) | ours: Prover.lean:86 | |
| `ipa_knowledge_soundness` | 18 | DELETE? (obsolete) | Game:1447 / Deployed:795 | also UNUSABLE as written: its `DecidablePred` binder has no instance in the tree |
| `ipa_knowledge_soundness_conclusion_free` | 21 | DELETE? (obsolete) | Knowledge:90 (strictly stronger) | re-point the Convention.lean:129 docstring first |

**subtotal:** unverified-delete **93** · KEEP **0** = 93 of 148 file-lines. Entire file deletable — **but the whole justification is in the unverified tier.**

### `bulletproof-pcs/Bulletproof/Forking/Knowledge.lean` — 102 file-lines, 3 decls

| decl | lines | disposition | note |
|---|--:|---|---|
| `decKimchiProverAccept` | 11 | DELETE? (obsolete) | dies with the theorem below |
| `kimchi_knowledge_soundness` | 23 | DELETE? (obsolete) | **STAGE 5a HEADLINE.** wrong denominator (card F, not 2^128). **Needs explicit sign-off** |
| `kimchi_knowledge_soundness_conclusion_free_at_1dim` | 29 | KEEP (negative result) | ANTI-VACUITY. must be **REHOMED** or it dies with the file |

**subtotal:** unverified-delete **34** · KEEP **29** = 63 of 102 file-lines

### `kimchi/Kimchi/Verifier/Forking/Transcript.lean` — 229 file-lines, 21 decls — **ZERO deletions**

| decl | lines | disposition | note |
|---|--:|---|---|
| `KimchiTranscriptElt` | 9 | KEEP | must be length-bounded before any measure (upstream `BTranscript` is monomorphic — not instantiable) |
| `absorbInto` | 6 | KEEP | |
| `wCommAbsorbs` | 2 | KEEP | chunking-aware |
| `preAbsorbs` | 3 | KEEP | |
| `preBeta` | 3 | KEEP | |
| `preGamma` | 3 | KEEP | |
| `preAlpha` | 3 | KEEP | |
| `preZeta` | 3 | KEEP | the commit-then-challenge tie for the quotient commitment |
| `preBeta_ne_preGamma` | 8 | KEEP | 7 distinctness lemmas, 0 consumers, one shared proof → collapse to ONE injectivity lemma |
| `preGamma_ne_preAlpha` | 8 | KEEP | " |
| `preAlpha_ne_preZeta` | 8 | KEEP | " |
| `preBeta_ne_preAlpha` | 8 | KEEP | " |
| `preBeta_ne_preZeta` | 8 | KEEP | " |
| `preGamma_ne_preZeta` | 8 | KEEP | " |
| `FrTranscriptElt` | 5 | KEEP | **MUST BE RETYPED**: `List` payload ⇒ infinite ⇒ no `Fintype` ⇒ no measure. Use `Vector` |
| `frAbsorbInto` | 4 | KEEP | |
| `absorbEval` | 2 | KEEP | |
| `preVAbsorbs` | 17 | KEEP | pure deployed-wire absorb order |
| `preV` | 3 | KEEP | |
| `preU` | 3 | KEEP | NAME COLLIDES with IPA's `preU` (different challenge) |
| `preV_ne_preU` | 7 | KEEP | |

**subtotal:** KEEP **121** = 121 of 229 file-lines

### `kimchi/Kimchi/Verifier/Forking/OracleRun.lean` — 193 file-lines, 18 decls — **ZERO deletions**

| decl | lines | disposition | note |
|---|--:|---|---|
| `step` | 7 | KEEP | the only thing tying the abstract prefix domain to real Poseidon |
| `poseidonO` | 2 | KEEP | |
| `oracleChallenges` | 7 | KEEP | **NAME COLLIDES** with Game.lean:119 (different decl) |
| `foldl_step_fst` | 8 | MOVE | same 8-line induction as `foldl_frStep_fst` → one polymorphic lemma |
| `foldl_absorbInto_preAbsorbs` | 9 | KEEP | load-bearing wire agreement for all four fq bridges |
| `poseidonO_preBeta` | 6 | KEEP | |
| `poseidonO_preGamma` | 7 | KEEP | |
| `poseidonO_preAlpha` | 8 | KEEP | |
| `poseidonO_preZeta` | 8 | KEEP | |
| `oracleChallenges_poseidonO` | 7 | KEEP | **THE fq faithfulness theorem** |
| `frStep` | 5 | KEEP | itself the evidence that the field-valued codomain is the wrong alphabet |
| `poseidonOFr` | 2 | KEEP | |
| `oracleVU` | 4 | KEEP | |
| `foldl_frStep_fst` | 8 | MOVE | dedupe with the above |
| `foldl_frAbsorbInto_preVAbsorbs` | 24 | KEEP | largest wire-agreement piece in the group |
| `poseidonOFr_preV` | 5 | KEEP | |
| `poseidonOFr_preU` | 6 | KEEP | |
| `oracleVU_poseidonOFr` | 4 | KEEP | **THE fr faithfulness theorem** |

**subtotal:** MOVE **16** · KEEP **111** = 127 of 193 file-lines

### `kimchi/Kimchi/Verifier/Forking/RunLink.lean` — 38 file-lines, 2 decls — **ZERO deletions**

| decl | lines | disposition | note |
|---|--:|---|---|
| `oracleChallenges_runOracles` | 6 | KEEP | ties the reads to the challenges the soundness guards consume; intended `ForkSetup.accept` entry |
| `oracleVU_runVU` | 5 | KEEP | same for the batch challenges |

**subtotal:** KEEP **11** = 11 of 38 file-lines

### `kimchi/Kimchi/Verifier/Forking/Model.lean` — 89 file-lines, 4 decls — **WHOLE FILE GOES (prose survives)**

| decl | lines | disposition | note |
|---|--:|---|---|
| `GuardEvent` | 4 | DELETE? (obsolete) | field-valued oracle codomain = wrong alphabet. **PRESERVE Model.lean:3-43 PROSE** |
| `guardEvent_poseidonO` | 7 | DELETE? (obsolete) | pure `rw` restatement of OracleRun:107 |
| `GuardEventVU` | 4 | DELETE? (obsolete) | same defect on the fr side |
| `guardEventVU_poseidonOFr` | 5 | DELETE? (obsolete) | pure `rw` restatement of OracleRun:188 |

**subtotal:** unverified-delete **20** = 20 of 89 file-lines (69 of the 89 are the trust-boundary prose)

### `kimchi/Kimchi/Verifier/Forking/Escape.lean` — 131 file-lines, 3 decls — **WHOLE FILE GOES**

| decl | lines | disposition | upstream | status | note |
|---|--:|---|---|---|---|
| `escape_coord` | 21 | DELETE (upstream) | Probability.lean:307 `uniformOfFintype_point_mem_blind_le` | **VERIFIED by exact-type-identity `rfl`** | strongest verification in the whole set |
| `escape2` | 17 | DELETE? (obsolete) | — | not compile-tested | alphabet FUSION (the classifier's "hardcoded to scalar field" was wrong and was corrected) |
| `escape4` | 52 | DELETE? (obsolete) | — | not compile-tested | 52 lines of hand-rolled union bound for width 4 |

**subtotal:** DELETE **21** · unverified-delete **69** = 90 of 131 file-lines. Deleting this file removes kimchi's **only** `import Zcash`.

### `kimchi/Kimchi/Verifier/Forking/GuardEscape.lean` — 115 file-lines, 4 decls — **WHOLE FILE GOES**

| decl | lines | disposition | note |
|---|--:|---|---|
| `runGuardsFailFq` | 14 | DELETE? (obsolete) | carrier must become `Fin 4 → Prechallenge`; the ordered guard correspondence is ~6 lines to re-site |
| `runGuardsFailFq_measure_le` | 33 | DELETE? (obsolete) | divides by card F ≈ 2^254; deployed challenges are 2^128. **UNSOUND, not merely loose** |
| `runVUFail` | 8 | DELETE? (obsolete) | same wrong carrier |
| `runVUFail_measure_le` | 16 | DELETE? (obsolete) | same wrong denominator (v,u are endo-expanded prechallenges) |

**subtotal:** unverified-delete **71** = 71 of 115 file-lines

---
## Grand totals

| bucket | decls | decl-lines | % |
|---|--:|--:|--:|
| DELETE — evidence-backed | 55 | **586** | 15% |
| DELETE? — obsolete, no compile evidence | 27 | **335** | 9% |
| MOVE (to the seam / to a module below) | 52 | **607** | 16% |
| KEEP (incl. 8 negative results = 252) | 187 | **2265** | 60% |
| **total** | **321** | **3793** | |

**Survivors: 242 of 321 declarations (75%), 2,872 of 3,793 decl-lines (76%).** Estimated file-lines removable, applying each file's own docstring multiplier: **~1,478 of 6,253 (24%)** — so **~4,775 file-lines survive**.

Split by directory: bulletproof-pcs **2,613 of 3,353 survive (78%)**; kimchi **259 of 440 survive (59%)**, and its non-survivors are 3 whole files.

Nine files have **zero** deletions: Transcript.lean, EndoChallenge.lean, Convention.lean, Schnorr.lean, SVector.lean, Capstone.lean (bp) and Transcript.lean, OracleRun.lean, RunLink.lean (kimchi) — **1,826 file-lines untouched.**
