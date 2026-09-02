# The probabilistic soundness line (retired — recovery record)

This document records a development that was **deleted** from the `kimchi` and
`bulletproof-pcs` packages. It follows the precedent of `standard-model-line.md`: the tree is
preserved in git, and this file is what lets someone reconstruct it, or decide not to,
without re-deriving the reasoning.

## What was retired, and why

The forking / knowledge-soundness layer: per-curve knowledge soundness of the deployed kimchi
and IPA verifiers in the random-oracle model, over the forking extractor, with the
discrete-log hardness of the Pasta curves as a hypothesis of the statements.

It was retired because **it came up inconclusive**. The endpoints were real theorems with
clean axiom closures, but what they bought was structural rather than concrete: the
extractor's cost bound (audit O-1a) is exponential in `k` and in the challenge domain, so at
the discharged `R = (2·2¹²⁸ + 1)^(k+1)` a reduction permitted that many oracle calls solves
Pasta discrete log outright, leaving `hHard` satisfiable only at `ε ≈ 1`. The conditional
average that would have fixed this (audit O-1b) rests on a fork-spread hypothesis
(`KimchiForkSpreadFamily`) that **nothing in the tree witnessed at deployed parameters**, and
the abstract `σ₀ = 4` exhibit over `Pre = Fin 5` does not transfer. So the average branch was
reachable only at the same worst-case number. ε was posited, never derived from a time bound.

That is a lot of machinery — ~20,000 lines and a dependency on `Zcash/ironwood` — standing
behind a claim that does not do the work its name suggests. Retiring it removes 28% of the
tree's built bytes and one git dependency, and removes the standing risk that a reader takes
the endpoint names at face value.

## What is left, and what it now means

`Kimchi.Verifier.kimchiVerify` and `Bulletproof.Ipa.verify`/`verifyFrom` remain, and are
**specifications**: the transcriptions proof-systems' `kimchi/src/verifier.rs` and
`poly-commitment` are measured against, and the anchors a circuit implementation is proved
faithful to. `Kimchi/Verifier/Reflect.lean` remains, naming every intermediate of
`kimchiVerify`'s body as a closed form — those are the per-stage specs that a fragment of an
in-circuit verifier lands on, which is why they are rooted rather than deleted.

Nothing in the tree now claims, assumes, or needs: discrete-log hardness, a random-oracle
idealisation, or any cryptographic hypothesis. `Schnorr/` is the exemplar of the statement
shape that replaces the retired one — *relative* faithfulness, "every satisfying valuation of
the compiled circuit certifies the wire verifier", which needs no soundness result about the
wire verifier and asserts none.

## Where the tree is

Full history, `formal/` on `main`:

| Commit | Subject |
| --- | --- |
| `55721550` | kimchi: the deployed verifier is knowledge-sound, per curve — no Fiat–Shamir axiom (#280) |
| `5591e023` | bulletproof-pcs, kimchi: prove the deployed extractor's worst-case cost bound (audit O-1a) (#283) |
| `a1e8a33c` | bulletproof-pcs, kimchi: conditional-average extractor cost, knowledge-soundness twin endpoints (audit O-1b) (#285) |

Deleted in this change — 34 files, ~21,000 lines:

- `kimchi/Kimchi/Verifier/KnowledgeSoundness.lean` (the two per-curve endpoints, their
  conditional-average twins, the cost bounds, the AGM un-batching lemmas)
- `kimchi/Kimchi/Verifier/Capstone/{Algebraic,Reflection}.lean`
- `kimchi/Kimchi/Verifier/Forking/{Honest,Bridge,Transcript,OracleRun,RunLink}.lean`
  (`FSFaithful`, `wins_iff_kimchiVerify`, the honest-family anti-vacuity guards)
- `kimchi/Kimchi/Verifier/Reduction/{Soundness,Correspond,Binding}.lean`
- `bulletproof-pcs/Bulletproof/Forking/*` (12 files, incl. `Game.lean`, `Deployed.lean`,
  `KnowledgeSoundness.lean` — `ipa{Vesta,Pallas}_knowledge_sound`,
  `deployedExtract_failure_measure_le`)
- `bulletproof-pcs/Bulletproof/{Soundness.lean,Soundness/SingleOpening.lean,Reflection.lean}`
  (binding as no-DL-relation, single-opening extraction, the executable/abstract bridge)
- both packages' `scripts/check_locked_target.sh` + `locked_target.expected`, and
  `bulletproof-pcs/scripts/check_{extractor_computes,ironwood_generic}.{lean,sh}`
- the `Zcash/ironwood` require, from all three lakefiles

Ten planning documents went with it (`architecture.md` — "Kimchi soundness — target
architecture", a proposal for re-layering the proof that is gone; `locked-target.md`,
`minimum-support.md`, `w{2,3,5}-*-scope.md`, `agm-reuse-scope.md`,
`forking-consolidation-plan.md`, `ironwood-{refoundation-plan,generic-application}.md`).

The external-audit records
(`external-audit-report.md`, `external-audit-followup.md`, `statement-audit-*.md`) were
**kept**: they are the record of an outside engagement, and deleting them would destroy
provenance rather than dead weight. Read them as history — their open items O-1a/O-1b and the
standing invariants that protected the forking tree no longer describe this repository.

## The second pass: the ideal polynomial protocol

A follow-up cut removed the *idealized* protocol layer that sat between the arithmetization
and the retired endpoints — three files, 1,279 lines, 5.5 MB of olean:

- `Kimchi/Protocol/{Accepts,Equation}.lean` — `Accepts`, the polynomial verifier "stated with
  no reference to any commitment scheme," and its soundness `Protocol.sound`
- `Kimchi/Index/Degree.lean` — the degree accounting (`degreeBound`, `aggregate_natDegree_le`,
  `t_zH_natDegree_le`) that the quantitative ζ bound consumed

**Why.** `Accepts` models a verifier with oracle access to the prover's polynomials. The
deployed verifier is `kimchiVerify`, which opens commitments; the bridge between the two was
`Verifier/Reduction/*`, retired above. Without that bridge `Protocol.sound` is a theorem about
an object nothing else in the tree references.

**What was deliberately kept, after a first attempt cut too deep.** An earlier revision of
this pass also removed the arithmetization — `satisfies_iff_fullFamily_dvd`, copy soundness,
and the Schwartz–Zippel layer — on the grounds that the SZ argument was "counting dressed as
soundness." That was wrong, and it was reverted. `dvd_separation` is deterministic algebra: a
Vandermonde / too-many-roots argument concluding `Z_H ∣ aggregate(α, C) → ∀ k, Z_H ∣ C k` for
α outside an *explicit* finite set whose cardinality is proved (`card_badAlphas_le`, `≤
n·(K−1)`). No probability appears in any statement; the probabilistic reading is a remark. The
layer was orphaned when its consumers above it were cut — dead by reachability, not by
falsity — and those are different reasons to delete something.

So the tree keeps, and now roots explicitly:

- `Index.satisfies_iff_fullFamily_dvd` — the arithmetization, and the only result linking
  `Index.Satisfies` to the committed polynomial family
- `Index.satisfies_of_evalCheck` — the same at an evaluation check, which is what makes
  "verify at a single point" legitimate, with `card_bad{Alphas,Zetas}_le` rooted beside it as
  the anti-vacuity companions
- `Index.copy_soundness_of_dvd` and the GrandProduct multiset core — the permutation
  argument's own conclusion
- the index's derived columns, the column encoding, and the polynomial lift
  (`Lift.Argument.bridge`) — what the verifier's commitments commit to

Two fixture drivers replay this layer against production data (`check_index_fixture.sh`,
`check_perm_fixture.sh`) and pass.

## If it is ever wanted back

Recover the files from the commits above, restore the `Zcash` require in `lakefile.toml`,
`kimchi/lakefile.toml` and `bulletproof-pcs/lakefile.toml` (rev
`83a98f7fb3bcd8f87ddf0a459dcab96a782d91d8`), and restore the root imports, the two
`roots.txt` blocks, the two axiom-gate root blocks, and the CI steps this change removed.
Before doing any of that, read `external-audit-followup.md` §O-1b: the substance was open
when the tree was retired, and reviving the machinery does not close it.

## What replaces it

Nothing, deliberately. The next work on this tree is the in-circuit direction — proving
circuit implementations of the kimchi verifier faithful to `kimchiVerify` — for which see
`circuit-verifier-faithfulness.md` and the `schnorr/` package. That line is independent of
soundness in both directions: it neither assumes the wire verifier is sound nor establishes
that it is.
