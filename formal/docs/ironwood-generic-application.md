# Applying ironwood's forking machinery generically (IPA now, kimchi next)

Pin: `zcash/ironwood` `83a98f7f`, at `formal/.lake/packages/Zcash`.

Every claim of the form "upstream applies at our types" is a compiled example in
`bulletproof-pcs/scripts/check_ironwood_generic.lean`, run by
`bulletproof-pcs/scripts/check_ironwood_generic.sh`. Each is discharged by `exact`ing an upstream
declaration; nothing there is proved locally, and **no patch is applied to the pin**.

## 1. Result

The forking tower splits in two, and the split is not where the module names suggest.

Everything from the game statement down to the per-round escape pricing is generic in the *oracle
alphabet*: it asks for `Fintype`, `Nonempty`, `Zero`, `DecidableEq` and nothing else. It therefore
instantiates verbatim at our 128-bit prechallenge alphabet, and the error divides by `2 ^ 128`.

Ironwood's own *application* of that machinery — `Forking/Adversary/Algebraic.lean`, 2,436 lines —
is monomorphic at `VestaG`/`Fp` and their halo2 `Shape`/`VerifyingKey`. **We do not need it.** Our
route consumes the generic layer directly and exits through the certificate kernel
(`deployed_forking_tree` → `deployedToAcceptVWitnessCore` → `ipa_extractV`), which our frozen
`Forking/Capstone.lean` already assembles. So the reuse surface is patch-free.

The one thing we must write is the seam, and it is one structure (§4).

## 2. Genericity map (measured)

Occurrences of `VestaG`, of `Fp`, and of generic curve binders:

| Layer | Modules | Lines | `VestaG` | `Fp` | generic `G` |
| --- | --- | --- | --- | --- | --- |
| combinatorics / probability | `Forking/{Tree,Ordering,Probability,KnowledgeError}` | 1,126 | 0 | 0 | — |
| oracle model | `Forking/Adversary/{OracleComp,DomainReduction,Adaptive}` | 2,057 | 0 | 25 | 3 |
| run accounting | `Forking/Adversary/{ExpectedRuns,ExpectedRunsPoly}` | 1,168 | 0 | 0 | 1 |
| tree extraction | `Forking/{Extractor,Assembly}`, `IpaSoundness` | 693 | 0 | 0 | 3 |
| recursive extractor | `Forking/Adversary/Recursive` | 1,425 | 0 | 5 | 0 (46 `F`) |
| legacy rewinding | `Forking/Rewind` | 552 | 0 | 104 | 1 |
| **their application** | `Forking/Adversary/{Algebraic,PreIpa,Provenance}` | 3,522 | **266** | 480 | 30 |
| deployed endpoints | `Vesta`, `Main`, `KnowledgeSoundness` | 987 | 55 | 176 | 4 |

`Algebraic.lean` alone: 259 `VestaG`, zero curve binders. Its monomorphism rests on nothing — the
only Vesta-specific term in the file is `local instance : Inhabited VestaG := ⟨0⟩` (:19), and the
four declarations it imports from the curve-specific `Soundness/Vesta.lean` are already generic
where it matters: `evalVector_zero` (:153, `{F} [Field F]`), `adjustedWitness` (:157, no curve),
`commit_adjustedWitness` (:161) and `sum_getD_single` (:256), both `{G} [AddCommGroup G]
[Module Fp G]`. The Orchard-specific imports from `AGM/ProbabilityVesta.lean` feed only the
URS-identification *variants* of the endpoints.

Three parameters are fused into one type in their glue (`computedDeployedAlgebraicInstance`,
`Algebraic.lean`:669): the curve; the challenge alphabet, since `O : … → Fp` makes every bound
divide by `Fintype.card Fp`; and the pre-IPA challenge count, a literal `10`/`Fin 11`. Unfusing
those would be three upstream PRs. We take none of them, because the layer beneath the fusion is
already generic in all three.

## 3. What applies at our alphabet, verified

`Pre := Fin (2 ^ 128)` carries `Zero`, `DecidableEq`, `Fintype`, `Nonempty`. With those:

| upstream declaration | location | our use |
| --- | --- | --- |
| `PrefixDecode` | `Adaptive.lean`:15 | transcript round/chain bookkeeping; no alphabet arithmetic |
| `fsWinsFull` | `Adaptive.lean`:30 | **the game.** Zero instance binders; `m` pre-IPA and `k` forked reads are already parameters |
| `nextForkChallenge` + `_isSome_of_good`/`_output_fresh`/`_output_attempt`/`_other_good_mem_rest`/`_two_more` | `Recursive.lean`:242, :258, :323, :347, :285, :417 | the sampling-without-replacement scanner |
| `ThreeForkSuccess`, `recursiveForkEscape`, `_subset_triple` | `Recursive.lean`:168, :174, :179 | the per-round escape set is 3 points |
| `RecursiveForkTape.toCoins_complete` | `Recursive.lean`:147 | discharges the scanner's `hcomplete` |
| `RecursiveForkReached`, `_child`, `RecursiveRunHistory` | `Recursive.lean`:1063, :1074, :780 | coin-tree traversal |
| `escapesDuringC_measure_le'` | `OracleComp.lean`:728 | per-run pricing; codomain is a bare `Fintype` |
| `uniformOfFintype_toOuterMeasure_triple_le` | `Probability.lean`:339 | the `3 / \|Pre\|` per round |

Two facts settle the architecture:

**Our game is already theirs.** The frozen `Wins` (`Game.lean`:129) equals `fsWinsFull` at `m = 0`
by `Iff.rfl` — no bridging lemma. So one statement serves bare IPA (`m = 0`) and kimchi (`m > 0`),
and the win condition stays `VerifierAcceptsAt`, the wire verifier.

**Assembled, these give the endpoint bound with `m` free.** `shared_failure_measure_le` in the
check file derives `≤ (Q + N) * (3 / 2 ^ 128)` for an `fsWinsFull` game at arbitrary `m`, from
upstream names only. `m` costs nothing in the bound: only the `N` forked prefixes are completed.

**Correction to a premise this project carried.** `RecursiveForkReached` was believed to carry a
gratuitous `[Field F]` from `Recursive.lean`'s section line, forcing our local restatement. It
carries **no instance binders at all** — Lean includes a section variable in a `def` only by use,
and the `omit` at :1072 serves the adjacent *theorem*. Verified by instantiating at a payload
structure with no algebra (check file §8). `Game.lean`:612/623/1052 are deletable today,
patch-free. Field coupling in that file is real only in `recursiveAlgebraicForkFrom` (:507), which
uses `u⁻¹` at :557 — correct and unavoidable, since inversion happens on the *expanded* challenge.

## 4. The seam: one structure, two instantiations

```lean
/-- The forked-slot challenge map. Both fields are THEOREMS at Pasta, never assumptions. -/
structure Alphabet (F Q : Type*) where
  expand  : Q → F
  inj     : Function.Injective expand
  ne_zero : ∀ q, expand q ≠ 0
```

Ironwood's code is the instance `Q := F`, `expand := id`. Our instance is proved:
`Prechallenge` (`Deployed.lean`:90), `expandPre` (:99),
`expandPre_{vesta,pallas}_{injective,ne_zero}` (:105/:110/:116/:120), from
`endoExpand_{vesta,pallas}_{injOn,ne_zero}` (`EndoChallenge.lean`).

Injectivity is the *only* property the counting needs: the extractor's bad event is "the expanded
challenge lands in a set of at most 3 field elements", whose preimage under an injective `expand`
has at most 3 elements of `Q`, so the per-query fraction is `3 / Fintype.card Q`. Nonvanishing is
what deletes the zero-slice summand (`fsAdvantageFull_zero_slice_le`, `Adaptive.lean`:37)
altogether: no expanded challenge is ever `0`, so all `m` copies drop out.

Around it, `ForkSetup F G T Q Pf m` carries what a protocol supplies: the `m` pre-IPA prefixes with
a **per-index** expansion `expandPre : Fin m → Q → F` (kimchi needs this — β,γ are a plain 128-bit
cast, `FqSponge.lean`:113, while α,ζ,v,u are endo-expanded, :132), the plonk-guard bad sets with a
cardinality bound, the `σ.k + 1` forked prefixes with `DecodesFromPrefixes`, the claim and its AGM
root representation, the wire `accept` with its faithfulness equation, and upstream's
`stable`/`stable_update` freeze slots. The endpoint has two additive summands:

```
≤ (Q₀ + σ.k + 1) * (3 / |Q|)      -- extraction: exactly today's Game.lean:1447 bound
  + (Q₀ + m)     * (bPre / |Q|)   -- plonk guards: identically 0 at m = 0
```

Instantiation (a), bare IPA at `m = 0`, is a record literal over declarations `Deployed.lean`
already contains; `extract` at `m = 0` is definitionally `deployedExtract` (:775), and
`failure_measure_le` there is the single remaining `sorry` at `Deployed.lean`:812, whose route is
`wireWins_iff_wins` (:548) forward, then this theorem, then `card_prechallenge` (:95).

Instantiation (b), kimchi at `m = 6`: phase 2 is byte-identical, because kimchi's opening proof
*is* `Bulletproof.Ipa.Proof` and its verifier ends in `Ipa.verifyFrom` (`Kimchi.lean`:513). Only
phase 1 and `accept` are new. Node type `Tfq ⊕ Tfr`, one finite structured type per sponge — never
`List`, which admits no `PMF.uniformOfFintype`.

## 5. Consequences for our tree

**Deletions, patch-free (~385 lines of `Game.lean`).** The `scanFork` family (:248/:373/:402/
:427/:518/:573/:586) → upstream's scanner; `PreThreeForkSuccess`/`preForkEscape`/`_subset_triple`
(:465/:472/:479) → upstream's escape triple; `KimchiForkReached`/`_child`/`KimchiRunHistory`
(:612/:623/:1052) → upstream's traversal. `Game.lean`'s abstract section
(`variable {T Pre Pf}`, :114) is why these were re-proved — the fix is to carry `Zero`/`DecidableEq`
on the new module's section, not to patch upstream. One honest cost: upstream's escape set is
`{u | u = 0 ∨ good u}` with the *alphabet's* zero, so prechallenge `0` is rejected even though
`expandPre C 0 ≠ 0`. That is completeness-only, ≤1 point per round, already inside the `3/|Q|` the
round is charged. It must never be read as `expand 0 = 0`.

**Keeps, correctly.** `verifierAcceptsAt_of_deferred_delta` (:158) — the proof that dropping
commit-then-challenge makes the theorem false, hence why `dec` is a hypothesis; `DecodesFromPrefixes`
(:172); the Schnorr leaf level, since ours is `foldHalves` and upstream's is `foldGens`/`u⁻¹`; the
whole anti-vacuity section. Ironwood ships no wins-on-every-table companion for any of its fork
games, so every instantiation owes its own.

**Obsoletes in kimchi.** `Forking/GuardEscape.lean` — `runGuardsFailFq_measure_le` (:61) and
`runVUFail_measure_le` (:104) divide by `Fintype.card C.ScalarField` over a uniform *field* vector,
the wrong denominator for six 128-bit prechallenges — and `Forking/Escape.lean`'s `escape2`/`escape4`
(:58/:78), hardcoded to a uniform `Fintype F` codomain.

## 6. Residual constraints, stated

1. **Arity 3 is not negotiable.** `Extractable` (`Tree.lean`:28), `kerr` (:23),
   `escapeSet_subset_triple` (:66) and `uniformOfFintype_toOuterMeasure_triple_le`
   (`Probability.lean`:339) hardcode 3. The Schnorr wrapper and the plonk phase are absorbed as
   extra *rounds*, never by widening the fork.
2. **Efficiency is inherited, not fixed.** `nextForkChallenge_two_more` needs the tape to enumerate
   all `2 ^ 128` prechallenges — `Prop`-only, never `#eval`'d. Upstream's only unconditional run
   bound is `(2|F|+1)^k` (`reductionEfficient_exponential`, `Algebraic.lean`:1440); polynomial AFK
   is explicitly open (`ExpectedRuns.lean`:6-7).
3. **Never parameterize `kimchiVerify`'s FS source.** `kimchiVerify_reflects` discharges its
   obligations by bare definitional coercion (`Reflect.lean`:194, :206), which only checks cheaply
   while the 20 `run*` defs mirror the verifier body let-for-let. Desynchronizing them deep-unfolds
   the Poseidon folds into `maximum recursion depth` (measured twice). Build `kimchiVerifyAt` as a
   *separate* predicate over challenge values plus a faithfulness theorem.
4. **Deliberately unmodelled, to be declared at the seam:** the two base-field squeezes `t`
   (`FqSponge.lean`:91) and `fqDigest` (`Kimchi.lean`:194, non-injective — 0 on overflow). Neither
   is ever forked over, so both stay deterministic functions of the proof inside `accept`.

## 7. Adoptable independently

`Zcash/Meta/AxiomCheck.lean` (82 lines, importable) provides `assert_axioms d [+native]` and
`assert_computable d [+choice] [+native]`, the latter failing the build unless `d` is a plain `def`.
`Zcash/TrustBoundary.lean` (356 lines) is their whole census in one file. Our "extractors are
computable" and "no new axioms" invariants are enforced today by shell scripts plus one `#eval`
fixture; these make them per-declaration build obligations.
