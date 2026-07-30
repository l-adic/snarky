# W3 scope — the guard-escape engine (challenge-vector measure bounds)

**Status: IMPLEMENTED (branch `w3-guard-escape`) — all four §3 deliverables proven, no
sorries; §4's order of work was executed inline in one pass (the spine `escape_coord` closed
via `Equiv.piSplitAt` + `map_uniformOfFintype_equiv` + `uniformOfFintype_prod_fiber_bound`
exactly as designed, and the rest followed the pattern), so no Archon hand-off was needed.**

**SUPERSEDED — the deliverables were proved, then deleted in favour of the upstream
equivalents, so the declarations named below no longer exist.** Both files this document
designs are gone (`forking-consolidation-plan.md` step 1: `git rm Escape.lean +
GuardEscape.lean`), and `escape_coord` — the spine the banner above credits — occurs in **no**
`.lean` file in the tree. Its disposition is recorded in `forking-consolidation-plan.md`'s
ledger, in the row keyed `escape_coord` (`:748` as of this note): `DELETE (upstream)`, mapped to
`Zcash…Forking/Probability.lean:307 uniformOfFintype_point_mem_blind_le` and **verified by
exact-type-identity `rfl`** — the strongest verification in that whole ledger. So read §§1–4 as
the design record of a landed and then upstreamed result, not as a scaffold to build. The body's
line references are likewise historical and have not been re-checked (standing decision).

Child of `ironwood-refoundation-plan.md` §5/W3, successor to W2
(PR #273: the oracle model + run-level faithfulness). This document pins W3's design against
the *verified* signatures on both sides, records one deliberate restaging vs. the plan's
wording, and defines the scaffold.

---

## 1. What W3 must bound (verified inventory)

The terminal roots (`kimchi{Vesta,Pallas}_run_sound_algebraic_ft`) conclude
`RunBounds ∧ RunGuardImp` and take `hξ`/`hr` as hypotheses. The failure event W3 measures is
"some guard antecedent fails", with this exact structure (`Capstone/Reflection.lean:1010`):

| # | challenge | antecedent | set is a function of | card bound (source) |
|---|---|---|---|---|
| 1 | β | `∉ soundBadB idx runW` | nothing (challenge-free data) | `≤ 7(n−zk)` (`RunBounds.1`) |
| 2 | γ | `∉ soundBadG idx runW β` | β | `≤ 7(n−zk)` (`RunBounds.2.1`, ∀β) |
| 3 | α | `∉ soundBadA idx pubView runW runZ β γ` | β, γ | `≤ n(K−1)` (`RunBounds.2.2.1`, ∀βγ) |
| 4 | ζ | `∉ soundBadZ … β γ α (ftChunkAssembly …)` | β, γ, α | `≤ 9n` (`RunBounds.2.2.2`, ∀βγα, needs `t.natDegree < 7n`) |
| 5 | ζ | `≠ 1` | — | `1` |
| 6 | ζ | `≠ ω^(n−zk)` | — | `1` |
| 7 | v | `hξ : polyscale ∉ badXiOf σ aRef pointFn evalFn` | the fq outcome (pointFn/evalFn are ζ-derived) | `≤ 2(m−1)` (`card_badXiOf_le`) |
| 8 | u | `hr : evalscale ∉ badROf … polyscale` | fq outcome, v | `≤ 1` (`card_badROf_le`) |

Verified support:
- `runInput = runInputP … (runVU …).1 (runVU …).2` — so `hξ`/`hr` constrain exactly the
  `(v, u)` that W2's `oracleVU_runVU` pins to the fr prefixes; rows 1–4 constrain exactly the
  `runOracles` projections that `oracleChallenges_runOracles` pins to the fq prefixes.
- `RunBounds` is *already a conclusion* of the terminal roots — W3 consumes it as a hypothesis
  and stays root-free.
- Row 4's side condition: `ftChunkAssembly_natDegree_lt` (private, `Capstone/Algebraic.lean:352`)
  gives `natDegree < nt·2^k`; with `htpos`, `cp.tComm_le : nt ≤ 7nc` and `hk : nc·2^k = n` this
  yields `< 7n`.
- Rows 7–8: `card_badXiOf_le` / `card_badROf_le` (private, `Algebraic.lean:90/104`) — uniform in
  `x`/`E`/`ξ`, so they hold at the ζ-derived instantiations pointwise.
- **Three privates must be surfaced** (un-`private`, same norm as W2's `frSpec`):
  `card_badXiOf_le`, `card_badROf_le`, `ftChunkAssembly_natDegree_lt`.

## 2. The restaging (deliberate, vs. the plan's wording)

The plan states W3's deliverable as "the measure of **oracles** on which any antecedent fails".
That form cannot be stated at W3: the only uniform-table measure in the ironwood toolkit is
`PMF.uniformOfFintype (T → F)`, which **requires `Fintype T`**, and our transcript domain
(`List (KimchiTranscriptElt C)`) is infinite. Ironwood handles this at the *game* layer
(`DomainReduction`: `reachSet`/`restrictTo` over an `OracleComp` adversary's finite reachable
support) — i.e. exactly the machinery W4 assembles anyway. Restaging:

- **W3 = the challenge-vector escape engine**: measure bounds over
  `PMF.uniformOfFintype (Fin k → F)` — the distribution of the challenge *vector* itself.
  This is 100% of the counting content.
- **W4 = the table transport + game**: `uniformOfFintype_fresh_read_bound`
  (`Zcash…Forking/Probability.lean:156`) lifts a vector-level bound `hS` to the finite-domain
  table measure along the prefix injection `φ` — `hφ : Function.Injective φ` is discharged by
  W2's distinctness lemmas, `S`/`hS` by W3's events/bounds, and `choice` absorbs the adversary's
  other reads. The interface is exact; nothing in W3 is thrown away.

## 3. Design

### `Forking/Escape.lean` — generic sequential escape (FIRST `Zcash` import)

Concrete arities beat dependent-`Fin` generality (the consumers are one 4-chain and one
2-chain):

```
theorem escape2 (S₁ : Finset F) (S₂ : F → Finset F) {b₁ b₂ : ℕ}
    (h₁ : S₁.card ≤ b₁) (h₂ : ∀ x, (S₂ x).card ≤ b₂) :
    (PMF.uniformOfFintype (Fin 2 → F)).toOuterMeasure
      {χ | χ 0 ∈ S₁ ∨ χ 1 ∈ S₂ (χ 0)} ≤ (b₁ + b₂) / Fintype.card F

theorem escape4 (S₁ …) (S₂ : F → _) (S₃ : F → F → _) (S₄ : F → F → F → _) … :
    … {χ | χ 0 ∈ S₁ ∨ χ 1 ∈ S₂ (χ 0) ∨ χ 2 ∈ S₃ (χ 0) (χ 1) ∨ χ 3 ∈ S₄ (χ 0) (χ 1) (χ 2)}
      ≤ (b₁ + b₂ + b₃ + b₄) / Fintype.card F
```

Spine: outer-measure subadditivity for the union, then one lemma per coordinate —
`escape_coord`: the measure of `{χ : Fin k → F | χ i ∈ S (χ ∘ earlier)}` is `≤ b/|F|` when
every section has card `≤ b`. Proof by counting through
`uniformOfFintype_toOuterMeasure_set` (measure = card/|domain|) and a fiber count; ironwood's
`uniformOfFintype_prod_fiber_bound` is the model. Events over `Fin k → F` (not tuples) because
that is the exact shape `fresh_read_bound`'s `S : X → Set (ι → F)` consumes in W4.

### `Forking/GuardEscape.lean` — the run-level instantiation

- `runGuardsFailFq σ cvk cp pub idx aRef aT : Set (Fin 4 → F)` — rows 1–6, with the two ζ
  boundary points folded into row 4's set (`… ∪ {1, ω^(n−zk)}`, card `+2`).
- `runGuardsFailFq_measure_le` : given `RunBounds …` (+ `htpos`, `hk`, `tComm_le` for the
  degree side condition), measure `≤ (7(n−zk) + 7(n−zk) + n(K−1) + (9n + 2))/|F|` — by
  `escape4`.
- `runVUFail σ cvk cp pub aRef : Set (Fin 2 → F)` — rows 7–8 at the run's
  `pointFn`/`evalFn` (ζ-derived data enters as fixed parameters; chronology is respected
  because the fr event is stated *per fq outcome*, matching the fr sponge running after ζ).
- `runVUFail_measure_le` : measure `≤ (2(m−1) + 1)/|F|` at `m = (runInput …).commitments.size`
  — by `escape2`.

The events are `RunGuardImp`'s antecedents verbatim with the challenge *reads* replaced by the
vector coordinates — the exact `S`-families W4 hands to `fresh_read_bound`, whose `O ∘ φ`
instantiation then reconnects to `runOracles`/`runVU` through W2's `RunLink`.

### Trust surface

No new axiom, no `sorry` at landing, gate unchanged — W3 is theorems-only (measure bounds are
plain Mathlib probability over `PMF.uniformOfFintype`). The Poseidon-RO boundary (Option A)
is untouched; it is consumed only when W4 interprets these bounds as statements about the
deployed sponge.

## 4. Order of work

1. Un-private the three `Capstone/Algebraic.lean` lemmas (visibility only).
2. `Escape.lean`: statements + prove `escape_coord`/`escape2` inline (calibration — the
   counting reduction is the only genuinely new proof shape in W3); `escape4` likely
   Archon-able once the pattern stands.
3. `GuardEscape.lean`: statements; proofs are instantiation + arithmetic (Archon-able).
4. Gates: `lake build Kimchi` 0-sorry, axiom gate unchanged, `#print axioms` on the two
   measure lemmas = base axioms only. CI note: this adds the first `import Zcash…` to a built
   target, so CI starts compiling ironwood's `Forking/Probability` closure (already verified
   to build in-workspace during W1).
