# The standard-model / forking-lemma soundness line (removed — recovery record)

This document records a self-contained development that was **deleted** from the `Kimchi`
package on branch `kimchi-cut-standard-model` (step 1 of the kimchi reorganization; see
`kimchi-reorg.md`). It is preserved here so the argument can be reconstructed from git if a
standard-model soundness statement is ever wanted.

## Why it was cut

The kimchi verifier-soundness formalization has **one terminal theorem** (user decision,
2026-07-15): the AGM reading `kimchi{Vesta,Pallas}_run_sound_algebraic_ft` — for an
*algebraic* prover (one that supplies SRS-basis representations of what it commits), a
single accepted run gives `∃ wTab, Satisfies idx (pubView idx pub) wTab`. Its trust closure
is `propext / Classical.choice / Quot.sound + kimchi_fiat_shamir_{curve} + CompElliptic
native-decide certificates` — nothing else.

The development below is the **standard-model / forking-lemma alternative**: it removes the
AGM representations at the cost of a *rewinding extractor*, reached either as a soundness-error
count over the challenge space or as a density-to-grid forking argument. It is internally
self-contained — **nothing on the AGM/terminal path consumes any of it** (verified by grep +
a dead-code pass over `roots.txt` before removal) — and it is the strictly harder,
research-level statement the user chose *not* to pursue. Keeping it as live, gated API
implied a second supported soundness endpoint. It is therefore removed, with this record.

`Quotient/SchwartzZippel.lean` is **not** part of this cut: it is the shared counting
foundation the whole PIOP and the AGM path rest on. Only the forking-specific counting
toolkit (`Quotient/Rectangle.lean`) and the two Capstone sections below were removed.

## Footprint (what was deleted)

- **`Kimchi/Verifier/Capstone.lean`** — the two sections `## The soundness error (capstone
  1.4)` and `## The grid from density (forking stage (a))`, i.e. everything between the run-level
  corollaries (`kimchi{V,P}_run_sound`) and the AGM section `## The algebraic-prover corollary`.
  Declarations removed:
  - private counting helpers `card_filter_pair`, `card_filter_head`, `card_filter_pos1`–`pos4`,
    `card_filter_last_eq` (the tuple-cardinality slice bounds);
  - `soundnessErrorBound` (the error constant), `kimchiBundle_sound_error`,
    `kimchiVesta_sound_error`, `kimchiPallas_sound_error` (the soundness-error reading);
  - `batchAcceptSet` (the strategy's accepting `(ξ, r)` set), `kimchiBatchAcc_of_density`,
    `kimchiVesta_sound_density`, `kimchiPallas_sound_density` (the density-to-grid capstones).
  - The `import Kimchi.Quotient.Rectangle` line.
- **`Kimchi/Quotient/Rectangle.lean`** — the whole file (the forking-lemma counting toolkit,
  imported **only** by Capstone's density section). Declarations: `rowDeg`, `colSet`, `rowsFor`,
  `mem_colSet`, `mem_rowsFor`, `card_colSet`, `sum_rowDeg`, `key_ineq`, `double_count`,
  `exists_rectangle`, `rowSlice`, `mem_rowSlice`, `card_rowSlice`, `heavyRows`, `mem_heavyRows`,
  `card_heavyRows`, `card_pow_fiber_le`, `exists_distinct_powers`.
- **`kimchi/roots.txt`** and **`kimchi/scripts/check_axioms.lean`** — the roots
  `kimchi{Vesta,Pallas}_sound_error`, `Kimchi.Quotient.exists_rectangle`,
  `kimchi{Vesta,Pallas}_sound_density`, `Kimchi.Quotient.card_heavyRows`,
  `Kimchi.Quotient.exists_distinct_powers`, `Kimchi.Quotient.mem_heavyRows`,
  `Kimchi.Quotient.mem_rowSlice` and their manifest comment blocks.
- **`Kimchi.lean`** — the `import Kimchi.Quotient.Rectangle` aggregation line.

## What each root stated

### The soundness-error reading (capstone 1.4)

`soundnessErrorBound n zkRows = 7·(n−zkRows) + 7·(n−zkRows) + n·(gateAlphaCount +
permAlphaCount − 1) + degreeBound n + 2` — the union-bound constant collecting the four bad-set
sizes of `kimchiBundle_sound` plus the two degenerate `ζ` values.

`kimchiBundle_sound_error` collapsed `kimchiBundle_sound`'s four separately-quantified bad sets
into **one** bad-tuple set over the challenge space `F⁴`:

> `∃ badTuples : Finset (F×F×F×F), badTuples.card ≤ soundnessErrorBound n zkRows · |F|³ ∧
> ∀ β γ α ζ, (β,γ,α,ζ) ∉ badTuples → [the FiatShamirTreeB grid + acceptance + quotient
> identity] → ∃ wTab, Satisfies idx pub wTab`

i.e. all but a `soundnessErrorBound / |F|` fraction of the `|F|⁴` challenge tuples are good,
with **no** residual side conditions (memberships, `ζ` guards, and the degree bound are all
absorbed into `badTuples`). The quotient strategy `tOf : F→F→F→Polynomial F` is *adaptive* (a
function of `(β,γ,α)`, mirroring the Fiat–Shamir commit-order), with degree bound `htdeg` a
strategy-level hypothesis. Pure counting — no probability library. `kimchi{Vesta,Pallas}_sound_error`
were the deployed-verifier instances (through the `kimchiBatchAcc_bundle_{curve}` bridge over
`Fp`/`Fq`), carrying `kimchiVesta_sound`'s trust story verbatim (the grid `T`, per-node
`poseidon_fiat_shamir_{curve}`, DL-binding).

The proof of the collapse: six `Finset.card_filter`/`Fintype.sum_prod_type` slice bounds
(`card_filter_pos1`–`pos4` for the four challenge axes, `card_filter_last_eq` twice for the two
degenerate `ζ` values), assembled by `Finset.filter_or` + `Finset.card_union_le`, matched to
`soundnessErrorBound` by `ring`.

The run-level corollaries deliberately did **not** carry this reading: a fixed run's sponge
outputs are not random, so reading the error as a probability over a real run *is* the
Fiat–Shamir heuristic itself.

### The density-to-grid forking argument (forking stage (a))

`batchAcceptSet C σ cs es x₀ x₁ P = { (ξ,r) | Ipa.verify C σ (mkInput … (P ξ r)) = true }` —
the accepting `(ξ,r)` pairs of a batch-opening *strategy* `P : ξ → r → Ipa.Proof` for one fixed
batched claim `(cs, es)` at the two points. Membership is deployed acceptance itself (a decidable
`Bool` equality, never reducing `Ipa.verify`).

`kimchiBatchAcc_of_density` was the forking-lemma combinatorial stage, **proved without any new
axiom**: a strategy accepted on a dense enough accepting set yields the 43×2 special-soundness
extraction grid `KimchiBatchAcc` (with `T.zC = zC` by construction). The density hypothesis was

> `42 · |F| · (|F| · (|F| − 1)) < |acc| · (|acc| − |F|)`   where `acc = batchAcceptSet …`

— the `exists_rectangle` threshold at `K = 43` (42 = 43−1), asking accepting density `≳ √(42/|F|)`
(about `2⁻¹²⁴` at the `≈ 2²⁵⁴` Pasta scalar fields). `kimchi{Vesta,Pallas}_sound_density` composed
this with `kimchi{Vesta,Pallas}_sound` to conclude satisfiability from strategy + density +
DL-binding + key-correspondence (Fiat–Shamir still via the poseidon axioms, per grid node).

### The counting engine (`Quotient/Rectangle.lean`)

Generic finite-combinatorics over a `Finset (α × β)`, the Kővári–Sós–Turán / heavy-rows idea:

- `exists_rectangle S K h` — a dense subset of a product contains a `K × 2` combinatorial
  rectangle (`K` rows sharing an ordered column pair). Proof: `double_count` lower-bounds the
  ordered-distinct-column-pair count via Cauchy–Schwarz over the row degrees (`key_ineq` +
  `sum_rowDeg`), then pigeonhole over the `|β|·(|β|−1)` ordered pairs. Threshold
  `(K−1)·|α|·|β|·(|β|−1) < |S|·(|S|−|α|)`.
- `heavyRows S θ` / `card_heavyRows` — the rows of degree `> θ`, Markov-bounded from total density.
- `card_pow_fiber_le` / `exists_distinct_powers` — `n`-th-power fibers are root sets (`≤ n`), so
  `K` distinct `n`-th powers exist outside any small excluded set; the distinct-challenge selection
  feeding the transcript tree.
- Supporting: `rowDeg`, `colSet`, `rowsFor`, `rowSlice`, and their membership/cardinality lemmas.

## How to recover

`git show <this-branch>^:kimchi/Kimchi/Quotient/Rectangle.lean` restores the engine; the two
Capstone sections and the roots/`check_axioms.lean`/`Kimchi.lean` entries are in the same commit's
parent. The development depended only on `SchwartzZippel` (surviving), `kimchiBundle_sound`,
`kimchi{Vesta,Pallas}_sound`, and the `kimchiBatchAcc_bundle_{curve}` bridges — all still present.
