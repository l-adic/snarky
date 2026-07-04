# Verifier sub-circuits: assembling the gate compositions upward

**Goal.** Go *up* from the per-gate composition proofs to whole **verifier sub-circuits** — the
operations a Pickles Step/Wrap circuit actually performs — by composing the gate results through
*dataflow* (one gate block's output feeds the next block's input, threaded by copy constraints),
and ultimately **bridge the in-circuit verifier to the protocol-level IPA soundness already proven
in `Kimchi.Commitment.IPA`**. That bridge is the point of the whole stack: it turns "a witness
satisfies the wrap-verifier circuit" into "an IPA opening was genuinely verified", reducing
recursion soundness to the four Pasta postulates.

**Definition of done, per rung** (the vertical-slice discipline): the Lean theorem, a real dumped
fixture the verified `check` accepts, and a `CheckReconstruction` case confirming the
reconstruction matches the dump. No rung ships proof-only.

## Rung 0 (done): the scale-and-combine term `p' = acc + [s]·T`

The atomic MSM term of the IPA opening check (`addComplete acc (scaleFast1 g s)`,
proof-systems `wrap_verifier`). Delivered as `Kimchi.Circuit.VarBaseMul.scaleCombine_sound` +
`fixtures/scale_combine_step.json` + a reconstruction case — the first genuine
gate-output→gate-input dataflow (`VarBaseMul` result into a `CompleteAdd` input), built on the
`Circuit.append` combinator.

The statement is the **full complete-add disjunction** — either the add's `inf` flag is set and
`acc + [s]·T = 0`, or the flag is clear and the output cells carry the affine sum. No branch is
hypothesized away: the vertical case is genuinely reachable (`acc = −[s]·T` is legitimate input)
and the theorem covers it. Likewise the init doubling's `inf = 0` is *derived*
(`Point.add_self_ne_zero`), not assumed, throughout the grounded VarBaseMul stack.

**Remaining caveat (= the work of Rung 1).** The reconstruction is a sub-window: the dump's 7
public rows are dropped, `acc` and the init are hypotheses, and the scalar is pinned via
`gateLadder` of the witness rather than the public register.

## Rung 1 (done): the fully-public statement (the real dump, whole, no slicing)

`Circuits/ScaleCombinePub.lean`: the whole dumped circuit reconstructed — 7 public rows, the init
`CompleteAdd` doubling, the `VarBaseMul` chain **embedded at row 8** (wires shifted,
`Satisfies.of_embed`), the combine, and the trailing `inf`-assert row. `scaleCombinePub_sound`
concludes purely over the public vector:

> `(pub 5, pub 6) = (pub 3, pub 4) + [s] • (pub 0, pub 1)` with
> `(s : F) = unshiftType1 (5m) (pub 2)` — up to the combine's flagged vertical case.

Everything Rung 0 hypothesized is derived from the circuit: the init `[2]·T` (doubling row), the
register init `n₀ = 0` (the dump's `inf`-into-register-column trick + the assert row), the scalar's
field image (`gateRegister_cast` + `gateLadder_eq_register`), every `y ≠ 0` (odd group order).
Remaining hypotheses: base/acc on the curve, the bit budget, and at full width the forbidden-band
exclusion on the witness's ladder. Validated: `CheckReconstruction`'s FULL case runs `check` on the
*unsliced* dump with its real `publicInputs` — accepts, and rejects a tamper. This is the statement
shape every later rung should have: **witness fully existential, conclusion over `pub` alone.**

## Rung 2 (done): the parametric `n`-term MSM

`Circuits/Msm.lean`: `msmCircuit m n` is built **recursively** — block `i` (rows
`[i·(2m+2), (i+1)·(2m+2))`) is an init doubling, the chain, and a combine whose first input is the
previous combine's output; `msmCircuit m (n+1) = (msmCircuit m n).append (block n)`. `msm_sound` is
a structural induction: `of_append` hands the prefix to the IH, `of_embed` projects the last
block's chain, and `blockStep` (init doubling → `scaleFast1` → combine) advances the accumulator:

> the last combine's output cells carry `acc + ∑_{i ≤ n} [sᵢ]·Tᵢ`.

Per-block hypotheses mirror the single-term theorems; each combine's `inf = 0` is a hypothesis
(an `n`-fold statement under flagged verticals would enumerate first-failure prefixes — the
per-term vertical case is `scaleCombine_sound`'s disjunction). Validated:
`fixtures/msm2_step.json` (a real 2-term MSM dump — uniform contiguous `2m+2`-row blocks, as the
circuit assumes) is accepted by `msmCircuit 51 2` and rejects a tamper. Canonical scalars
(`[0, order)`, sister field) compose via `exists_canonical_scalar` as in #6.

## Rung 3: the endo side — and the sibling-consistency theorem

Two results:
- **`addComplete (endo q c) delta` — done** (`endoCombine_sound` in `EndoMulStep.lean`): the
  `EndoMul`-result→`CompleteAdd` pairing, full complete-add disjunction, validated against
  `fixtures/endo_combine_step.json` (`emCombCircuit 32`, rows 10–43).
- **EndoScalar ↔ EndoMul consistency — done** (`Circuits/EndoSibling.lean`,
  `pallas_sibling_consistency`): an `EndoMulScalar` run and an `EndoMul` chain processing the
  **same crumb stream** produce `[s]·T` with `(s : F) = a₈·λ + b₈` — the scalar multiplied onto
  the point is the very field element the scalar run computed, both circuit soundness results
  joined at `EndoScalar.toField` instantiated at the concrete `pallas_lam`. The crumb-stream
  equality is the honest interface hypothesis; discharging it from one squeezed challenge's
  decomposition rows is the Fiat–Shamir rung's job.

## Rung 4 (done): Fiat–Shamir inside the proof

`Circuits/FiatShamir.lean`: the whole transcript-to-challenge pipeline reconstructed from a real
dump (`fixtures/fiat_shamir_step.json`) — a Poseidon sponge over the public inputs, the squeezed
state split as `sq = lo + 2¹²⁸·hi` (a double-`Generic` truncation row), and the 128-bit challenge
`lo` decoded by an `EndoMulScalar` block whose final register is copy-wired to `lo`.
`fiatShamir_sound` concludes over the public vector: the sponge output (`chainPerm coeffs
(pub 0, pub 1, pub 2)` — a *function of the inputs*) equals `nReconstruct (crumbs) + 2¹²⁸·hi`,
and `pub 3 = toField (crumbs) vesta_lam` — the challenge is **derived**, not hypothesized. This is
the discharge path for Rung 3b's crumb-interface hypothesis.

Two by-products: `Satisfies.of_embed'` (the generalized embedding — a block's self-looped cells
may carry the host's own pin wires), and a **checker strengthening**: reconstructing the dump
exposed that the Generic checker ignored the second gate of kimchi's double generic row
(`eval2` now conjoined into `rowHolds`; all fixtures re-validated under the stronger checker).

*Fidelity gap*: `hi`'s range is unconstrained (aliasing mod `p`); the real protocol's challenge
canonicity needs a range check on `hi` — a second decomposition block, mechanical to add.

## Rungs 5–6 (done): the circuit ↔ commitment-layer IPA bridge

`Circuits/IpaBridge.lean`. The meeting point is `recombine` — the verifier's recombined commitment
`Q = P + v•U + ∑ⱼ (uⱼ⁻¹•Lⱼ + uⱼ•Rⱼ)` — which is *exactly* a `2k`-term MSM. Two pieces of glue make
the layers meet: the point group becomes a **module over its scalar field**
(`Module (ZMod W.order) W.Point` via `AddCommGroup.zmodModule` from `order_smul` — this is where
the 2-cycle lives, `ZMod (Vesta.order) = PallasBaseField`), and the circuit's ℤ-scalars cross by
`Int.cast_smul_eq_zsmul`, per-block cast hypotheses pinning each ladder scalar to a challenge or
its inverse.

- **Rung 5** (`msm_recombine`): a satisfying witness of the `2k`-block MSM circuit — accumulator
  `P + v•U`, block bases the cross-commitments, block scalars casting to `u⁻¹/u` — carries
  `recombine σ P v u lr` in its output cells, verbatim in the commitment layer's vocabulary.
- **Rung 6** (`circuit_ipa_soundness`, the capstone): the circuit-derived `Q`, the asserted
  Schnorr equation over the output cells (its sides are further scale-and-combine blocks of the
  Rung 0–4 shapes; stated in point form), and the `sg`-check give `VerifierAccepts`; then
  `ipa_soundness` — under the commitment layer's own stated Fiat–Shamir rewinding hypothesis —
  yields `∃ a r, openingRelation σ P x v a r`. **Circuit satisfaction has become knowledge
  soundness**, over the four Pasta postulates (plus `FiatShamirTree`, the commitment layer's
  declared trust boundary).

*Remaining fidelity work*: instantiate the outer Schnorr sides as their own reconstructed blocks
(mechanical, the same shapes), and a full `ipaFinalCheckCircuit` dump once the Pickles test
context is pluggable into the dumper.

## Cross-cutting upgrades

- **Close the reconstruction seam.** Fixture gate lists are concrete data: generate each fixture's
  gate array as a Lean term and prove `fixtureGates = (reconstruction).gates` by `decide`/`rfl` —
  turning `CheckReconstruction`'s empirical accept/tamper run into a kernel-checked equality (keep
  the runnable as CI smoke for the *witness* side). After Rung 1 removes slicing, this is plain
  array equality.
- **Completeness axis.** Every fixture is already an *empirical* completeness witness (the honest
  solver satisfied the circuit). Formal `complete_*` theorems for sub-circuits (chainBuild-style
  honest witnesses) are worth adding at Rung 1 and Rung 6, where "the verifier circuit is
  satisfiable for every valid proof" is part of the recursion story.
- **Derive the last per-point hypotheses at Pasta.** `hy1 ≠ 0` (input-1 of a complete add) is
  refutable at the Pasta curves from the odd prime group order (a `y = 0` point would be
  2-torsion); deriving it would leave the base/`acc` nonsingularity as the only genuinely external
  facts.
