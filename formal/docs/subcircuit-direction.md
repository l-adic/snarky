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

## Rung 1: the fully-public statement (the real dump, whole, no slicing)

The dumped `scale_combine` circuit pins **everything** to public inputs (verified against the
fixture's wires): rows 0–1 = the base `T` → the init doubling row 7; row 2 = the scalar → the
**final register `n'`** (cell `(108,5)` — the Type1 shifted value); rows 3–4 = `acc` → the
combine's inputs; rows 5–6 = **the output** → the combine's `x3,y3`. So the honest target is a
relation purely over the public vector:

> For any witness satisfying the *entire* reconstructed circuit (public rows + init doubling +
> chain + combine): `(pub 5, pub 6) = (pub 3, pub 4) + [unshiftType1 (pub 2)] • (pub 0, pub 1)`.

Everything needed exists: `AddCompleteStep`'s public-row extraction, `vbmCircuitGrounded`'s init
doubling, `scalarMul_shifted`/`unshiftType1` for the register form, `exists_canonical_scalar` for
the sister-field scalar, and `Circuit.append` for the assembly. This sets the statement shape every
later rung should have: **witness fully existential, conclusion over `pub` alone.**

## Rung 2: the parametric `n`-term MSM

`acc + ∑ᵢ [sᵢ]·Gᵢ` — not a 2-term toy; the machinery is already parametric in the chain length, so
go straight to `n` blocks folded through the adds (add `i`'s output wired to add `i+1`'s input-1,
its nonsingularity *produced* by the complete-add case split, the Rung-0 thread iterated). This is
`combined_polynomial` / the Lagrange-base MSM (`PublicInputCommit`). State the scalars canonically
(`[0, order)`, sister base field) via the #6 lift.

## Rung 3: the endo side — and the sibling-consistency theorem

Two results:
- **`addComplete (endo q c) delta`** (IPA.purs:441): the `EndoMul`-result→`CompleteAdd` pairing,
  same shape as Rung 0.
- **EndoScalar ↔ EndoMul consistency.** There is no wire dataflow between them (they are siblings
  consuming the same squeezed challenge) — but that *is* the theorem: in a circuit containing an
  `EndoMulScalar` run and an `EndoMul` chain wired to the **same challenge crumbs**, the point
  result is `[toField(challenge)]·T` for the *very field element the circuit computed*. Both Lean
  developments already meet at `EndoScalar.toField` (`pallas_endoMul`'s scalar is stated in it), so
  this is a join of two proven results at a shared public challenge — the verifier fact "the scalar
  used on points equals the scalar used in-field".

## Rung 4: Fiat–Shamir inside the proof

`PoseidonStep` gives the transcript gate. Compose it: challenges squeezed from an in-circuit
Poseidon sponge feed the EndoScalar/EndoMul blocks of Rung 3. The statement upgrades from "for any
challenge `c`" to "for the challenge *the transcript derives*" — the first piece of in-circuit
Fiat–Shamir soundness, and the last gate family not yet composed by dataflow.

## Rung 5: `ipaFinalCheckCircuit`, assembled

The IPA final check (`Pickles/IPA.purs:375`) is exactly Rungs 2 + 3 + 4 stitched: sponge-derived
challenges, endo scalar-muls, the challenge-polynomial MSM, complete adds. Assemble, don't re-prove.

## Rung 6 (the capstone): the bridge to `Kimchi.Commitment.IPA`

The repo already has protocol-level IPA soundness (`ipa_soundness`, `ipaRelation_of_acceptV`,
multi-poly/multi-point batching). The bridge theorem:

> Any witness satisfying the (reconstructed, fully-public) IPA-final-check circuit yields an
> accepted `Kimchi.Commitment.IPA.Verify` run on the public commitments/evaluations — so the
> commitment-layer soundness applies, and the claimed evaluations are binding.

This connects the two existing bodies of proof (circuit layer ↔ commitment layer) into one
statement: **circuit-satisfaction ⇒ cryptographic verification**, over the trusted base of the
four Pasta postulates. It is the reason the sub-circuit direction exists.

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
