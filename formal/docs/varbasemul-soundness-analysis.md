# VarBaseMul: soundness vs. completeness of the incomplete-addition guard

## TL;DR

The kimchi `VarBaseMul` (variable-base scalar multiplication) custom gate uses
**incomplete** elliptic-curve addition, which is undefined when an accumulator hits
`±T`. A `forbidden_shifted_values` check is supposed to keep that from happening. That
check is **incomplete** — the OCaml source flags it itself (`impls.ml:10`,
*"TODO: I think there are other forbidden values as well"*) — and we computed exactly
what it misses.

The headline result is that **the deployed circuit is sound** for the real Pasta
parameters. The incomplete check is a **completeness** (liveness) gap of probability
`≈ 2⁻²⁵¹`, not a soundness hole. Soundness comes from two facts that have *nothing to do
with the forbidden check*: the gate constraints themselves rule out one degeneracy, and
the circuit-field register bound rules out the other.

This corrects an earlier framing in which the incompleteness looked like a soundness
gap. The distinction turns entirely on telling apart two superficially-similar
degeneracies that have **opposite** consequences.

---

## 1. The gate and its precondition

Each `VarBaseMul` sub-step computes `out = (in − (2b−1)·T) + in` (i.e. `2·in ± T`) with
two **incomplete** chord-and-tangent additions, using two slopes `s₁, s₂`. Writing the
input accumulator `(xᵢ, yᵢ)`, target `T = (xT, yT)`, the gate's 21 constraints include,
per bit:

```
(#2)  (xᵢ − xT)·s₁ = yᵢ − (2b−1)·yT
(#3)  u² = t²·(xₒ − xT + s₁²)        with  t = 2xᵢ + xT − s₁²,  u = 2yᵢ − t·s₁
(#4)  (yₒ + yᵢ)·t = (xᵢ − xₒ)·u
```

`s₁` is the slope of the first addition; its denominator is `xᵢ − xT`. `s₂ = u/t` is the
slope of the second; its denominator is `t = 2xᵢ + xT − s₁²`. The gate is *correct*
only on its precondition

```
xᵢ ≠ xT      (first addition non-vertical)
t  ≠ 0       (second addition non-vertical)
```

In Lean this is `Kimchi.Gate.VarBaseMul.singleBit_sound`: `singleBitHolds ∧ xᵢ ≠ xT ∧
t ≠ 0 ⟹ out = (in + Q) + in`. It says **nothing** when the precondition fails.

The two failure modes correspond to the two accumulator-level degeneracies:

* **x-condition**: `aᵢ = ±T`, i.e. `xᵢ = xT`.
* **t-condition**: `2·aᵢ = ∓T`, i.e. `t = 0`.

---

## 2. Two degeneracies, opposite consequences

### 2a. x-condition (`xᵢ = xT`) — a genuine soundness break

When `aᵢ = ±T`, constraint #2 collapses: `xᵢ − xT = 0`, and (for the matching bit)
`yᵢ − (2b−1)yT = 0` as well, so #2 becomes `0·s₁ = 0` — satisfied for **any** `s₁`. The
slope is free. A crafted witness picks a bogus `s₁`, lets #3/#4 *determine* a consistent
`(xₒ, yₒ)`, and the gate accepts a **wrong** output. This is real and demonstrated:
`kimchi/src/tests/varbasemul.rs::varbase_mul_accepts_degenerate_invalid_witness`
(`verify_witness = Ok` on a forged step) and `…::varbase_mul_exploit_forged_proof` (a
full `prove_and_verify` succeeds while the attested point is off-curve). **But note the
hypothesis: this requires feeding the gate an input accumulator equal to `±T`.**

### 2b. t-condition (`t = 0`) — a completeness failure, NOT soundness

Here `xᵢ ≠ xT`, so constraint #2 **pins** `s₁ = (yᵢ − (2b−1)yT)/(xᵢ − xT)`. With `t = 0`,
constraint #3 becomes `u² = 0`, so `u = 0`; but `u = 2yᵢ − t·s₁ = 2yᵢ`, forcing
`yᵢ = 0`. On a curve of **odd prime order there is no 2-torsion**, so no affine point has
`y = 0`. Hence `t = 0` makes constraint #3 **unsatisfiable**: *no* witness — honest or
malicious — exists. The honest prover simply cannot produce one (it divides by zero;
see `packages/snarky-kimchi/test/.../VarBaseMul.purs`, the `DivisionByZero` test). There
is no slope freedom and no forgery: this is a **liveness** failure, not a soundness one.

The asymmetry is the crux: `xᵢ = xT` *frees* a constraint; `t = 0` *kills* a constraint.

---

## 3. The deployed forbidden check and what it misses

`forbidden_shifted_values` (`impls.ml:16`, ported verbatim to PureScript
`Snarky.Types.Shifted.forbiddenShiftedValues`) forbids registers `t ≡ −2ⁿ` or
`−2ⁿ−1 (mod order)` — **two** residues. In terms of the decoded scalar `s = 2t + 2ⁿ + 1`
that is `s + 2ⁿ ≡ ±1 (mod order)`.

The *complete* set of degenerate scalars (computed exhaustively) is, for the Pasta
parameters (and provably `⊆` it for any `order ≡ 1 mod 4`),

```
s ≡ {0, ±1, ±2, ±3, 5, 7, 9, 11}  (mod order)      — 11 residues
```

The deployed 2 residues are essentially disjoint from these (they sit `≈ 2¹²⁶` away). So
the deployed check does **not** exclude the degenerate scalars — the `TODO` is real.

---

## 4. Reachability: which degeneracies can a *valid* witness reach?

A register `t` must be a valid circuit-field element: `0 ≤ t < circuitMod`, where
`circuitMod` is the *other* Pasta prime (`Pallas.ScalarField` for the Vesta circuit, and
vice-versa). Both Pasta primes are `≈ 2²⁵⁴`; the group order being multiplied is the
other. Enumerating every reachable degeneracy (they are confined to the top three ladder
inputs, `d ≤ 3`) and filtering to valid registers:

| degeneracy | consequence | valid registers (in-field) | out-of-field |
|---|---|---|---|
| **x-condition** (`k ≡ ±1`) | **soundness** | **0** | 4 |
| **t-condition** (`2k ≡ ±1`) | completeness | 6 | 6 |

(Identical for both the Vesta and Pallas circuits.) The soundness-breaking x-condition
registers all satisfy `t ≈ 2²⁵⁴ + 2δ` where `δ = order − 2²⁵⁴ ≈ 4.6·10³⁷`, i.e.
`t ≈ 2²⁵⁴ + 9.1·10³⁷`, while `circuitMod ≈ 2²⁵⁴ + 4.6·10³⁷`. So each such register
**exceeds the circuit field by `≈ 4.6·10³⁷`** and is not representable. Equivalently: the
maximum scalar a register can encode is `s = 2t + 2ⁿ + 1 < 2·circuitMod + 2ⁿ`, and every
x-condition `s` lies above that bound. The field bound excludes them by a hair, but
definitively.

The 6 in-field t-condition registers are the only reachable degeneracies — and §2b shows
they admit no witness at all.

---

## 5. Conclusion: sound, modulo a `≈ 2⁻²⁵¹` completeness gap

For the deployed Pasta circuit:

* No valid scalar can drive the accumulator onto `±T` (x-condition unreachable) ⟹ the
  *only* soundness-breaking configuration cannot occur.
* The reachable degeneracies (t-condition) admit no satisfying witness ⟹ a prover that
  hits one simply fails to produce a proof.

Therefore **the circuit is sound**: there is no valid witness certifying a false
`n·T = P`. The incompleteness of `forbidden_shifted_values` is a **completeness/liveness**
gap — an honest prover whose (Fiat-Shamir-derived) scalar lands on one of the 6 in-field
t-condition registers cannot prove, with probability `≈ 6/2²⁵⁴ ≈ 2⁻²⁵¹`. Negligible.

---

## 6. Where the soundness actually comes from

Strikingly, **neither** ingredient is the forbidden check:

* **t-conditions are self-enforced by the gate constraints.** Given a nonsingular
  accumulator on a prime-order curve (`y ≠ 0`), `t = 0` is unsatisfiable. The constraints
  guarantee `t ≠ 0` for free.
* **x-conditions are excluded by the circuit-field register bound.** No representable
  register reaches `k ≡ ±1`.

So the deployed circuit would be sound **even with no forbidden check at all**. The
check's real purpose is *completeness*: it is meant to steer the honest prover away from
the (unsatisfiable) t-condition scalars — and it does so incompletely, hence the residual
`2⁻²⁵¹` liveness gap.

---

## 7. Relationship to the Lean formalization, and the gap

What is proved (axiom-clean, `formal/Kimchi/...`):

* `Gate.VarBaseMul.singleBit_sound` — the gate is correct **given** non-degeneracy.
* `Cycle.gate_step_advance`, `Cycle.nonDegen_of_not_forbidden` — `s ∉ {11 residues}
  ⟹ NonDegen` (for `order ≡ 1 mod 4` + one-wrap regime), i.e. the *complete* forbidden
  set discharges non-degeneracy.
* `Circuit.VarBaseMul.varBaseMul_sound` / `scalarMul_shifted` — `NonDegen ⟹ P = s·T`.

These give **`s ∉ {11} ⟹ P = s·T`**. They do **not** yield "the deployed circuit is
sound", for two reasons:

1. they concern the **11-residue** set, not the deployed **2-residue** check; and
2. the conclusion of §5 rests on facts that are **not formalized**: the t-condition
   infeasibility (§2b) and the x-condition unreachability (§4).

Reading "sound" off Lean is therefore the subject of follow-up **(b)**: prove the two
missing lemmas and assemble the deployed-soundness theorem.

### Scope of (b)

Target theorem (over the concrete Pasta `CMCurve`):

```
varBaseMul_deployed_sound :
  (∀ i, GateData c.W (g i)) ∧ (register < circuitMod) ∧ <init/linking>
    ⟹ P m = s · T
```

proved via two new lemmas, *neither of which needs the forbidden set*:

* **(A) `tne_of_holds`** — the t-conditions come from the constraints + prime order:
  `singleBitHolds ∧ W.Nonsingular xᵢ yᵢ ∧ Nat.Prime order ⟹ t ≠ 0`. Proof: `t = 0`
  ⟹ (constraint #3) `2yᵢ = 0` ⟹ `yᵢ = 0` ⟹ a 2-torsion affine point, contradicting odd
  prime order. This is *simpler* than our current `hsound` route to `t ≠ 0` (which goes
  through `2k ≢ ±1`), and removes the t-conditions from `NonDegen` entirely.

* **(B) `xne_of_register_bound`** — the x-conditions are excluded by the field bound:
  at the concrete Pasta order, `register < circuitMod ⟹ xᵢ ≠ xT` for every step. This
  needs the concrete prime (like the tight-set work): the integer ladder top satisfies
  `k_L = 2·register + 2ⁿ + 1 < 2·circuitMod + 2ⁿ`, which lies strictly below every
  x-condition value `k_L ≡ ±1 (mod order)` reachable in the one-wrap regime. A finite
  bound-check at the concrete order.

Then `(A) + (B) ⟹ ∀ i, NonDegen (g i)`, and the existing chain closes `P m = s·T`. The
forbidden check does not appear — exactly mirroring §6.

---

## Appendix: evidence

* Gate-level forgery (x-condition, the mechanism): `proof-systems/kimchi/src/tests/
  varbasemul.rs::varbase_mul_accepts_degenerate_invalid_witness`,
  `::varbase_mul_exploit_forged_proof` (real `prove_and_verify`, off-curve `P`).
* Completeness failure (t-condition, the reachable case): `packages/snarky-kimchi/test/
  Test/Snarky/Circuit/Kimchi/VarBaseMul.purs` (`DivisionByZero` on the in-field register
  `45560315531419706090280762371685220352`).
* Exhaustive computation (the 11-residue set; the x-vs-t reachability table) — the scalar
  arithmetic over the concrete Pasta primes; reproduced in §3–§4.
* Lean: `formal/Kimchi/Ladder.lean` (`ladder_nondegen`, `ladder_nondegen_tight`),
  `formal/Kimchi/Cycle/{NonDegen,Soundness}.lean`.
