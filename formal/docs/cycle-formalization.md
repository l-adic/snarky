# Scoping: the Pasta two-cycle formalization

Status: **scoped, not started.** Phase 0 axioms stub at `Kimchi/Cycle/Axioms.lean`.

## Why

The gate formalizations (`AddComplete`, `VarBaseMul`, `EndoScalar`, `EndoMul`)
prove soundness over a **single field `F`**. For the **point** computations that is
honest — the group law and `[n]·P` (`n : ℤ`) genuinely live over the coordinate
field. But every **scalar** claim — `VarBaseMul`'s `[s]·T`, `EndoScalar`'s `a·λ+b`,
`endoMul_toField` — silently identifies the coordinate field with the **scalar
field** (the group order). On Pasta these are *different* primes: Pallas has
coordinates in `F_p` and group order `q`; Vesta is the mirror. The single-`F` model
conflates them, and is only "correct" under an unstated `Shifted_value` range
condition (the very thing the cycle machinery exists to guarantee).

The goal: make the scalar claims faithful — a gate over circuit field `F_p`, on a
curve of order `q`, produces a scalar genuinely in `ℤ/q`, with the in-circuit
register a `Shifted_value` encoding of that `ℤ/q` scalar.

## Two levels (you can stop at the first)

- **Level 1 — one curve, two fields.** `E/F_p`, coords in `F_p`, scalar field
  `ℤ/q`. Makes `VarBaseMul`'s `[s]·T` and `EndoMul`'s `[k]·T` honest (`s,k ∈ ℤ/q`).
  No second curve needed. The minimal fix for the per-gate conflation.
- **Level 2 — the full cycle.** Two curves `E_p/F_p` (order `q`), `E_q/F_q`
  (order `p`) with the reciprocity. This is what `endoMul_toField` actually needs:
  `EndoScalar` runs natively in one field and `EndoMul`'s point-mul happens on the
  curve whose **scalar field is that field** — different circuits, joined only by the
  cycle.

## The axiom boundary (unavoidable, Pasta-specific)

Three facts Mathlib cannot prove — stated as the load-bearing axioms, externally
checkable, instantiated for Pallas/Vesta:

1. **Curve order / scalar action.** The point group has exponent dividing `order`
   (for Pasta: cyclic of prime `order`), so scalars act through `ℤ/order`. *Needs
   Schoof — not in Mathlib; the value is a 255-bit constant.*
2. **The CM eigenvalue.** `∃ β ∈ F, λ ∈ ℤ` with `β³ = 1`, `λ³ ≡ 1 (mod order)`, and
   the coordinate map `φ(x,y) = (β·x, y)` realizes `φ(P) = [λ]·P`. *Endomorphism-ring
   / CM structure — not in Mathlib.* (Same fact `endoMul_scalar` already hypothesizes,
   now properly typed `λ ∈ ℤ/order`.)
3. **Reciprocity (Level 2 only).** `|E_p| = card F_q`, `|E_q| = card F_p`.

Everything else builds on these. The formalization is sound *modulo these checkable
Pasta facts* — the standard situation (you can't derive a 255-bit curve order from
first principles). They WILL appear in `#print axioms`; that is correct and honest.

## The real (provable) work

4. **Scalar reduction.** From axiom 1, `[n]P = [n mod order]P`.
5. **`Shifted_value` encoding.** `shift`/`unshift : F_p ↔ ℤ/order` (Type1
   `s = 2t + 2^n + 1`, Type2 split + low-bit correction), a **range predicate**, and
   faithfulness (inverse on range). Mirrors the existing `Snarky.Types.Shifted`
   (PureScript) and `pickles/shifted_value.ml`. We already have `unshiftType1` /
   `shiftType1` as single-field stand-ins; this gives them their true cross-field
   types.
6. **The bridge.** Connect the *existing* point lemmas to `ℤ/order` scalars via the
   encoding. Crux: in the `Shifted_value` range (`< min(p,q)`), the register's integer
   value satisfies `n mod p = n mod q`, so base-field rep and scalar-field value
   coincide — exactly the property we'd been silently assuming.

## The big reuse

**The EC point soundness stays as-is and is already honest.** `secant_add`,
`(P+Q)+P`, the GLV folds, `chain_endo`, `chain_scalarMul` — all genuinely over the
coordinate field with `ℤ`-scalars. The cycle work is **purely additive**: a
scalar-field layer + encoding *on top of* the existing point lemmas. No
elliptic-curve geometry is re-proven.

## Phasing

- **Phase 0** — axioms file (`CMCurve` / `TwoCycle`: orders, eigenvalue, reciprocity).
  *Stubbed.*
- **Phase 1** — `ℤ/order` scalar action + re-state **one** gate (VarBaseMul) over the
  two-field model with the encoding bridge. Validates the approach on the simplest
  gate.
- **Phase 2** — the `Shifted_value` Type1/Type2 encoding + faithfulness (the fiddly
  range bookkeeping: 128-bit challenges vs 255-bit fields).
- **Phase 3** — re-state EndoScalar / EndoMul with the proper scalar field.
- **Phase 4** — two curves + reciprocity → `endoMul_toField` as a *genuine*
  cross-field theorem.

## Effort & risk

- **Level 1 ≈ one gate's worth of work** (encoding + bridge + one re-statement).
  Tractable, high payoff — retroactively makes the existing scalar claims faithful.
- **Level 2 is bigger** (two-curve setup + reciprocity) but bounded, and the only way
  `endoMul_toField` becomes real rather than within-model.
- **Main risk**: the range bookkeeping in `Shifted_value` (Phase 2) — the fiddliest
  part, but exactly the kind of thing Aristotle handled for the gates.
- **The axioms are load-bearing** and will surface in `#print axioms` (no longer
  "standard-only" — correct: the curve facts genuinely aren't Mathlib theorems).

## Recommendation

Do **Phase 0–1 as a spike**: small, proves out the encoding-bridge pattern on
VarBaseMul, and immediately upgrades a real scalar claim from "within-model" to
"faithful (mod the 3 axioms)." If the axiom surface and range bookkeeping feel
acceptable, continue; if not, little is spent.
