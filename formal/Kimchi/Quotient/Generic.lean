import Kimchi.Quotient.Lift
import Kimchi.Gate.Generic

/-!
# The double generic gate's constraint polynomials and the divisibility checkpoint

The polynomial lift of kimchi's **double** generic gate (`generic.rs`,
`CONSTRAINTS = 2`) and the first end-to-end "gate holds on every row iff the
constraint polynomials are divisible by `Z_H`" thread. Commitment-free, built
directly on `Kimchi.Quotient.Domain`.

The row-level gate predicate is `Kimchi.Gate.Generic.Holds` (defined in
`Kimchi/Gate/Generic.lean` — the double generic gate's two cell constraints); this
file owns only the *polynomial* side — the constraint polynomials over column
interpolants and the divisibility bridge.

## Column layout (from `generic.rs`)

A generic row carries 15 witness cells `w : Fin 15 → F` and 15 coefficient cells
`q : Fin 15 → F`. The row packs **two** generic gates: the first uses registers
`w 0, w 1, w 2` with coefficients `q 0 … q 4`; the second uses `w 3, w 4, w 5`
with coefficients `q 5 … q 9` (`q 10 … q 14` are unused here).

Source: kimchi `generic.rs` (module doc + `constraint_checks`, l.245–250):

    * w0·c0 + w1·c1 + w2·c2 + w0·w1·c3 + c4
    * w3·c5 + w4·c6 + w5·c7 + w3·w4·c8 + c9

where the `cᵢ` are the coefficients (`q` here).
-/

namespace Kimchi.Quotient

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The constraint polynomials of a circuit

Given witness/coefficient column polynomials `W, Q : Fin 15 → F[X]`, the gate's
two constraints lift verbatim to the polynomial ring: replace each cell by its
column polynomial. -/

/-- The first constraint polynomial
`E₁ = Q₀·W₀ + Q₁·W₁ + Q₂·W₂ + Q₃·(W₀·W₁) + Q₄`. -/
noncomputable def genericE1 (Q W : Fin 15 → Polynomial F) : Polynomial F :=
  Q 0 * W 0 + Q 1 * W 1 + Q 2 * W 2 + Q 3 * (W 0 * W 1) + Q 4

/-- The second constraint polynomial
`E₂ = Q₅·W₃ + Q₆·W₄ + Q₇·W₅ + Q₈·(W₃·W₄) + Q₉`. -/
noncomputable def genericE2 (Q W : Fin 15 → Polynomial F) : Polynomial F :=
  Q 5 * W 3 + Q 6 * W 4 + Q 7 * W 5 + Q 8 * (W 3 * W 4) + Q 9

/-- **Per-row bridge, first constraint.** For a circuit table `wTab, qTab` with
column polynomials `W c = columnPoly (fun i => wTab i c)` and
`Q c = columnPoly (fun i => qTab i c)`, evaluating `E₁` at the node `ω^i`
recovers the left-hand side of the first constraint at row `i`.

Evaluation at `ω^i` is a ring homomorphism, so it distributes over the sums and
products of `genericE1`; then `eval_columnPoly` reduces each `W c` / `Q c` to
the corresponding cell value. -/
theorem eval_genericE1 (hω : IsPrimitiveRoot ω n)
    (wTab qTab : Fin n → Fin 15 → F) (i : Fin n) :
    (genericE1 (fun c => columnPoly ω (fun j => qTab j c))
        (fun c => columnPoly ω (fun j => wTab j c))).eval (ω ^ (i : ℕ))
      = qTab i 0 * wTab i 0 + qTab i 1 * wTab i 1 + qTab i 2 * wTab i 2
        + qTab i 3 * (wTab i 0 * wTab i 1) + qTab i 4 := by
  simp only [genericE1, eval_add, eval_mul, eval_columnPoly hω]

/-- **Per-row bridge, second constraint.** Identical to `eval_genericE1`, using
columns `3, 4, 5` and coefficients `5 … 9`. -/
theorem eval_genericE2 (hω : IsPrimitiveRoot ω n)
    (wTab qTab : Fin n → Fin 15 → F) (i : Fin n) :
    (genericE2 (fun c => columnPoly ω (fun j => qTab j c))
        (fun c => columnPoly ω (fun j => wTab j c))).eval (ω ^ (i : ℕ))
      = qTab i 5 * wTab i 3 + qTab i 6 * wTab i 4 + qTab i 7 * wTab i 5
        + qTab i 8 * (wTab i 3 * wTab i 4) + qTab i 9 := by
  simp only [genericE2, eval_add, eval_mul, eval_columnPoly hω]

/-! ## The `Argument` instance

The generic gate plugs into the `Argument` primitive of `Kimchi.Quotient.Lift` exactly like
the other five gates: the gate row `Gate.Generic R` is assembled from the current-row cells
(as `w`) and the coefficient cells (as `q`); the next-row family is unused (single-row). -/

/-- **Generic cell map.** Assemble a `Gate.Generic R` from current-row cells `cur` (→ `w`) and
coefficient cells `coeff` (→ `q`). -/
def genericCellMap {R : Type*} (cur coeff : Fin 15 → R) : Gate.Generic R :=
  ⟨coeff, cur⟩

/-- **Generic `Argument` instance.** The gate's constraint list `Gate.Generic.constraints`
read through `genericCellMap`; naturality is the gate module's `Generic.constraints_map` at
the underlying ring hom. -/
def genericArgument : Argument F where
  constraints env := (genericCellMap env.witnessCurr env.coeff).constraints
  constraints_map f env :=
    Gate.Generic.constraints_map f.toRingHom (genericCellMap env.witnessCurr env.coeff)

/-! ## The divisibility checkpoint

The first end-to-end gate-to-divisibility theorem: the gate holds on every row
of the table iff both constraint polynomials vanish on `H`, i.e. are divisible
by `Z_H`. Mirrors kimchi's prover-side check (`generic.rs` `verify_generic`,
l.364–368): the combined generic polynomial is accepted iff
`res.divide_by_vanishing_poly(d1)` has zero remainder. -/

/-- **Generic rows hold iff constraint polynomials are divisible.** Fix a
primitive `n`-th root `ω` (`0 < n`) and a circuit table `wTab, qTab` with column
polynomials `W c = columnPoly (fun i => wTab i c)`,
`Q c = columnPoly (fun i => qTab i c)`. Then both constraint polynomials are
divisible by `Z_H` iff the double generic gate holds at every row.

By `zH_dvd_iff`, `Z_H ∣ E ↔ ∀ i < n, E(ω^i) = 0`; by `eval_genericE1/2`,
`E₁(ω^i) = 0` (resp. `E₂`) is exactly the first (resp. second) constraint of
`Gate.Generic.Holds` at row `i`. Commuting `∧` past `∀` merges the two
per-constraint statements. Pure polynomial algebra — no probabilistic content
here. -/
theorem genericRows_iff_dvd (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab qTab : Fin n → Fin 15 → F) :
    (zH F n ∣
        genericE1 (fun c => columnPoly ω (fun i => qTab i c))
          (fun c => columnPoly ω (fun i => wTab i c)) ∧
      zH F n ∣
        genericE2 (fun c => columnPoly ω (fun i => qTab i c))
          (fun c => columnPoly ω (fun i => wTab i c))) ↔
      ∀ i, (Gate.Generic.mk (qTab i) (wTab i)).Holds := by
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  -- Route through the abstract `Argument` engine at the instance `genericArgument`.
  have key := (genericArgument (F := F)).rows_iff_dvd hω hn wTab qTab
  -- Unfold the instance: the polynomial-environment constraint list is
  -- `[genericE1 Q W, genericE2 Q W]` and the row-environment one is `[c₁ i, c₂ i]`, the two
  -- entries of `Gate.Generic.Holds`.
  simp only [genericArgument, polyEnv, rowEnv, genericCellMap,
    Gate.Generic.constraints, List.forall_mem_cons, List.not_mem_nil, false_implies,
    forall_const, and_true] at key
  simp only [Gate.Generic.holds_iff]
  exact key

end Kimchi.Quotient
