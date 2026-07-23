import Mathlib

/-!
# α-aggregation and constraint separation

Polynomial-algebra infrastructure for kimchi's quotient
argument. It is **commitment-free**: everything lives over an abstract field `[Field F]`,
with a primitive `n`-th root of unity supplied as a hypothesis
(`hω : IsPrimitiveRoot ω n`, `0 < n`).

kimchi combines the several constraint polynomials of a circuit into a single polynomial by
taking a linear combination in consecutive powers of one challenge `α`, one power per
constraint (`references/alphas.rs`, context only). This file models that combination and
proves the **separation** property the soundness argument needs: if the aggregate is
divisible by `Z_H` for enough distinct values of `α`, then *each* individual constraint
polynomial is divisible by `Z_H`.

The "enough distinct αs" premise is an ordinary injectivity hypothesis, **not** a
Fiat–Shamir definition; the underlying mathematics is a Vandermonde / too-many-roots
separation and is standard.

## Contents

* `aggregate` — the α-aggregate `∑_c α^c • E c ∈ F[X]`.
* `dvd_separation` — divisibility of the aggregate at enough distinct challenges separates
  across the individual constraint polynomials.
-/

namespace Kimchi

open Polynomial

variable {F : Type*} [Field F] {n k : ℕ} {ω : F}

/-! ## The aggregate polynomial -/

/-- The **α-aggregate** of a finite family of constraint polynomials `E : Fin k → F[X]`:
the linear combination `∑_{c : Fin k} α^c • E c ∈ F[X]` in consecutive powers of the
challenge `α`. -/
noncomputable def aggregate (α : F) (E : Fin k → Polynomial F) : Polynomial F :=
  ∑ c : Fin k, α ^ (c : ℕ) • E c


end Kimchi
