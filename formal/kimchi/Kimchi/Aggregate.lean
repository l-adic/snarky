import Mathlib

/-!
# α-aggregation

Polynomial-algebra infrastructure for kimchi's quotient
argument. It is **commitment-free**: everything lives over an abstract field `[Field F]`.

kimchi combines the several constraint polynomials of a circuit into a single polynomial by
taking a linear combination in consecutive powers of one challenge `α`, one power per
constraint (`references/alphas.rs`, context only). This file models that combination, and
defines one thing: `aggregate`, the α-aggregate `∑_c α^c • E c ∈ F[X]`.

The separation property the soundness argument needs — that divisibility of the aggregate by
`Z_H` forces *each* individual constraint polynomial to be divisible by `Z_H` — is
`dvd_separation` in `Kimchi/SchwartzZippel.lean`, in the counting form: a single challenge
`α` suffices, provided it avoids an explicitly bounded bad set. The underlying mathematics is
a Vandermonde / too-many-roots argument and is standard.
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
