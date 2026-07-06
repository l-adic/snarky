import Kimchi.Quotient.Domain
import Kimchi.Quotient.Shifted
import Kimchi.Quotient.Aggregate
import Kimchi.Quotient.Pinning

/-!
# The generic lift engine

Polynomial-algebra infrastructure. **Commitment-free**: everything lives over
an abstract field `[Field F]` with a primitive `n`-th root of unity supplied as a hypothesis
(`ω : F`, `hω : IsPrimitiveRoot ω n`, `0 < n`).

Every gate's "rows hold iff the constraint polynomials are divisible by `Z_H`" theorem is one
instantiation of a single abstract lemma. The lemma takes the list `P` of constraint
polynomials, the per-row list `rowCons i` of field-level constraint expressions, and a
**bridge** hypothesis asserting that evaluating `P` at the node `ω^i` reproduces `rowCons i`.
**No gate formula is ever restated at this layer.**

## The `ArgumentEnv` / `Argument` pair

The per-gate interface mirrors kimchi's `argument.rs`:

* `ArgumentEnv R` is the cell environment a gate's constraints may read, anchored at a row —
  the current-row witness cells, the next-row witness cells (cyclic `i + 1`), and the
  current row's coefficient cells. It is the Lean counterpart of kimchi's `ArgumentEnv`
  restricted to the cell accessors (`witness_curr` / `witness_next` / `coeff`).
* `Argument F` is one gate's constraint family: a list of constraint expressions defined over
  every commutative `F`-algebra `R` from an `ArgumentEnv R`, together with its naturality
  square along `F`-algebra homomorphisms. It is the Lean counterpart of kimchi's `Argument`
  trait: `constraints` is `constraint_checks`, generic over the carrier the way
  `constraint_checks` is generic over `T : ExprOps` — kimchi runs the same code at `T = F`
  (direct row checks) and `T = E<F>` (the symbolic expressions compiled into the quotient),
  and `constraints_map` is the corresponding agreement between the two instantiations, which
  Rust gets for free by parametricity and Lean states as a proof obligation.

Genericity over `F`-algebras (rather than plain rings) is what absorbs gate **parameters**
(EndoMul's endomorphism constant, EndoScalar's interpolating-cubic coefficients): each becomes
the image under `algebraMap F R` of a fixed element of `F`, and the evaluation morphism is the
`F`-algebra hom `Polynomial.aeval (ω^i) : F[X] →ₐ[F] F`, which fixes those images.

The two carrier instantiations are packaged once, gate-independently: `rowEnv` (the field-level
cells of row `i`) and `polyEnv` (the column interpolants, with `shift` on the next-row side).
`polyEnv_map_aeval` — evaluation at a node carries `polyEnv` to `rowEnv` — is the one bridge
proof in the library; every per-gate bridge is `constraints_map` pasted onto it.

## Contents

* `rows_iff_dvd_of` — the ungated engine:
  `(∀ E ∈ P, Z_H ∣ E) ↔ ∀ i, ∀ e ∈ rowCons i, e = 0`.
* `rowsSel_iff_dvd` — the selector-gated engine: divisibility of `S · E` (with
  `S = columnPoly ω sel` a boolean selector column) is equivalent to the row constraints
  holding only on the selected rows.
* `dvd_of_evalCheck` — the composed pinning→separation engine, stated over an abstract family
  of constraint polynomials with no gate content.
* `ArgumentEnv`, `rowEnv`, `polyEnv`, `polyEnv_map_aeval` — the cell environment, its two
  carrier instantiations, and the evaluation bridge between them.
* `Argument` with `bridge` / `rows_iff_dvd` / `rowsSel_iff_dvd` / `soundness` — the per-gate
  interface and its four engine corollaries, each stated once.

Source of truth: `blueprint/src/chapters/Kimchi_Quotient_Lift.tex`.
-/

namespace Kimchi.Quotient

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The ungated engine -/

/-- **Rows hold iff the constraint polynomials are divisible by `Z_H`.** Given a primitive
`n`-th root of unity `ω` (with `0 < n`), a list `P` of constraint polynomials, per-row
constraint lists `rowCons`, and the bridge hypothesis stating that evaluating `P` at the node
`ω^i` reproduces `rowCons i`, the whole list is divisible by the vanishing polynomial iff every
per-row constraint expression is zero. -/
theorem rows_iff_dvd_of (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (P : List (Polynomial F))
    (rowCons : Fin n → List F)
    (hbridge : ∀ i : Fin n, P.map (·.eval (ω ^ (i : ℕ))) = rowCons i) :
    (∀ E ∈ P, zH F n ∣ E) ↔ ∀ i, ∀ e ∈ rowCons i, e = 0 := by
  constructor
  · intro h i e he
    rw [← hbridge i, List.mem_map] at he
    obtain ⟨E, hE, rfl⟩ := he
    exact (zH_dvd_iff hω hn E).mp (h E hE) i i.isLt
  · intro h E hE
    rw [zH_dvd_iff hω hn]
    intro i hi
    have hmem : E.eval (ω ^ i) ∈ rowCons ⟨i, hi⟩ := by
      rw [← hbridge ⟨i, hi⟩]
      exact List.mem_map.mpr ⟨E, hE, rfl⟩
    exact h ⟨i, hi⟩ (E.eval (ω ^ i)) hmem

/-! ## The selector-gated engine -/

/-- **Selector-gated rows iff divisible.** kimchi multiplies a gate's constraints by a boolean
selector column `S = columnPoly ω sel` that is `1` on the rows the gate occupies and `0`
elsewhere. Divisibility of `S · E` by `Z_H` is equivalent to the row constraints holding only
on the selected rows: an inactive row (`sel i = 0`) imposes nothing. -/
theorem rowsSel_iff_dvd (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (P : List (Polynomial F))
    (rowCons : Fin n → List F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1)
    (hbridge : ∀ i : Fin n, P.map (·.eval (ω ^ (i : ℕ))) = rowCons i) :
    (∀ E ∈ P, zH F n ∣ (columnPoly ω sel) * E) ↔
      ∀ i, sel i = 1 → ∀ e ∈ rowCons i, e = 0 := by
  constructor
  · intro h i hsi e he
    rw [← hbridge i, List.mem_map] at he
    obtain ⟨E, hE, rfl⟩ := he
    have hd := (zH_dvd_iff hω hn _).mp (h E hE) i i.isLt
    rw [eval_mul, eval_columnPoly hω sel i, hsi, one_mul] at hd
    exact hd
  · intro h E hE
    rw [zH_dvd_iff hω hn]
    intro i hi
    rw [eval_mul]
    have heq : (columnPoly ω sel).eval (ω ^ i) = sel ⟨i, hi⟩ :=
      eval_columnPoly hω sel ⟨i, hi⟩
    rw [heq]
    rcases hsel ⟨i, hi⟩ with h0 | h1
    · rw [h0, zero_mul]
    · rw [h1, one_mul]
      have hmem : E.eval (ω ^ i) ∈ rowCons ⟨i, hi⟩ := by
        rw [← hbridge ⟨i, hi⟩]
        exact List.mem_map.mpr ⟨E, hE, rfl⟩
      exact h ⟨i, hi⟩ h1 (E.eval (ω ^ i)) hmem

/-! ## The composed pinning–separation engine -/

/-- **Divisibility from the aggregated eval-check.** Fix a primitive `n`-th root `ω`, an
injective node vector `ζ : Fin N → F`, an injective challenge vector `α : Fin k → F`, and two
families `E, t : Fin k → F[X]`. Under the abstract degree bound `D < N` on the aggregate and
on `t s · Z_H`, if the aggregated eval-check
`(aggregate (α s) E)(ζ p) = (t s · Z_H)(ζ p)` holds for every challenge `s` and node `p`, then
`Z_H ∣ E c` for every constraint index `c`.

Proof: for each `s`, `zH_dvd_of_evals` pins `Z_H ∣ aggregate (α s) E`; feeding
this to `dvd_separation` across the `k` distinct challenges yields `Z_H ∣ E c`. -/
theorem dvd_of_evalCheck {k N : ℕ}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin k → F) (hα : Function.Injective α)
    (E t : Fin k → Polynomial F) (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) E).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s : Fin k, ∀ p : Fin N,
        (aggregate (α s) E).eval (ζ p) = (t s * zH F n).eval (ζ p)) :
    ∀ c, zH F n ∣ E c :=
  dvd_separation hω hn α hα E
    (fun s => zH_dvd_of_evals hω hn ζ hζ (aggregate (α s) E) (t s) D
      (hCdeg s) (htdeg s) hD (hcheck s))

/-! ## The cell environment -/

/-- **The cell environment of a gate row.** The three cell families a gate's constraints may
read, anchored at a row: the current-row witness cells, the next-row witness cells (cyclic
`i + 1`), and the current row's coefficient cells. Lean counterpart of kimchi's `ArgumentEnv`
(`argument.rs`), restricted to the cell accessors (`witness_curr` / `witness_next` /
`coeff`). -/
structure ArgumentEnv (R : Type u) where
  witnessCurr : Fin 15 → R
  witnessNext : Fin 15 → R
  coeff : Fin 15 → R

/-- Push a carrier map `f : R → S` through an environment, cell by cell in each family. -/
def ArgumentEnv.map {R S : Type u} (f : R → S) (env : ArgumentEnv R) : ArgumentEnv S :=
  ⟨f ∘ env.witnessCurr, f ∘ env.witnessNext, f ∘ env.coeff⟩

/-- **Row environment.** The field-level cells at row `i` of a witness table `wTab` and a
coefficient table `qTab`: current row `wTab i`, next row `wTab (i + 1)` (cyclic), coefficients
`qTab i`. -/
def rowEnv [NeZero n] (wTab qTab : Fin n → Fin 15 → F) (i : Fin n) : ArgumentEnv F :=
  ⟨wTab i, wTab (i + 1), qTab i⟩

/-- **Polynomial environment.** The column interpolants of the tables: `columnPoly` of each
witness column on the current side, its `shift` on the next side, and `columnPoly` of each
coefficient column on the coefficient side. -/
noncomputable def polyEnv (ω : F) (wTab qTab : Fin n → Fin 15 → F) :
    ArgumentEnv (Polynomial F) :=
  ⟨fun c => columnPoly ω (fun j => wTab j c),
   fun c => shift ω (columnPoly ω (fun j => wTab j c)),
   fun c => columnPoly ω (fun j => qTab j c)⟩

/-- **Environment evaluation bridge.** Evaluating the polynomial environment at the node `ω^i`
— i.e. mapping the `F`-algebra hom `aeval (ω^i)` through it — yields the row environment at
`i`: `eval_columnPoly` on the current and coefficient sides, `eval_shift_columnPoly` on the
next side. This is the one evaluation bridge in the library; every gate reaches its own bridge
by pasting its naturality square onto this equation. -/
theorem polyEnv_map_aeval [NeZero n] (hω : IsPrimitiveRoot ω n)
    (wTab qTab : Fin n → Fin 15 → F) (i : Fin n) :
    (polyEnv ω wTab qTab).map ⇑(aeval (ω ^ (i : ℕ)) : Polynomial F →ₐ[F] F)
      = rowEnv wTab qTab i := by
  simp only [polyEnv, ArgumentEnv.map, rowEnv]
  congr 1
  · funext c
    simp only [Function.comp_apply, Polynomial.coe_aeval_eq_eval, eval_columnPoly hω]
  · funext c
    simp only [Function.comp_apply, Polynomial.coe_aeval_eq_eval, eval_shift_columnPoly hω]
  · funext c
    simp only [Function.comp_apply, Polynomial.coe_aeval_eq_eval, eval_columnPoly hω]

/-! ## The `Argument` primitive over `F`-algebras -/

/-- **The `Argument` primitive.** One gate's constraint family: the list of constraint
expressions read from an `ArgumentEnv R`, defined for every commutative `F`-algebra `R`,
together with its naturality square along `F`-algebra homomorphisms. Counterpart of kimchi's
`Argument` trait (`argument.rs`): `constraints` is `constraint_checks`, and `constraints_map`
is the agreement between its carrier instantiations that Rust obtains by parametricity.

Gate parameters that are fixed field elements (an endomorphism coefficient, interpolating-cubic
coefficients) enter through `algebraMap F R`, which every `f : R →ₐ[F] S` fixes
(`AlgHom.commutes`) — this is what makes a uniform naturality square possible across gates with
different parameters. -/
structure Argument (F : Type u) [Field F] where
  constraints : ∀ {R : Type u} [CommRing R] [Algebra F R], ArgumentEnv R → List R
  constraints_map : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
      (f : R →ₐ[F] S) (env : ArgumentEnv R),
    (constraints env).map f = constraints (env.map f)

/-- **`Argument` eval bridge.** Evaluating the constraint polynomials of the polynomial
environment at the node `ω^i` reproduces the field-level constraints of the row environment:
the naturality square `constraints_map` at `aeval (ω^i)`, pasted onto `polyEnv_map_aeval`. -/
theorem Argument.bridge [NeZero n] (G : Argument F) (hω : IsPrimitiveRoot ω n)
    (wTab qTab : Fin n → Fin 15 → F) (i : Fin n) :
    (G.constraints (polyEnv ω wTab qTab)).map (·.eval (ω ^ (i : ℕ)))
      = G.constraints (rowEnv wTab qTab i) := by
  have hfun : (fun E : Polynomial F => E.eval (ω ^ (i : ℕ)))
      = ⇑(aeval (ω ^ (i : ℕ)) : Polynomial F →ₐ[F] F) := by
    funext E; rw [Polynomial.coe_aeval_eq_eval]
  rw [hfun, G.constraints_map, polyEnv_map_aeval hω]

/-- **`Argument` rows iff divisible.** The gate's constraint polynomials (its constraints at
the polynomial environment) are all divisible by `Z_H` iff its field-level constraints vanish
at every row. Immediate instance of `rows_iff_dvd_of` at the `Argument` bridge. -/
theorem Argument.rows_iff_dvd [NeZero n] (G : Argument F) (hω : IsPrimitiveRoot ω n)
    (wTab qTab : Fin n → Fin 15 → F) :
    (∀ E ∈ G.constraints (polyEnv ω wTab qTab), zH F n ∣ E)
      ↔ ∀ i, ∀ e ∈ G.constraints (rowEnv wTab qTab i), e = 0 :=
  rows_iff_dvd_of hω (Nat.pos_of_neZero n) _
    (fun i => G.constraints (rowEnv wTab qTab i)) (G.bridge hω wTab qTab)

/-- **`Argument` selector-gated rows iff divisible.** For a boolean selector column
`S = columnPoly ω sel`, divisibility of every `S · E` by `Z_H` is equivalent to the gate's
field-level constraints vanishing on the selected rows only. Instance of `rowsSel_iff_dvd` at
the `Argument` bridge; the selector multiplication mirrors kimchi's
`index(gate_type) * combined_constraints` gating (`argument.rs`). -/
theorem Argument.rowsSel_iff_dvd [NeZero n] (G : Argument F) (hω : IsPrimitiveRoot ω n)
    (wTab qTab : Fin n → Fin 15 → F) (sel : Fin n → F)
    (hsel : ∀ i, sel i = 0 ∨ sel i = 1) :
    (∀ E ∈ G.constraints (polyEnv ω wTab qTab), zH F n ∣ (columnPoly ω sel) * E)
      ↔ ∀ i, sel i = 1 → ∀ e ∈ G.constraints (rowEnv wTab qTab i), e = 0 :=
  Kimchi.Quotient.rowsSel_iff_dvd hω (Nat.pos_of_neZero n) _
    (fun i => G.constraints (rowEnv wTab qTab i)) sel hsel (G.bridge hω wTab qTab)

/-! ## Quotient-argument soundness -/

/-- **`Argument` quotient soundness.** With the abstract quotient-argument hypotheses over the
selector-gated family `c ↦ (columnPoly ω sel) * (constraints (polyEnv ω wTab qTab)).get c` —
an injective node vector `ζ`, an injective challenge vector `α`, an abstract degree bound
`D < N`, and the aggregated eval-check passing at every challenge and node — every
selector-active row satisfies the gate's row constraints, i.e. every constraint expression of
the row environment is zero.

Proof: apply `dvd_of_evalCheck` to the gated family to obtain
`∀ c, zH ∣ (columnPoly ω sel) * (constraints …).get c`; converting the `Fin length` indexing to
`∈ constraints …` membership and feeding the instance's selector-gated
`Argument.rowsSel_iff_dvd` gives the row constraints on the selected rows. -/
theorem Argument.soundness [DecidableEq F] {N : ℕ} [NeZero n] (G : Argument F)
    (hω : IsPrimitiveRoot ω n)
    (wTab qTab : Fin n → Fin 15 → F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (G.constraints (polyEnv ω wTab qTab)).length → F)
    (hα : Function.Injective α)
    (t : Fin (G.constraints (polyEnv ω wTab qTab)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c => columnPoly ω sel *
        (G.constraints (polyEnv ω wTab qTab)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c => columnPoly ω sel *
        (G.constraints (polyEnv ω wTab qTab)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ i, sel i = 1 → ∀ e ∈ G.constraints (rowEnv wTab qTab i), e = 0 := by
  have hdvd := dvd_of_evalCheck hω (Nat.pos_of_neZero n) ζ hζ α hα
    (fun c => columnPoly ω sel * (G.constraints (polyEnv ω wTab qTab)).get c)
    t D hD hCdeg htdeg hcheck
  apply (G.rowsSel_iff_dvd hω wTab qTab sel hsel).mp
  intro E hE
  obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hE
  exact hdvd c

end Kimchi.Quotient
