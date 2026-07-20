import Kimchi.Quotient.Domain
import Kimchi.Quotient.Shifted
import Kimchi.Quotient.Aggregate
import Kimchi.Quotient.SchwartzZippel

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
-/

namespace Kimchi.Quotient

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The ungated engine -/

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
private theorem polyEnv_map_aeval [NeZero n] (hω : IsPrimitiveRoot ω n)
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


/-! ## Quotient-argument soundness — single-challenge (counting) form -/

/-- **`Argument` quotient soundness, single-challenge form.** The counting–Schwartz–Zippel
analogue of `Argument.soundness`: the injective challenge family `α : Fin _ → F`, the injective
node family `ζ : Fin N → F`, and the per-challenge quotient family `t : Fin _ → F[X]` all
collapse — to a *single* challenge `α` (avoiding the proved-small `badAlphas` set), a *single*
good node `ζ` (avoiding the proved-small `badZetas` set of the aggregate), and a *single*
quotient `t`. No injectivity, no degree bounds. Conclusion is identical to `Argument.soundness`:
every selector-active row satisfies the gate's row constraints.

The single-ζ counting bridge the per-gate soundness wrappers (`Index/GateSoundness.lean`
and the gate-quotient modules) delegate to; it composes the single-ζ counting
`dvd_of_evalCheck`. -/
theorem Argument.soundness [DecidableEq F] [NeZero n] (G : Argument F)
    (hω : IsPrimitiveRoot ω n)
    (wTab qTab : Fin n → Fin 15 → F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1)
    (α : F)
    (hα : α ∉ badAlphas (fun c => columnPoly ω sel *
        (G.constraints (polyEnv ω wTab qTab)).get c) ω n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (fun c => columnPoly ω sel *
        (G.constraints (polyEnv ω wTab qTab)).get c)) t n)
    (hcheck : (aggregate α (fun c => columnPoly ω sel *
        (G.constraints (polyEnv ω wTab qTab)).get c)).eval ζ
        = (t * zH F n).eval ζ) :
    ∀ i, sel i = 1 → ∀ e ∈ G.constraints (rowEnv wTab qTab i), e = 0 := by
  have hdvd := dvd_of_evalCheck hω
    (fun c => columnPoly ω sel * (G.constraints (polyEnv ω wTab qTab)).get c)
    α hα t ζ hζ hcheck
  apply (G.rowsSel_iff_dvd hω wTab qTab sel hsel).mp
  intro E hE
  obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hE
  exact hdvd c

end Kimchi.Quotient
