import Kimchi.Domain
import Kimchi.Shifted
import Kimchi.Aggregate
import Kimchi.SchwartzZippel

/-!
# The gate-argument primitive

The polynomial-lift interface a gate's constraints are read through. **Commitment-free**:
everything lives over an abstract field `[Field F]` with a primitive `n`-th root of unity
supplied as a hypothesis (`ω : F`, `hω : IsPrimitiveRoot ω n`, `0 < n`). No gate formula is
ever restated at this layer — a gate supplies its constraint family and reuses the one
evaluation bridge below.

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
`Argument.bridge` — evaluation at a node carries `polyEnv` to `rowEnv` — is the one bridge
in the library; every per-gate bridge is that gate's `constraints_map` pasted onto it.

## Contents

* `ArgumentEnv`, `rowEnv`, `polyEnv` — the cell environment and its two carrier
  instantiations (field-level row cells, and column interpolants with `shift` on the
  next-row side).
* `Argument`, `Argument.bridge` — one gate's constraint family, and the evaluation bridge
  carrying its polynomial-side constraints to the row-side ones.
-/

namespace Kimchi.Quotient

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}
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

end Kimchi.Quotient
