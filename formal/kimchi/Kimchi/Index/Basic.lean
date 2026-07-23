import Kimchi.Permutation.Wiring
import Kimchi.Gate.Poseidon

/-!
# The kimchi index: the circuit as data

A kimchi circuit as the constraint system carries it (`ConstraintSystem`,
proof-systems `circuits/constraints.rs`): a gate table — one `GateRow` per domain row,
with its gate type, its fifteen coefficient cells, and its seven wire pointers — plus the
domain generator, the coset shifts, the base-field endomorphism coefficient, and the
zero-knowledge and public-input row counts. The index carries its laws: a value of
`Index F n` is wellformed by construction (primitive generator, coset shifts, bounded
row regions, a region-preserving bijective wiring), in the manner of `SWPoint`. On
concrete data every law is decidable — the generator and shift conditions through the
certificates of `Kimchi/Permutation/Wiring.lean`, the rest by `Fintype` instances — so
parsers construct indices by deciding, never by trusting.

**One stored representation.** The table is `Fin`-indexed data; the satisfiability
predicate (`Satisfies`) and every proof consume it directly. Everything else is a
*derived view* with its bridge proved at the definition site:

* the **coefficient table** (`coeffTable`) — the `qTab` that the quotient layer's
  `rowEnv` consumes: a `GateRow`'s coefficients become `ArgumentEnv.coeff` there. The
  stored row and the evaluation environment share nothing else: `ArgumentEnv` is a
  per-row view of witness *and* coefficients at evaluation time; `GateRow` is the static
  circuit datum (type, coefficients, wiring);
* the **row forms** (`selectorRow`, `coeffRow`, `sigmaAddrRow`) — computable functions
  read off the table: the 0/1 indicator of a gate type, the coefficient columns, and the
  wired-to addresses of the permutation;
* the **interpolants** (`selectorPoly`, `coeffPoly`, `sigmaPoly`) — the `columnPoly`
  images of the row forms, the polynomials the quotient layer consumes; each evaluates
  back to its row form on the domain (`eval_selectorPoly` …), and the sigma interpolants
  are exactly the wiring instantiation's (`sigmaPoly_eq_wiring`, definitional);
* the **wiring permutation** (`wiringPerm`) — the stored successor map is kimchi's
  encoding of the wiring (each cell points to the next cell of its copy cycle); it is a
  permutation by the index's own law, and its underlying function is the stored map
  (`wiringPerm_apply`, definitional).

Gate types are the formalized six plus `zero` (no constraint — padding and wiring-only
rows). Flagged optional gates (range check, foreign field, lookups) are out of scope.
-/

namespace Kimchi.Index

open Polynomial Kimchi.Permutation

/-- The modeled gate types: the six formalized gates and the constraint-free `zero`. -/
inductive GateType where
  | zero
  | generic
  | poseidon
  | completeAdd
  | varBaseMul
  | endoMul
  | endoScalar
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The gate types whose constraints read the *next* row as well as their own
(`witness_next` in kimchi's `ArgumentEnv`; the `cellMap cur nxt` transcriptions in the
quotient layer). Everything else is single-row. -/
def GateType.twoRow : GateType → Bool
  | .poseidon | .varBaseMul | .endoMul => true
  | _ => false

/-- One row of the gate table: the gate type, the fifteen coefficient cells, and the
seven wire pointers (each permuted cell names the next cell of its copy cycle —
kimchi's cyclic-successor encoding of the wiring). The coefficients feed
`ArgumentEnv.coeff` through `rowEnv` when the row is evaluated. -/
structure GateRow (F : Type*) (n : ℕ) where
  typ : GateType
  coeffs : Fin coeffCols → F
  wires : Fin permCols → Fin permCols × Fin n

/-- The wiring as a map on cells, read off a gate table: the stored successor
pointers. -/
private def wiringMapOf {F : Type*} {n : ℕ} (gates : Fin n → GateRow F n)
    (c : Fin permCols × Fin n) : Fin permCols × Fin n :=
  (gates c.2).wires c.1

/-- The index: the gate table and the domain/permutation constants
(`ConstraintSystem`), carrying its laws — a value of this type is wellformed by
construction. On concrete data every law is decidable (the generator and shift
conditions through the `Wiring.lean` certificates), so parsers decide them rather than
assume them. -/
structure _root_.Kimchi.Index (F : Type*) [Field F] (n : ℕ) where
  gates : Fin n → GateRow F n
  publicCount : ℕ
  zkRows : ℕ
  omega : F
  /-- The base-field endomorphism coefficient `β` (a primitive cube root of unity —
  `pallas_endo`/`vesta_endo` at Pasta): kimchi's `cs.endo`, consumed by the `EndoMul`
  gate. The scalar-field eigenvalue `λ` is challenge-expansion data (the sponge's
  `Spec.lam`), not index data. -/
  endoBase : F
  /-- The Poseidon-round MDS matrix — per-curve data like `endoBase`: production
  evaluates the gate expression with `G::sponge_params().mds`, the PROOF curve's
  scalar-side table (`fp_kimchi` for Vesta proofs, `fq_kimchi` for Pallas proofs).
  Data only, no law — the wire correspondence pins it to the deployed table. -/
  mds : Gate.Poseidon.Mds F
  shifts : Fin permCols → F
  omega_prim : IsPrimitiveRoot omega n
  /-- Production's zero-knowledge row count is `(16·nc + 5)/7` (constraints.rs:979),
  which is at least `3` at every chunk count `nc ≥ 1`. The permutation argument's
  three-factor mask needs at least `2` (`zkpm_eval_ne_zero`), and the aggregate degree
  accounting needs `3 ≤ n` — both covered by the production bound. -/
  zk_three : 3 ≤ zkRows
  zk_le : zkRows ≤ n
  public_le : publicCount ≤ n - zkRows
  shifts_coset : CosetShifts omega shifts
  wiring_bijective : Function.Bijective (wiringMapOf gates)
  wiring_region : ∀ c : Fin permCols × Fin n,
    ((c.2 : ℕ) < n - zkRows) ↔ (((wiringMapOf gates c).2 : ℕ) < n - zkRows)
  /-- The public region is kimchi's public-input gadget: the first `publicCount` rows
  are generic gates (`gate.rs` places `GenericGateSpec::Pub` rows first)… -/
  public_generic : ∀ i : Fin n, (i : ℕ) < publicCount → (gates i).typ = .generic
  /-- …carrying the `Pub` coefficient row — `1` in the first cell, `0` elsewhere
  (`generic.rs`: `coeffs[0] = F::one()` over zeros) — so the slot-`0` aggregate member
  pins the first witness column to the public input there… -/
  public_coeffs : ∀ i : Fin n, (i : ℕ) < publicCount →
    ∀ c : Fin coeffCols, (gates i).coeffs c = if c = 0 then 1 else 0
  /-- …and the masked rows are identity-wired: the zero-knowledge rows carry no copy
  constraints, so `Satisfies`' whole-grid copy conjunct closes over them trivially… -/
  masked_identity : ∀ c : Fin permCols × Fin n, n - zkRows ≤ ((c.2 : ℕ)) →
    wiringMapOf gates c = c
  /-- …and carry no gates either: kimchi's gate table stops at the circuit, so no
  constraint *sits on* a masked row — the gate members vanish there because the
  selectors do, whatever the cells hold… -/
  masked_zero : ∀ i : Fin n, n - zkRows ≤ (i : ℕ) → (gates i).typ = .zero
  /-- …and no constraint *reads into* the mask from outside: a two-row gate at the
  last unmasked row would have the first masked row in its footprint. With
  `masked_identity`, `public_le`, and `masked_zero`, this closes the last read edge
  into the mask — the constraint system's whole footprint is the unmasked region,
  so `Satisfies` depends only on the unmasked rows. -/
  masked_boundary : ∀ i : Fin n, (i : ℕ) + 1 = n - zkRows →
    (gates i).typ.twoRow = false


variable {F : Type*} [Field F] {n : ℕ}

/-- The wiring map of the index. -/
def wiringMap (idx : Index F n) : Fin permCols × Fin n → Fin permCols × Fin n :=
  wiringMapOf idx.gates

/-! ## The wiring permutation -/

/-- The wiring as a permutation — the proofs' view of the stored successor map. -/
noncomputable def wiringPerm (idx : Index F n) : Equiv.Perm (Fin permCols × Fin n) :=
  Equiv.ofBijective _ idx.wiring_bijective

theorem wiringPerm_regionPreserving (idx : Index F n) :
    RegionPreserving idx.zkRows idx.wiringPerm :=
  idx.wiring_region

/-! ## Derived columns: row forms -/

/-- The coefficient table — the `qTab` the quotient layer's `rowEnv` consumes. -/
def coeffTable (idx : Index F n) : Fin n → Fin coeffCols → F :=
  fun i => (idx.gates i).coeffs

/-- The boundary row of the unmasked region, `n − zkRows` — the `rowLast` argument of
the permutation constraints. -/
def unmaskedEnd (idx : Index F n) : Fin n :=
  ⟨n - idx.zkRows, by have := idx.zk_three; have := idx.zk_le; omega⟩

/-- The selector column of a gate type: the 0/1 indicator over the rows. -/
def selectorRow (idx : Index F n) (g : GateType) : Fin n → F :=
  fun i => if (idx.gates i).typ = g then 1 else 0

/-- The `c`-th coefficient column over the rows. -/
def coeffRow (idx : Index F n) (c : Fin coeffCols) : Fin n → F :=
  fun i => idx.coeffTable i c

/-- The `col`-th sigma column over the rows: the COMMITTED σ cell — the address of the
wired-to cell, ZEROED on the interior mask rows `[n − zkRows + 2, n − 1)` (production
"Zero out the sigmas in the zk rows", constraints.rs:538–544; the rows where the
three-factor permutation mask lets the recurrence run; empty range at `zkRows = 3`). -/
def sigmaAddrRow (idx : Index F n) (col : Fin permCols) : Fin n → F :=
  fun i => if n - idx.zkRows + 2 ≤ (i : ℕ) ∧ (i : ℕ) < n - 1 then 0
    else addr idx.omega idx.shifts (idx.wiringMap (col, i))

/-! ## Derived columns: interpolants and their bridges -/

/-- The selector polynomial: the interpolant of the indicator column. -/
noncomputable def selectorPoly (idx : Index F n) (g : GateType) : Polynomial F :=
  columnPoly idx.omega (idx.selectorRow g)

/-- The coefficient polynomial of column `c`. -/
noncomputable def coeffPoly (idx : Index F n) (c : Fin coeffCols) : Polynomial F :=
  columnPoly idx.omega (idx.coeffRow c)

/-- The sigma polynomial of column `col`. -/
noncomputable def sigmaPoly (idx : Index F n) (col : Fin permCols) : Polynomial F :=
  columnPoly idx.omega (idx.sigmaAddrRow col)

theorem eval_sigmaPoly (idx : Index F n) (col : Fin permCols) (i : Fin n) :
    (idx.sigmaPoly col).eval (idx.omega ^ (i : ℕ)) = idx.sigmaAddrRow col i :=
  eval_columnPoly idx.omega_prim _ i

/-- The index's sigma interpolants are the wiring instantiation's, at the derived
permutation — definitionally: the stored successor map underlies both. -/
theorem sigmaPoly_eq_wiring (idx : Index F n) (col : Fin permCols) :
    idx.sigmaPoly col
      = Permutation.sigmaPoly idx.omega idx.zkRows idx.shifts idx.wiringPerm col :=
  rfl

/-- Construct an index from raw data by *deciding* every law — the deserialization
boundary: the generator and shift laws through the `Wiring.lean` certificates, the rest
by their `Fintype`/`Decidable` instances. `none` exactly when some law fails. -/
def build? [DecidableEq F] (gates : Fin n → GateRow F n) (publicCount zkRows : ℕ)
    (omega endoBase : F) (mds : Gate.Poseidon.Mds F) (shifts : Fin permCols → F) :
    Option (Index F n) :=
  if h : (∃ k < n + 1, n = 2 ^ k)
      ∧ primitiveRootCertificate omega n = true
      ∧ cosetShiftsCertificate shifts n = true
      ∧ 3 ≤ zkRows ∧ zkRows ≤ n ∧ publicCount ≤ n - zkRows
      ∧ Function.Bijective (wiringMapOf gates)
      ∧ (∀ c : Fin permCols × Fin n,
          ((c.2 : ℕ) < n - zkRows) ↔ (((wiringMapOf gates c).2 : ℕ) < n - zkRows))
      ∧ (∀ i : Fin n, (i : ℕ) < publicCount → (gates i).typ = .generic)
      ∧ (∀ i : Fin n, (i : ℕ) < publicCount →
          ∀ c : Fin coeffCols, (gates i).coeffs c = if c = 0 then 1 else 0)
      ∧ (∀ c : Fin permCols × Fin n, n - zkRows ≤ ((c.2 : ℕ)) → wiringMapOf gates c = c)
      ∧ (∀ i : Fin n, n - zkRows ≤ (i : ℕ) → (gates i).typ = .zero)
      ∧ (∀ i : Fin n, (i : ℕ) + 1 = n - zkRows → (gates i).typ.twoRow = false) then
    have homega : IsPrimitiveRoot omega n :=
      isPrimitiveRoot_of_certificate'
        (let ⟨k, _, hk⟩ := h.1; ⟨k, hk⟩) h.2.1
    some { gates := gates, publicCount := publicCount, zkRows := zkRows
           omega := omega, endoBase := endoBase, mds := mds, shifts := shifts
           omega_prim := homega
           zk_three := h.2.2.2.1
           zk_le := h.2.2.2.2.1
           public_le := h.2.2.2.2.2.1
           shifts_coset := cosetShifts_of_certificate homega h.2.2.1
           wiring_bijective := h.2.2.2.2.2.2.1
           wiring_region := h.2.2.2.2.2.2.2.1
           public_generic := h.2.2.2.2.2.2.2.2.1
           public_coeffs := h.2.2.2.2.2.2.2.2.2.1
           masked_identity := h.2.2.2.2.2.2.2.2.2.2.1
           masked_zero := h.2.2.2.2.2.2.2.2.2.2.2.1
           masked_boundary := h.2.2.2.2.2.2.2.2.2.2.2.2 }
  else none


end Kimchi.Index
