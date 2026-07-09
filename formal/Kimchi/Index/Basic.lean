import Kimchi.Quotient.Wiring

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
certificates of `Kimchi/Quotient/Wiring.lean`, the rest by `Fintype` instances — so
parsers construct indices by deciding, never by trusting.

**One stored representation.** The table is `Fin`-indexed data; the satisfiability
predicate (milestone A2) and every proof consume it directly. Everything else is a
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

open Polynomial Kimchi.Quotient Kimchi.Quotient.Permutation

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

/-- One row of the gate table: the gate type, the fifteen coefficient cells, and the
seven wire pointers (each permuted cell names the next cell of its copy cycle —
kimchi's cyclic-successor encoding of the wiring). The coefficients feed
`ArgumentEnv.coeff` through `rowEnv` when the row is evaluated. -/
structure GateRow (F : Type*) (n : ℕ) where
  typ : GateType
  coeffs : Fin 15 → F
  wires : Fin 7 → Fin 7 × Fin n

/-- The wiring as a map on cells, read off a gate table: the stored successor
pointers. -/
def wiringMapOf {F : Type*} {n : ℕ} (gates : Fin n → GateRow F n)
    (c : Fin 7 × Fin n) : Fin 7 × Fin n :=
  (gates c.2).wires c.1

/-- The index: the gate table and the domain/permutation constants
(`ConstraintSystem`), carrying its laws — a value of this type is wellformed by
construction. On concrete data every law is decidable (the generator and shift
conditions through the `Wiring.lean` certificates), so parsers decide them rather than
assume them. -/
structure Index (F : Type*) [Field F] (n : ℕ) where
  gates : Fin n → GateRow F n
  publicCount : ℕ
  zkRows : ℕ
  omega : F
  /-- The base-field endomorphism coefficient `β` (a primitive cube root of unity —
  `pallas_endo`/`vesta_endo` at Pasta): kimchi's `cs.endo`, consumed by the `EndoMul`
  gate. The scalar-field eigenvalue `λ` is challenge-expansion data (the sponge's
  `Spec.lam`), not index data. -/
  endoBase : F
  shifts : Fin 7 → F
  omega_prim : IsPrimitiveRoot omega n
  zk_pos : 0 < zkRows
  zk_le : zkRows ≤ n
  public_le : publicCount ≤ n - zkRows
  shifts_coset : CosetShifts omega shifts
  wiring_bijective : Function.Bijective (wiringMapOf gates)
  wiring_region : ∀ c : Fin 7 × Fin n,
    ((c.2 : ℕ) < n - zkRows) ↔ (((wiringMapOf gates c).2 : ℕ) < n - zkRows)
  /-- The public region is kimchi's public-input gadget: the first `publicCount` rows
  are generic gates (`gate.rs` places `GenericGateSpec::Pub` rows first)… -/
  public_generic : ∀ i : Fin n, (i : ℕ) < publicCount → (gates i).typ = .generic
  /-- …carrying the `Pub` coefficient row — `1` in the first cell, `0` elsewhere
  (`generic.rs`: `coeffs[0] = F::one()` over zeros) — so the slot-`0` aggregate member
  pins the first witness column to the public input there… -/
  public_coeffs : ∀ i : Fin n, (i : ℕ) < publicCount →
    ∀ c : Fin 15, (gates i).coeffs c = if c = 0 then 1 else 0
  /-- …and the masked rows are identity-wired: the zero-knowledge rows carry no copy
  constraints, so `Satisfies`' whole-grid copy conjunct closes over them trivially. -/
  masked_identity : ∀ c : Fin 7 × Fin n, n - zkRows ≤ ((c.2 : ℕ)) →
    wiringMapOf gates c = c

namespace Index

variable {F : Type*} [Field F] {n : ℕ}

/-- The wiring map of the index. -/
def wiringMap (idx : Index F n) : Fin 7 × Fin n → Fin 7 × Fin n :=
  wiringMapOf idx.gates

/-! ## The wiring permutation -/

/-- The wiring as a permutation — the proofs' view of the stored successor map. -/
noncomputable def wiringPerm (idx : Index F n) : Equiv.Perm (Fin 7 × Fin n) :=
  Equiv.ofBijective _ idx.wiring_bijective

@[simp]
theorem wiringPerm_apply (idx : Index F n) (c : Fin 7 × Fin n) :
    idx.wiringPerm c = idx.wiringMap c :=
  rfl

theorem wiringPerm_regionPreserving (idx : Index F n) :
    RegionPreserving idx.zkRows idx.wiringPerm :=
  idx.wiring_region

/-! ## Derived columns: row forms -/

/-- The coefficient table — the `qTab` the quotient layer's `rowEnv` consumes. -/
def coeffTable (idx : Index F n) : Fin n → Fin 15 → F :=
  fun i => (idx.gates i).coeffs

/-- The selector column of a gate type: the 0/1 indicator over the rows. -/
def selectorRow (idx : Index F n) (g : GateType) : Fin n → F :=
  fun i => if (idx.gates i).typ = g then 1 else 0

theorem selectorRow_boolean (idx : Index F n) (g : GateType) (i : Fin n) :
    idx.selectorRow g i = 0 ∨ idx.selectorRow g i = 1 := by
  unfold selectorRow
  split <;> simp

/-- The `c`-th coefficient column over the rows. -/
def coeffRow (idx : Index F n) (c : Fin 15) : Fin n → F :=
  fun i => idx.coeffTable i c

/-- The `col`-th sigma column over the rows: the address of the wired-to cell. -/
def sigmaAddrRow (idx : Index F n) (col : Fin 7) : Fin n → F :=
  fun i => addr idx.omega idx.shifts (idx.wiringMap (col, i))

/-! ## Derived columns: interpolants and their bridges -/

/-- The selector polynomial: the interpolant of the indicator column. -/
noncomputable def selectorPoly (idx : Index F n) (g : GateType) : Polynomial F :=
  columnPoly idx.omega (idx.selectorRow g)

/-- The coefficient polynomial of column `c`. -/
noncomputable def coeffPoly (idx : Index F n) (c : Fin 15) : Polynomial F :=
  columnPoly idx.omega (idx.coeffRow c)

/-- The sigma polynomial of column `col`. -/
noncomputable def sigmaPoly (idx : Index F n) (col : Fin 7) : Polynomial F :=
  columnPoly idx.omega (idx.sigmaAddrRow col)

theorem eval_selectorPoly (idx : Index F n) (g : GateType) (i : Fin n) :
    (idx.selectorPoly g).eval (idx.omega ^ (i : ℕ)) = idx.selectorRow g i :=
  eval_columnPoly idx.omega_prim _ i

theorem eval_coeffPoly (idx : Index F n) (c : Fin 15) (i : Fin n) :
    (idx.coeffPoly c).eval (idx.omega ^ (i : ℕ)) = idx.coeffRow c i :=
  eval_columnPoly idx.omega_prim _ i

theorem eval_sigmaPoly (idx : Index F n) (col : Fin 7) (i : Fin n) :
    (idx.sigmaPoly col).eval (idx.omega ^ (i : ℕ)) = idx.sigmaAddrRow col i :=
  eval_columnPoly idx.omega_prim _ i

/-- The index's sigma interpolants are the wiring instantiation's, at the derived
permutation — definitionally: the stored successor map underlies both. -/
theorem sigmaPoly_eq_wiring (idx : Index F n) (col : Fin 7) :
    idx.sigmaPoly col
      = Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm col :=
  rfl

/-- Construct an index from raw data by *deciding* every law — the deserialization
boundary: the generator and shift laws through the `Wiring.lean` certificates, the rest
by their `Fintype`/`Decidable` instances. `none` exactly when some law fails. -/
def build? [DecidableEq F] (gates : Fin n → GateRow F n) (publicCount zkRows : ℕ)
    (omega endoBase : F) (shifts : Fin 7 → F) : Option (Index F n) :=
  if h : (∃ k < n + 1, n = 2 ^ k)
      ∧ primitiveRootCertificate omega n = true
      ∧ cosetShiftsCertificate shifts n = true
      ∧ 0 < zkRows ∧ zkRows ≤ n ∧ publicCount ≤ n - zkRows
      ∧ Function.Bijective (wiringMapOf gates)
      ∧ (∀ c : Fin 7 × Fin n,
          ((c.2 : ℕ) < n - zkRows) ↔ (((wiringMapOf gates c).2 : ℕ) < n - zkRows))
      ∧ (∀ i : Fin n, (i : ℕ) < publicCount → (gates i).typ = .generic)
      ∧ (∀ i : Fin n, (i : ℕ) < publicCount →
          ∀ c : Fin 15, (gates i).coeffs c = if c = 0 then 1 else 0)
      ∧ (∀ c : Fin 7 × Fin n, n - zkRows ≤ ((c.2 : ℕ)) → wiringMapOf gates c = c) then
    have homega : IsPrimitiveRoot omega n :=
      isPrimitiveRoot_of_certificate'
        (let ⟨k, _, hk⟩ := h.1; ⟨k, hk⟩) h.2.1
    some { gates := gates, publicCount := publicCount, zkRows := zkRows
           omega := omega, endoBase := endoBase, shifts := shifts
           omega_prim := homega
           zk_pos := h.2.2.2.1
           zk_le := h.2.2.2.2.1
           public_le := h.2.2.2.2.2.1
           shifts_coset := cosetShifts_of_certificate homega h.2.2.1
           wiring_bijective := h.2.2.2.2.2.2.1
           wiring_region := h.2.2.2.2.2.2.2.1
           public_generic := h.2.2.2.2.2.2.2.2.1
           public_coeffs := h.2.2.2.2.2.2.2.2.2.1
           masked_identity := h.2.2.2.2.2.2.2.2.2.2 }
  else none

end Index

end Kimchi.Index
