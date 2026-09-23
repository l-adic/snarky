import Kimchi.Permutation.Wiring
import Kimchi.Gate.Poseidon

/-!
# The kimchi index: the circuit as data

A kimchi circuit as the constraint system carries it (proof-systems
`circuits/constraints.rs`): a gate table — one `GateRow` per domain row, with its gate type,
coefficient cells and wire pointers — plus the domain generator, the coset shifts, the
base-field endomorphism coefficient, the Poseidon MDS matrix, and the zero-knowledge and
public-input row counts. A value of `Index F n` carries its laws (primitive generator, coset
shifts, bounded row regions, a region-preserving bijective wiring), so it is wellformed by
construction. On concrete data every law is decidable, and `build?` constructs an index by
deciding them.

## One stored representation

The table is `Fin`-indexed data; `Satisfies` and every proof consume it directly. Everything
else is a derived view, bridged at its definition:

* `coeffTable` — the coefficient table, read as `ArgumentEnv.coeff` by the quotient layer;
* the row forms `selectorRow`, `coeffRow`, `sigmaAddrRow` — a gate type's 0/1 indicator, a
  coefficient column, and a committed σ column;
* the interpolants `selectorPoly`, `coeffPoly`, `sigmaPoly` — the `columnPoly` images of the
  row forms; the sigma ones are the wiring instantiation's (`sigmaPoly_eq_wiring`);
* `wiringPerm` — the stored successor map as a permutation.

Gate types are the six formalized gates plus `zero` (padding and wiring-only rows). The
optional gates (range check, foreign field, lookups) are out of scope.
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
  deriving DecidableEq, Inhabited, Fintype

/-- The gate types whose constraints also read the next row (`ArgumentEnv.witnessNext`). -/
private def GateType.twoRow : GateType → Bool
  | .poseidon | .varBaseMul | .endoMul => true
  | _ => false

/-- One row of the gate table: its gate type, coefficient cells and wire pointers. -/
structure GateRow (F : Type*) (n : ℕ) where
  /-- The row's gate type. -/
  typ : GateType
  /-- The row's coefficient cells (`coeffCols`), read as `ArgumentEnv.coeff`. -/
  coeffs : Fin coeffCols → F
  /-- The row's wire pointers (`permCols`): each permuted cell names the next cell of its
  copy cycle. -/
  wires : Fin permCols → Fin permCols × Fin n

/-- A gate table's wire pointers as a map on cells. -/
private def wiringMapOf {F : Type*} {n : ℕ} (gates : Fin n → GateRow F n)
    (c : Fin permCols × Fin n) : Fin permCols × Fin n :=
  (gates c.2).wires c.1

/-- The index: the gate table and the domain and permutation constants, carrying their
laws. `build?` decides the laws on concrete data. -/
structure _root_.Kimchi.Index (F : Type*) [Field F] (n : ℕ) where
  /-- The gate table: one `GateRow` per domain row. -/
  gates : Fin n → GateRow F n
  /-- The number of public-input rows. -/
  publicCount : ℕ
  /-- The number of zero-knowledge rows. -/
  zkRows : ℕ
  /-- The domain generator, a primitive `n`-th root of unity (`omega_prim`). -/
  omega : F
  /-- The base-field endomorphism coefficient `β`, a primitive cube root of unity
  (`pallasEndo`/`vestaEndo` at Pasta), read by the `EndoMul` gate. The scalar-field
  eigenvalue `λ` (`EndoSpec.lam`) is challenge-expansion data, not index data. -/
  endoBase : F
  /-- The Poseidon gate's MDS matrix: per-curve data, the proof curve's scalar-side sponge
  table. No law constrains it here. -/
  mds : Gate.Poseidon.Mds F
  /-- The permutation coset shifts, one per permuted column (`shifts_coset`). -/
  shifts : Fin permCols → F
  omega_prim : IsPrimitiveRoot omega n
  /-- Production's zero-knowledge row count `(16·nc + 5)/7` is at least `3` at every chunk
  count `nc ≥ 1`; the permutation argument's three-factor mask needs at least `2`. -/
  zk_three : 3 ≤ zkRows
  zk_le : zkRows ≤ n
  public_le : publicCount ≤ n - zkRows
  shifts_coset : CosetShifts omega shifts
  wiring_bijective : Function.Bijective (wiringMapOf gates)
  wiring_region : ∀ c : Fin permCols × Fin n,
    ((c.2 : ℕ) < n - zkRows) ↔ (((wiringMapOf gates c).2 : ℕ) < n - zkRows)
  /-- The first `publicCount` rows are the public-input rows: generic gates… -/
  public_generic : ∀ i : Fin n, (i : ℕ) < publicCount → (gates i).typ = .generic
  /-- …with coefficients `1` in the first cell and `0` elsewhere, so the slot-`0` aggregate
  member pins the first witness column to the public input there… -/
  public_coeffs : ∀ i : Fin n, (i : ℕ) < publicCount →
    ∀ c : Fin coeffCols, (gates i).coeffs c = if c = 0 then 1 else 0
  /-- …and the masked rows are identity-wired, so `Satisfies`' whole-grid copy conjunct
  holds on them trivially… -/
  masked_identity : ∀ c : Fin permCols × Fin n, n - zkRows ≤ ((c.2 : ℕ)) →
    wiringMapOf gates c = c
  /-- …and carry no gate, so every selector, and with it every gate member, vanishes
  there… -/
  masked_zero : ∀ i : Fin n, n - zkRows ≤ (i : ℕ) → (gates i).typ = .zero
  /-- …and the last unmasked row holds no two-row gate, whose footprint would reach the
  first masked row. Together these make `Satisfies` depend only on the unmasked rows. -/
  masked_boundary : ∀ i : Fin n, (i : ℕ) + 1 = n - zkRows →
    (gates i).typ.twoRow = false


variable {F : Type*} [Field F] {n : ℕ}

/-- The wiring map of the index. -/
def wiringMap (idx : Index F n) : Fin permCols × Fin n → Fin permCols × Fin n :=
  wiringMapOf idx.gates

/-! ## The wiring permutation -/

/-- The wiring map as a permutation of the cells. -/
noncomputable def wiringPerm (idx : Index F n) : Equiv.Perm (Fin permCols × Fin n) :=
  Equiv.ofBijective _ idx.wiring_bijective

/-! ## Derived columns: row forms -/

/-- The coefficient table: each row's coefficient cells. -/
def coeffTable (idx : Index F n) : Fin n → Fin coeffCols → F :=
  fun i => (idx.gates i).coeffs

/-- The first masked row, `n − zkRows`: the end row passed to `Permutation.constraints`. -/
def unmaskedEnd (idx : Index F n) : Fin n :=
  ⟨n - idx.zkRows, by have := idx.zk_three; have := idx.zk_le; omega⟩

/-- The selector column of a gate type: the 0/1 indicator over the rows. -/
def selectorRow (idx : Index F n) (g : GateType) : Fin n → F :=
  fun i => if (idx.gates i).typ = g then 1 else 0

/-- The `c`-th coefficient column over the rows. -/
def coeffRow (idx : Index F n) (c : Fin coeffCols) : Fin n → F :=
  fun i => idx.coeffTable i c

/-- The `col`-th committed σ column: the address of the wired-to cell, zeroed on the
interior mask rows `[n − zkRows + 2, n − 1)` as in `Permutation.sigmaPoly`. -/
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

/-- The sigma interpolants are `Permutation.sigmaPoly` at `wiringPerm`, definitionally. -/
theorem sigmaPoly_eq_wiring (idx : Index F n) (col : Fin permCols) :
    idx.sigmaPoly col
      = Permutation.sigmaPoly idx.omega idx.zkRows idx.shifts idx.wiringPerm col :=
  rfl

/-- The index of a cell in the wiring tables: column-major, `c·n + i`. -/
private def cellIdx {n : ℕ} (c : Fin permCols × Fin n) : ℕ := (c.1 : ℕ) * n + (c.2 : ℕ)

/-- The predecessor table of a gate table's wiring, built in one pass: at each cell's
index, the cell whose pointer names it, if any. -/
private def wiringPredTable {F : Type*} {n : ℕ} (gates : Fin n → GateRow F n) :
    Array (Option (Fin permCols × Fin n)) :=
  (List.finRange n).foldl
    (fun tab i => (List.finRange permCols).foldl
      (fun tab c => tab.setIfInBounds (cellIdx (wiringMapOf gates (c, i))) (some (c, i))) tab)
    (Array.replicate (permCols * n) none)

/-- The map a predecessor table encodes; a cell without an entry maps to itself. -/
private def wiringPred {n : ℕ} (tab : Array (Option (Fin permCols × Fin n)))
    (y : Fin permCols × Fin n) : Fin permCols × Fin n :=
  ((tab[cellIdx y]?).bind id).getD y

/-- Construct an index from raw data by deciding every law: the generator and shift laws
through `primitiveRootCertificate` and `cosetShiftsCertificate`, the wiring's bijectivity
through two round trips with its predecessor table (linear in the cells, where deciding
`Function.Bijective` outright is quadratic), the rest by their decidability instances.
`none` exactly when a law fails or `n` is not a power of two. -/
def build? [DecidableEq F] (gates : Fin n → GateRow F n) (publicCount zkRows : ℕ)
    (omega endoBase : F) (mds : Gate.Poseidon.Mds F) (shifts : Fin permCols → F) :
    Option (Index F n) :=
  let pred := wiringPredTable gates
  if h : (∃ k < n + 1, n = 2 ^ k)
      ∧ primitiveRootCertificate omega n = true
      ∧ cosetShiftsCertificate shifts n = true
      ∧ 3 ≤ zkRows ∧ zkRows ≤ n ∧ publicCount ≤ n - zkRows
      ∧ (∀ x : Fin permCols × Fin n, wiringPred pred (wiringMapOf gates x) = x)
      ∧ (∀ y : Fin permCols × Fin n, wiringMapOf gates (wiringPred pred y) = y)
      ∧ (∀ c : Fin permCols × Fin n,
          ((c.2 : ℕ) < n - zkRows) ↔ (((wiringMapOf gates c).2 : ℕ) < n - zkRows))
      ∧ (∀ i : Fin n, (i : ℕ) < publicCount → (gates i).typ = .generic)
      ∧ (∀ i : Fin n, (i : ℕ) < publicCount →
          ∀ c : Fin coeffCols, (gates i).coeffs c = if c = 0 then 1 else 0)
      ∧ (∀ c : Fin permCols × Fin n, n - zkRows ≤ ((c.2 : ℕ)) → wiringMapOf gates c = c)
      ∧ (∀ i : Fin n, n - zkRows ≤ (i : ℕ) → (gates i).typ = .zero)
      ∧ (∀ i : Fin n, (i : ℕ) + 1 = n - zkRows → (gates i).typ.twoRow = false) then
    have ⟨hpow, hprim, hcoset, hzk_three, hzk_le, hpublic_le, hleft, hright, hregion,
      hgeneric, hcoeffs, hmask_id, hmask_zero, hmask_boundary⟩ := h
    have hbij : Function.Bijective (wiringMapOf gates) :=
      Function.bijective_iff_has_inverse.mpr ⟨wiringPred pred, hleft, hright⟩
    have homega : IsPrimitiveRoot omega n :=
      isPrimitiveRoot_of_certificate' (let ⟨k, _, hk⟩ := hpow; ⟨k, hk⟩) hprim
    some { gates := gates, publicCount := publicCount, zkRows := zkRows
           omega := omega, endoBase := endoBase, mds := mds, shifts := shifts
           omega_prim := homega
           zk_three := hzk_three
           zk_le := hzk_le
           public_le := hpublic_le
           shifts_coset := cosetShifts_of_certificate homega hcoset
           wiring_bijective := hbij
           wiring_region := hregion
           public_generic := hgeneric
           public_coeffs := hcoeffs
           masked_identity := hmask_id
           masked_zero := hmask_zero
           masked_boundary := hmask_boundary }
  else none


end Kimchi.Index
