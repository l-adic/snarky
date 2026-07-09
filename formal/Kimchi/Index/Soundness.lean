import Kimchi.Index.Satisfies
import Kimchi.Quotient.Soundness

/-!
# Quotient soundness at the index

The per-family quotient soundness theorems, restated to consume `Index` data. Each gate's
quotient soundness (`Kimchi/Quotient/*`) takes an abstract selector with a booleanness
hypothesis and abstract coefficient/constant inputs; here the selector is the index's own
`selectorRow` (whose booleanness is `selectorRow_boolean` — nothing to assume), the
coefficient table is `coeffTable`, the `EndoMul` constant is `endoBase`, and the
permutation side consumes the index's wiring permutation, shifts, and their bundled laws.
Each conclusion is phrased on gate-typed rows — `(idx.gates i).typ = g → Holds …` —
matching the corresponding `rowSatisfies` branch, and the permutation conclusion is the
copy fragment of `Satisfies` on the unmasked region.

Two deliberate gaps, both Phase-B assembly work, documented where they bite:

* the `generic` bridge concludes the *plain* `Generic.Holds` — the deployed aggregate
  adds the public polynomial to the first generic constraint (`Generic.withPublic` in
  `rowSatisfies`), and the public-aware family is part of the full-aggregate modeling;
* the copy conclusion covers the unmasked region only — the zkpm gating erases the
  argument's grip on the masked rows by design, and `Satisfies`' whole-grid copy
  conjunct holds there for honest witnesses because masked rows are identity-wired.
-/

namespace Kimchi.Index

open Polynomial Kimchi.Quotient

namespace Index

variable {F : Type*} [Field F] [DecidableEq F] {n N : ℕ} [NeZero n]

/-- A selector value of `1` names the row's gate type. -/
theorem selectorRow_eq_one (idx : Index F n) {g : GateType} {i : Fin n}
    (htyp : (idx.gates i).typ = g) : idx.selectorRow g i = 1 := by
  simp [selectorRow, htyp]

/-- **CompleteAdd quotient soundness at the index.** The quotient hypotheses over the
selector-gated constraint family — the selector being the index's own indicator column —
give the gate's `Holds` on every CompleteAdd-typed row. -/
theorem addComplete_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)).length
      → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)).length
      → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .completeAdd) *
        (Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)).get
          c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .completeAdd) *
        (Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)).get
          c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ i, (idx.gates i).typ = .completeAdd →
      Gate.AddComplete.Holds (AddComplete.rowWitness wTab i) := by
  intro i htyp
  exact AddComplete.soundness idx.omega_prim (Nat.pos_of_neZero n) wTab
    (idx.selectorRow .completeAdd) (idx.selectorRow_boolean _) ζ hζ α hα t D hD
    hCdeg htdeg hcheck i (idx.selectorRow_eq_one htyp)

/-- **VarBaseMul quotient soundness at the index.** -/
theorem varBaseMul_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)).length
      → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)).length
      → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .varBaseMul) *
        (Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)).get
          c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .varBaseMul) *
        (Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)).get
          c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ i, (idx.gates i).typ = .varBaseMul →
      Gate.VarBaseMul.Holds (VarBaseMul.rowWitness wTab i) := by
  intro i htyp
  exact VarBaseMul.soundness idx.omega_prim wTab
    (idx.selectorRow .varBaseMul) (idx.selectorRow_boolean _) ζ hζ α hα t D hD
    hCdeg htdeg hcheck i (idx.selectorRow_eq_one htyp)

/-- **EndoMul quotient soundness at the index.** The endomorphism constant is the
index's `endoBase`. -/
theorem endoMul_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.EndoMul.constraints (C idx.endoBase)
      (EndoMul.polyWitness idx.omega wTab)).length → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.EndoMul.constraints (C idx.endoBase)
      (EndoMul.polyWitness idx.omega wTab)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .endoMul) *
        (Gate.EndoMul.constraints (C idx.endoBase)
          (EndoMul.polyWitness idx.omega wTab)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .endoMul) *
        (Gate.EndoMul.constraints (C idx.endoBase)
          (EndoMul.polyWitness idx.omega wTab)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ i, (idx.gates i).typ = .endoMul →
      Gate.EndoMul.Holds idx.endoBase (EndoMul.rowWitness wTab i) := by
  intro i htyp
  exact EndoMul.soundness idx.endoBase idx.omega_prim wTab
    (idx.selectorRow .endoMul) (idx.selectorRow_boolean _) ζ hζ α hα t D hD
    hCdeg htdeg hcheck i (idx.selectorRow_eq_one htyp)

/-- **EndoScalar quotient soundness at the index.** -/
theorem endoScalar_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.EndoScalar.constraints
      (EndoScalar.polyWitness idx.omega wTab) (F := F)).length → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.EndoScalar.constraints
      (EndoScalar.polyWitness idx.omega wTab) (F := F)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .endoScalar) *
        (Gate.EndoScalar.constraints
          (EndoScalar.polyWitness idx.omega wTab) (F := F)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .endoScalar) *
        (Gate.EndoScalar.constraints
          (EndoScalar.polyWitness idx.omega wTab) (F := F)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ i, (idx.gates i).typ = .endoScalar →
      Gate.EndoScalar.Holds (EndoScalar.rowWitness wTab i) := by
  intro i htyp
  exact EndoScalar.soundness idx.omega_prim (Nat.pos_of_neZero n) wTab
    (idx.selectorRow .endoScalar) (idx.selectorRow_boolean _) ζ hζ α hα t D hD
    hCdeg htdeg hcheck i (idx.selectorRow_eq_one htyp)

/-- **Poseidon quotient soundness at the index.** The round constants are the index's
coefficient columns (`rcPoly` over `coeffTable`); the conclusion's round-constant view
is `rcMap (idx.coeffTable i)` — the `rowSatisfies` spelling — definitionally. -/
theorem poseidon_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.Poseidon.constraints (Poseidon.rcPoly idx.omega idx.coeffTable)
      (Poseidon.polyWitness idx.omega wTab)).length → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.Poseidon.constraints (Poseidon.rcPoly idx.omega idx.coeffTable)
      (Poseidon.polyWitness idx.omega wTab)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .poseidon) *
        (Gate.Poseidon.constraints (Poseidon.rcPoly idx.omega idx.coeffTable)
          (Poseidon.polyWitness idx.omega wTab)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .poseidon) *
        (Gate.Poseidon.constraints (Poseidon.rcPoly idx.omega idx.coeffTable)
          (Poseidon.polyWitness idx.omega wTab)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ i, (idx.gates i).typ = .poseidon →
      Gate.Poseidon.Holds (Poseidon.rcMap (idx.coeffTable i))
        (Poseidon.rowWitness wTab i) := by
  intro i htyp
  exact Poseidon.soundness idx.omega_prim wTab idx.coeffTable
    (idx.selectorRow .poseidon) (idx.selectorRow_boolean _) ζ hζ α hα t D hD
    hCdeg htdeg hcheck i (idx.selectorRow_eq_one htyp)

/-- **Generic quotient soundness at the index**, through the `Argument` engine. The
conclusion is the *plain* `Generic.Holds` on the row's coefficients and cells; the
deployed aggregate adds the public polynomial to the first generic constraint
(`Generic.withPublic` in `rowSatisfies`), and that public-aware family belongs to the
full-aggregate assembly (Phase B). -/
theorem generic_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin ((genericArgument (F := F)).constraints
      (polyEnv idx.omega wTab idx.coeffTable)).length → F)
    (hα : Function.Injective α)
    (t : Fin ((genericArgument (F := F)).constraints
      (polyEnv idx.omega wTab idx.coeffTable)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .generic) *
        ((genericArgument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c =>
        columnPoly idx.omega (idx.selectorRow .generic) *
        ((genericArgument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ i, (idx.gates i).typ = .generic →
      Gate.Generic.Holds ⟨idx.coeffTable i, wTab i⟩ := by
  intro i htyp
  have h := (genericArgument (F := F)).soundness idx.omega_prim wTab idx.coeffTable
    (idx.selectorRow .generic) (idx.selectorRow_boolean _) ζ hζ α hα t D hD
    hCdeg htdeg hcheck i (idx.selectorRow_eq_one htyp)
  simpa [genericArgument, genericCellMap, rowEnv, Gate.Generic.Holds] using h

/-! ## Copy soundness at the index -/

open Kimchi.Quotient.Permutation in
/-- The witness table's permuted columns as interpolants — what the permutation
argument's committed columns are for a table witness. -/
noncomputable def permWitnessPoly (idx : Index F n) (wTab : Fin n → Fin 15 → F) :
    Fin 7 → Polynomial F :=
  fun col => columnPoly idx.omega (fun j => cellValue wTab (col, j))

theorem eval_permWitnessPoly (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (col : Fin 7) (j : Fin n) :
    (idx.permWitnessPoly wTab col).eval (idx.omega ^ (j : ℕ)) = cellValue wTab (col, j) :=
  eval_columnPoly idx.omega_prim _ j

open Kimchi.Quotient.Permutation in
/-- **Copy soundness at the index, divisibility form.** For the index's wiring, shifts,
and sigma columns (all bundled laws): if at every node of an injective `(β, γ)` grid the
prover supplies an accumulator whose three permutation constraints are divisible by
`Z_H`, the witness takes equal values across every wire of the unmasked region. This is
the copy fragment of `Satisfies` there; the masked rows are outside the argument's grip
by design (zkpm gating), and honest witnesses satisfy them because masked rows are
identity-wired. -/
theorem copy_soundness_of_dvd (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    {M NN : ℕ} (b : Fin M → F) (g : Fin NN → F)
    (hb : Function.Injective b) (hg : Function.Injective g)
    (hM : 7 * (n - idx.zkRows) < M) (hN : 7 * (n - idx.zkRows) < NN)
    (zg : Fin M → Fin NN → Polynomial F)
    (hdvd : ∀ a c s, zH F n ∣ Permutation.constraints idx.omega idx.zkRows (zg a c)
      (idx.permWitnessPoly wTab)
      (Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) idx.shifts
      (b a) (g c) (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd s) :
    ∀ c : Fin 7 × Fin (n - idx.zkRows),
      cellValue wTab (idx.wiringMap (embCell idx.zkRows c))
        = cellValue wTab (embCell idx.zkRows c) := by
  intro c
  have h := copy_soundness_wired_of_dvd idx.omega_prim (Nat.pos_of_neZero n) idx.zk_pos
    idx.zk_le (idx.permWitnessPoly wTab) idx.shifts idx.shifts_coset idx.wiringPerm
    idx.wiringPerm_regionPreserving b g hb hg hM hN zg hdvd c
  rw [show idx.wiringPerm (embCell idx.zkRows c) = idx.wiringMap (embCell idx.zkRows c)
      from rfl] at h
  rw [eval_permWitnessPoly] at h
  rw [show idx.omega ^ ((c.2 : ℕ)) = idx.omega ^ (((embCell idx.zkRows c).2 : Fin n) : ℕ)
      from rfl, eval_permWitnessPoly] at h
  exact h

open Kimchi.Quotient.Permutation in
/-- **Copy soundness at the index.** As `copy_soundness_of_dvd`, with each grid node's
divisibilities obtained from the derandomized quotient checks. -/
theorem copy_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    {M NN NNN : ℕ} (b : Fin M → F) (g : Fin NN → F)
    (hb : Function.Injective b) (hg : Function.Injective g)
    (hM : 7 * (n - idx.zkRows) < M) (hN : 7 * (n - idx.zkRows) < NN)
    (zg : Fin M → Fin NN → Polynomial F)
    (α : Fin M → Fin NN → Fin 3 → F) (hα : ∀ a c, Function.Injective (α a c))
    (ζ : Fin M → Fin NN → Fin NNN → F) (hζ : ∀ a c, Function.Injective (ζ a c))
    (t : Fin M → Fin NN → Fin 3 → Polynomial F) (D : ℕ) (hD : D < NNN)
    (hCdeg : ∀ a c s, (aggregate (α a c s)
      (Permutation.constraints idx.omega idx.zkRows (zg a c)
        (idx.permWitnessPoly wTab)
        (Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) idx.shifts
        (b a) (g c) (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd)).natDegree ≤ D)
    (htdeg : ∀ a c s, (t a c s * zH F n).natDegree ≤ D)
    (hcheck : ∀ a c s p, (aggregate (α a c s)
      (Permutation.constraints idx.omega idx.zkRows (zg a c)
        (idx.permWitnessPoly wTab)
        (Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) idx.shifts
        (b a) (g c) (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd)).eval (ζ a c p)
      = (t a c s * zH F n).eval (ζ a c p)) :
    ∀ c : Fin 7 × Fin (n - idx.zkRows),
      cellValue wTab (idx.wiringMap (embCell idx.zkRows c))
        = cellValue wTab (embCell idx.zkRows c) :=
  idx.copy_soundness_of_dvd wTab b g hb hg hM hN zg fun a c =>
    dvd_of_evalCheck idx.omega_prim (Nat.pos_of_neZero n) (ζ a c) (hζ a c) (α a c)
      (hα a c) _ (t a c) D hD (hCdeg a c) (htdeg a c) (hcheck a c)

end Index

end Kimchi.Index
