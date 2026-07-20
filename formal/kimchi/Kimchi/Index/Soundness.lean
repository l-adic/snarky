import Kimchi.Index.Satisfies
import Kimchi.Quotient.Soundness
import Kimchi.Quotient.SchwartzZippel

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

## Single-challenge (counting Schwartz–Zippel) form

The random-challenge surrogate is now the **counting** argument, not the injective-α family:
each theorem consumes ONE challenge `α : F` known to lie outside the proved-small bad set
`badAlphas <constraint family> ω n` (`|badAlphas| ≤ n · (K − 1)` by `card_badAlphas_le`), and
ONE quotient `t : Polynomial F`. The per-challenge `∀ s` quantifier is gone. The evaluation
challenge is likewise a single `ζ : F` known to lie outside `badZetas <aggregate> t n` — the
ζ-node family has been collapsed to one counting challenge, so the injective ζ vector, its
degree bounds `D`, and the per-node `∀ p` are all gone. Every delegation goes through
`Argument.soundness`, the single-(α, ζ) analogue of `Kimchi.Quotient.Argument.soundness`
composing `dvd_of_evalCheck`.

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


variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} [NeZero n]

/-! ## Project-local Mathlib supplement — single-α Argument soundness -/

omit [DecidableEq F] [NeZero n] in
/-- A selector value of `1` names the row's gate type. -/
theorem selectorRow_eq_one (idx : Index F n) {g : GateType} {i : Fin n}
    (htyp : (idx.gates i).typ = g) : idx.selectorRow g i = 1 := by
  simp [selectorRow, htyp]

/-- **CompleteAdd quotient soundness at the index.** The single-α quotient hypotheses over the
selector-gated constraint family — the selector being the index's own indicator column, the
challenge `α` outside `badAlphas` — give the gate's `Holds` on every CompleteAdd-typed row. -/
theorem addComplete_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (α : F)
    (hα : α ∉ badAlphas (fun c =>
        columnPoly idx.omega (idx.selectorRow .completeAdd) *
        (Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)).get c)
      idx.omega n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .completeAdd) *
        (Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)).get c))
      t n)
    (hcheck : (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .completeAdd) *
        (Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)).get
          c)).eval ζ
        = (t * zH F n).eval ζ) :
    ∀ i, (idx.gates i).typ = .completeAdd →
      Gate.AddComplete.Holds (AddComplete.rowWitness wTab i) := by
  intro i htyp
  exact Argument.soundness AddComplete.argument idx.omega_prim wTab wTab
    (idx.selectorRow .completeAdd) (idx.selectorRow_boolean _) α hα t ζ hζ
    hcheck i (idx.selectorRow_eq_one htyp)

/-- **VarBaseMul quotient soundness at the index.** -/
theorem varBaseMul_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (α : F)
    (hα : α ∉ badAlphas (fun c =>
        columnPoly idx.omega (idx.selectorRow .varBaseMul) *
        (Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)).get c)
      idx.omega n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .varBaseMul) *
        (Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)).get c))
      t n)
    (hcheck : (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .varBaseMul) *
        (Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)).get
          c)).eval ζ
        = (t * zH F n).eval ζ) :
    ∀ i, (idx.gates i).typ = .varBaseMul →
      Gate.VarBaseMul.Holds (VarBaseMul.rowWitness wTab i) := by
  intro i htyp
  exact Argument.soundness VarBaseMul.argument idx.omega_prim wTab wTab
    (idx.selectorRow .varBaseMul) (idx.selectorRow_boolean _) α hα t ζ hζ
    hcheck i (idx.selectorRow_eq_one htyp)

/-- **EndoMul quotient soundness at the index.** The endomorphism constant is the
index's `endoBase`. -/
theorem endoMul_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (α : F)
    (hα : α ∉ badAlphas (fun c =>
        columnPoly idx.omega (idx.selectorRow .endoMul) *
        (Gate.EndoMul.constraints (C idx.endoBase)
          (EndoMul.polyWitness idx.omega wTab)).get c) idx.omega n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .endoMul) *
        (Gate.EndoMul.constraints (C idx.endoBase)
          (EndoMul.polyWitness idx.omega wTab)).get c)) t n)
    (hcheck : (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .endoMul) *
        (Gate.EndoMul.constraints (C idx.endoBase)
          (EndoMul.polyWitness idx.omega wTab)).get c)).eval ζ
        = (t * zH F n).eval ζ) :
    ∀ i, (idx.gates i).typ = .endoMul →
      Gate.EndoMul.Holds idx.endoBase (EndoMul.rowWitness wTab i) := by
  intro i htyp
  exact Argument.soundness (EndoMul.argument idx.endoBase) idx.omega_prim wTab wTab
    (idx.selectorRow .endoMul) (idx.selectorRow_boolean _) α hα t ζ hζ
    hcheck i (idx.selectorRow_eq_one htyp)

/-- **EndoScalar quotient soundness at the index.** -/
theorem endoScalar_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (α : F)
    (hα : α ∉ badAlphas (fun c =>
        columnPoly idx.omega (idx.selectorRow .endoScalar) *
        (Gate.EndoScalar.constraints
          (EndoScalar.polyWitness idx.omega wTab) (F := F)).get c) idx.omega n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .endoScalar) *
        (Gate.EndoScalar.constraints
          (EndoScalar.polyWitness idx.omega wTab) (F := F)).get c)) t n)
    (hcheck : (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .endoScalar) *
        (Gate.EndoScalar.constraints
          (EndoScalar.polyWitness idx.omega wTab) (F := F)).get c)).eval ζ
        = (t * zH F n).eval ζ) :
    ∀ i, (idx.gates i).typ = .endoScalar →
      Gate.EndoScalar.Holds (EndoScalar.rowWitness wTab i) := by
  intro i htyp
  exact Argument.soundness EndoScalar.argument idx.omega_prim wTab wTab
    (idx.selectorRow .endoScalar) (idx.selectorRow_boolean _) α hα t ζ hζ
    hcheck i (idx.selectorRow_eq_one htyp)

/-- **Poseidon quotient soundness at the index.** The round constants are the index's
coefficient columns (`rcPoly` over `coeffTable`); the conclusion's round-constant view
is `rcMap (idx.coeffTable i)` — the `rowSatisfies` spelling — definitionally. -/
theorem poseidon_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (α : F)
    (hα : α ∉ badAlphas (fun c =>
        columnPoly idx.omega (idx.selectorRow .poseidon) *
        (Gate.Poseidon.constraints (Poseidon.rcPoly idx.omega idx.coeffTable)
          (Poseidon.polyWitness idx.omega wTab)).get c) idx.omega n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .poseidon) *
        (Gate.Poseidon.constraints (Poseidon.rcPoly idx.omega idx.coeffTable)
          (Poseidon.polyWitness idx.omega wTab)).get c)) t n)
    (hcheck : (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .poseidon) *
        (Gate.Poseidon.constraints (Poseidon.rcPoly idx.omega idx.coeffTable)
          (Poseidon.polyWitness idx.omega wTab)).get c)).eval ζ
        = (t * zH F n).eval ζ) :
    ∀ i, (idx.gates i).typ = .poseidon →
      Gate.Poseidon.Holds (Poseidon.rcMap (idx.coeffTable i))
        (Poseidon.rowWitness wTab i) := by
  intro i htyp
  exact Argument.soundness Poseidon.argument idx.omega_prim wTab idx.coeffTable
    (idx.selectorRow .poseidon) (idx.selectorRow_boolean _) α hα t ζ hζ
    hcheck i (idx.selectorRow_eq_one htyp)

/-- **Generic quotient soundness at the index**, through the `Argument` engine. The
conclusion is the *plain* `Generic.Holds` on the row's coefficients and cells; the
deployed aggregate adds the public polynomial to the first generic constraint
(`Generic.withPublic` in `rowSatisfies`), and that public-aware family belongs to the
full-aggregate assembly (Phase B). -/
theorem generic_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (α : F)
    (hα : α ∉ badAlphas (fun c =>
        columnPoly idx.omega (idx.selectorRow .generic) *
        ((genericArgument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable)).get c) idx.omega n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .generic) *
        ((genericArgument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable)).get c)) t n)
    (hcheck : (aggregate α (fun c =>
        columnPoly idx.omega (idx.selectorRow .generic) *
        ((genericArgument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable)).get c)).eval ζ
        = (t * zH F n).eval ζ) :
    ∀ i, (idx.gates i).typ = .generic →
      Gate.Generic.Holds ⟨idx.coeffTable i, wTab i⟩ := by
  intro i htyp
  have h := Argument.soundness (genericArgument (F := F)) idx.omega_prim wTab idx.coeffTable
    (idx.selectorRow .generic) (idx.selectorRow_boolean _) α hα t ζ hζ
    hcheck i (idx.selectorRow_eq_one htyp)
  simpa [genericArgument, genericCellMap, rowEnv, Gate.Generic.Holds] using h

/-! ## Copy soundness at the index -/

open Kimchi.Quotient.Permutation in
/-- The witness table's permuted columns as interpolants — what the permutation
argument's committed columns are for a table witness. -/
noncomputable def permWitnessPoly (idx : Index F n) (wTab : Fin n → Fin 15 → F) :
    Fin 7 → Polynomial F :=
  fun col => columnPoly idx.omega (fun j => cellValue wTab (col, j))

omit [DecidableEq F] [NeZero n] in
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
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).2 : ℕ))) β)
    (zg : Polynomial F)
    (hdvd : ∀ s, zH F n ∣ Permutation.constraints idx.omega idx.zkRows zg
      (idx.permWitnessPoly wTab)
      (Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) idx.shifts
      β γ (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd s) :
    ∀ c : Fin 7 × Fin (n - idx.zkRows),
      cellValue wTab (idx.wiringMap (embCell idx.zkRows c))
        = cellValue wTab (embCell idx.zkRows c) := by
  intro c
  have h := copy_soundness_wired_of_dvd idx.omega_prim (Nat.pos_of_neZero n) idx.zk_pos
    idx.zk_le (idx.permWitnessPoly wTab) idx.shifts idx.shifts_coset idx.wiringPerm
    idx.wiringPerm_regionPreserving β γ hβ hγ zg hdvd c
  rw [show idx.wiringPerm (embCell idx.zkRows c) = idx.wiringMap (embCell idx.zkRows c)
      from rfl] at h
  rw [eval_permWitnessPoly] at h
  rw [show idx.omega ^ ((c.2 : ℕ)) = idx.omega ^ (((embCell idx.zkRows c).2 : Fin n) : ℕ)
      from rfl, eval_permWitnessPoly] at h
  exact h

open Kimchi.Quotient.Permutation in
/-- **Copy soundness at the index.** As `copy_soundness_of_dvd`, with each grid node's
divisibility obtained from the derandomized single-challenge quotient check: one challenge
`α a c` per `(β, γ)` node, outside the node's `badAlphas` set, and one quotient `t a c`. -/
theorem copy_soundness (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).2 : ℕ))) β)
    (zg : Polynomial F)
    (α : F)
    (hα : α ∉ badAlphas
      (Permutation.constraints idx.omega idx.zkRows zg
        (idx.permWitnessPoly wTab)
        (Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) idx.shifts
        β γ (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd) idx.omega n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α
      (Permutation.constraints idx.omega idx.zkRows zg
        (idx.permWitnessPoly wTab)
        (Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) idx.shifts
        β γ (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd)) t n)
    (hcheck : (aggregate α
      (Permutation.constraints idx.omega idx.zkRows zg
        (idx.permWitnessPoly wTab)
        (Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) idx.shifts
        β γ (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd)).eval ζ
      = (t * zH F n).eval ζ) :
    ∀ c : Fin 7 × Fin (n - idx.zkRows),
      cellValue wTab (idx.wiringMap (embCell idx.zkRows c))
        = cellValue wTab (embCell idx.zkRows c) :=
  idx.copy_soundness_of_dvd wTab β γ hβ hγ zg
    (dvd_of_evalCheck idx.omega_prim _ α hα t ζ hζ hcheck)


end Kimchi.Index
