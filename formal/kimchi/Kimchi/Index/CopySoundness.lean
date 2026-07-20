import Kimchi.Index.Satisfies
import Kimchi.Quotient.Soundness
import Kimchi.Quotient.SchwartzZippel

/-!
# Copy soundness at the index

The permutation argument's quotient soundness restated to consume `Index` data: the argument
consumes the index's wiring permutation, shifts, and their bundled laws, and the conclusion is
the copy fragment of `Satisfies`. As with the per-gate bridges the challenges are single
counting challenges, and the delegation goes through `Argument.soundness`.

The conclusion covers the unmasked region only — the zero-knowledge gating erases the
argument's grip on the masked rows by design, and the whole-grid copy conjunct of `Satisfies`
holds there for honest witnesses because masked rows are identity-wired.
-/

namespace Kimchi.Index

open Polynomial Kimchi.Quotient

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} [NeZero n]

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
