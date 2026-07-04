import Kimchi.Circuit
import Zcash.Snark.Soundness.Permutation

/-!
# `copyHolds` from the permutation argument — discharging the modeling note

Our `Satisfies` takes the copy constraints *extensionally*: `copyHolds` demands each cell equal
the cell its wire points at, and `Circuit.lean` records as a modeling note that in real kimchi
these equalities are *enforced* by the permutation (grand-product) polynomial argument, not given.

The vendored Ironwood formalization (Zcash's halo2 soundness effort — the same permutation
argument) proves the kernel this note appeals to: `prod_pair_inj` (grand product ⇒ multiset of
`(value, label)` pairs identity) and `perm_values_eq_iff` (multiset identity + injective labels ⇒
one-step value invariance `value c = value (σ c)`).

This file composes their kernel with our layer. Kimchi's wire map *is* the permutation — each
cell's wire names the next cell of its copy cycle — so one-step invariance under σ **is**
`copyHolds`, verbatim. `copyHolds_of_multiset` derives our extensional statement from the
multiset identity, turning the modeling note into a theorem, with the remaining distance to the
polynomial itself being exactly Ironwood's own documented residue: the grand-product telescoping
(boundary/blinding rows) that yields the multiset identity, and label distinctness (`δ`-coset
disjointness, a keygen property).
-/

namespace Kimchi.Circuit.Permutation

open Kimchi.Circuit

/-- A grid position (row below `n`, column below 7) as a witness cell. -/
def toCell {n : ℕ} (p : Fin n × Fin 7) : Cell := (p.1.val, p.2.val)

/-- **`copyHolds` is a consequence of the permutation argument.** Given

    * a permutation `σ` of the circuit's `size × 7` grid that agrees with the wire map
      (`toCell (σ p)` is where `p`'s wire points — kimchi's sigma, verbatim),
    * an injective labelling (the `δʲ·ωⁱ` cell names; injectivity is the keygen's δ-coset
      disjointness), and
    * the multiset-of-pairs identity Ironwood's grand-product kernel extracts from the
      permutation polynomial,

    every cell equals the cell its wire points at — our extensional `copyHolds`. -/
theorem copyHolds_of_multiset {F : Type} [Zero F] (c : Circuit F) (w : Witness F)
    (σ : Equiv.Perm (Fin c.gates.size × Fin 7))
    {L : Type} (label : Fin c.gates.size × Fin 7 → L)
    (hlabel : Function.Injective label)
    (hσ : ∀ p : Fin c.gates.size × Fin 7,
      toCell (σ p) = (c.gateAt p.1.val).wires.getD p.2.val (toCell p))
    (hms : Finset.univ.val.map (fun p => (w.cell (toCell p), label p))
      = Finset.univ.val.map (fun p => (w.cell (toCell p), label (σ p)))) :
    copyHolds c w := by
  have hstep :=
    (Zcash.Snark.perm_values_eq_iff σ hlabel (fun p => w.cell (toCell p))).mp hms
  intro r hr k hk
  have h := hstep (⟨r, hr⟩, ⟨k, hk⟩)
  rw [hσ (⟨r, hr⟩, ⟨k, hk⟩)] at h
  exact h

/-- The cycle-level corollary: any two grid cells in the same σ-cycle hold equal values —
    the full copy-constraint statement, via Ironwood's `perm_copy_constraints`. -/
theorem cell_eq_of_sameCycle {F : Type} [Zero F] (c : Circuit F) (w : Witness F)
    (σ : Equiv.Perm (Fin c.gates.size × Fin 7))
    {L : Type} (label : Fin c.gates.size × Fin 7 → L)
    (hlabel : Function.Injective label)
    (hms : Finset.univ.val.map (fun p => (w.cell (toCell p), label p))
      = Finset.univ.val.map (fun p => (w.cell (toCell p), label (σ p))))
    {p q : Fin c.gates.size × Fin 7} (hpq : σ.SameCycle p q) :
    w.cell (toCell p) = w.cell (toCell q) :=
  Zcash.Snark.perm_copy_constraints σ hlabel (fun p => w.cell (toCell p)) hms hpq

end Kimchi.Circuit.Permutation
