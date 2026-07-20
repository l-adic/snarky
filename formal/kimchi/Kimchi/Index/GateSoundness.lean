import Kimchi.Index.Satisfies
import Kimchi.Quotient.SchwartzZippel

/-!
# Per-gate quotient soundness at the index

The per-gate quotient soundness theorems restated to consume `Index` data. Each gate's
quotient soundness takes an abstract selector with a booleanness hypothesis and abstract
coefficient/constant inputs; here the selector is the index's own `selectorRow` (whose
booleanness is `selectorRow_boolean` — nothing to assume), the coefficient table is
`coeffTable`, and the `EndoMul` constant is `endoBase`. Each conclusion is phrased on
gate-typed rows — `(idx.gates i).typ = g → Holds …` — matching the corresponding
`rowSatisfies` branch.

## Single-challenge (counting Schwartz–Zippel) form

The random-challenge surrogate is the **counting** argument, not the injective-α family:
each theorem consumes ONE challenge `α : F` known to lie outside the proved-small bad set
`badAlphas <constraint family> ω n` (`|badAlphas| ≤ n · (K − 1)` by `card_badAlphas_le`), and
ONE quotient `t : Polynomial F`. The evaluation challenge is likewise a single `ζ : F` known
to lie outside `badZetas <aggregate> t n`. Every delegation goes through `Argument.soundness`,
the single-(α, ζ) analogue of `Kimchi.Quotient.Argument.soundness` composing `dvd_of_evalCheck`.

The `generic` bridge concludes the *plain* `Generic.Holds`: the deployed aggregate adds the
public polynomial to the first generic constraint (`Generic.withPublic` in `rowSatisfies`),
so the public-aware family is settled with the aggregate rather than here.
-/

namespace Kimchi.Index

open Polynomial Kimchi.Quotient

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} [NeZero n]

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

end Kimchi.Index
