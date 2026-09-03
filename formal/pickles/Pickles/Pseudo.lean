import Snarky.DSL.Field
import Snarky.DSL.Boolean

set_option mvcgen.warning false

/-!
# Pseudo-domain selection

Port of the PureScript `Pickles.Pseudo.mask` (OCaml `pseudo.ml`): the mask-select
`∑ᵢ bᵢ · xᵢ` over a vector of bits and values, one row per entry.

## Main definitions

* `Pseudo.mask`: the products, emitted last-to-first as OCaml's right-to-left `Vector.map`
  does, summed affinely.

## Main results

* `Pseudo.mask_spec`: the output reads as `∑ᵢ bᵢ · xᵢ`.
-/

namespace Pickles.Pseudo

open Std.Do Snarky

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- The products `bᵢ · xᵢ`, in entry order, emitted last-to-first. -/
private def products : List (BoolVar F × FVar F) → CircuitM F c (List (FVar F))
  | [] => pure []
  | (b, x) :: rest => do
    let tail ← products rest
    let t ← mul (↑b) x
    pure (t :: tail)

/-- The mask-select `∑ᵢ bᵢ · xᵢ` (PS `Pseudo.mask`): one `mul` row per entry, the sum an
affine combination. -/
def mask (bits : List (BoolVar F)) (xs : List (FVar F)) : CircuitM F c (FVar F) := do
  let terms ← products (bits.zip xs)
  pure (terms.foldl CVar.add_ (.const 0))

variable [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}

/-- The products read entrywise. -/
private theorem products_spec :
    ∀ entries : List (BoolVar F × FVar F),
      ⦃⌜True⌝⦄ products (c := Builder V c) entries
      ⦃⇓ r _ => ⌜r.map (·.val V) = entries.map fun e => (↑e.1 : CVar F).val V * e.2.val V⌝⦄
  | [] => by
    simp only [products]
    mvcgen
  | (b, x) :: rest => by
    simp only [products]
    have ih := products_spec rest
    mvcgen [ih]
    rename_i _ _ _ hrest _ _ hx
    simp [hrest, hx]

/-- Under any valuation the mask-select reads as `∑ᵢ bᵢ · xᵢ`, the sum over the paired
entries. -/
theorem mask_spec (bits : List (BoolVar F)) (xs : List (FVar F)) :
    ⦃⌜True⌝⦄ mask (c := Builder V c) bits xs
    ⦃⇓ r _ => ⌜r.val V
      = ((bits.zip xs).map fun e => (↑e.1 : CVar F).val V * e.2.val V).sum⌝⦄ := by
  simp only [mask]
  have h := products_spec (c := c) (V := V) (bits.zip xs)
  mvcgen [h]
  rename_i _ terms _ hterms
  have hfold : ∀ (l : List (FVar F)) (acc : CVar F),
      (l.foldl CVar.add_ acc).val V = acc.val V + (l.map (·.val V)).sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons y l ih => intro acc; simp [List.foldl_cons, ih, CVar.val_add_, add_assoc]
  rw [hfold, hterms]
  simp

end Pickles.Pseudo
