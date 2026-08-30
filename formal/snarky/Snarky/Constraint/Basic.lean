import Snarky.WP

/-!
# The reference constraint system

`Basic` is the constraint type most backends supply: rank-one, equality, square and
booleanity rows. It instantiates the three class layers — the constructors
(`BasicSystem`), the semantics (`ConstraintHolds`) and the agreement between them
(`LawfulBasicSystem`) — so the gadget libraries' laws hold of something.

The semantics is a `Prop` over the total reading, not a decision over a partial table:
the prover fills the table and the constraints are read afterwards, so a row is never
"unsatisfied because unassigned". A decidable mirror arrives with a consumer that needs
to run the check.
-/

namespace Snarky

universe u

variable {F : Type}

/-- The basic constraint rows. -/
inductive Basic (F : Type u) where
  /-- Rank-one: `left · right = output`. -/
  | r1cs (left right output : CVar F)
  /-- Equality: the two expressions read equal. -/
  | equal (a b : CVar F)
  /-- Square: `a · a = sq`. -/
  | square (a sq : CVar F)
  /-- Booleanity: the expression reads `0` or `1`. -/
  | boolean (x : CVar F)
  deriving Repr, DecidableEq

/-- Each constructor is its own row. -/
instance instBasicSystemBasic : BasicSystem F (Basic F) where
  r1cs := .r1cs
  equal := .equal
  square := .square
  boolean := .boolean

/-- A row's reading: the identity it names, under the valuation. -/
def Basic.Holds [Add F] [Mul F] [Zero F] [One F] (V : Valuation F) : Basic F → Prop
  | .r1cs l r o => l.val V * r.val V = o.val V
  | .equal a b => a.val V = b.val V
  | .square a sq => a.val V * a.val V = sq.val V
  | .boolean x => x.val V = 0 ∨ x.val V = 1

instance instConstraintHoldsBasic [Add F] [Mul F] [Zero F] [One F] :
    ConstraintHolds F (Basic F) :=
  ⟨Basic.Holds⟩

/-- The constructors mean what they say: each law is the corresponding arm of `Holds`. -/
instance instLawfulBasicSystemBasic [Add F] [Mul F] [Zero F] [One F] :
    LawfulBasicSystem F (Basic F) where
  holds_equal _ _ _ := Iff.rfl
  holds_r1cs _ _ _ _ := Iff.rfl
  holds_square _ _ _ := Iff.rfl
  holds_boolean _ _ := Iff.rfl

end Snarky
