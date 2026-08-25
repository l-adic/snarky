import Snarky.Constraint.Basic
import Snarky.DSL.Assert

/-!
# A struct, derived

The derivation exercised end to end: a point over `a` is a product `a × a` up to an
equivalence, so its encoding, its check, its selection and the laws of both are
inherited — the value at `F`, the bundle at `FVar F`, through the one equivalence.
Nothing is proven about points themselves.
-/

namespace Snarky

variable {F c : Type}

/-- A point over `a`: the value at `a := F`, the bundle at `a := FVar F`. -/
structure Point (a : Type) where
  x : a
  y : a

/-- A point, as a product. -/
def Point.equiv (a : Type) : Point a ≃ a × a where
  toFun p := (p.x, p.y)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instCircuitTypePoint : CircuitType F (Point F) (Point (FVar F)) :=
  CircuitType.ofShape Point.equiv

instance instCheckedTypePoint [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] :
    CheckedType F c (Point F) (Point (FVar F)) :=
  CheckedType.ofShape Point.equiv

instance instIfThenElsePoint [Field F] [DecidableEq F] [BasicSystem F c] :
    IfThenElse F c (Point (FVar F)) :=
  IfThenElse.ofShape Point.equiv

instance instLawfulIfThenElsePoint [Field F] [DecidableEq F] [BasicSystem F c] :
    LawfulIfThenElse F c (Point F) (Point (FVar F)) :=
  LawfulIfThenElse.ofShape Point.equiv

/-! The inherited readings, at the struct's fields. -/

example (st : ProverState F) (p : Point (FVar F)) :
    CircuitType.Scoped (val := Point F) st p ↔ p.x.Scoped st ∧ p.y.Scoped st := by
  simp [CircuitType.scoped_ofEquiv, Point.equiv]

example [Add F] [Mul F] [Zero F] (st : ProverState F) (p : Point (FVar F)) :
    CircuitType.readVal (val := Point F) st.env.get p
      = ⟨p.x.val st.env.get, p.y.val st.env.get⟩ := by
  simp [CircuitType.readVal_ofEquiv, Point.equiv]

/-! The inherited gadgets: a point selects and asserts equal, with the laws of both. -/

example [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (b : BoolVar F) (t e : Point (FVar F)) (bb : Bool)
    (tv ev : Point F) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := Bool) st b bb ∧
        CircuitType.ReadsAs (val := Point F) st t tv ∧
        CircuitType.ReadsAs (val := Point F) st e ev)
      (select (c := c) b t e)
      (fun a st' => CircuitType.ReadsAs (val := Point F) st' a (if bb then tv else ev)) :=
  LawfulIfThenElse.select_complete b t e bb tv ev

example [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (t e : Point (FVar F)) (a : Point F) :
    Complete (F := F) (c := c) (fun st => CircuitType.Scoped (val := Point F) st t ∧
        CircuitType.Scoped (val := Point F) st e ∧
        CircuitType.Reads st.env.get t a ∧ CircuitType.Reads st.env.get e a)
      (assertEq (c := c) (val := Point F) t e) (fun _ _ => True) :=
  assertEq_complete t e a

/-! The laws are not vacuous: they hold at the reference constraint system. -/

example [Field F] [DecidableEq F] (b : BoolVar F) (t e : Point (FVar F)) (bb : Bool)
    (tv ev : Point F) :
    Complete (F := F) (c := Basic F)
      (fun st => CircuitType.ReadsAs (val := Bool) st b bb ∧
        CircuitType.ReadsAs (val := Point F) st t tv ∧
        CircuitType.ReadsAs (val := Point F) st e ev)
      (select (c := Basic F) b t e)
      (fun a st' => CircuitType.ReadsAs (val := Point F) st' a (if bb then tv else ev)) :=
  LawfulIfThenElse.select_complete b t e bb tv ev

/-- The rows a point's selection emits at the reference system: its `y` before its `x`. -/
example [Field F] [DecidableEq F] (vb x₁ y₁ x₂ y₂ : Variable) (nv : Nat) :
    (build (select (F := F) (c := Basic F) (BoolVar.unchecked (.var vb))
        (⟨.var x₁, .var y₁⟩ : Point (FVar F)) ⟨.var x₂, .var y₂⟩) nv).constraints =
      [Basic.r1cs (.var vb) (CVar.sub_ (.var y₁) (.var y₂)) (CVar.sub_ (.var nv) (.var y₂)),
       Basic.r1cs (.var vb) (CVar.sub_ (.var x₁) (.var x₂))
         (CVar.sub_ (.var (nv + 1)) (.var x₂))] := by
  unfold IfThenElse.select instIfThenElsePoint IfThenElse.ofShape IfThenElse.ofEquiv
    instIfThenElseProd instIfThenElseFVar selectField
  rfl

end Snarky
