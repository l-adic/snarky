/-!
# The generic gate

The generic gate, modeled exactly as `GenericPlonkConstraint`.

The high-level snarky `Basic` constraints (R1CS / Square / Equal / Boolean) are
not primitives at this layer: `GenericPlonk.purs:reduce` lowers every one of them
to the generic gate

      cl·vl + cr·vr + co·vo + m·(vl·vr) + c = 0

(see `Snarky.Constraint.Kimchi.Types.GenericPlonkConstraint`). So we model the
generic gate exactly, plus the system-level "all gates hold" relation and its
executable checker.

## Main result

`satisfies_iff` — the executable checker `satisfies` faithfully decides the
relational spec `Satisfies` (every generic gate in a list holds on an
assignment).

## Supporting development

The gate model (`Generic` / `Generic.holds` / `Generic.ok`), the per-gate
reflection `Generic.ok_iff`, and a runnable multiplication example.
-/

namespace Kimchi.Gate

/-! ## Trace primitives.

    Kimchi is PLONKish: the primitive is a row in a 15-column execution trace, not
    an R1CS triple. These layer-agnostic pieces — a wire (column position), an
    assignment (a value per wire), and the optional-slot convention — are used only
    by this generic-gate model; the custom EC gates work directly over field-element
    witnesses instead. Still over `Int` (no Mathlib) so it builds in seconds. -/

/-- A wire is a column position in the trace, identified by its variable index. -/
abbrev Wire := Nat

/-- A witness: a value per wire. -/
abbrev Assignment := Array Int

/-- Read a wire; out-of-range as 0 for totality. -/
def Assignment.get (a : Assignment) (w : Wire) : Int := a.getD w 0

/-- The value of an optional wire slot. A `none` slot contributes 0 — and in
    `reduce`, a `none` wire always comes paired with a zeroed coefficient, so this
    convention is faithful (constants live in the `c` term, not in slots). -/
def slot (a : Assignment) : Option Wire → Int
  | none   => 0
  | some w => a.get w

/-- One generic gate. Field names match the PureScript record so the
    correspondence is checkable by eye: `cl,vl` left coeff/var; `cr,vr` right;
    `co,vo` output; `m` the multiplication coeff; `c` the constant. (Kimchi packs
    TWO generic gates per 15-column row — the left half and a `queuedGenericGate`
    right half; we model a single half, the atomic constraint.) -/
structure Generic where
  cl : Int
  vl : Option Wire
  cr : Int
  vr : Option Wire
  co : Int
  vo : Option Wire
  m  : Int
  c  : Int
deriving Repr

/-- RELATIONAL spec for one generic gate — a `Prop`, the identity on paper. -/
def Generic.holds (g : Generic) (a : Assignment) : Prop :=
  g.cl * slot a g.vl + g.cr * slot a g.vr + g.co * slot a g.vo
    + g.m * (slot a g.vl * slot a g.vr) + g.c = 0

/-- EXECUTABLE checker for one generic gate — a `Bool`, runnable. -/
def Generic.ok (g : Generic) (a : Assignment) : Bool :=
  (g.cl * slot a g.vl + g.cr * slot a g.vr + g.co * slot a g.vo
    + g.m * (slot a g.vl * slot a g.vr) + g.c) == 0

/-! ## System-level spec, checker, and the bridge between them. -/

def Satisfies (gs : List Generic) (a : Assignment) : Prop :=
  ∀ g ∈ gs, g.holds a

def satisfies (gs : List Generic) (a : Assignment) : Bool :=
  gs.all (·.ok a)

theorem Generic.ok_iff (g : Generic) (a : Assignment) :
    g.ok a = true ↔ g.holds a := by
  simp [Generic.ok, Generic.holds]

theorem satisfies_iff (gs : List Generic) (a : Assignment) :
    satisfies gs a = true ↔ Satisfies gs a := by
  simp [satisfies, Satisfies, List.all_eq_true, Generic.ok_iff]

/-! ## Example: a multiplication `w0 * w1 = w2`, as the generic gate.

    This is exactly the `R1CS (Just,Just,Just)` case of `reduce`
    (GenericPlonk.purs:28): plain wires give cl=cr=0, co=1, m=-1, c=0, i.e.
        1·w2 + (-1)·(w0·w1) = 0   ⟺   w2 = w0·w1. -/

def mulGate : Generic :=
  { cl := 0, vl := some 0
  , cr := 0, vr := some 1
  , co := 1, vo := some 2
  , m  := -1
  , c  := 0 }

def egGood : Assignment := #[3, 4, 12]   -- 3 * 4 = 12  ✓
def egBad  : Assignment := #[3, 4, 13]   -- 3 * 4 ≠ 13  ✗

#eval satisfies [mulGate] egGood   -- true
#eval satisfies [mulGate] egBad    -- false

-- Prove the spec by running the checker and reflecting through `satisfies_iff`:
example : Satisfies [mulGate] egGood := by rw [← satisfies_iff]; rfl
example : ¬ Satisfies [mulGate] egBad := by rw [← satisfies_iff]; decide

end Kimchi.Gate
