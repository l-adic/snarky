/-
  ConstraintSystem.lean

  Kimchi is PLONKish, so the primitive is NOT an R1CS triple — it is a row in a
  15-column execution trace tagged by a `GateKind`, and each kind imposes a
  polynomial identity on the columns of its row (and, for some kinds, the next
  row).

  This module holds the layer-agnostic primitives — wires, assignments, the slot
  convention, and the gate-kind tag. Each gate's identity lives in its own file
  under `Kimchi/Gates/`.

  Still over `Int` (no Mathlib) so it builds in seconds; the shape is unchanged
  when `Int` becomes a Pasta field.
-/

namespace Kimchi

/-- A wire is a column position in the trace, identified by its variable index. -/
abbrev Wire := Nat

/-- A witness: a value per wire. -/
abbrev Assignment := Array Int

/-- Read a wire; out-of-range as 0 for totality. -/
def Assignment.get (a : Assignment) (w : Wire) : Int := a.getD w 0

/-- The value of an optional wire slot. A `none` slot contributes 0 — and in
    `reduce`, a `none` wire always comes paired with a zeroed coefficient, so
    this convention is faithful (constants live in the `c` term, not in slots). -/
def slot (a : Assignment) : Option Wire → Int
  | none   => 0
  | some w => a.get w

/-- The kimchi gate set, mirroring `Snarky.Constraint.Kimchi.Types.GateKind`.
    Only `generic` is given its identity (in `Kimchi/Gates/Generic.lean`); the
    rest are genuinely custom multi-row gates whose identities are added file by
    file under `Kimchi/Gates/`. -/
inductive GateKind
  | generic      -- the catch-all linear+bilinear gate (modeled in Gates/Generic)
  | addComplete  -- complete EC point addition          (Gates/AddComplete)
  | poseidon     -- 5 rounds of the Poseidon permutation (custom, TODO)
  | varBaseMul   -- variable-base scalar multiplication  (custom, TODO)
  | endoMul      -- endomorphism-optimized scalar mul     (custom, TODO)
  | endoScalar   -- endoscalar decomposition              (custom, TODO)
  | zero         -- padding / no constraint
deriving Repr, DecidableEq

end Kimchi
