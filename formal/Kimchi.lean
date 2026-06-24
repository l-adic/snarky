-- Library root: a formalization of the kimchi proof system.
-- Re-exports the EC oracle, the generic gate, and the custom-gate identities.
import Kimchi.Curve
import Kimchi.Gate.Generic
import Kimchi.Gate.AddComplete
import Kimchi.Gate.EndoScalar
import Kimchi.Gate.VarBaseMul
import Kimchi.Gate.EndoMul
import Kimchi.Circuit.VarBaseMul
import Kimchi.Circuit.EndoScalar
import Kimchi.Circuit.EndoMul
import Kimchi.Cycle.Axioms
import Kimchi.Cycle.VarBaseMul
import Kimchi.Cycle.Shifted
import Kimchi.Cycle.EndoMul
import Kimchi.Cycle.Pasta

/-- The headline results of this formalization, in narrative order. `make lean-docs`
    renders these first; everything else is the supporting definitions and lemmas they
    rest on. The arc: each gate's soundness → the `EndoMul ∘ EndoScalar` recoding → the
    faithful two-field account → the real Pasta curve. -/
def Kimchi.mainResults : List Lean.Name :=
  [``Kimchi.Gate.AddComplete.ok_iff,            -- complete EC addition (in/out of ∞)
   ``Kimchi.Circuit.VarBaseMul.scalarMul_caller, -- VarBaseMul computes [s]·T
   ``Kimchi.Circuit.EndoScalar.endoScalar_spec,  -- EndoScalar computes a·λ + b
   ``Kimchi.Circuit.EndoMul.endoMul_ab,          -- EndoMul's GLV coeffs ARE EndoScalar's a, b
   ``Kimchi.Circuit.EndoMul.endoMul_toField,     -- EndoMul computes [EndoScalar.toField]·T
   ``Kimchi.Cycle.varBaseMul_faithful,           -- faithful VarBaseMul (scalar field, in range)
   ``Kimchi.Cycle.endoMul_faithful,              -- faithful EndoMul — Level-1 capstone
   ``Kimchi.Cycle.Pasta.pallas_endoMul_faithful] -- the same, on the real Pallas curve
