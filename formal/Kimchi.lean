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

/-- The headline results of this formalization. `make lean-docs` renders these first;
    everything else is the supporting definitions and lemmas they rest on. Three
    groups: (1) each gate's soundness — and, for AddComplete, completeness; (2) the
    VarBaseMul *circuit* computes scalar multiplication (PS `scaleFast1 g a ~
    scalarMul (fromShifted a) g`); (3) the EndoMul circuit relates to EndoScalar (PS
    `endo g a ~ scalarMul (toFieldPure a endoScalar) g`). The faithful two-field /
    Pasta results are a refinement and live below, in the supporting material. -/
def Kimchi.mainResults : List Lean.Name :=
  [-- (1) gate soundness (AddComplete also completeness)
   ``Kimchi.Gate.AddComplete.sound_point_noninf, -- output = group sum (finite case)
   ``Kimchi.Gate.AddComplete.sound_point_inf,    -- output = 0 (infinity case)
   ``Kimchi.Gate.AddComplete.complete_noninf,    -- honest prover can always witness
   ``Kimchi.Gate.VarBaseMul.gate_scalarMul,      -- the double-and-add accumulation
   ``Kimchi.Gate.EndoScalar.gate_endoScalar,     -- the row runs Algorithm 2
   ``Kimchi.Gate.EndoMul.row_sound,              -- the row's two windows add correctly
   -- (2) the VarBaseMul circuit computes scalar multiplication
   ``Kimchi.Circuit.VarBaseMul.scalarMul_caller, -- [s]·T = scalarMul (fromShifted a) g
   -- (3) the EndoMul circuit relates to EndoScalar
   ``Kimchi.Circuit.EndoMul.endoMul_toField]     -- [EndoScalar.toField]·T
