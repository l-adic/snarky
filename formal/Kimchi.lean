-- Library root: a formalization of the kimchi proof system.
-- Re-exports the EC oracle, the generic gate, and the custom-gate identities, plus the
-- VarBaseMul scalar-multiplication soundness (abstract + instantiated at the Pasta curves).
import Kimchi.Curve
import Kimchi.Pasta
import Kimchi.Shifted
import Kimchi.Gate.Generic
import Kimchi.Gate.AddComplete
import Kimchi.Gate.VarBaseMul
import Kimchi.Gate.EndoScalar
import Kimchi.Gate.EndoMul

-- The ingested constraint-system model + verified plonkish checker ([03/13]): the faithful
-- Lean model of the dumped gate list, with an executable `check` proven faithful by `check_iff`.
-- Only Generic / Zero / CompleteAdd rows are constrained so far; later PRs add the custom gates.
import Kimchi.Field.Pasta
import Kimchi.Checker.Row
import Kimchi.Checker.Generic
import Kimchi.Circuit
import Kimchi.Json
import Kimchi.Circuit.VarBaseMul
import Kimchi.Circuit.EndoScalar
import Kimchi.Circuit.EndoMul
import Kimchi.Commitment.IPA.Soundness
import Kimchi.Commitment.IPA.Soundness.Batch
import Kimchi.Quotient.Generic
import Kimchi.Quotient.Soundness
