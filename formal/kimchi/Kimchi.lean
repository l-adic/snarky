-- Library root: a formalization of the kimchi proof system.
-- Re-exports the EC oracle, the generic gate, and the custom-gate identities, plus the
-- VarBaseMul scalar-multiplication soundness (abstract + instantiated at the Pasta curves).
import Pasta.Shifted
import Kimchi.Gate.Generic
import Kimchi.Gate.AddComplete
import Kimchi.Gate.VarBaseMul
import Kimchi.Gate.EndoScalar
import Kimchi.Gate.EndoMul
import Kimchi.Gate.Poseidon
import Kimchi.Gate.Semantics.Generic
import Kimchi.Gate.Semantics.AddComplete
import Kimchi.Gate.Semantics.VarBaseMul
import Kimchi.Gate.Semantics.EndoScalar
import Kimchi.Gate.Semantics.EndoMul
import Kimchi.Gate.Semantics.Poseidon
import Bulletproof.Protocol
import Bulletproof.Soundness
import Kimchi.Quotient.Generic
import Kimchi.Quotient.EndoScalar
import Kimchi.Quotient.Poseidon
import Kimchi.Quotient.Accumulator
import Kimchi.Quotient.Copy
import Kimchi.Index.Basic
import Kimchi.Index.Satisfies
import Kimchi.Index.Aggregate
import Kimchi.Index.Degree
import Kimchi.Index.GateSoundness
import Kimchi.Index.CopySoundness
import Kimchi.Quotient.Wiring
import Kimchi.Quotient.Permutation
import Kimchi.Quotient.GrandProduct
import Bulletproof.Wire
-- Side A — the idealized polynomial protocol and its soundness
import Kimchi.Protocol.Linearization
import Kimchi.Protocol.Equation
import Kimchi.Protocol.Correspond
import Kimchi.Protocol.Binding
import Kimchi.Protocol.Soundness
-- Side B — the concrete PCS instantiation
import Bulletproof.Reflection
import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Reflect
import Kimchi.Verifier.Capstone
