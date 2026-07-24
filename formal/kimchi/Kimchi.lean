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
import Kimchi.Lift
import Kimchi.Permutation.Copy
import Kimchi.Index.Basic
import Kimchi.Index.Satisfies
import Kimchi.Index.Aggregate
import Kimchi.Index.Degree
import Kimchi.Index.CopySoundness
import Kimchi.Permutation.Wiring
import Kimchi.Permutation.Permutation
import Kimchi.GrandProduct
import Bulletproof.Wire
-- Side A — the polynomial protocol (PCS-free) and its soundness
import Kimchi.Protocol.Accepts
import Kimchi.Protocol.Linearization
import Kimchi.Protocol.Equation
-- Side B — the PCS reduction and the concrete wire verifier
import Bulletproof.Reflection
import Kimchi.Verifier.Reduction.Correspond
import Kimchi.Verifier.Reduction.Binding
import Kimchi.Verifier.Reduction.Soundness
import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Reflect
import Kimchi.Verifier.Wire
import Kimchi.Verifier.Capstone.Standard
import Kimchi.Verifier.Capstone.Algebraic
import Kimchi.Verifier.Capstone.Reflection

-- W2 · Fiat–Shamir random-oracle model (fq side)
import Kimchi.Verifier.Forking.Model
