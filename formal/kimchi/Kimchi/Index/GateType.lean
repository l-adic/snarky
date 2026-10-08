/-!
# The gate types

The modeled gate types, in a module with no imports so the circuit backend can tag its
emitted rows with the index model's own type without importing the index.
-/

namespace Kimchi.Index

/-- The modeled gate types: the six formalized gates and the constraint-free `zero`. -/
inductive GateType where
  | zero
  | generic
  | poseidon
  | completeAdd
  | varBaseMul
  | endoMul
  | endoScalar
  deriving DecidableEq, Inhabited

end Kimchi.Index
