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

/-- A gate type's name, as its constructor is spelled. -/
def GateType.name : GateType → String
  | .zero => "zero"
  | .generic => "generic"
  | .poseidon => "poseidon"
  | .completeAdd => "completeAdd"
  | .varBaseMul => "varBaseMul"
  | .endoMul => "endoMul"
  | .endoScalar => "endoScalar"

end Kimchi.Index
