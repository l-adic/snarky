import Snarky.Kimchi.Backend.Compile
import Kimchi.Index.Basic
import Kimchi.Columns

/-!
# The index of a source's lowering

`IndexOf` says that an index's gate table is a source's lowering and assembly, and that every
index parameter a constraint reads is the index's. The lifting theorems take it as a premise,
and the compiled-index constructor proves it of the index it builds. It is stated over the
production lowering and assembly only, with no part of the lowering's proof development.

## Main definitions

- `directBuilt`, `directGates`: a source's lowering from a counter, and its assembled gates at
  given public variables.
- `KimchiConstraint.ParamsAgree`: a constraint's index parameters, where it reads any, are the
  given ones.
- `IndexOf`, `IndexOf.publicIndex`: an index of a source's lowering, and a public variable's
  public row.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky

variable {F : Type} [Field F] [DecidableEq F]

/-- The fragment's lowering: the builder's reduction folded over `source` from the counter
`nv`, the queue flushed. -/
def directBuilt (source : List (KimchiConstraint F)) (nv : Variable) : KimchiBuilt F Unit :=
  reduceBuilt ⟨(), nv, source⟩

/-- The assembled gate table of the fragment's lowering at the given public variables: the
public rows, then the body rows, wired through the reduction's union-find. -/
def directGates (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) : List (AssembledGate F) :=
  (gateDataOf (directBuilt source nv) publicVars).2.1

deriving instance DecidableEq for Kimchi.Gate.Poseidon.Mds

/-- A constraint's index parameters, when it reads any: a Poseidon block's matrix, an
endomorphism multiplication's coefficient. -/
def KimchiConstraint.ParamsAgree (mds : Gate.Poseidon.Mds F) (endoBase : F) :
    KimchiConstraint F → Prop
  | .poseidon c => Poseidon.mdsOf c.mds = mds
  | .endoMul c => c.endo = endoBase
  | _ => True

instance KimchiConstraint.decidableParamsAgree (mds : Gate.Poseidon.Mds F) (endoBase : F)
    (c : KimchiConstraint F) : Decidable (c.ParamsAgree mds endoBase) := by
  unfold KimchiConstraint.ParamsAgree
  split <;> infer_instance

/-- An index whose gate table is the fragment's lowering and assembly: the public count is
the public variables', the assembled rows fit before the masked rows, and at each assembled
row the gate type, the zero-extended coefficients and the seven wire targets are the
assembly's. The remaining rows are left to the index's own laws. -/
structure IndexOf {n : ℕ} (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) (idx : Index F n) : Prop where
  /-- The public rows are the public variables'. -/
  publicCount : idx.publicCount = publicVars.length
  /-- Every constraint reading an index parameter reads the index's. -/
  params : ∀ c ∈ source, c.ParamsAgree idx.mds idx.endoBase
  /-- The assembled rows fit before the masked rows. -/
  fits : (directGates source publicVars nv).length ≤ n - idx.zkRows
  /-- Each assembled row's gate type. -/
  typ : ∀ (i : Fin n) (hi : i.val < (directGates source publicVars nv).length),
    (idx.gates i).typ = (directGates source publicVars nv)[i.val].kind
  /-- Each assembled row's coefficients, zero beyond the emitted list. -/
  coeffs : ∀ (i : Fin n) (hi : i.val < (directGates source publicVars nv).length)
    (c : Fin coeffCols),
    (idx.gates i).coeffs c = (directGates source publicVars nv)[i.val].coeffs.getD c.val 0
  /-- Each assembled row's wire targets, column then row. -/
  wires : ∀ (i : Fin n) (hi : i.val < (directGates source publicVars nv).length)
    (c : Fin permCols),
    (((idx.gates i).wires c).1 : ℕ) = ((directGates source publicVars nv)[i.val].wires[c]).col ∧
    (((idx.gates i).wires c).2 : ℕ) = ((directGates source publicVars nv)[i.val].wires[c]).row

/-- A public variable's position as a public row of the index. -/
def IndexOf.publicIndex {n : ℕ} {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} {idx : Index F n} (h : IndexOf source publicVars nv idx)
    (i : Fin publicVars.length) : Fin idx.publicCount :=
  ⟨i, by have := h.publicCount; omega⟩

end Snarky.Kimchi
