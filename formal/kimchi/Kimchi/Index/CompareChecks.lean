import Kimchi.Index.Compare
import Mathlib.Tactic.NormNum.Prime

/-!
# Index comparison checks

The comparator decided in the kernel on indices built by `build?` over a field of 113
elements, on a domain of 16 with three masked rows: a public row, a generic row whose first
two wired cells point at each other, and padding. Two constructions of that table, one by
cases on the row and one by list lookup, build equal indices. Each one-datum change that
still builds an index is reported at its datum: the gate type, a coefficient, the wiring of
the generic row restored to the identity, a padding row's coefficient, the public count, the
masked-row count, another generator, another shift, another endomorphism coefficient and
another matrix. A wiring that is not a permutation is refused by the constructor instead.

A family of two members on domains of 16 and 8 compares equal to itself, reports a member
differing in its endomorphism coefficient, and reports a size differing before any member.
A consumer transports satisfaction from the first index to its twin along the equality the
comparison returns.

## Main results

- `compare_accepts`, `compare_rejects`, `build_rejects_wiring`: the comparator on the
  domain of 16.
- `family_accepts`, `family_rejects`: the comparator on families.
- `satisfiesVec_twin`: satisfaction transported along a successful comparison.
-/

namespace Kimchi.Index

/-- The carrier: a field with `16 ∣ 112` and seven cosets of the sixteenth roots of unity. -/
private abbrev K := ZMod 113

private instance : Fact (Nat.Prime 113) := ⟨by norm_num⟩

/-- A zero gate, each cell wired to itself. -/
private def zeroRow {n : ℕ} (i : Fin n) : GateRow K n :=
  { typ := .zero, coeffs := fun _ => 0, wires := fun c => (c, i) }

/-- A public-input row: generic, a unit first coefficient, each cell wired to itself. -/
private def publicRow {n : ℕ} (i : Fin n) : GateRow K n :=
  { typ := .generic, coeffs := fun c => if c = 0 then 1 else 0, wires := fun c => (c, i) }

/-- A generic row at the given coefficients whose first two wired cells point at each other. -/
private def swappedRow {n : ℕ} (i : Fin n) (coeffs : Fin coeffCols → K) : GateRow K n :=
  { typ := .generic, coeffs,
    wires := fun c => if c = 0 then (1, i) else if c = 1 then (0, i) else (c, i) }

/-- The generic row's coefficients: the column index. -/
private def coeffsA : Fin coeffCols → K := fun c => (c.val : K)

/-- The table, by cases on the row. -/
private def tableA : Fin 16 → GateRow K 16 := fun i =>
  if i.val = 0 then publicRow i else if i.val = 1 then swappedRow i coeffsA else zeroRow i

/-- The same table, by list lookup. -/
private def tableA' : Fin 16 → GateRow K 16 := fun i =>
  ([publicRow (0 : Fin 16), swappedRow (1 : Fin 16) coeffsA][i.val]?).getD (zeroRow i)

/-- The table with one row replaced. -/
private def tableWith (j : ℕ) (row : GateRow K 16) : Fin 16 → GateRow K 16 := fun i =>
  if i.val = j then row else tableA i

/-- The matrix the indices carry. -/
private def mds0 : Gate.Poseidon.Mds K :=
  { m00 := 0, m01 := 0, m02 := 0, m10 := 0, m11 := 0, m12 := 0, m20 := 0, m21 := 0, m22 := 0 }

/-- Another matrix. -/
private def mds1 : Gate.Poseidon.Mds K := { mds0 with m00 := 1 }

/-- Powers of the generator `3`: one representative per coset of the sixteenth roots. -/
private def shifts0 : Fin permCols → K := fun c => [1, 3, 9, 27, 81, 17, 51].getD c.val 0

/-- The same with the last replaced by another member of its coset, `51 · 40`. -/
private def shifts1 : Fin permCols → K := fun c => [1, 3, 9, 27, 81, 17, 6].getD c.val 0

/-- The generic row at another gate type. -/
private def rowTyp : GateRow K 16 := { swappedRow (1 : Fin 16) coeffsA with typ := .completeAdd }

/-- The generic row at another third coefficient. -/
private def rowCoeff : GateRow K 16 := swappedRow 1 fun c => if c = 2 then 5 else coeffsA c

/-- The generic row with the identity wiring. -/
private def rowWire : GateRow K 16 :=
  { swappedRow (1 : Fin 16) coeffsA with wires := fun c => (c, 1) }

/-- A padding row with a coefficient. -/
private def rowPad : GateRow K 16 := { zeroRow 5 with coeffs := fun c => if c = 0 then 7 else 0 }

/-- The generic row with both of its first cells pointing at its second: not a permutation. -/
private def rowBad : GateRow K 16 :=
  { swappedRow (1 : Fin 16) coeffsA with
    wires := fun c => if c = 0 ∨ c = 1 then (1, 1) else (c, 1) }

/-- An index at the table and the default data, built. -/
private def at16 (t : Fin 16 → GateRow K 16) (publicCount zkRows : ℕ) (omega endoBase : K)
    (mds : Gate.Poseidon.Mds K) (shifts : Fin permCols → K) (h : (build? t publicCount zkRows
      omega endoBase mds shifts).isSome := by decide +kernel) : Index K 16 :=
  (build? t publicCount zkRows omega endoBase mds shifts).get h

private def idxA : Index K 16 := at16 tableA 1 3 40 0 mds0 shifts0
private def idxA' : Index K 16 := at16 tableA' 1 3 40 0 mds0 shifts0
private def idxTyp : Index K 16 := at16 (tableWith 1 rowTyp) 1 3 40 0 mds0 shifts0
private def idxCoeff : Index K 16 := at16 (tableWith 1 rowCoeff) 1 3 40 0 mds0 shifts0
private def idxWire : Index K 16 := at16 (tableWith 1 rowWire) 1 3 40 0 mds0 shifts0
private def idxPad : Index K 16 := at16 (tableWith 5 rowPad) 1 3 40 0 mds0 shifts0
private def idxPublic : Index K 16 := at16 tableA 0 3 40 0 mds0 shifts0
private def idxZk : Index K 16 := at16 tableA 1 4 40 0 mds0 shifts0
private def idxOmega : Index K 16 := at16 tableA 1 3 42 0 mds0 shifts0
private def idxShifts : Index K 16 := at16 tableA 1 3 40 0 mds0 shifts1
private def idxEndo : Index K 16 := at16 tableA 1 3 40 1 mds0 shifts0
private def idxMds : Index K 16 := at16 tableA 1 3 40 0 mds1 shifts0

/-- The two constructions of the table build equal indices. -/
theorem compare_accepts : checkIndexEq idxA idxA' = true := by
  decide +kernel

/-- Each one-datum change is reported at its datum. -/
theorem compare_rejects :
    compareIndex? idxA idxTyp = some (.typ 1) ∧
    compareIndex? idxA idxCoeff = some (.coeff 1 2) ∧
    compareIndex? idxA idxWire = some (.wire 1 0) ∧
    compareIndex? idxA idxPad = some (.coeff 5 0) ∧
    compareIndex? idxA idxPublic = some .publicCount ∧
    compareIndex? idxA idxZk = some .zkRows ∧
    compareIndex? idxA idxOmega = some .omega ∧
    compareIndex? idxA idxShifts = some (.shifts 6) ∧
    compareIndex? idxA idxEndo = some .endoBase ∧
    compareIndex? idxA idxMds = some .mds := by
  decide +kernel

/-- A wiring that is not a permutation, both of the generic row's first cells pointing at
its second, is refused by the constructor. -/
theorem build_rejects_wiring : (build? (tableWith 1 rowBad) 1 3 40 0 mds0 shifts0).isNone := by
  decide +kernel

/-! ## Families -/

/-- A table on a domain of eight: a public row and padding. -/
private def tableS : Fin 8 → GateRow K 8 := fun i => if i.val = 0 then publicRow i else zeroRow i

/-- The index on eight rows: `18` generates the eighth roots of unity. -/
private def idxS : Index K 8 :=
  (build? tableS 1 3 18 0 mds0 shifts0).get (by decide +kernel)

/-- The same at another endomorphism coefficient. -/
private def idxS' : Index K 8 :=
  (build? tableS 1 3 18 1 mds0 shifts0).get (by decide +kernel)

/-- Domains of 16 and 8. -/
private def sizes : Fin 2 → ℕ := Fin.cons 16 (Fin.cons 8 finZeroElim)

/-- Domains of 16 and 16. -/
private def sizes16 : Fin 2 → ℕ := Fin.cons 16 (Fin.cons 16 finZeroElim)

/-- The family on 16 and 8. -/
private def fam : (i : Fin 2) → Index K (sizes i) :=
  Fin.cons (α := fun i => Index K (sizes i)) idxA (Fin.cons idxS finZeroElim)

/-- The family with the second member at another endomorphism coefficient. -/
private def fam' : (i : Fin 2) → Index K (sizes i) :=
  Fin.cons (α := fun i => Index K (sizes i)) idxA (Fin.cons idxS' finZeroElim)

/-- The family on 16 and 16. -/
private def fam16 : (i : Fin 2) → Index K (sizes16 i) :=
  Fin.cons (α := fun i => Index K (sizes16 i)) idxA (Fin.cons idxA' finZeroElim)

/-- A family compares equal to itself. -/
theorem family_accepts : compareFamily? sizes sizes fam fam = none := by
  decide +kernel

/-- A member's datum is reported at the member; a size is reported before any member. -/
theorem family_rejects :
    compareFamily? sizes sizes fam fam' = some (.member 1 .endoBase) ∧
    compareFamily? sizes sizes16 fam fam16 = some (.size 1) := by
  decide +kernel

/-- Satisfaction transported to the twin along the comparison's equality. -/
theorem satisfiesVec_twin {m : ℕ} (pub : Vector K m) (ha : idxA.publicCount = m)
    (hb : idxA'.publicCount = m) (table : Fin 16 → Fin wCols → K)
    (h : idxA.SatisfiesVec pub ha table) : idxA'.SatisfiesVec pub hb table :=
  (SatisfiesVec_of_eq (compareIndex?_eq_none_iff.mp (by decide +kernel)) ha hb).mp h

end Kimchi.Index
