import Pickles.Env
import Kimchi.Index.Interpolation
import Kimchi.Index.Basic
import Kimchi.Columns

/-!
# Verifier keys derived from indices

Derive all committed columns from the index and the SRS by inverse NTT and accelerated MSM.
The column order is permutation, coefficients, then the six selectors. Only selectors carry
the fixed blinding base, once per chunk. `deriveColumns_eq` connects the executable result to
the index's polynomial commitments. `compareColumns?` reports a column and chunk, and its
success means every commitment agrees.

`KeyCorresponds` retains the polynomial correspondence and the key's metadata, including the
shape's accumulator count and the SRS's chunk count. The existing `Key` supplies the digest
equation; the commitments are checked independently of that digest.
-/

namespace Pickles

open Kimchi Kimchi.Index Kimchi.Verifier Bulletproof CompPoly.CPolynomial.NTT
open scoped Kimchi

/-- The committed columns: permutation, coefficient and gate-selector columns. -/
abbrev KeyColumn := Fin (permCols + coeffCols + selectorCols)

/-- A selector column's gate type, in verifier-key order. -/
def selectorGate (c : Fin selectorCols) : GateType :=
  (#v[GateType.generic, .poseidon, .completeAdd, .varBaseMul, .endoMul, .endoScalar])[c]

/-- The row values of a committed column. -/
def keyColumnRow {F : Type} [Field F] {n : Nat} (idx : Index F n) (c : KeyColumn) :
    Fin n → F :=
  if h : c.val < permCols then idx.sigmaAddrRow ⟨c.val, h⟩
  else if h' : c.val < permCols + coeffCols then
    idx.coeffRow ⟨c.val - permCols, by omega⟩
  else idx.selectorRow (selectorGate ⟨c.val - (permCols + coeffCols), by omega⟩)

/-- The polynomial a committed column interpolates. -/
noncomputable def keyColumnPoly {F : Type} [Field F] {n : Nat}
    (idx : Index F n) (c : KeyColumn) : Polynomial F :=
  columnPoly idx.omega (keyColumnRow idx c)

/-- A key's committed columns in index-column order. -/
def keyColumns {C : Ipa.KimchiCurve} {nc : Nat} (vk : KimchiVK C nc) :
    Vector (Vector C.Point nc) (permCols + coeffCols + selectorCols) :=
  vk.sigmaComm ++ vk.coefficientsComm ++
    #v[vk.genericComm, vk.poseidonComm, vk.completeAddComm,
      vk.mulComm, vk.emulComm, vk.endomulScalarComm]

/-- Assemble a verifier key from computed commitment columns and index metadata, then
compute its digest. The supplied key is not an argument. -/
@[noinline] private def keyOfColumns (C : Ipa.KimchiCurve) {logN nc : Nat}
    (idx : Index C.ScalarField (2 ^ logN)) (hnc : 0 < nc) (previous : Nat)
    (columns : Vector (Vector C.Point nc) (permCols + coeffCols + selectorCols)) :
    KimchiVK C nc :=
  let vk : KimchiVK C nc :=
    { nc_pos := hnc, domainLog2 := logN, omega := idx.omega
      sigmaComm := Vector.ofFn fun c => columns[c.val]'(by omega)
      coefficientsComm := Vector.ofFn fun c => columns[permCols + c.val]'(by omega)
      genericComm := columns[permCols + coeffCols]
      poseidonComm := columns[permCols + coeffCols + 1]
      completeAddComm := columns[permCols + coeffCols + 2]
      mulComm := columns[permCols + coeffCols + 3]
      emulComm := columns[permCols + coeffCols + 4]
      endomulScalarComm := columns[permCols + coeffCols + 5]
      shifts := Vector.ofFn idx.shifts, zkRows := idx.zkRows, publicCount := idx.publicCount
      publicCount_le := idx.public_le.trans (Nat.sub_le _ _)
      prevChallenges := previous, endo := idx.endoBase, digest := 0 }
  { vk with digest := vk.indexDigest }

private theorem keyOfColumns_columns (C : Ipa.KimchiCurve) {logN nc : Nat}
    (idx : Index C.ScalarField (2 ^ logN)) (hnc : 0 < nc) (previous : Nat)
    (columns : Vector (Vector C.Point nc) (permCols + coeffCols + selectorCols)) :
    keyColumns (keyOfColumns C idx hnc previous columns) = columns := by
  simp only [keyColumns, keyOfColumns]
  apply Vector.ext
  intro i hi
  by_cases hσ : i < permCols
  · rw [Vector.getElem_append_left (by omega : i < permCols + coeffCols),
      Vector.getElem_append_left hσ, Vector.getElem_ofFn]
  · by_cases hc : i < permCols + coeffCols
    · rw [Vector.getElem_append_left hc, Vector.getElem_append_right (by omega) (by omega),
        Vector.getElem_ofFn]
      congr 1
      dsimp only
      omega
    · rw [Vector.getElem_append_right hi (by omega)]
      have hlow : permCols + coeffCols ≤ i := by omega
      interval_cases i <;> rfl

private theorem keyOfColumns_digest (C : Ipa.KimchiCurve) {logN nc : Nat}
    (idx : Index C.ScalarField (2 ^ logN)) (hnc : 0 < nc) (previous : Nat)
    (columns : Vector (Vector C.Point nc) (permCols + coeffCols + selectorCols)) :
    (keyOfColumns C idx hnc previous columns).digest =
      (keyOfColumns C idx hnc previous columns).indexDigest := rfl

/-- The polynomial commitment expected at a column and chunk. -/
noncomputable def columnCommitment (C : Ipa.KimchiCurve) {n : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField n) (col : KeyColumn) (chunk : Nat) : C.Point :=
  commitPolyChunk C σ (keyColumnPoly idx col) chunk +
    if permCols + coeffCols ≤ col.val then σ.h else 0

/-- The index's NTT domain, with nonzero domain size in the scalar field. -/
def indexDomain {F : Type} [Field F] {logN : Nat} (idx : Index F (2 ^ logN))
    (hn : ((2 ^ logN : Nat) : F) ≠ 0) : Domain F :=
  ⟨logN, idx.omega, idx.omega_prim, hn⟩

/-- Commit all index columns independently of the supplied key's commitments. -/
@[noinline] def deriveColumns (C : Ipa.KimchiCurve) {logN : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField (2 ^ logN)) (hn : ((2 ^ logN : Nat) : C.ScalarField) ≠ 0)
    (nc : Nat) : Vector (Vector C.Point nc) (permCols + coeffCols + selectorCols) :=
  Vector.ofFn fun col =>
    let points := commitColumn C σ (indexDomain idx hn) nc (keyColumnRow idx col)
    if permCols + coeffCols ≤ col.val then points.map (· + σ.h) else points

/-- Derive the complete verifier key from an index, SRS and shape accumulator count. -/
def deriveKey (C : Ipa.KimchiCurve) {logN nc : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField (2 ^ logN)) (hn : ((2 ^ logN : Nat) : C.ScalarField) ≠ 0)
    (hnc : 0 < nc) (previous : Nat) : KimchiVK C nc :=
  keyOfColumns C idx hnc previous (deriveColumns C σ idx hn nc)

/-- Derivation assembles exactly the computed commitment columns. -/
theorem deriveKey_columns (C : Ipa.KimchiCurve) {logN nc : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField (2 ^ logN)) (hn : ((2 ^ logN : Nat) : C.ScalarField) ≠ 0)
    (hnc : 0 < nc) (previous : Nat) :
    keyColumns (deriveKey C σ idx hn hnc previous) = deriveColumns C σ idx hn nc := by
  exact keyOfColumns_columns C idx hnc previous _

/-- The derived digest is the digest of the derived commitments. -/
theorem deriveKey_digest (C : Ipa.KimchiCurve) {logN nc : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField (2 ^ logN)) (hn : ((2 ^ logN : Nat) : C.ScalarField) ≠ 0)
    (hnc : 0 < nc) (previous : Nat) :
    (deriveKey C σ idx hn hnc previous).digest =
      (deriveKey C σ idx hn hnc previous).indexDigest :=
  keyOfColumns_digest C idx hnc previous _

/-- Each derived column chunk is the corresponding polynomial commitment. -/
theorem deriveColumns_eq (C : Ipa.KimchiCurve) {logN : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField (2 ^ logN)) (hn : ((2 ^ logN : Nat) : C.ScalarField) ≠ 0)
    (nc : Nat) (col : KeyColumn) (chunk : Fin nc) :
    (deriveColumns C σ idx hn nc)[col][chunk] = columnCommitment C σ idx col chunk.val := by
  simp only [deriveColumns, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · simp [Vector.getElem_map, columnCommitment, keyColumnPoly, indexDomain, *]
    exact commitColumn_eq C σ (indexDomain idx hn) nc (keyColumnRow idx col) chunk
  · simp [columnCommitment, keyColumnPoly, indexDomain, *]
    exact commitColumn_eq C σ (indexDomain idx hn) nc (keyColumnRow idx col) chunk

/-- A commitment disagreement, located at its column and chunk. -/
structure KeyColumnDiff where
  /-- The committed column. -/
  column : KeyColumn
  /-- The commitment chunk. -/
  chunk : Nat
  deriving DecidableEq

/-- The first difference between two vectors of commitment columns. -/
def compareColumns? {G : Type} [DecidableEq G] {nc : Nat}
    (a b : Vector (Vector G nc) (permCols + coeffCols + selectorCols)) :
    Option KeyColumnDiff :=
  (List.finRange (permCols + coeffCols + selectorCols)).findSome? fun col =>
    ((List.finRange nc).find? (fun chunk => decide (a[col][chunk] ≠ b[col][chunk]))).map
      (fun chunk => ⟨col, chunk.val⟩)

/-- Success of the located comparator is equality of all commitment columns. -/
theorem compareColumns?_eq_none_iff {G : Type} [DecidableEq G] {nc : Nat}
    {a b : Vector (Vector G nc) (permCols + coeffCols + selectorCols)} :
    compareColumns? a b = none ↔ a = b := by
  rw [compareColumns?, List.findSome?_eq_none_iff]
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    let col : KeyColumn := ⟨i, hi⟩
    have hc := h col (List.mem_finRange _)
    have hn : (List.finRange nc).find?
        (fun chunk => decide (a[col][chunk] ≠ b[col][chunk])) = none := by
      simpa using hc
    simpa using List.find?_eq_none.mp hn ⟨j, hj⟩ (List.mem_finRange _)
  · rintro rfl
    simp [List.find?_eq_none]

/-- A supplied key commits to this index under this SRS, at the shape's accumulator count. -/
structure KeyCorresponds {C : Ipa.KimchiCurve} {nc n : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField n) (K : Key C nc) (previous : Nat) : Prop where
  /-- The key's domain is the index's domain. -/
  domain : n = K.cvk.n
  /-- The key uses the SRS's chunk count for its domain. -/
  chunks : nc = chunkCount σ.k K.cvk.domainLog2
  /-- The public rows agree. -/
  publicCount : K.cvk.publicCount = idx.publicCount
  /-- The masked rows agree. -/
  zkRows : K.cvk.zkRows = idx.zkRows
  /-- The domain generator agrees. -/
  omega : K.cvk.omega = idx.omega
  /-- The permutation shifts agree. -/
  shifts : ∀ c : Fin permCols, K.cvk.shifts[c] = idx.shifts c
  /-- The endomorphism coefficient agrees. -/
  endo : K.cvk.endo = idx.endoBase
  /-- The index uses the verifier's implicit Poseidon matrix. -/
  mds : idx.mds = mdsOfParams C.frSponge.params
  /-- The accumulator count is the shape's. -/
  prevChallenges : K.cvk.prevChallenges = previous
  /-- Every commitment is the corresponding polynomial's commitment under the SRS. -/
  columns : ∀ (col : KeyColumn) (chunk : Fin nc),
    (keyColumns K.cvk)[col][chunk] = columnCommitment C σ idx col chunk.val

/-- A verifier-key disagreement, before or during commitment comparison. -/
inductive KeyFailure where
  /-- The domain size differs. -/
  | domain
  /-- The chunk count differs from the SRS's. -/
  | chunks
  /-- The public-input count differs. -/
  | publicCount
  /-- The masked-row count differs. -/
  | zkRows
  /-- The generator differs. -/
  | omega
  /-- The permutation shifts differ. -/
  | shifts
  /-- The endomorphism coefficient differs. -/
  | endo
  /-- The Poseidon matrix differs from the verifier's. -/
  | mds
  /-- The accumulator count differs from the shape's. -/
  | prevChallenges
  /-- A committed column differs at its chunk. -/
  | commitment (diff : KeyColumnDiff)

private def deriveAt (C : Ipa.KimchiCurve) (s : PastaShape C) {n nc : Nat}
    (σ : SRS C.Point) (idx : Index C.ScalarField n) (K : Key C nc)
    (hd : n = K.cvk.n) (previous : Nat) :=
  keyColumns (deriveKey C σ (cast (congrArg (Index C.ScalarField) hd) idx)
    (K.natCast_n_ne_zero s) K.cvk.nc_pos previous)

private theorem deriveAt_eq (C : Ipa.KimchiCurve) (s : PastaShape C) {n nc : Nat}
    (σ : SRS C.Point) (idx : Index C.ScalarField n) (K : Key C nc)
    (hd : n = K.cvk.n) (previous : Nat) (col : KeyColumn) (chunk : Fin nc) :
    (deriveAt C s σ idx K hd previous)[col][chunk] = columnCommitment C σ idx col chunk.val := by
  cases hd
  unfold deriveAt
  rw [deriveKey_columns]
  exact deriveColumns_eq C σ idx (K.natCast_n_ne_zero s) nc col chunk

/-- Check metadata first, then derive commitments from the index and SRS and retain their
polynomial correspondence. No supplied commitment participates in derivation. -/
def checkKey? {C : Ipa.KimchiCurve} (s : PastaShape C) {n nc : Nat}
    (σ : SRS C.Point) (idx : Index C.ScalarField n) (K : Key C nc) (previous : Nat) :
    Except KeyFailure (PLift (KeyCorresponds σ idx K previous)) :=
  if hd : n = K.cvk.n then
    if hc : nc = chunkCount σ.k K.cvk.domainLog2 then
      if hp : K.cvk.publicCount = idx.publicCount then
        if hz : K.cvk.zkRows = idx.zkRows then
          if ho : K.cvk.omega = idx.omega then
            if hs : K.cvk.shifts = Vector.ofFn idx.shifts then
              if he : K.cvk.endo = idx.endoBase then
                if hm : idx.mds = mdsOfParams C.frSponge.params then
                  if hv : K.cvk.prevChallenges = previous then
                    let expected := deriveAt C s σ idx K hd previous
                    match h : compareColumns? (keyColumns K.cvk) expected with
                    | some d => .error (.commitment d)
                    | none => .ok ⟨⟨hd, hc, hp, hz, ho,
                        fun c => by simpa using congrArg (fun v => v[c]) hs, he, hm, hv,
                        fun col chunk => by
                          rw [compareColumns?_eq_none_iff.mp h]
                          exact deriveAt_eq C s σ idx K hd previous col chunk⟩⟩
                  else .error .prevChallenges
                else .error .mds
              else .error .endo
            else .error .shifts
          else .error .omega
        else .error .zkRows
      else .error .publicCount
    else .error .chunks
  else .error .domain

/-- A commitment disagreement described by its polynomial column and chunk. -/
def KeyFailure.describe : KeyFailure → String
  | .domain => "domain size"
  | .chunks => "SRS chunk count"
  | .publicCount => "public-input count"
  | .zkRows => "masked-row count"
  | .omega => "domain generator"
  | .shifts => "permutation shifts"
  | .endo => "endomorphism coefficient"
  | .mds => "Poseidon matrix"
  | .prevChallenges => "shape accumulator count"
  | .commitment d =>
    let c := d.column.val
    let column := if c < permCols then s!"sigma {c}"
      else if c < permCols + coeffCols then s!"coefficient {c - permCols}"
      else ["generic", "poseidon", "completeAdd", "varBaseMul", "endoMul", "endoScalar"].getD
        (c - (permCols + coeffCols)) "selector"
    s!"{column}, chunk {d.chunk}"

end Pickles
