import Kimchi.Verifier.Kimchi
import Kimchi.Index.Satisfies
import Kimchi.Index.Interpolation
import Kimchi.Index.Basic
import Kimchi.Columns

/-!
# Verifier keys derived from indices

Derive all committed columns from the index and the SRS by inverse NTT and accelerated MSM.
The column order is permutation, coefficients, then the six selectors. Only selectors carry
the fixed blinding base, once per chunk. The derivation proof connects the executable result to
the index's polynomial commitments. `compareColumns?` reports a column and chunk, and its
success means every commitment agrees.

`KeyCorresponds` retains the polynomial correspondence and the key's metadata, including the
declared accumulator count and the SRS's chunk count. `KimchiVK` supplies the digest
equation; the commitments are checked independently of that digest.
-/

namespace Kimchi.Verifier

open Kimchi Kimchi.Index Kimchi.Verifier Bulletproof CompPoly.CPolynomial.NTT
open scoped Kimchi

/-- The committed columns: permutation, coefficient and gate-selector columns. -/
abbrev KeyColumn := Fin (permCols + coeffCols + selectorCols)

/-- A selector column's gate type, in verifier-key order. -/
private def selectorGate (c : Fin selectorCols) : GateType :=
  (#v[GateType.generic, .poseidon, .completeAdd, .varBaseMul, .endoMul, .endoScalar])[c]

/-- The row values of a committed column. -/
private def keyColumnRow {F : Type} [Field F] {n : Nat} (idx : Index F n) (c : KeyColumn) :
    Fin n → F :=
  if h : c.val < permCols then idx.sigmaAddrRow ⟨c.val, h⟩
  else if h' : c.val < permCols + coeffCols then
    idx.coeffRow ⟨c.val - permCols, by omega⟩
  else idx.selectorRow (selectorGate ⟨c.val - (permCols + coeffCols), by omega⟩)

/-- The polynomial a committed column interpolates. -/
private noncomputable def keyColumnPoly {F : Type} [Field F] {n : Nat}
    (idx : Index F n) (c : KeyColumn) : Polynomial F :=
  columnPoly idx.omega (keyColumnRow idx c)

/-- A key's committed columns in index-column order. -/
def keyColumns {C : Ipa.KimchiCurve} {nc : Nat} (vk : KimchiVK C nc) :
    Vector (Vector C.Point nc) (permCols + coeffCols + selectorCols) :=
  vk.sigmaComm ++ vk.coefficientsComm ++
    #v[vk.genericComm, vk.poseidonComm, vk.completeAddComm,
      vk.mulComm, vk.emulComm, vk.endomulScalarComm]

/-- The polynomial commitment expected at a column and chunk. -/
noncomputable def columnCommitment (C : Ipa.KimchiCurve) {n : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField n) (col : KeyColumn) (chunk : Nat) : C.Point :=
  commitPolyChunk C σ (keyColumnPoly idx col) chunk +
    if permCols + coeffCols ≤ col.val then σ.h else 0

/-- The index's NTT domain. -/
private def indexDomain {F : Type} [Field F] {logN : Nat} (idx : Index F (2 ^ logN)) :
    Domain F :=
  ⟨logN, idx.omega, idx.omega_prim⟩

/-- Commit all index columns independently of the supplied key's commitments. -/
@[noinline] private def deriveColumns (C : Ipa.KimchiCurve) {logN : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField (2 ^ logN)) (nc : Nat) : Vector (Vector C.Point nc) (permCols + coeffCols + selectorCols) :=
  Vector.ofFn fun col =>
    let points := commitColumn C σ (indexDomain idx) nc (keyColumnRow idx col)
    if permCols + coeffCols ≤ col.val then points.map (· + σ.h) else points

/-- Each derived column chunk is the corresponding polynomial commitment. -/
private theorem deriveColumns_eq (C : Ipa.KimchiCurve) {logN : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField (2 ^ logN)) (nc : Nat) (col : KeyColumn) (chunk : Fin nc) :
    (deriveColumns C σ idx nc)[col][chunk] = columnCommitment C σ idx col chunk.val := by
  simp only [deriveColumns, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · simp [Vector.getElem_map, columnCommitment, keyColumnPoly, indexDomain, *]
    exact commitColumn_eq C σ (indexDomain idx) nc (keyColumnRow idx col) chunk
  · simp [columnCommitment, keyColumnPoly, indexDomain, *]
    exact commitColumn_eq C σ (indexDomain idx) nc (keyColumnRow idx col) chunk

/-- A commitment disagreement, located at its column and chunk. -/
structure KeyColumnDiff where
  /-- The committed column. -/
  column : KeyColumn
  /-- The commitment chunk. -/
  chunk : Nat

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

/-- A supplied key commits to this index under this SRS, at the declared accumulator count. -/
structure KeyCorresponds {C : Ipa.KimchiCurve} {nc n : Nat} (σ : SRS C.Point)
    (idx : Index C.ScalarField n) (K : KimchiVK C nc) (previous : Nat) : Prop where
  /-- The key's domain is the index's domain. -/
  domain : n = K.n
  /-- The key uses the SRS's chunk count for its domain. -/
  chunks : nc = chunkCount σ.k K.domainLog2
  /-- The public rows agree. -/
  publicCount : K.publicCount = idx.publicCount
  /-- The masked rows agree. -/
  zkRows : K.zkRows = idx.zkRows
  /-- The domain generator agrees. -/
  omega : K.omega = idx.omega
  /-- The permutation shifts agree. -/
  shifts : ∀ c : Fin permCols, K.shifts[c] = idx.shifts c
  /-- The endomorphism coefficient agrees. -/
  endo : K.endo = idx.endoBase
  /-- The index uses the verifier's implicit Poseidon matrix. -/
  mds : idx.mds = mdsOfParams C.frSponge.params
  /-- The accumulator count is the declared count. -/
  prevChallenges : K.prevChallenges = previous
  /-- Every commitment is the corresponding polynomial's commitment under the SRS. -/
  columns : ∀ (col : KeyColumn) (chunk : Fin nc),
    (keyColumns K)[col][chunk] = columnCommitment C σ idx col chunk.val

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
  /-- The accumulator count differs from the declared count. -/
  | prevChallenges
  /-- A committed column differs at its chunk. -/
  | commitment (diff : KeyColumnDiff)

private def deriveAt (C : Ipa.KimchiCurve) {n nc : Nat}
    (σ : SRS C.Point) (idx : Index C.ScalarField n) (K : KimchiVK C nc)
    (hd : n = K.n) :=
  deriveColumns C σ (cast (congrArg (Index C.ScalarField) hd) idx) nc

private theorem deriveAt_eq (C : Ipa.KimchiCurve) {n nc : Nat}
    (σ : SRS C.Point) (idx : Index C.ScalarField n) (K : KimchiVK C nc)
    (hd : n = K.n) (col : KeyColumn) (chunk : Fin nc) :
    (deriveAt C σ idx K hd)[col][chunk] = columnCommitment C σ idx col chunk.val := by
  cases hd
  unfold deriveAt
  exact deriveColumns_eq C σ idx nc col chunk

/-- Check metadata first, then derive commitments from the index and SRS and retain their
polynomial correspondence. No supplied commitment participates in derivation. -/
def checkKey? {C : Ipa.KimchiCurve} {n nc : Nat}
    (σ : SRS C.Point) (idx : Index C.ScalarField n) (K : KimchiVK C nc) (previous : Nat) :
    Except KeyFailure (PLift (KeyCorresponds σ idx K previous)) :=
  if hd : n = K.n then
    if hc : nc = chunkCount σ.k K.domainLog2 then
      if hp : K.publicCount = idx.publicCount then
        if hz : K.zkRows = idx.zkRows then
          if ho : K.omega = idx.omega then
            if hs : K.shifts = Vector.ofFn idx.shifts then
              if he : K.endo = idx.endoBase then
                if hm : idx.mds = mdsOfParams C.frSponge.params then
                  if hv : K.prevChallenges = previous then
                    let expected := deriveAt C σ idx K hd
                    match h : compareColumns? (keyColumns K) expected with
                    | some d => .error (.commitment d)
                    | none => .ok ⟨⟨hd, hc, hp, hz, ho,
                        fun c => by simpa using congrArg (fun v => v[c]) hs, he, hm, hv,
                        fun col chunk => by
                          rw [compareColumns?_eq_none_iff.mp h]
                          exact deriveAt_eq C σ idx K hd col chunk⟩⟩
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
  | .prevChallenges => "accumulator count"
  | .commitment d =>
    let column := if h : d.column.val < permCols then s!"sigma {d.column.val}"
      else if h' : d.column.val < permCols + coeffCols then
        s!"coefficient {d.column.val - permCols}"
      else s!"{(selectorGate ⟨d.column.val - (permCols + coeffCols), by omega⟩).name} selector"
    s!"{column}, chunk {d.chunk}"

/-- A proof is accepted under a corresponding key, but no witness satisfies its index at the
accepted public input. The SRS is fixed; this predicate asserts no probability bound. -/
def KimchiFailure {curve : Ipa.KimchiCurve} {n nc : Nat}
    (σ : SRS curve.Point) (idx : Kimchi.Index curve.ScalarField n) (key : KimchiVK curve nc)
    (p : KimchiProof curve nc σ.k) (pub : Vector curve.ScalarField idx.publicCount) : Prop :=
  KeyCorresponds σ idx key key.prevChallenges ∧
    kimchiVerify curve σ key p pub.toArray = true ∧
    ¬ ∃ table, idx.SatisfiesVec pub rfl table

/-- Acceptance under a corresponding key yields an index witness or Kimchi failure,
with the SRS fixed throughout. -/
theorem satisfiesVec_or_failure {C : Ipa.KimchiCurve} {n nc m previous : Nat}
    {σ : SRS C.Point} {idx : Kimchi.Index C.ScalarField n} {key : KimchiVK C nc}
    (hkey : KeyCorresponds σ idx key previous)
    (p : KimchiProof C nc σ.k) (pub : Vector C.ScalarField m) (hpub : idx.publicCount = m)
    (haccept : kimchiVerify C σ key p pub.toArray = true) :
    (∃ table, idx.SatisfiesVec pub hpub table) ∨
      KimchiFailure σ idx key p (pub.cast hpub.symm) := by
  subst m
  by_cases holds : ∃ table, idx.SatisfiesVec pub rfl table
  · exact Or.inl holds
  · exact Or.inr ⟨by simpa only [hkey.prevChallenges] using hkey, haccept, holds⟩

end Kimchi.Verifier
