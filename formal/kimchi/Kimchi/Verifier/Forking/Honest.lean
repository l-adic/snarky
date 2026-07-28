import Kimchi.Columns
import Kimchi.Verifier.KnowledgeSoundness
import Zcash.Snark.Soundness.Forking.Adversary.DomainReduction

/-!
# Anti-vacuity: the degenerate kimchi instantiation

The kimchi knowledge-soundness endpoints bound the measure of `Wins ∧ ¬ExtractsWitness`.
Such a bound says nothing if it is the FIRST conjunct that makes the set small — "nobody
ever convinces the verifier, so nothing ever fails to be extracted". Ruling that reading
out means exhibiting a family whose acceptance conjunct holds. This module builds that
family bottom-up, starting from the degenerate data and the computation that decides
which shape the argument can take.

**Why the opening argument's template does not transport.** For the standalone opening
argument (`Bulletproof/Forking/KnowledgeSoundness.lean`, `trivialInput` /
`honestFamily_accepts_everywhere`) the claim is a FREE parameter of the family, so one
takes the all-zero claim: its combined commitment is `0` and its combined inner product
`cipOf` is `0`, and the pair `(0, 0)` opens it at EVERY public basis. Kimchi's claim is
not free — it is DERIVED by the verifier from the key, the public input, the proof and
its own six pre-opening challenges. This module computes that derived claim at the most
degenerate data available (`zeroProof`, empty public input) and finds:

* every batch row claims `(0, 0)` except the `ft` row;
* the `ft` row COMMITS to `0` (`ftComm_runInputWith_zero`) but claims the
  accumulator-boundary quotient
  `ft₀ = (ζⁿ − 1)(α²²(ζ − ω^{n−z}) + α²³(ζ − 1)) / ((ζ − ω^{n−z})(ζ − 1))`
  — the only term of `Linearization.ftEval0` that survives all-zero
  evaluations: the σ side carries the factor `z(ζω) = 0`, the shift side carries `z(ζ) = 0`,
  the gate linearization is selector-weighted, and the public evaluation is zero;
* hence `cipOf` of the derived claim is `v^{nc} · ft₀`, which is non-zero away from an
  explicit locus.

A zero commitment claiming a non-zero combined evaluation is a discrete-log relation among
the basis elements, so acceptance at an ARBITRARY public basis is not provable — it is the
hardness assumption the endpoints charge for. Acceptance must therefore be targeted at the
SAMPLED bases `augOfSetup (Zcash.Snark.scalarBasis B s)`, which is all the endpoints'
failure set is indexed by.

The honest verifying key of an index at an SRS is also here (`honestVK`), with the
key–index correspondence holding definitionally (`honestVK_corresponds`): the
correspondence IS the statement that the key's committed columns are the indexer's
outputs.
-/

namespace Kimchi.Verifier.Forking

open Bulletproof Bulletproof.Forking Bulletproof.Ipa.Forking Kimchi.Index Kimchi.Verifier
open Kimchi.Verifier.KnowledgeSoundness

variable {C : Ipa.CommitmentCurve}

/-- The zero evaluation pair at every chunk. -/
private def zeroPE (C : Ipa.CommitmentCurve) (nc : ℕ) :
    PointEvaluations (Vector C.ScalarField nc) :=
  ⟨Vector.replicate nc 0, Vector.replicate nc 0⟩

/-- Every column evaluation zero. -/
private def zeroEvals (C : Ipa.CommitmentCurve) (nc : ℕ) :
    ProofEvaluations (Vector C.ScalarField nc) where
  w := Vector.replicate wCols (zeroPE C nc)
  z := zeroPE C nc
  s := Vector.replicate sigmaRows (zeroPE C nc)
  coefficients := Vector.replicate coeffCols (zeroPE C nc)
  genericSelector := zeroPE C nc
  poseidonSelector := zeroPE C nc
  completeAddSelector := zeroPE C nc
  mulSelector := zeroPE C nc
  emulSelector := zeroPE C nc
  endomulScalarSelector := zeroPE C nc

/-- The all-zero proof.

The quotient array is `nc` **zero** chunks rather than empty: `KimchiFamily.htpos`
demands `0 < tComm.size`, so a family built on an empty array cannot exist. Taking `nc`
chunks (rather than the single chunk of the blueprint) keeps `tComm_le` unconditional —
`nc ≤ 7 * nc` — and none of the computations below change, since the polyscale
combination of an all-zero list is `0` either way (`combineCommitments_eq_zero`). -/
private def zeroProof (C : Ipa.CommitmentCurve) (nc k : ℕ) : KimchiProof C nc k where
  wComm := Vector.replicate wCols (Vector.replicate nc 0)
  zComm := Vector.replicate nc 0
  tComm := Array.replicate nc 0
  tComm_le := by simp; omega
  evals := zeroEvals C nc
  pubEvals := .carried (zeroPE C nc)
  ftEval1 := 0
  opening := ⟨Vector.replicate k (0, 0), 0, 0, 0, 0⟩

/-! ## The honest verifying key -/

/-- The index with its Poseidon MDS retuned to the curve's own scalar-side table. -/
private def indexAtCurve (C : Ipa.CommitmentCurve) {n : ℕ} (idx : Index C.ScalarField n) :
    Index C.ScalarField n :=
  { idx with mds := mdsOfParams C.frParams }

/-- The honest verifying key of an index at an SRS: every committed column is the
indexer's own output, every scalar-side parameter is read off the index, and the
Lagrange table is the basis polynomials' chunk commitments. -/
private noncomputable def honestVK [Module C.ScalarField C.Point] (σ : SRS C.Point) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) : KimchiVK C nc where
  domainLog2 := d
  omega := idx.omega
  sigmaComm := Vector.ofFn fun i : Fin permCols =>
    Vector.ofFn fun c : Fin nc => commitPolyChunk σ (idx.sigmaPoly i) (c : ℕ)
  coefficientsComm := Vector.ofFn fun cc : Fin coeffCols =>
    Vector.ofFn fun c : Fin nc => commitPolyChunk σ (idx.coeffPoly cc) (c : ℕ)
  genericComm := Vector.ofFn fun c : Fin nc =>
    commitPolyMaskedChunk σ (idx.selectorPoly .generic) (c : ℕ)
  poseidonComm := Vector.ofFn fun c : Fin nc =>
    commitPolyMaskedChunk σ (idx.selectorPoly .poseidon) (c : ℕ)
  completeAddComm := Vector.ofFn fun c : Fin nc =>
    commitPolyMaskedChunk σ (idx.selectorPoly .completeAdd) (c : ℕ)
  mulComm := Vector.ofFn fun c : Fin nc =>
    commitPolyMaskedChunk σ (idx.selectorPoly .varBaseMul) (c : ℕ)
  emulComm := Vector.ofFn fun c : Fin nc =>
    commitPolyMaskedChunk σ (idx.selectorPoly .endoMul) (c : ℕ)
  endomulScalarComm := Vector.ofFn fun c : Fin nc =>
    commitPolyMaskedChunk σ (idx.selectorPoly .endoScalar) (c : ℕ)
  shifts := Vector.ofFn idx.shifts
  zkRows := idx.zkRows
  endo := idx.endoBase
  digest := 0
  lagrangeBasis := Array.ofFn fun j : Fin (2 ^ d) =>
    Vector.ofFn fun c : Fin nc =>
      commitPolyChunk σ (columnPoly idx.omega (Kimchi.Permutation.rowIndicator j)) (c : ℕ)

/-- **The key–index correspondence holds by construction.** -/
private theorem honestVK_corresponds [Module C.ScalarField C.Point] (σ : SRS C.Point) (nc : ℕ)
    {d : ℕ} (idx : Index C.ScalarField (2 ^ d)) :
    KimchiVK.Corresponds σ (honestVK σ nc (indexAtCurve C idx)) (indexAtCurve C idx) := by
  refine ⟨?_, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · simp [VKCorresponds, KimchiVK.comms, indexerOf, honestVK]
  · funext i; simp [honestVK]
  · intro j _ hj c
    simp [honestVK, indexAtCurve]

/-! ## The chunk combination at an all-zero chunk vector -/

/-- The chunk-combination fold reads only the chunk values, so an all-zero list leaves
the accumulator alone. -/
private theorem combineAt_foldl_zero {F : Type*} [Field F] (xM : F) :
    ∀ (l : List F), (∀ x ∈ l, x = 0) → ∀ a w : F,
      (l.foldl (fun (acc : F × F) c => (acc.1 + acc.2 * c, acc.2 * xM)) (a, w)).1 = a
  | [], _, _, _ => rfl
  | c :: t, h, a, w => by
      have hc : c = 0 := h c (by simp)
      have ih := combineAt_foldl_zero xM t (fun x hx => h x (by simp [hx])) (a + w * c) (w * xM)
      simpa [hc] using ih

/-- `combineAt` at an all-zero chunk vector is zero. -/
private theorem combineAt_replicate_zero {F : Type*} [Field F] (xM : F) (nc : ℕ) :
    combineAt xM (Array.replicate nc (0 : F)) = 0 := by
  have h : ∀ x ∈ (Array.replicate nc (0 : F)).toList, x = 0 := by
    intro x hx
    rw [Array.toList_replicate] at hx
    exact List.eq_of_mem_replicate hx
  rw [combineAt, ← Array.foldl_toList]
  exact combineAt_foldl_zero xM _ h 0 1

/-! ## The linearization evaluations at the all-zero proof -/

/-- The all-zero linearization environment. -/
private def zeroLinEvals (C : Ipa.CommitmentCurve) :
    Kimchi.Protocol.Linearization.Evals C.ScalarField where
  w _ := 0
  wOmega _ := 0
  z := 0
  zOmega := 0
  s _ := 0
  coeffs _ := 0
  genericSelector := 0
  poseidonSelector := 0
  completeAddSelector := 0
  mulSelector := 0
  emulSelector := 0
  endoScalarSelector := 0

/-- Chunk-combining the all-zero proof's evaluations gives the all-zero environment. -/
private theorem linEvals_zeroProof (nc k : ℕ) (zetaM zetaOmegaM : C.ScalarField) :
    (zeroProof C nc k).linEvals zetaM zetaOmegaM = zeroLinEvals C := by
  ext <;>
    simp [KimchiProof.linEvals, zeroProof, zeroEvals, zeroPE, zeroLinEvals,
      combineAt_replicate_zero]

/-! ## The derived `ft` evaluation -/

/-! ## The batch stream at the degenerate data -/

/-! ## The `ft` row's commitment -/

/-- The polyscale combination reads only the commitments, so an all-zero list leaves the
accumulator alone. -/
private theorem combineCommitments_foldl_zero (ξ : C.ScalarField) :
    ∀ (l : List C.Point), (∀ P ∈ l, P = 0) → ∀ (a : C.Point) (w : C.ScalarField),
      (l.foldl (fun (acc : C.Point × C.ScalarField) P =>
        (acc.1 + acc.2.val • P, acc.2 * ξ)) (a, w)).1 = a
  | [], _, _, _ => rfl
  | P :: t, h, a, w => by
      have hP : P = 0 := h P (by simp)
      have ih := combineCommitments_foldl_zero ξ t (fun x hx => h x (by simp [hx]))
        (a + w.val • P) (w * ξ)
      simpa [hP] using ih

/-- `Ipa.combineCommitments` at an all-zero commitment list is zero. -/
private theorem combineCommitments_eq_zero (ξ : C.ScalarField) (cs : Array C.Point)
    (h : ∀ P ∈ cs, P = 0) : Ipa.combineCommitments C ξ cs = 0 := by
  rw [Ipa.combineCommitments, ← Array.foldl_toList]
  exact combineCommitments_foldl_zero ξ cs.toList (by simpa using h) 0 1

/-- The permutation scalar vanishes at the all-zero evaluations (its `z(ζω)` factor
does). -/
private theorem permScalar_zeroLinEvals (β γ α zkpmZ : C.ScalarField) :
    Kimchi.Protocol.Linearization.permScalar β γ α zkpmZ (zeroLinEvals C) = 0 := by
  simp [Kimchi.Protocol.Linearization.permScalar, zeroLinEvals]

/-- **The `ft` row of the derived claim commits to `0`.** The permutation scalar
vanishes, so the `σ`-commitment term drops, and the all-zero proof carries no quotient
chunks. Together with the non-vanishing of the derived combined evaluation this is the discrete-log
relation of Corollary "acceptance at an arbitrary basis would break binding": a zero
commitment claiming a non-zero combined evaluation. -/
private theorem ftComm_runInputWith_zero (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (β γ α ζ v u : C.ScalarField) (hnc : nc < nc + 1 + tailRowCount * nc) :
    ((runInputWith σ cvk (zeroProof C nc σ.k) #[] β γ α ζ v u).commitments[nc]'hnc)
      = 0 := by
  simp only [runInputWith, Vector.getElem_map]
  rw [Vector.getElem_append, dif_pos (by omega : nc < nc + 1),
    Vector.getElem_append, dif_neg (by omega)]
  simp only [Nat.sub_self, linEvals_zeroProof, permScalar_zeroLinEvals]
  show Ipa.combineCommitments C _ _ - _ • Ipa.combineCommitments C _ (Array.replicate nc 0) = 0
  rw [combineCommitments_eq_zero _ _ (by simp), combineCommitments_eq_zero _ _ (by simp)]
  simp

/-! ## The derived combined inner product -/

/-! ## The boundary quotient does not vanish -/

/-! ## Toward the scalar-basis opening witness

At a basis `augOfSetup (scalarBasis B s)` every generator is a scalar multiple of one
fixed point `B`, so the hiding commitment collapses to a single multiple of `B` and an
opening witness is a solution of TWO linear equations in `(a, ρ)`. This section is the
linear algebra of that reduction: the collapse, and the two solvable regimes (a live
blinding slot; an invertible `2 × 2` minor of `(s, b)`). -/

section ScalarBasis

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A generator commitment against generators that are all multiples of one point
collapses to a single multiple of that point. -/
private theorem commitGen_smul_base {N : ℕ} (B : G) (s a : Fin N → F) :
    commitGen (fun i => s i • B) a = (∑ i, a i * s i) • B := by
  simp [commitGen, smul_smul, ← Finset.sum_smul]

/-- **The scalar-basis hiding commitment**: `Commitσ(a, ρ) = (⟨a, s⟩ + ρ·s_bl) · B`. -/
private theorem commit_smul_base (σ : SRS G) (B : G) (s : Fin (2 ^ σ.k) → F) (sb : F)
    (hg : σ.g = fun i => s i • B) (hh : σ.h = sb • B)
    (a : Fin (2 ^ σ.k) → F) (ρ : F) :
    commit σ a ρ = ((∑ i, a i * s i) + ρ * sb) • B := by
  rw [commit, hg, hh, commitGen_smul_base, smul_smul, ← add_smul]

/-- **Solvability with a live blinding slot.** With `s_bl ≠ 0` the first equation is
solved by the blinding coefficient alone, so only `⟨a, b⟩ = cip` constrains `a`, and a
single non-zero entry of `b` suffices. -/
private theorem exists_pair_of_blind_ne_zero {N : ℕ} (s b : Fin N → F) (sb lam cip : F)
    (hsb : sb ≠ 0) (i0 : Fin N) (hb : b i0 ≠ 0) :
    ∃ (a : Fin N → F) (ρ : F),
      (∑ i, a i * s i) + ρ * sb = lam ∧ (∑ i, a i * b i) = cip := by
  set a : Fin N → F := fun i => if i = i0 then cip / b i0 else 0 with ha
  refine ⟨a, (lam - ∑ i, a i * s i) / sb, ?_, ?_⟩
  · field_simp
    ring
  · simp [ha, ite_mul, div_mul_cancel₀ _ hb]

end ScalarBasis

/-- **The scalar-basis opening witness** (the live-blinding-slot regime). At a basis whose
generators and blinding base are the multiples `s i • B`, `s_bl • B` of one point, a claim
whose combined commitment is `lam • B` and whose combined evaluation vector has some
non-zero entry admits an opening witness at ANY combined inner product `cip` — in
particular at the non-zero `cip` the derived kimchi claim carries. -/
private theorem exists_openingRelationB_smul_base [Module C.ScalarField C.Point]
    (σ : SRS C.Point) (B : C.Point) (s : Fin (2 ^ σ.k) → C.ScalarField)
    (sb : C.ScalarField) (hg : σ.g = fun i => s i • B) (hh : σ.h = sb • B)
    (hsb : sb ≠ 0) (lam cip : C.ScalarField) (bvec : Fin (2 ^ σ.k) → C.ScalarField)
    (i0 : Fin (2 ^ σ.k)) (hb : bvec i0 ≠ 0) :
    ∃ (a : Fin (2 ^ σ.k) → C.ScalarField) (ρ : C.ScalarField),
      openingRelationB σ (lam • B) bvec cip a ρ := by
  obtain ⟨a, ρ, h1, h2⟩ :=
    exists_pair_of_blind_ne_zero s bvec sb lam cip hsb i0 hb
  refine ⟨a, ρ, ?_, ?_⟩
  · rw [commit_smul_base σ B s sb hg hh, h1]
  · rw [innerProduct, h2]

/-! ## The sampled basis read as an SRS

The knowledge-soundness endpoints measure over the sampled setup slots injected into the
augmented index, i.e. over bases `augOfSetup (Zcash.Snark.scalarBasis B s)`. Reading such a
basis back as an SRS gives exactly the shape `exists_openingRelationB_smul_base` wants: the
generators are `s (gen i) • B` and the blinding base is `s blind • B`. Both are
definitional — `srsOfBasis` is `srsOf ∘ ursOfAugmentedBasis`, whose `g`/`w` slots read the
basis at `gen i` / `w`, and `augOfSetup` routes those to the setup slots. -/

/-- **The sampled SRS's generators.** -/
private theorem srsOfBasis_scalarBasis_g [Module C.ScalarField C.Point] (k : ℕ) (B : C.Point)
    (s : SetupIndex (2 ^ k) → C.ScalarField) :
    (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s))).g
      = fun i => s (SetupIndex.gen i) • B := rfl

/-- **The sampled SRS's blinding base.** -/
private theorem srsOfBasis_scalarBasis_h [Module C.ScalarField C.Point] (k : ℕ) (B : C.Point)
    (s : SetupIndex (2 ^ k) → C.ScalarField) :
    (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s))).h = s SetupIndex.blind • B :=
  rfl

/-! ## The line through the sampled base

At a sampled basis every public group element the verifier ever touches is a multiple of
the one point `B`. The predicate below names that, and the lemmas record that the whole
batch-stream construction stays inside it: the line is a submodule, so it is closed under
the group operations, the two scalar actions the code uses (field-side `•` and the
`ZMod.val` natural action inside `Ipa.combineCommitments`), and every commitment form the
verifier builds. -/

section InLine

variable [Module C.ScalarField C.Point]

/-- `P` **lies in the line through** `B`: it is a scalar multiple of `B`. At the sampled
bases the endpoints measure over this holds for every public group element, which is what
makes the derived kimchi claim openable there. -/
private def InLine (C : Ipa.CommitmentCurve) [Module C.ScalarField C.Point] (B P : C.Point) :
    Prop :=
  ∃ c : C.ScalarField, P = c • B

namespace InLine

variable {B P Q : C.Point}

/-- Every multiple of `B` lies in the line. -/
private theorem of_smul (B : C.Point) (c : C.ScalarField) : InLine C B (c • B) := ⟨c, rfl⟩

/-- The line contains the zero point. -/
theorem zero (B : C.Point) : InLine C B 0 := ⟨0, (zero_smul _ _).symm⟩

/-- The line is closed under addition. -/
private theorem add (hP : InLine C B P) (hQ : InLine C B Q) : InLine C B (P + Q) := by
  obtain ⟨c, rfl⟩ := hP
  obtain ⟨d, rfl⟩ := hQ
  exact ⟨c + d, (add_smul _ _ _).symm⟩

/-- The line is closed under the field-side scalar action. -/
private theorem smul (c : C.ScalarField) (hP : InLine C B P) : InLine C B (c • P) := by
  obtain ⟨d, rfl⟩ := hP
  exact ⟨c * d, (mul_smul _ _ _).symm⟩

/-- The line is closed under finite sums. -/
theorem sum {ι : Type*} (t : Finset ι) (f : ι → C.Point)
    (h : ∀ i ∈ t, InLine C B (f i)) : InLine C B (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using zero B
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self _ _)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A generator commitment against generators in the line stays in the line. -/
private theorem of_commitGen {n : ℕ} (g : Fin n → C.Point) (a : Fin n → C.ScalarField)
    (h : ∀ i, InLine C B (g i)) : InLine C B (Bulletproof.commitGen g a) :=
  sum _ _ fun i _ => (h i).smul _

/-- The line is closed under the abstract combined commitment. -/
private theorem of_combinedCommitment (ξ : C.ScalarField) {n : ℕ} (f : Fin n → C.Point)
    (h : ∀ i, InLine C B (f i)) :
    InLine C B (Bulletproof.combinedCommitment ξ f) :=
  sum _ _ fun i _ => (h i).smul _

end InLine

/-- Every generator of an SRS whose generators are the multiples `s i • B` lies in the
line — the line-membership hypothesis shape, from
`srsOfBasis_scalarBasis_g`. -/
private theorem inLine_of_g_eq {σ : SRS C.Point} {B : C.Point}
    {s : Fin (2 ^ σ.k) → C.ScalarField} (hg : σ.g = fun i => s i • B) (i : Fin (2 ^ σ.k)) :
    InLine C B (σ.g i) := by
  rw [hg]
  exact InLine.of_smul B (s i)

/-- A chunk commitment at a scalar SRS lies in the line. -/
private theorem inLine_commitPolyChunk {σ : SRS C.Point} {B : C.Point}
    {s : Fin (2 ^ σ.k) → C.ScalarField} (hg : σ.g = fun i => s i • B)
    (p : Polynomial C.ScalarField) (c : ℕ) : InLine C B (commitPolyChunk σ p c) :=
  InLine.of_commitGen _ _ (inLine_of_g_eq hg)

/-- A masked chunk commitment at a scalar SRS lies in the line. -/
private theorem inLine_commitPolyMaskedChunk {σ : SRS C.Point} {B : C.Point}
    {s : Fin (2 ^ σ.k) → C.ScalarField} {sb : C.ScalarField}
    (hg : σ.g = fun i => s i • B) (hh : σ.h = sb • B)
    (p : Polynomial C.ScalarField) (c : ℕ) :
    InLine C B (commitPolyMaskedChunk σ p c) :=
  (inLine_commitPolyChunk hg p c).add (hh ▸ InLine.of_smul B sb)

/-! ## Every commitment of the derived claim lies in the line -/

/-- Every tail-row commitment of the honest key at the all-zero proof lies in the line:
each is either a commitment the all-zero proof carries (hence `0`) or one of the honest
key's committed columns, which is a chunk commitment against the same scalar SRS. -/
private theorem tailRowsOf_fst_inLine {σ : SRS C.Point} {B : C.Point}
    {s : Fin (2 ^ σ.k) → C.ScalarField} {sb : C.ScalarField}
    (hg : σ.g = fun i => s i • B) (hh : σ.h = sb • B) {nc d k : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (q r : ℕ)
    (hq : q < tailRowCount) (hr : r < nc) :
    InLine C B ((((tailRowsOf C (honestVK σ nc idx) (zeroProof C nc k))[q]'hq)[r]'hr).1) := by
  rcases Nat.lt_or_ge q litRowCount with h | h
  · rw [tailRows_read_lit C q h]
    interval_cases q <;>
      simp only [litRowsOf, zipSeg, zeroProof, honestVK, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Fin.getElem_fin, Vector.getElem_ofFn,
        Vector.getElem_replicate]
    · exact InLine.zero B
    · exact inLine_commitPolyMaskedChunk hg hh _ _
    · exact inLine_commitPolyMaskedChunk hg hh _ _
    · exact inLine_commitPolyMaskedChunk hg hh _ _
    · exact inLine_commitPolyMaskedChunk hg hh _ _
    · exact inLine_commitPolyMaskedChunk hg hh _ _
    · exact inLine_commitPolyMaskedChunk hg hh _ _
  · rcases Nat.lt_or_ge q 22 with h2 | h2
    · obtain ⟨q', rfl⟩ : ∃ q', q = 7 + q' := ⟨q - 7, by omega⟩
      rw [tailRows_read_w C q' (by omega)]
      simp only [zipSeg, zeroProof, Fin.getElem_fin, Vector.getElem_ofFn,
        Vector.getElem_replicate]
      exact InLine.zero B
    · rcases Nat.lt_or_ge q 37 with h3 | h3
      · obtain ⟨q', rfl⟩ : ∃ q', q = 22 + q' := ⟨q - 22, by omega⟩
        rw [tailRows_read_c C q' (by omega)]
        simp only [zipSeg, honestVK, Fin.getElem_fin, Vector.getElem_ofFn]
        exact inLine_commitPolyChunk hg _ _
      · obtain ⟨q', rfl⟩ : ∃ q', q = 37 + q' := ⟨q - 37, by omega⟩
        rw [tailRows_read_s C q' (by omega)]
        simp only [zipSeg, honestVK, Fin.getElem_fin, Vector.getElem_ofFn]
        exact inLine_commitPolyChunk hg _ _

/-- The flattened tail region's commitments all lie in the line. -/
private theorem tailFlatten_fst_inLine {σ : SRS C.Point} {B : C.Point}
    {s : Fin (2 ^ σ.k) → C.ScalarField} {sb : C.ScalarField}
    (hg : σ.g = fun i => s i • B) (hh : σ.h = sb • B) {nc d k : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (t : ℕ) (ht : t < tailRowCount * nc) :
    InLine C B
      (((tailRowsOf C (honestVK σ nc idx) (zeroProof C nc k)).flatten[t]'ht).1) := by
  have hnc : 0 < nc := by
    by_contra h
    have : nc = 0 := by omega
    omega
  obtain ⟨q, r, hq, hr, rfl⟩ :
      ∃ q r, q < tailRowCount ∧ r < nc ∧ t = q * nc + r := by
    refine ⟨t / nc, t % nc, ?_, Nat.mod_lt _ hnc, ?_⟩
    · exact Nat.div_lt_of_lt_mul (by omega)
    · rw [Nat.mul_comm]
      exact (Nat.div_add_mod t nc).symm
  rw [flatten_read _ q r hq hr]
  exact tailRowsOf_fst_inLine hg hh idx q r hq hr

/-- **Every commitment of the derived batched claim lies in the line.** The `nc` public
chunks are the blinding base `σ.h` (the empty public input takes the `pub.size = 0`
branch of `publicCommitment`); the `ft` row is `0` (`ftComm_runInputWith_zero`); every
tail row is either a commitment the all-zero proof carries or one of the honest key's
committed columns (`tailFlatten_fst_inLine`). -/
private theorem commitments_runInputWith_inLine {σ : SRS C.Point} {B : C.Point}
    {s : Fin (2 ^ σ.k) → C.ScalarField} {sb : C.ScalarField}
    (hg : σ.g = fun i => s i • B) (hh : σ.h = sb • B) {nc d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (β γ α ζ v u : C.ScalarField)
    (i : ℕ) (hi : i < nc + 1 + tailRowCount * nc) :
    InLine C B
      ((runInputWith σ (honestVK σ nc idx) (zeroProof C nc σ.k) #[] β γ α ζ v
        u).commitments[i]'hi) := by
  rcases Nat.lt_or_ge i nc with h | h
  · simp only [runInputWith, Vector.getElem_map]
    rw [Vector.getElem_append, dif_pos (by omega : i < nc + 1),
      Vector.getElem_append, dif_pos h]
    simp only [publicCommitment, Array.size_empty, ↓reduceIte, Vector.getElem_ofFn,
      Fin.getElem_fin, Vector.getElem_replicate]
    exact hh ▸ InLine.of_smul B sb
  · rcases Nat.eq_or_lt_of_le h with rfl | h2
    · rw [ftComm_runInputWith_zero σ (honestVK σ nc idx) β γ α ζ v u hi]
      exact InLine.zero B
    · simp only [runInputWith, Vector.getElem_map]
      rw [Vector.getElem_append, dif_neg (by omega)]
      exact tailFlatten_fst_inLine hg hh idx (i - (nc + 1)) (by omega)

/-- **The derived claim's combined commitment is a multiple of the sampled base.** This
is the first of the two hypotheses `exists_openingRelationB_smul_base` needs. -/
private theorem combinedCommitment_runInputWith_smul_base {σ : SRS C.Point} {B : C.Point}
    {s : Fin (2 ^ σ.k) → C.ScalarField} {sb : C.ScalarField}
    (hg : σ.g = fun i => s i • B) (hh : σ.h = sb • B) {nc d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (β γ α ζ v u : C.ScalarField) :
    ∃ lam : C.ScalarField,
      Bulletproof.combinedCommitment
          (runInputWith σ (honestVK σ nc idx) (zeroProof C nc σ.k) #[] β γ α ζ v u).polyscale
          (runInputWith σ (honestVK σ nc idx) (zeroProof C nc σ.k) #[] β γ α ζ v
            u).commitmentFn
        = lam • B :=
  InLine.of_combinedCommitment _ _ fun i =>
    commitments_runInputWith_inLine hg hh idx β γ α ζ v u i i.isLt

end InLine

/-! ## The combined evaluation vector does not vanish

The second hypothesis of `exists_openingRelationB_smul_base` is that the combined
evaluation vector has a non-zero entry. Its zeroth entry is `∑ j, u ^ j` — independent of
the evaluation points, because `evalVector`'s zeroth entry is `x ^ 0 = 1` at every `x`. At
kimchi's two evaluation points that is `1 + u`. -/

section EvalVector

variable {F : Type*} [Field F]

/-- **The zeroth entry of the combined evaluation vector** is the geometric sum of the
evalscale, whatever the evaluation points are. -/
private theorem combinedEvalVector_zero (N : ℕ) (hN : 0 < N) (r : F) {m : ℕ} (x : Fin m → F) :
    combinedEvalVector N r x ⟨0, hN⟩ = ∑ j : Fin m, r ^ (j : ℕ) := by
  simp [combinedEvalVector, evalVector]

/-- **The first entry of the combined evaluation vector** is the evalscale-combination of
the evaluation points themselves. -/
private theorem combinedEvalVector_one (N : ℕ) (hN : 1 < N) (r : F) {m : ℕ} (x : Fin m → F) :
    combinedEvalVector N r x ⟨1, hN⟩ = ∑ j : Fin m, r ^ (j : ℕ) * x j := by
  simp [combinedEvalVector, evalVector]

/-- **The combined evaluation vector has a non-zero entry at every evalscale**, as soon as
the two evaluation points differ and the vector has length at least two: at `r = -1` the
zeroth entry `1 + r` degenerates, but then the first entry is `x₀ − x₁`.

This removes the exclusion `u ≠ -1` from the opening statements below at the cost of
`ζ ≠ ζω`, which the
verifier's own two evaluation points supply whenever `ζ ≠ 0` and `ω ≠ 1`. -/
private theorem combinedEvalVector_exists_ne_zero (N : ℕ) (hN : 1 < N) (r : F)
    (x : Fin evalPts → F) (hx : x 0 ≠ x 1) :
    ∃ i : Fin N, combinedEvalVector N r x i ≠ 0 := by
  by_cases h : (1 : F) + r = 0
  · refine ⟨⟨1, hN⟩, ?_⟩
    rw [combinedEvalVector_one N hN r x, Fin.sum_univ_two]
    have hr : r = -1 := by linear_combination h
    simpa [hr] using fun hc => hx (by linear_combination hc)
  · refine ⟨⟨0, by omega⟩, ?_⟩
    rw [combinedEvalVector_zero N (by omega) r x, Fin.sum_univ_two]
    simpa using h

end EvalVector

/-! ## The derived claim is openable at a sampled basis

Assembling: the combined commitment is `lam • B`
(`combinedCommitment_runInputWith_smul_base`), the combined evaluation vector has a
non-zero zeroth entry, and the blinding slot is live — the
three hypotheses of `exists_openingRelationB_smul_base`. The `U` override the opening
layer's acceptance theorem carries changes neither `g` nor `h`, so the scalar-basis shape
survives it. -/

/-- The derived batched claim of the honest key at the all-zero proof and the empty public
input — the claim every statement of this section is about, named so the assembled
statements stay readable. -/
private noncomputable def honestClaim [Module C.ScalarField C.Point] (σ : SRS C.Point) (nc : ℕ)
    {d : ℕ} (idx : Index C.ScalarField (2 ^ d)) (β γ α ζ v u : C.ScalarField) :
    Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts :=
  runInputWith σ (honestVK σ nc idx) (zeroProof C nc σ.k) #[] β γ α ζ v u

/-! ## The proof the honest adversary emits

The honest adversary does not emit `zeroProof`: it emits the degenerate proof with its
opening field replaced by the opening proof the opening layer's honest machine produces.
Nothing the verifier derives from a proof other than the IPA proof itself reads that
field, so the derived claim is the same claim — up to its own `proof` slot. -/

/-- The degenerate proof carrying a given opening proof. -/
private def zeroProofWith (C : Ipa.CommitmentCurve) (nc k : ℕ) (op : Ipa.Proof C k) :
    KimchiProof C nc k :=
  { zeroProof C nc k with opening := op }

/-- The quotient array of the degenerate proof has `nc` chunks — the shape
`KimchiFamily.htpos` reads, which is why `zeroProof` carries zero chunks rather than
none. -/
@[simp] private theorem zeroProofWith_tComm_size (nc k : ℕ) (op : Ipa.Proof C k) :
    (zeroProofWith C nc k op).tComm.size = nc := by
  simp [zeroProofWith, zeroProof]

/-- **Replacing the opening changes only the claim's `proof` slot.** Definitional: the
batch stream reads the evaluations, the commitment chunks and `ftEval1`, none of which the
opening field touches. -/
private theorem runInputWith_zeroProofWith (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (β γ α ζ v u : C.ScalarField) (op : Ipa.Proof C σ.k) :
    runInputWith σ cvk (zeroProofWith C nc σ.k op) pub β γ α ζ v u
      = { runInputWith σ cvk (zeroProof C nc σ.k) pub β γ α ζ v u with proof := op } := rfl

/-! ## The verifier's size guard at the empty public input

`kimchiVerifyWith` is the public-input size guard followed by the challenge-generic opening
verifier on the derived claim. At the empty public input the guard passes unconditionally,
so acceptance of the honest family reduces to the opening branch — the second half of the
acceptance theorem, the first being the openability of the derived claim. -/

/-- **The guard passes at the empty public input**, at any key and any proof. -/
private theorem kimchiVerifyWith_empty_pub [Module C.ScalarField C.Point] {nc : ℕ}
    (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (β γ α ζ v u : C.ScalarField) (uBase : C.Point) (chals : Vector C.ScalarField σ.k)
    (c : C.ScalarField) :
    kimchiVerifyWith σ cvk cp #[] β γ α ζ v u uBase chals c
      = Ipa.verifyWith C σ uBase chals c (runInputWith σ cvk cp #[] β γ α ζ v u) := by
  rw [kimchiVerifyWith_eq_verifyWith]
  simp

/-! ## The scalar-SRS hypothesis, bundled

Every statement below needs the SRS to be `s i • B`, `sb • B` with `sb ≠ 0`. Bundling that
into one PROPOSITION (rather than carrying `B`, `s`, `sb` as data) is what lets the honest
adversary be defined at every basis by a `dif` on it: two proofs of the same proposition
are definitionally equal, so the machine extracted from either is the same machine. -/

/-- An SRS all of whose generators and whose blinding base are multiples of one point, with
a live blinding slot — the shape `exists_openingRelationB_smul_base` consumes. -/
private def IsScalarSRS (σ : SRS C.Point) [Module C.ScalarField C.Point] : Prop :=
  ∃ (B : C.Point) (s : Fin (2 ^ σ.k) → C.ScalarField) (sb : C.ScalarField),
    σ.g = (fun i => s i • B) ∧ σ.h = sb • B ∧ sb ≠ 0

/-- The sampled bases the endpoints measure over are scalar, as soon as the sampled
blinding multiplier is live. -/
private theorem isScalarSRS_srsOfBasis_scalarBasis [Module C.ScalarField C.Point] (k : ℕ)
    (B : C.Point) (s : SetupIndex (2 ^ k) → C.ScalarField)
    (hsb : s SetupIndex.blind ≠ 0) :
    IsScalarSRS (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s))) :=
  ⟨B, _, _, srsOfBasis_scalarBasis_g k B s, srsOfBasis_scalarBasis_h k B s, hsb⟩

/-! ## Openability without the `u ≠ -1` exclusion

The direct openability argument excludes `u = -1`, the value at which the zeroth
entry `1 + u` of the combined evaluation vector degenerates. That exclusion is about a
challenge the ORACLE supplies, so an adversary that must win on EVERY table cannot afford
it. `combinedEvalVector_exists_ne_zero` trades it for `ζ ≠ ζω`, which the run's own data
supplies: `ζ` is an endo-expanded prechallenge, hence non-zero, and the index's root of
unity is not `1`. -/

/-- The derived claim's two evaluation points, read off `runInputWith`'s `xs`. -/
private theorem honestClaim_pointFn [Module C.ScalarField C.Point] (σ : SRS C.Point) (nc : ℕ)
    {d : ℕ} (idx : Index C.ScalarField (2 ^ d)) (β γ α ζ v u : C.ScalarField) :
    (honestClaim σ nc idx β γ α ζ v u).pointFn 0 = ζ ∧
      (honestClaim σ nc idx β γ α ζ v u).pointFn 1 = ζ * idx.omega :=
  ⟨rfl, rfl⟩

/-- **The derived claim is openable at a scalar SRS, at every evalscale and every opening
base.** The `u ≠ -1` exclusion is replaced by
`ζ ≠ 0` and `ω ≠ 1` — both properties of data the adversary controls or the oracle's
expansion guarantees, hence available at every oracle table. The base `U` is free for the
reason that the relation never reads `σ.U`. -/
private theorem exists_openingRelationB_honestClaim_of_ne [Module C.ScalarField C.Point]
    {σ : SRS C.Point} (hscal : IsScalarSRS σ)
    (hk : 0 < σ.k) {nc d : ℕ} (idx : Index C.ScalarField (2 ^ d))
    (β γ α ζ v u : C.ScalarField) (hζ : ζ ≠ 0) (hω : idx.omega ≠ 1) (U : C.Point) :
    ∃ (a : Fin (2 ^ σ.k) → C.ScalarField) (ρ : C.ScalarField),
      openingRelationB
        { σ with U := U }
        (Bulletproof.combinedCommitment (honestClaim σ nc idx β γ α ζ v u).polyscale
          (honestClaim σ nc idx β γ α ζ v u).commitmentFn)
        (combinedEvalVector (2 ^ σ.k) (honestClaim σ nc idx β γ α ζ v u).evalscale
          (honestClaim σ nc idx β γ α ζ v u).pointFn)
        (Ipa.cipOf (honestClaim σ nc idx β γ α ζ v u)) a ρ := by
  obtain ⟨B, s, sb, hg, hh, hsb⟩ := hscal
  obtain ⟨lam, hlam⟩ :=
    combinedCommitment_runInputWith_smul_base (σ := σ) hg hh idx β γ α ζ v u
  have hN : 1 < 2 ^ σ.k := by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ σ.k := Nat.pow_le_pow_right (by norm_num) hk
  have hx : (honestClaim σ nc idx β γ α ζ v u).pointFn 0
      ≠ (honestClaim σ nc idx β γ α ζ v u).pointFn 1 := by
    rw [(honestClaim_pointFn σ nc idx β γ α ζ v u).1,
      (honestClaim_pointFn σ nc idx β γ α ζ v u).2]
    intro h
    exact hω (mul_left_cancel₀ hζ (by rw [mul_one]; exact h)).symm
  obtain ⟨i0, hb⟩ := combinedEvalVector_exists_ne_zero (2 ^ σ.k) hN
    (honestClaim σ nc idx β γ α ζ v u).evalscale
    (honestClaim σ nc idx β γ α ζ v u).pointFn hx
  rw [show Bulletproof.combinedCommitment (honestClaim σ nc idx β γ α ζ v u).polyscale
      (honestClaim σ nc idx β γ α ζ v u).commitmentFn = lam • B from hlam]
  exact exists_openingRelationB_smul_base _ B s sb hg hh hsb lam _ _ i0 hb

/-! ## Every commitment of the derived claim has an SRS representation

The algebraic-group fields of a `KimchiFamily` demand a coefficient vector and a blinder
for every row of the run's flat commitment stream. At the degenerate data every row is one
of four shapes — `0`, the blinding base `σ.h`, an unblinded chunk commitment, or a masked
chunk commitment — and each has an evident representation. Crucially none of them reads
the oracle table or the six pre-opening challenges, which is what makes the family's
prefix-determinacy fields hold by reflexivity. -/

section Representation

variable [Module C.ScalarField C.Point]

/-- A group element with a known SRS representation. -/
private def Representable (σ : SRS C.Point) (P : C.Point) : Prop :=
  ∃ (a : Fin (2 ^ σ.k) → C.ScalarField) (ρ : C.ScalarField), Bulletproof.commit σ a ρ = P

private theorem rep_zero (σ : SRS C.Point) : Representable σ 0 :=
  ⟨0, 0, by simp [Bulletproof.commit, Bulletproof.commitGen]⟩

private theorem rep_commitPolyChunk (σ : SRS C.Point) (p : Polynomial C.ScalarField)
    (c : ℕ) : Representable σ (commitPolyChunk σ p c) :=
  ⟨fun i => (chunkPoly (2 ^ σ.k) p c).coeff (i : ℕ), 0, by
    simp [Bulletproof.commit, commitPolyChunk, commitPoly]⟩

private theorem rep_commitPolyMaskedChunk (σ : SRS C.Point) (p : Polynomial C.ScalarField)
    (c : ℕ) : Representable σ (commitPolyMaskedChunk σ p c) :=
  ⟨fun i => (chunkPoly (2 ^ σ.k) p c).coeff (i : ℕ), 1, by
    simp [Bulletproof.commit, commitPolyMaskedChunk, commitPolyChunk, commitPoly]⟩

/-- Every tail-row commitment of the honest key at the all-zero proof is representable —
the representation twin of `tailRowsOf_fst_inLine`, with the same case split. -/
private theorem tailRowsOf_fst_representable (σ : SRS C.Point) {nc d k : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (q r : ℕ) (hq : q < tailRowCount) (hr : r < nc) :
    Representable σ
      ((((tailRowsOf C (honestVK σ nc idx) (zeroProof C nc k))[q]'hq)[r]'hr).1) := by
  rcases Nat.lt_or_ge q litRowCount with h | h
  · rw [tailRows_read_lit C q h]
    interval_cases q <;>
      simp only [litRowsOf, zipSeg, zeroProof, honestVK, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Fin.getElem_fin, Vector.getElem_ofFn,
        Vector.getElem_replicate]
    · exact rep_zero σ
    · exact rep_commitPolyMaskedChunk σ _ _
    · exact rep_commitPolyMaskedChunk σ _ _
    · exact rep_commitPolyMaskedChunk σ _ _
    · exact rep_commitPolyMaskedChunk σ _ _
    · exact rep_commitPolyMaskedChunk σ _ _
    · exact rep_commitPolyMaskedChunk σ _ _
  · rcases Nat.lt_or_ge q 22 with h2 | h2
    · obtain ⟨q', rfl⟩ : ∃ q', q = 7 + q' := ⟨q - 7, by omega⟩
      rw [tailRows_read_w C q' (by omega)]
      simp only [zipSeg, zeroProof, Fin.getElem_fin, Vector.getElem_ofFn,
        Vector.getElem_replicate]
      exact rep_zero σ
    · rcases Nat.lt_or_ge q 37 with h3 | h3
      · obtain ⟨q', rfl⟩ : ∃ q', q = 22 + q' := ⟨q - 22, by omega⟩
        rw [tailRows_read_c C q' (by omega)]
        simp only [zipSeg, honestVK, Fin.getElem_fin, Vector.getElem_ofFn]
        exact rep_commitPolyChunk σ _ _
      · obtain ⟨q', rfl⟩ : ∃ q', q = 37 + q' := ⟨q - 37, by omega⟩
        rw [tailRows_read_s C q' (by omega)]
        simp only [zipSeg, honestVK, Fin.getElem_fin, Vector.getElem_ofFn]
        exact rep_commitPolyChunk σ _ _

/-- The flattened tail region is representable everywhere. -/
private theorem tailFlatten_fst_representable (σ : SRS C.Point) {nc d k : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (t : ℕ) (ht : t < tailRowCount * nc) :
    Representable σ
      (((tailRowsOf C (honestVK σ nc idx) (zeroProof C nc k)).flatten[t]'ht).1) := by
  have hnc : 0 < nc := by
    by_contra h
    have : nc = 0 := by omega
    omega
  obtain ⟨q, r, hq, hr, rfl⟩ :
      ∃ q r, q < tailRowCount ∧ r < nc ∧ t = q * nc + r := by
    refine ⟨t / nc, t % nc, ?_, Nat.mod_lt _ hnc, ?_⟩
    · exact Nat.div_lt_of_lt_mul (by omega)
    · rw [Nat.mul_comm]
      exact (Nat.div_add_mod t nc).symm
  rw [flatten_read _ q r hq hr]
  exact tailRowsOf_fst_representable σ idx q r hq hr

/-- **Every row of the derived claim's commitment stream has a representation that is
independent of the six pre-opening challenges.** The `nc` public chunks are the blinding
base (the empty public input takes `publicCommitment`'s `pub.size = 0` branch), the `ft`
row is `0` (`ftComm_runInputWith_zero`), and every tail row is either a commitment the
all-zero proof carries or one of the honest key's committed columns.

Challenge-independence is the point: it is what lets a `KimchiFamily` declare table-free
`aRef`/`ρRef`, so that `hrepPrefix` holds by reflexivity. -/
private theorem exists_rep_commitments (σ : SRS C.Point) {nc d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (i : ℕ) (hi : i < nc + 1 + tailRowCount * nc) :
    ∃ (a : Fin (2 ^ σ.k) → C.ScalarField) (ρ : C.ScalarField),
      ∀ β γ α ζ v u : C.ScalarField, Bulletproof.commit σ a ρ
        = ((runInputWith σ (honestVK σ nc idx) (zeroProof C nc σ.k) #[]
            β γ α ζ v u).commitments[i]'hi) := by
  rcases Nat.lt_or_ge i nc with h | h
  · refine ⟨0, 1, fun β γ α ζ v u => ?_⟩
    simp only [runInputWith, Vector.getElem_map]
    rw [Vector.getElem_append, dif_pos (by omega : i < nc + 1),
      Vector.getElem_append, dif_pos h]
    simp only [publicCommitment, Array.size_empty, ↓reduceIte, Vector.getElem_ofFn,
      Fin.getElem_fin, Vector.getElem_replicate]
    simp [Bulletproof.commit, Bulletproof.commitGen]
  · rcases Nat.eq_or_lt_of_le h with rfl | h2
    · refine ⟨0, 0, fun β γ α ζ v u => ?_⟩
      rw [ftComm_runInputWith_zero σ (honestVK σ nc idx) β γ α ζ v u hi]
      simp [Bulletproof.commit, Bulletproof.commitGen]
    · obtain ⟨a, ρ, hrep⟩ :=
        tailFlatten_fst_representable (nc := nc) (k := σ.k) σ idx (i - (nc + 1)) (by omega)
      refine ⟨a, ρ, fun β γ α ζ v u => ?_⟩
      simp only [runInputWith, Vector.getElem_map]
      rw [Vector.getElem_append, dif_neg (by omega)]
      exact hrep

end Representation

/-! ## The oracle-domain lift

The opening layer's honest machine is an oracle computation over OPENING nodes
(`Bulletproof.Ipa.Forking.IpaNode`); the kimchi game's adversary is one over KIMCHI nodes.
At the opening squeezes a kimchi node carries exactly the opening node's data — the
cross-terms gated by the round index, and `δ`/`sg` at the Schnorr squeeze — together with a
pre-opening block which, for the degenerate proof, does not depend on the opening at all.
So there is a map from opening nodes to kimchi nodes, and `Zcash.Snark.OracleComp.mapDomain`
transports a computation along it. -/

/-- The pre-opening block of the degenerate run: everything the sponge has absorbed by the
time the opening argument starts. It reads the digest, the public commitment chunks and the
NON-opening fields of the proof, so it is the same block for `zeroProofWith C nc k op` at
every `op`. -/
private def zeroPre (C : Ipa.CommitmentCurve) (nc k : ℕ) (digest : C.ScalarField)
    (publicComm : Fin nc → C.Point) : PreIpaData C nc :=
  (nodeAt digest publicComm (zeroProof C nc k) Squeeze.schnorr).pre

/-- **Lifting an opening node into the kimchi transcript.** Round `j` becomes the
`ipaRound j` squeeze while `j < k` and the Schnorr squeeze at `j = k`; the pre-opening
block is supplied as a parameter; the cross-terms, `δ` and `sg` are copied unchanged.
(`IpaNode.cip` has no kimchi counterpart — the kimchi transcript absorbs the combined inner
product as part of its own pre-opening block — and is discarded.) -/
private def liftIpaNode
    {nc k : ℕ} (pre : PreIpaData C nc) (t : IpaNode C k) : KimchiNode C nc k where
  idx := if h : (t.idx : ℕ) < k then Squeeze.ipaRound ⟨(t.idx : ℕ), h⟩ else Squeeze.schnorr
  pre := pre
  lr := t.lr
  delta := t.delta
  sg := t.sg

/-- The lift of the opening layer's round-`i` node is the kimchi node at `ipaRound i`. -/
private theorem liftIpaNode_nodeU {nc k : ℕ} (digest : C.ScalarField)
    (publicComm : Fin nc → C.Point) (cip : C.ScalarField) (op : Ipa.Proof C k) (i : Fin k) :
    liftIpaNode (zeroPre C nc k digest publicComm)
        (Bulletproof.Ipa.Forking.nodeU cip op i)
      = kimchiNodes digest publicComm (zeroProofWith C nc k op) (Squeeze.ipaRound i) := by
  unfold liftIpaNode
  rw [dif_pos (show ((Bulletproof.Ipa.Forking.nodeU cip op i).idx : ℕ) < k from i.isLt)]
  rfl

/-- The lift of the opening layer's Schnorr node is the kimchi node at the Schnorr
squeeze. -/
private theorem liftIpaNode_nodeC {nc k : ℕ} (digest : C.ScalarField)
    (publicComm : Fin nc → C.Point) (cip : C.ScalarField) (op : Ipa.Proof C k) :
    liftIpaNode (zeroPre C nc k digest publicComm)
        (Bulletproof.Ipa.Forking.nodeC cip op)
      = kimchiNodes digest publicComm (zeroProofWith C nc k op) Squeeze.schnorr := by
  unfold liftIpaNode
  rw [dif_neg (show ¬ ((Bulletproof.Ipa.Forking.nodeC cip op).idx : ℕ) < k from
    Nat.lt_irrefl k)]
  rfl

/-! ## The opening argument's honest chain, at an arbitrary opening base

The opening argument is checked at an SRS **together with a distinguished base point `U`**: the
verifier's fold invariant is an identity in `U`, and a transcript built for one `U` is not
accepted at another. The deployed opening layer pins that `U` to the COLD base
`uBaseOf C (Ipa.cipOf claim)` — the sponge base derived from claim data with the sponge started
at `FqSponge.init` — both in the wire win predicate `Bulletproof.Ipa.Forking.wireWins`
(`Forking/Deployed.lean`) and in the anti-vacuity companion
`Bulletproof.Ipa.Forking.honestNode_wireWins_everywhere` (`Forking/Honest.lean`). That is right
for the standalone opening, where the opening IS the whole protocol. The kimchi win event is
checked at the WARM post-`ζ` base instead, so the honest family must win THERE, and no rewriting
produces one statement from the other once the base is baked in.

**The base-generic layer lives upstream and is imported, not restated here.** `section AtBase` of
`Bulletproof/Forking/Honest.lean` provides exactly the four declarations the kimchi-side chain
consumes, and the file-level `open Bulletproof.Ipa.Forking` above brings them into scope under
their short names:

* `winsAtBase σ U claim O π` — the wire win predicate with the base a free parameter — together
  with `winsAtBase_uBaseOf`, the `rfl` recording that at the cold base it *is* `wireWins`;
* `winsAtBase_iff_wins` — the wire/abstract bridge at an arbitrary base, spent below in its
  BACKWARD direction (the honest machine's algebra delivers `Wins`, the family's win event lives
  on the wire);
* `honestNode_wins_everywhere_at` and `honestNode_winsAtBase_everywhere` — the honest machine's
  win on every table at an arbitrary base, abstract and on the wire respectively.

Freeing the base costs nothing mathematically, for three independent reasons the upstream section
spells out: `openingRelationB σ P b v a ρ` reads `σ.g` and `σ.h` and NEVER `σ.U`, so a witness at
one base is a witness at every base definitionally; the honest prover's acceptance invariant
`P + v • U = commitGen σ.g a + commitGen b a • U + ρ • σ.h` is an identity IN `U`; and the query
domain `Bulletproof.Ipa.Forking.nodes cip` is indexed by the claimed value, not by the base, so
base and transcript index decouple — which is what lets a warm base be plugged in below without a
fixed point arising. What this file adds on top is the kimchi-side chain: `honestMachineAt` and
`honestMachineAt_winsAtBase`, then the honest adversary at a base function and its win. -/

/-! ## The honest kimchi adversary

The adversary reads the six pre-opening challenges at the degenerate proof's own nodes —
computable without the opening, since none of those nodes touches the opening field — then
runs the opening layer's honest machine at the derived claim, transported along
`liftIpaNode`, and emits the degenerate proof carrying the opening the machine returns. -/

section Adversary

/-- **The opening layer's honest machine at the derived claim, at an arbitrary opening base.**
The same construction as the cold-base machine, run through
`honestNode_winsAtBase_everywhere` instead of the frozen cold-base
`Bulletproof.Ipa.Forking.honestNode_wireWins_everywhere`, so its output is accepted at the base
`U` the caller names rather than at `uBaseOf C (Ipa.cipOf …)`.

The witness it feeds is the same one: `exists_openingRelationB_honestClaim_of_ne` at `U`, which
is the cold witness verbatim because `openingRelationB` never reads `σ.U`. As there, everything
is at the prechallenge `qζ` rather than at `ζ`, so the non-vanishing of `ζ` is available at EVERY
oracle answer. -/
private theorem exists_honestMachineAt [Module C.ScalarField C.Point]
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    {σ : SRS C.Point} (hscal : IsScalarSRS σ) (hk : 0 < σ.k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (β γ α : C.ScalarField) (qζ : Prechallenge) (v u : C.ScalarField) (U : C.Point) :
    ∃ A : Zcash.Snark.OracleComp (IpaNode C σ.k) Prechallenge (Ipa.Proof C σ.k),
      A.QueryBound (σ.k + 1) ∧
        ∀ O : IpaNode C σ.k → Prechallenge,
          winsAtBase σ U (honestClaim σ nc idx β γ α (expandPre C qζ) v u) O (A.run O) := by
  obtain ⟨a, ρ, hopen⟩ := exists_openingRelationB_honestClaim_of_ne hscal hk idx
    β γ α (expandPre C qζ) v u (hne qζ) hω U
  exact honestNode_winsAtBase_everywhere hsmul hne σ U
    (honestClaim σ nc idx β γ α (expandPre C qζ) v u) a ρ hopen

/-- The honest machine at the base `U`, named so the adversary at `U` and its analysis refer to
the same computation. `noncomputable` only because it is extracted with
`.choose`. -/
private noncomputable def honestMachineAt [Module C.ScalarField C.Point]
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    {σ : SRS C.Point} (hscal : IsScalarSRS σ) (hk : 0 < σ.k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (β γ α : C.ScalarField) (qζ : Prechallenge) (v u : C.ScalarField) (U : C.Point) :
    Zcash.Snark.OracleComp (IpaNode C σ.k) Prechallenge (Ipa.Proof C σ.k) :=
  (exists_honestMachineAt hsmul hne hscal hk nc idx hω β γ α qζ v u U).choose

/-- The honest machine at `U` stays within the opening argument's own budget — the budget does
not depend on the base. -/
private theorem honestMachineAt_queryBound [Module C.ScalarField C.Point]
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    {σ : SRS C.Point} (hscal : IsScalarSRS σ) (hk : 0 < σ.k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (β γ α : C.ScalarField) (qζ : Prechallenge) (v u : C.ScalarField) (U : C.Point) :
    (honestMachineAt hsmul hne hscal hk nc idx hω β γ α qζ v u U).QueryBound
      (σ.k + 1) :=
  (exists_honestMachineAt hsmul hne hscal hk nc idx hω β γ α qζ v u U).choose_spec.1

/-- The honest machine at `U` produces an output the challenge-generic opening verifier accepts
**at `U`**, on every table — `winsAtBase σ U …` in place of the cold `wireWins σ …`. -/
private theorem honestMachineAt_winsAtBase [Module C.ScalarField C.Point]
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    {σ : SRS C.Point} (hscal : IsScalarSRS σ) (hk : 0 < σ.k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (β γ α : C.ScalarField) (qζ : Prechallenge) (v u : C.ScalarField) (U : C.Point)
    (O : IpaNode C σ.k → Prechallenge) :
    winsAtBase σ U (honestClaim σ nc idx β γ α (expandPre C qζ) v u) O
      ((honestMachineAt hsmul hne hscal hk nc idx hω β γ α qζ v u U).run O) :=
  (exists_honestMachineAt hsmul hne hscal hk nc idx hω β γ α qζ v u U).choose_spec.2 O

/-! ### The honest adversary at an arbitrary opening base

The cold-base adversary built its transcript for the cold base, because its machine did. The
base-generic sibling below builds it for a base the caller names.

The base is **not** a plain point but a function of the six pre-opening prechallenges, and that
is forced rather than decorative. The base the family's win event will eventually be checked at
is `KimchiFamily.warmBase`, which is `toGroup` of a squeeze at `preT` of the run's claim — and
the run's claim is `runInputWith` at the six challenges the table supplies, so the warm base
genuinely varies with the table. An adversary is one fixed computation, so a base slot that is a
plain point could never be instantiated there. What saves the construction is that the warm base
depends on the table only through those six answers (`preT` reads the claim through `cip` alone,
and the pre-opening absorb schedule never reads the `opening`
field), and the adversary has already read them by the time it must fix
a base. So the base is exactly a
function of the six prechallenges, which `honestAdversaryAtFn` below takes as given. -/

/-- **The honest kimchi adversary at a table-derived opening base.** Six queries at the
degenerate proof's pre-opening nodes, then the honest opening machine AT THE BASE
`Ubase qβ qγ qα qζ qv qu` transported along `liftIpaNode`, then the degenerate proof carrying
the opening it returns.

Taking the base as a function of the six answers rather than as a point is
what makes a warm, table-derived base reachable; see the section preamble. -/
private noncomputable def honestAdversaryAtFn [Module C.ScalarField C.Point]
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    {σ : SRS C.Point} (hscal : IsScalarSRS σ) (hk : 0 < σ.k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (Ubase : Prechallenge → Prechallenge → Prechallenge → Prechallenge → Prechallenge →
      Prechallenge → C.Point) :
    Zcash.Snark.OracleComp (KimchiNode C nc σ.k) Prechallenge (KimchiProof C nc σ.k) :=
  .query (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.beta) fun qβ =>
  .query (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.gamma) fun qγ =>
  .query (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.alpha) fun qα =>
  .query (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.zeta) fun qζ =>
  .query (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.polyscale) fun qv =>
  .query (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.evalscale) fun qu =>
    Bulletproof.Ipa.Forking.mapComp (zeroProofWith C nc σ.k)
      (Zcash.Snark.OracleComp.mapDomain (liftIpaNode (zeroPre C nc σ.k digest publicComm))
        (honestMachineAt hsmul hne hscal hk nc idx hω
          (squeezeExpand C (k := σ.k) Squeeze.beta qβ)
          (squeezeExpand C (k := σ.k) Squeeze.gamma qγ)
          (squeezeExpand C (k := σ.k) Squeeze.alpha qα) qζ
          (squeezeExpand C (k := σ.k) Squeeze.polyscale qv)
          (squeezeExpand C (k := σ.k) Squeeze.evalscale qu)
          (Ubase qβ qγ qα qζ qv qu)))

/-- **The base-generic honest adversary's query bound is `k + 7`** — six pre-opening queries and
the opening machine's `k + 1`, `mapDomain` and `mapComp` adding none. The base changes nothing:
`honestMachineAt_queryBound` is the same bound at every base. -/
private theorem honestAdversaryAtFn_queryBound [Module C.ScalarField C.Point]
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    {σ : SRS C.Point} (hscal : IsScalarSRS σ) (hk : 0 < σ.k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (Ubase : Prechallenge → Prechallenge → Prechallenge → Prechallenge → Prechallenge →
      Prechallenge → C.Point) :
    (honestAdversaryAtFn hsmul hne hscal hk nc idx hω digest publicComm Ubase).QueryBound
      (σ.k + 7) := by
  have hbase : ∀ (β γ α : C.ScalarField) (qζ : Prechallenge) (v u : C.ScalarField)
      (U : C.Point),
      (Bulletproof.Ipa.Forking.mapComp (zeroProofWith C nc σ.k)
        (Zcash.Snark.OracleComp.mapDomain
          (liftIpaNode (zeroPre C nc σ.k digest publicComm))
          (honestMachineAt hsmul hne hscal hk nc idx hω β γ α qζ v u U))).QueryBound
        (σ.k + 1) := by
    intro β γ α qζ v u U
    exact Bulletproof.Ipa.Forking.mapComp_queryBound _
      (Zcash.Snark.OracleComp.queryBound_mapDomain _
        (honestMachineAt_queryBound hsmul hne hscal hk nc idx hω β γ α qζ v u U))
  have h6 : (honestAdversaryAtFn hsmul hne hscal hk nc idx hω digest publicComm
      Ubase).QueryBound (σ.k + 1 + 1 + 1 + 1 + 1 + 1 + 1) := by
    unfold honestAdversaryAtFn
    exact Zcash.Snark.OracleComp.QueryBound.query fun qβ =>
      Zcash.Snark.OracleComp.QueryBound.query fun qγ =>
      Zcash.Snark.OracleComp.QueryBound.query fun qα =>
      Zcash.Snark.OracleComp.QueryBound.query fun qζ =>
      Zcash.Snark.OracleComp.QueryBound.query fun qv =>
      Zcash.Snark.OracleComp.QueryBound.query fun qu => hbase _ _ _ _ _ _ _
  exact h6.mono (by omega)

/-- **What the base-generic honest adversary emits**: the degenerate proof carrying the opening
the transported machine at the base `Ubase` (applied to the six answers the table supplied)
returns. -/
private theorem honestAdversaryAtFn_run [Module C.ScalarField C.Point]
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    {σ : SRS C.Point} (hscal : IsScalarSRS σ) (hk : 0 < σ.k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (Ubase : Prechallenge → Prechallenge → Prechallenge → Prechallenge → Prechallenge →
      Prechallenge → C.Point)
    (O : KimchiNode C nc σ.k → Prechallenge) :
    (honestAdversaryAtFn hsmul hne hscal hk nc idx hω digest publicComm Ubase).run O
      = zeroProofWith C nc σ.k
          ((honestMachineAt hsmul hne hscal hk nc idx hω
              (reads digest publicComm (zeroProof C nc σ.k) O Squeeze.beta)
              (reads digest publicComm (zeroProof C nc σ.k) O Squeeze.gamma)
              (reads digest publicComm (zeroProof C nc σ.k) O Squeeze.alpha)
              (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.zeta))
              (reads digest publicComm (zeroProof C nc σ.k) O Squeeze.polyscale)
              (reads digest publicComm (zeroProof C nc σ.k) O Squeeze.evalscale)
              (Ubase (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.beta))
                (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.gamma))
                (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.alpha))
                (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.zeta))
                (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.polyscale))
                (O (kimchiNodes digest publicComm (zeroProof C nc σ.k)
                  Squeeze.evalscale)))).run
            (O ∘ liftIpaNode (zeroPre C nc σ.k digest publicComm))) := by
  simp only [honestAdversaryAtFn, Zcash.Snark.OracleComp.run_query,
    Bulletproof.Ipa.Forking.mapComp_run, Zcash.Snark.OracleComp.run_mapDomain, reads]

end Adversary

/-! ## The honest adversary wins on every table -/

/-- **The honest adversary at `U` wins, at the challenges its own run collected.** The kernel
of the win theorem, stated at named challenges and a named base so that neither the six
oracle reads nor the base computation has to be spelled out inside the acceptance predicate.

Stated with `honestMachineAt`/`winsAtBase` in place of the cold machine and `wireWins`, and
the cold `uBaseOf C (Ipa.cipOf …)` slot of the verifier replaced by `U`. -/
private theorem honestAdversary_wins_aux_at [Module C.ScalarField C.Point]
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    {σ : SRS C.Point} (hscal : IsScalarSRS σ) (hk : 0 < σ.k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (O : KimchiNode C nc σ.k → Prechallenge) (β γ α v u : C.ScalarField)
    (qζ : Prechallenge) (U : C.Point) (op : Ipa.Proof C σ.k)
    (hop : op = (honestMachineAt hsmul hne hscal hk nc idx hω β γ α qζ v u U).run
      (O ∘ liftIpaNode (zeroPre C nc σ.k digest publicComm))) :
    kimchiVerifyWith σ (honestVK σ nc idx) (zeroProofWith C nc σ.k op) #[]
        β γ α (expandPre C qζ) v u U
        (Vector.ofFn fun i : Fin σ.k =>
          reads digest publicComm (zeroProofWith C nc σ.k op) O (Squeeze.ipaRound i))
        (reads digest publicComm (zeroProofWith C nc σ.k op) O Squeeze.schnorr)
      = true := by
  have hwin := honestMachineAt_winsAtBase hsmul hne hscal hk nc idx hω β γ α qζ v u U
    (O ∘ liftIpaNode (zeroPre C nc σ.k digest publicComm))
  rw [← hop] at hwin
  unfold winsAtBase honestClaim at hwin
  rw [kimchiVerifyWith_empty_pub, runInputWith_zeroProofWith]
  have hround : ∀ i : Fin σ.k,
      reads digest publicComm (zeroProofWith C nc σ.k op) O (Squeeze.ipaRound i)
        = expandPre C ((O ∘ liftIpaNode (zeroPre C nc σ.k digest publicComm))
            (Bulletproof.Ipa.Forking.nodeU
              (Ipa.cipOf (runInputWith σ (honestVK σ nc idx) (zeroProof C nc σ.k) #[]
                β γ α (expandPre C qζ) v u)) op i)) := by
    intro i
    rw [Function.comp_apply, liftIpaNode_nodeU]
    rfl
  have hfinal : reads digest publicComm (zeroProofWith C nc σ.k op) O Squeeze.schnorr
      = expandPre C ((O ∘ liftIpaNode (zeroPre C nc σ.k digest publicComm))
          (Bulletproof.Ipa.Forking.nodeC
            (Ipa.cipOf (runInputWith σ (honestVK σ nc idx) (zeroProof C nc σ.k) #[]
              β γ α (expandPre C qζ) v u)) op)) := by
    rw [Function.comp_apply, liftIpaNode_nodeC]
    rfl
  simp only [hround, hfinal]
  exact hwin

/-- **The base-generic honest adversary wins on every oracle table.** The challenge-generic
kimchi verifier accepts the proof it emits — with the six pre-opening challenges, the `k` round
challenges and the Schnorr challenge read off the table at the run's own nodes, and with the
opening base the run's own six answers determine.

It is stated at an arbitrary `cp` equal to the run, so that it applies verbatim to a family whose
adversary is the honest one only after a case split on the basis. -/
private theorem honestAdversaryAtFn_wins [Module C.ScalarField C.Point]
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    {σ : SRS C.Point} (hscal : IsScalarSRS σ) (hk : 0 < σ.k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (Ubase : Prechallenge → Prechallenge → Prechallenge → Prechallenge → Prechallenge →
      Prechallenge → C.Point)
    (O : KimchiNode C nc σ.k → Prechallenge) (cp : KimchiProof C nc σ.k)
    (hcp : cp =
      (honestAdversaryAtFn hsmul hne hscal hk nc idx hω digest publicComm Ubase).run O) :
    kimchiVerifyWith σ (honestVK σ nc idx) cp #[]
        (reads digest publicComm cp O Squeeze.beta)
        (reads digest publicComm cp O Squeeze.gamma)
        (reads digest publicComm cp O Squeeze.alpha)
        (reads digest publicComm cp O Squeeze.zeta)
        (reads digest publicComm cp O Squeeze.polyscale)
        (reads digest publicComm cp O Squeeze.evalscale)
        (Ubase (O (kimchiNodes digest publicComm cp Squeeze.beta))
          (O (kimchiNodes digest publicComm cp Squeeze.gamma))
          (O (kimchiNodes digest publicComm cp Squeeze.alpha))
          (O (kimchiNodes digest publicComm cp Squeeze.zeta))
          (O (kimchiNodes digest publicComm cp Squeeze.polyscale))
          (O (kimchiNodes digest publicComm cp Squeeze.evalscale)))
        (Vector.ofFn fun i : Fin σ.k => reads digest publicComm cp O (Squeeze.ipaRound i))
        (reads digest publicComm cp O Squeeze.schnorr)
      = true := by
  subst hcp
  rw [honestAdversaryAtFn_run hsmul hne hscal hk nc idx hω digest publicComm Ubase O]
  exact honestAdversary_wins_aux_at hsmul hne hscal hk nc idx hω digest publicComm O
    (reads digest publicComm (zeroProof C nc σ.k) O Squeeze.beta)
    (reads digest publicComm (zeroProof C nc σ.k) O Squeeze.gamma)
    (reads digest publicComm (zeroProof C nc σ.k) O Squeeze.alpha)
    (reads digest publicComm (zeroProof C nc σ.k) O Squeeze.polyscale)
    (reads digest publicComm (zeroProof C nc σ.k) O Squeeze.evalscale)
    (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.zeta))
    (Ubase (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.beta))
      (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.gamma))
      (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.alpha))
      (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.zeta))
      (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.polyscale))
      (O (kimchiNodes digest publicComm (zeroProof C nc σ.k) Squeeze.evalscale))) _ rfl

/-! ## The degenerate honest family

A `KimchiFamily` must present an adversary at EVERY basis, while the honest adversary needs
the basis to be scalar. The family therefore branches on `IsScalarSRS`: at a scalar basis it
is the honest adversary, elsewhere the constant degenerate proof. Only the scalar branch is
ever measured — the endpoints quantify over `augOfSetup (scalarBasis B s)` — and there
`familyAdversary_scalar` identifies the two.

The algebraic-group data is table-free: the coefficient vectors and blinders come from
`exists_rep_commitments`, which does not read the oracle, and the quotient chunks are the
`nc` zeros. That is exactly what makes the two prefix-determinacy fields reflexivity.

**The base the family must win at is the WARM one.** `KimchiFamily.Wins` feeds the generic
verifier `fam.warmBase basis O`, the point the deployed verifier squeezes from the post-`ζ`
sponge state, which varies with the oracle table. So the branching adversary is built from the
base-generic `honestAdversaryAtFn` rather than the cold `honestAdversary`, at the base function
`honestWarmBase` below — and `honestWarmBase_apply_eq_warmBase` is the one step that closes the
apparent circle between "the base the machine builds its transcript for" and "the base the run's
own proof determines". -/

section Family

variable [Module C.ScalarField C.Point]

/-- **The degenerate family's opening base, as a function of the six pre-opening
prechallenges.** `kimchiWarmBase` at the family's own SRS, verifying key and (empty) public
input, on the DEGENERATE proof `zeroProof`, at the six prechallenges packed into a `Fin preIpaChals`
tuple.

The proof slot is `zeroProof` rather than the run's own proof, and that is what makes the
definition well-founded: the honest adversary must fix a base *before* it knows which opening it
will emit, so a base that read the emitted proof could not be supplied to `honestAdversaryAtFn`
at all. Nothing is lost, because the warm base does not depend on the `opening` field — the
pre-`ζ` absorb schedule never touches it and `preT` reads the claim only through its value — so
`zeroProof` and the run's `zeroProofWith op` give the same point. That is
`honestWarmBase_apply_eq_warmBase`.

Project-local: it names the base at which this development's own degenerate family plays. -/
private noncomputable def honestWarmBase
    {k : ℕ} (nc : ℕ) {d : ℕ} (idx : Index C.ScalarField (2 ^ d))
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (qβ qγ qα qζ qv qu : Prechallenge) : C.Point :=
  kimchiWarmBase (srsOfBasis k basis) (honestVK (srsOfBasis k basis) nc idx) #[]
    (zeroProof C nc k) ![qβ, qγ, qα, qζ, qv, qu]

/-- **The base function, at the run's own six answers, IS the run's warm base.** Fix a proof `cp`
whose pre-opening payload is the degenerate one — every proof the family's adversary can emit is
of this shape, since it differs from `zeroProof` only in its `opening` field. Then evaluating
`honestWarmBase` at the table's answers at `cp`'s six pre-opening nodes returns exactly
`warmBase … cp O`, the base `KimchiFamily.Wins` checks the run at.

This is the single mathematical step of the warm retarget, and it is where the apparent
circularity dissolves. `honestAdversaryAtFn` hands its base function the six prechallenges it
read, so the base slot of `honestAdversaryAtFn_wins` is `honestWarmBase` at those six answers,
computed from `zeroProof`; the win event wants the same squeeze computed from the emitted proof.
Two rewrites close the gap: `warmBase_eq_kimchiWarmBase` (`rfl`) puts the win event's base into
challenge-tuple form, and `kimchiWarmBase_eq_of_preData_eq` — whose hypothesis is precisely
"same pre-opening payload" — exchanges `zeroProof` for `cp`. The six challenge slots then agree
because `preSqueeze` enumerates `β, γ, α, ζ, ξ, r` in the order the tuple packs them.

Project-local: both sides are this development's own constructions. -/
private theorem honestWarmBase_apply_eq_warmBase {k : ℕ} (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d))
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (cp : KimchiProof C nc k)
    (hpre : preDataOf (0 : C.ScalarField)
        (fun c => (publicCommitment C (srsOfBasis k basis)
          (honestVK (srsOfBasis k basis) nc idx) #[])[c]) (zeroProof C nc k)
      = preDataOf (0 : C.ScalarField)
        (fun c => (publicCommitment C (srsOfBasis k basis)
          (honestVK (srsOfBasis k basis) nc idx) #[])[c]) cp)
    (O : KimchiNode C nc k → Prechallenge) :
    honestWarmBase nc idx basis
        (O (kimchiNodes 0 (fun c => (publicCommitment C (srsOfBasis k basis)
          (honestVK (srsOfBasis k basis) nc idx) #[])[c]) cp Squeeze.beta))
        (O (kimchiNodes 0 (fun c => (publicCommitment C (srsOfBasis k basis)
          (honestVK (srsOfBasis k basis) nc idx) #[])[c]) cp Squeeze.gamma))
        (O (kimchiNodes 0 (fun c => (publicCommitment C (srsOfBasis k basis)
          (honestVK (srsOfBasis k basis) nc idx) #[])[c]) cp Squeeze.alpha))
        (O (kimchiNodes 0 (fun c => (publicCommitment C (srsOfBasis k basis)
          (honestVK (srsOfBasis k basis) nc idx) #[])[c]) cp Squeeze.zeta))
        (O (kimchiNodes 0 (fun c => (publicCommitment C (srsOfBasis k basis)
          (honestVK (srsOfBasis k basis) nc idx) #[])[c]) cp Squeeze.polyscale))
        (O (kimchiNodes 0 (fun c => (publicCommitment C (srsOfBasis k basis)
          (honestVK (srsOfBasis k basis) nc idx) #[])[c]) cp Squeeze.evalscale))
      = warmBase (srsOfBasis k basis) (honestVK (srsOfBasis k basis) nc idx) #[] 0 cp O := by
  rw [warmBase_eq_kimchiWarmBase, honestWarmBase,
    kimchiWarmBase_eq_of_preData_eq (srsOfBasis k basis) (honestVK (srsOfBasis k basis) nc idx)
      #[] 0 (zeroProof C nc k) cp _ hpre]
  congr 1
  funext i
  fin_cases i <;> rfl

open Classical in
/-- The family's adversary: the honest one at a scalar basis, at the warm base function
`honestWarmBase`; the constant degenerate proof elsewhere. -/
private noncomputable def familyAdversary
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0) {k : ℕ} (hk : 0 < k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) :
    Zcash.Snark.OracleComp (KimchiNode C nc k) Prechallenge (KimchiProof C nc k) :=
  if h : IsScalarSRS (srsOfBasis k basis) then
    honestAdversaryAtFn hsmul hne h hk nc idx hω 0
      (fun c => (publicCommitment C (srsOfBasis k basis)
        (honestVK (srsOfBasis k basis) nc idx) #[])[c])
      (honestWarmBase nc idx basis)
  else .pure (zeroProof C nc k)

/-- At a scalar basis the family's adversary IS the honest adversary at the warm base. -/
private theorem familyAdversary_scalar
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0) {k : ℕ} (hk : 0 < k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (h : IsScalarSRS (srsOfBasis k basis)) :
    familyAdversary hsmul hne hk nc idx hω basis
      = honestAdversaryAtFn hsmul hne h hk nc idx hω 0
        (fun c => (publicCommitment C (srsOfBasis k basis)
          (honestVK (srsOfBasis k basis) nc idx) #[])[c])
        (honestWarmBase nc idx basis) := by
  rw [familyAdversary, dif_pos h]

/-- **The family's adversary always emits the degenerate proof**, with some opening — the
fact behind both the quotient-shape field and the algebraic-representation fields. -/
private theorem familyAdversary_run
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0) {k : ℕ} (hk : 0 < k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : KimchiNode C nc k → Prechallenge) :
    ∃ op : Ipa.Proof C k,
      (familyAdversary hsmul hne hk nc idx hω basis).run O = zeroProofWith C nc k op := by
  rw [familyAdversary]
  split
  · rename_i h
    exact ⟨_, honestAdversaryAtFn_run hsmul hne h hk nc idx hω 0
      (fun c => (publicCommitment C (srsOfBasis k basis)
        (honestVK (srsOfBasis k basis) nc idx) #[])[c]) (honestWarmBase nc idx basis) O⟩
  · exact ⟨(zeroProof C nc k).opening, rfl⟩

/-- The family's adversary stays within `k + 7` queries at every basis. -/
private theorem familyAdversary_queryBound
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0) {k : ℕ} (hk : 0 < k) (nc : ℕ) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) :
    (familyAdversary hsmul hne hk nc idx hω basis).QueryBound (k + 7) := by
  rw [familyAdversary]
  split
  · rename_i h
    exact honestAdversaryAtFn_queryBound hsmul hne h hk nc idx hω 0
      (fun c => (publicCommitment C (srsOfBasis k basis)
        (honestVK (srsOfBasis k basis) nc idx) #[])[c]) (honestWarmBase nc idx basis)
  · exact Zcash.Snark.OracleComp.QueryBound.pure _ _

omit [Module C.ScalarField C.Point] in
/-- Reading a constant array: stated with the array as a bare variable so that `subst`
sidesteps the dependency of the index type on the array. -/
private theorem getElem_of_eq_replicate {α : Type*} {a : Array α} {n : ℕ} {x : α}
    (h : a = Array.replicate n x) (i : Fin a.size) : a[i] = x := by
  subst h; simp

omit [Module C.ScalarField C.Point] in
/-- Replacing a claim's opening proof leaves its commitment stream alone. -/
@[simp] private theorem commitmentFn_setProof {k m p : ℕ} (inp : Ipa.Input C k m p)
    (op : Ipa.Proof C k) (i : Fin m) :
    ({ inp with proof := op } : Ipa.Input C k m p).commitmentFn i = inp.commitmentFn i := rfl

/-- `exists_rep_commitments` at the proof the honest adversary actually emits, and in the
`commitmentFn` form the family's `hrep` field is stated in. -/
private theorem exists_rep_commitmentFn (σ : SRS C.Point) {nc d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (i : Fin (nc + 1 + tailRowCount * nc)) :
    ∃ (a : Fin (2 ^ σ.k) → C.ScalarField) (ρ : C.ScalarField),
      ∀ (op : Ipa.Proof C σ.k) (β γ α ζ v u : C.ScalarField),
        Bulletproof.commit σ a ρ
          = (runInputWith σ (honestVK σ nc idx) (zeroProofWith C nc σ.k op) #[]
              β γ α ζ v u).commitmentFn i := by
  obtain ⟨a, ρ, h⟩ := exists_rep_commitments σ idx (i : ℕ) i.isLt
  refine ⟨a, ρ, fun op β γ α ζ v u => ?_⟩
  rw [runInputWith_zeroProofWith, commitmentFn_setProof]
  exact h β γ α ζ v u

/-- **The degenerate honest family.** Empty public input, zero digest, the honest key of a
zero-arity circuit whose domain the chunking covers, the branching adversary above, and
table-free algebraic representations. -/
private noncomputable def honestKimchiFamily
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0) {k : ℕ} (hk : 0 < k) {nc : ℕ} (hnc : 0 < nc) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1) (hpc : idx.publicCount = 0)
    (hd : nc * 2 ^ k = 2 ^ d) :
    KimchiFamily C nc k (2 ^ d) where
  cvk := fun basis => honestVK (srsOfBasis k basis) nc (indexAtCurve C idx)
  pub := fun _ => #[]
  digest := fun _ => 0
  idx := indexAtCurve C idx
  adversary := fun basis =>
    familyAdversary hsmul hne hk nc (indexAtCurve C idx) hω basis
  Q := k + 7
  queryBound := fun basis =>
    familyAdversary_queryBound hsmul hne hk nc (indexAtCurve C idx) hω basis
  hnc := hnc
  hkn := hd
  hn := fun _ => rfl
  hvk := fun basis => honestVK_corresponds (srsOfBasis k basis) nc idx
  hpub := fun _ => hpc.symm
  htpos := by
    intro basis O
    obtain ⟨op, hop⟩ :=
      familyAdversary_run hsmul hne hk nc (indexAtCurve C idx) hω basis O
    rw [hop, zeroProofWith_tComm_size]
    exact hnc
  aRef := fun basis _ i =>
    (exists_rep_commitmentFn (srsOfBasis k basis) (indexAtCurve C idx) i).choose
  ρRef := fun basis _ i =>
    (exists_rep_commitmentFn (srsOfBasis k basis) (indexAtCurve C idx) i).choose_spec.choose
  hrep := by
    intro basis O i
    obtain ⟨op, hop⟩ :=
      familyAdversary_run hsmul hne hk nc (indexAtCurve C idx) hω basis O
    rw [runClaim, hop]
    exact (exists_rep_commitmentFn (srsOfBasis k basis) (indexAtCurve C idx)
      i).choose_spec.choose_spec op _ _ _ _ _ _
  aT := fun _ _ _ => 0
  ρT := fun _ _ _ => 0
  hTC := by
    intro basis O
    obtain ⟨op, hop⟩ :=
      familyAdversary_run hsmul hne hk nc (indexAtCurve C idx) hω basis O
    have hz : ((familyAdversary hsmul hne hk nc (indexAtCurve C idx) hω basis).run O).tComm
        = Array.replicate nc 0 := by
      rw [hop]; rfl
    intro j
    refine Eq.trans ?_ (getElem_of_eq_replicate hz j).symm
    simp [Bulletproof.commit, Bulletproof.commitGen]
  hrepPrefix := fun _ _ _ _ _ => ⟨rfl, rfl⟩
  hTPrefix := fun _ _ _ _ _ _ _ => ⟨rfl, rfl⟩

/-! ## The family accepts, so the endpoints' bound is about the extractor -/

/-- The degenerate family's warm base, with its four data fields spelled out. Definitional —
it exists only so that a rewrite can name the term, which a projection of the structure literal
does not let it do. -/
private theorem honestKimchiFamily_warmBase
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0) {k : ℕ} (hk : 0 < k) {nc : ℕ} (hnc : 0 < nc) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1) (hpc : idx.publicCount = 0)
    (hd : nc * 2 ^ k = 2 ^ d) (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) :
    (honestKimchiFamily hsmul hne hk hnc idx hω hpc hd).warmBase basis O
      = warmBase (srsOfBasis k basis) (honestVK (srsOfBasis k basis) nc (indexAtCurve C idx))
          #[] 0 (((honestKimchiFamily hsmul hne hk hnc idx hω hpc hd).adversary basis).run O)
          O := rfl

/-- **The honest family accepts on every table, at every sampled basis with a live blinding
multiplier.**

The base slot is where the proof does its work. `honestAdversaryAtFn_wins` delivers acceptance
with the verifier fed `honestWarmBase` at the six answers the run collected; `KimchiFamily.Wins`
asks for acceptance with it fed `fam.warmBase basis O`. Those are the same point by
`honestWarmBase_apply_eq_warmBase`, whose "same pre-opening payload" hypothesis holds because
the family's adversary always emits `zeroProofWith op` (`familyAdversary_run`) and `preDataOf`
never reads the `opening` field. -/
theorem honestKimchiFamily_wins
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0) {k : ℕ} (hk : 0 < k) {nc : ℕ} (hnc : 0 < nc) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1) (hpc : idx.publicCount = 0)
    (hd : nc * 2 ^ k = 2 ^ d) (B : C.Point) (sm : SetupIndex (2 ^ k) → C.ScalarField)
    (hsb : sm SetupIndex.blind ≠ 0) (O : Coins C nc k) :
    (honestKimchiFamily hsmul hne hk hnc idx hω hpc hd).Wins
      (augOfSetup (Zcash.Snark.scalarBasis B sm)) O := by
  have hs := isScalarSRS_srsOfBasis_scalarBasis k B sm hsb
  have hA : ((honestKimchiFamily hsmul hne hk hnc idx hω hpc hd).adversary
        (augOfSetup (Zcash.Snark.scalarBasis B sm))).run O
      = (honestAdversaryAtFn hsmul hne hs hk nc (indexAtCurve C idx) hω 0
        (fun c => (publicCommitment C
          (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B sm)))
          (honestVK (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B sm))) nc
            (indexAtCurve C idx)) #[])[c])
        (honestWarmBase nc (indexAtCurve C idx)
          (augOfSetup (Zcash.Snark.scalarBasis B sm)))).run O := by
    rw [show (honestKimchiFamily hsmul hne hk hnc idx hω hpc hd).adversary
        (augOfSetup (Zcash.Snark.scalarBasis B sm))
        = familyAdversary hsmul hne hk nc (indexAtCurve C idx) hω
          (augOfSetup (Zcash.Snark.scalarBasis B sm)) from rfl,
      familyAdversary_scalar hsmul hne hk nc (indexAtCurve C idx) hω _ hs]
    rfl
  have hwin := honestAdversaryAtFn_wins hsmul hne hs hk nc (indexAtCurve C idx) hω 0
    (fun c => (publicCommitment C
      (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B sm)))
      (honestVK (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B sm))) nc
        (indexAtCurve C idx)) #[])[c])
    (honestWarmBase nc (indexAtCurve C idx) (augOfSetup (Zcash.Snark.scalarBasis B sm)))
    O _ hA
  -- the run's proof carries the degenerate pre-opening payload: it is `zeroProofWith op`,
  -- and `preDataOf` never reads the `opening` field
  have hpre : preDataOf (0 : C.ScalarField)
      (fun c => (publicCommitment C
        (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B sm)))
        (honestVK (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B sm))) nc
          (indexAtCurve C idx)) #[])[c]) (zeroProof C nc k)
    = preDataOf (0 : C.ScalarField)
      (fun c => (publicCommitment C
        (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B sm)))
        (honestVK (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B sm))) nc
          (indexAtCurve C idx)) #[])[c])
      (((honestKimchiFamily hsmul hne hk hnc idx hω hpc hd).adversary
        (augOfSetup (Zcash.Snark.scalarBasis B sm))).run O) := by
    obtain ⟨op, hop⟩ := familyAdversary_run hsmul hne hk nc (indexAtCurve C idx) hω
      (augOfSetup (Zcash.Snark.scalarBasis B sm)) O
    rw [show ((honestKimchiFamily hsmul hne hk hnc idx hω hpc hd).adversary
        (augOfSetup (Zcash.Snark.scalarBasis B sm))).run O
        = (familyAdversary hsmul hne hk nc (indexAtCurve C idx) hω
          (augOfSetup (Zcash.Snark.scalarBasis B sm))).run O from rfl, hop]
    rfl
  unfold KimchiFamily.Wins
  rw [honestKimchiFamily_warmBase, ← honestWarmBase_apply_eq_warmBase nc (indexAtCurve C idx)
    (augOfSetup (Zcash.Snark.scalarBasis B sm)) _ hpre O]
  exact hwin

/-- **The bound the endpoints prove is a statement about the extractor.** On the honest
family the measured event `Wins ∧ ¬ExtractsWitness`, restricted to the non-excluded slice of
sampled multipliers, is exactly `¬ExtractsWitness`: the acceptance conjunct carries none of
the bound there. The kimchi twin of
`Bulletproof.Ipa.Forking.honestFamily_failure_set`.

**On the `Index` hypothesis.** This is stated for *every* index of the given shape, as the
endpoints are stated for every family — no particular circuit is fixed, and the soundness
results depend on no instance whatsoever. What an instance would add is only that the class is
non-empty, and that is not in doubt: `kimchi/scripts/check_index_fixture.sh` runs
`Index.build?` on dumped production circuits and requires it to accept, deciding the
primitive-root and coset certificates, the row bounds and the wiring laws on real data, then
checks `Satisfies` against the production witness. So the thirteen laws of `Index` are jointly
satisfiable, and demonstrated so on every CI run.

What is therefore still missing is a *proof term* rather than an evaluated check: a Lean-side
`Index` would turn that evidence into a theorem. It is worth having and it is not load-bearing.
The narrow extra the honest family wants is `publicCount = 0`, which production circuits do not
satisfy, so the witness would be a trivial circuit rather than a deployed one — enough to settle
inhabitation, and not to be read as a claim about deployed circuits. -/
theorem honestKimchiFamily_failure_set
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0) {k : ℕ} (hk : 0 < k) {nc : ℕ} (hnc : 0 < nc) {d : ℕ}
    (idx : Index C.ScalarField (2 ^ d)) (hω : idx.omega ≠ 1) (hpc : idx.publicCount = 0)
    (hd : nc * 2 ^ k = 2 ^ d) (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    {q : (SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k |
        (honestKimchiFamily hsmul hne hk hnc idx hω hpc hd).Wins
            (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 ∧
          ¬ (honestKimchiFamily hsmul hne hk hnc idx hω hpc hd).ExtractsWitness
            (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
        ∩ {q | q.1 SetupIndex.blind ≠ 0}
      = {q : (SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k |
          ¬ (honestKimchiFamily hsmul hne hk hnc idx hω hpc hd).ExtractsWitness
            (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
        ∩ {q | q.1 SetupIndex.blind ≠ 0} := by
  ext q
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨-, hext⟩, hb⟩
    exact ⟨hext, hb⟩
  · rintro ⟨hext, hb⟩
    exact ⟨⟨honestKimchiFamily_wins hsmul hne hk hnc idx hω hpc hd B q.1 hb q.2, hext⟩, hb⟩

end Family

/-! ## Non-vacuity of the family itself: a concrete index, and the two Pasta families

`honestKimchiFamily` is a CONSTRUCTION, taking an `Index` together with four side
conditions on it (`0 < k`, `0 < nc`, `idx.omega ≠ 1`, `idx.publicCount = 0`) and the
chunking equation `nc · 2ᵏ = 2ᵈ`. If no index satisfied those conditions the previous
section would be vacuous one floor up — the exact failure mode this module exists to rule
out, reappearing at the level of the family rather than of the adversary. This section
closes the loop: it exhibits an index, and with it a family, unconditionally on each curve
of the Pasta cycle.

**Four rows is the smallest admissible domain.** `Index.zk_three` and `Index.zk_le` force
`3 ≤ zkRows ≤ n`, and `n` is a power of two, so `n ≥ 4`. A primitive FOURTH root of unity
— a square root of `−1` — is therefore not a convenience but a requirement, and each Pasta
scalar field supplies one because its multiplicative order is divisible by `2 ³²`. The two
literals below are `g^((m − 1)/4)` at the non-residue `g = 5`, the generator CompElliptic's
own Tonelli–Shanks data uses; `vestaOmega` lives in `ZMod PALLAS_BASE_CARD` and
`pallasOmega` in `ZMod PALLAS_SCALAR_CARD`, the two curves' scalar fields.

**The laws are discharged by hand, not by `decide`.** `cosetShiftsCertificate` divides
shifts, and kernel reduction of a `ZMod` inverse at a 255-bit modulus (extended Euclid,
well-founded recursion) does not terminate in practice. `CosetShifts` is therefore
proved directly: a relation `sᵢ = sⱼ·ωᵉ` raised to the fourth power gives
`sᵢ⁴ = sⱼ⁴`, and the seven shifts `1,…,7` have pairwise distinct fourth powers
`1, 16, 81, 256, 625, 1296, 2401`, all far below either modulus. Only the generator's own
two-power certificate is used, and it is fed a hand-supplied `Prop` through
`decide_eq_true` rather than being evaluated. -/

section Trivial

open scoped ENNReal

variable {F : Type*} [Field F]

/-! ### The two Pasta instantiations -/

end Trivial

end Kimchi.Verifier.Forking
