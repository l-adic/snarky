import Mathlib
import Bulletproof.Soundness
import Kimchi.Verifier.Reduction.Binding
import Kimchi.Protocol.Equation

/-!
# Composed soundness

Batched opening acceptance, binding, and the key–index correspondence compose into
`Satisfies idx pub wTab`, at production chunking `nc · 2^σ.k = n` (production's
`chunk_size`, uniform across the batch): every committed batch row is its `nc`-chunk
vector, the claims are per chunk, and extraction consumes
`Bulletproof.chunked_batch_soundness` DIRECTLY — the bulletproof conclusion (an
assembled `q i` of degree `< nc · 2^σ.k = n`, chunk-window commit pins, per-chunk claim
reproduction) is exactly what the reduction needs. `nc = 1` is the one-chunk case.

Two structural consequences of chunking:

* **The public row is IN the batch** (44 rows, the public row first — `to_batch`
  order). At
  `nc = 1` the public evaluations are computed by the verifier — a barycentric identity
  with the committed public polynomial, no binding needed. At `nc > 1` they are
  PROOF-CARRIED, adversarial data (`MissingPublicInputEvaluation`, verifier.rs:335):
  their only tie to the public input is the batched opening against the
  verifier-computed public commitment. The reduction therefore takes the public
  commitment chunks `pubC` with their correspondence to the negated public interpolant
  (`hpubC` — per-chunk commitments of `-(idx.pubPoly pub)`, each carrying the unit
  blinder of the all-ones `mask_custom`) and pins the carried claims through binding.
* **The scalar side reads chunk-COMBINED claims** (`claimedEvals` at
  `ζ^{2^σ.k}` / `(ωζ)^{2^σ.k}` — the verifier's `evals.combine`), including the
  combined public claim (`claimedPub`) in `ft_eval0`'s public slot.

Trust boundary: challenge grids for Fiat–Shamir, no-DL-relation binding, the key–index
correspondence as hypothesis. The assembled witness polynomials have degree `< n`, so
`Kimchi.Protocol.sound` consumption never sees the SRS.
-/
open Bulletproof

namespace Kimchi.Verifier

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization
  Kimchi.Protocol.Equation Kimchi.Verifier

variable {F G : Type*}

/-! ## Cross-point uniqueness -/

/-- **Cross-point binding uniqueness**: two extracted witness pairs committing to the
same point carry the same row polynomial. From the no-DL-relation binding hypothesis via
`commitmentBinding_iff_no_relation` (the pair equality is consumed through
`congrArg Prod.fst`, mirroring `bound_eq_of_commitPoly`). Consumed wherever a commitment
is FIXED across the challenge grid: the witness rows and, per `(β, γ)`, the accumulator
row — applied per chunk. -/
theorem bound_unique [Field F] [AddCommGroup G] [Module F G] (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a a' : Fin (2 ^ σ.k) → F} {ρ ρ' : F}
    (h : commit σ a ρ = commit σ a' ρ') : rowPoly a = rowPoly a' := by
  have hbd : CommitmentBinding (F := F) σ :=
    (commitmentBinding_iff_no_relation σ).mpr hbind
  have hpair := @hbd (a, ρ) (a', ρ') h
  have ha : a = a' := congrArg Prod.fst hpair
  rw [ha]

/-- The six selector commitments of a verifier key, in gate enumeration order.
Generic over the commitment carrier, so the chunked reduction reuses it at
`Fin nc → G`. -/
private def selComm (comms : IndexComms G) : Fin selCount → G :=
  ![comms.generic, comms.poseidon, comms.completeAdd, comms.varBaseMul,
    comms.endoMul, comms.endoScalar]

/-- The gate type of the `j`-th selector row, in the same enumeration order as
`selComm`. -/
private def selGate : Fin selCount → GateType :=
  ![.generic, .poseidon, .completeAdd, .varBaseMul, .endoMul, .endoScalar]

/-! ## The batch assembly (44 logical rows)

The abstract rows are the deployed `to_batch` order (verifier.rs) with the ft row
omitted — the ft opening is consumed separately (the `_ft` terminals read it off the
run):

| row     | column                | `to_batch` push (verifier.rs)       |
| ------- | --------------------- | ----------------------------------- |
| `0`     | public                | :978 (commitment built at :834–858) |
| `1`     | accumulator `z`       | :991                                |
| `2–7`   | selectors (`selGate`) | :993–998                            |
| `8–22`  | witness `0–14`        | :1002                               |
| `23–37` | coefficients `0–14`   | :1004                               |
| `38–43` | σ `0–5`               | :1006                               |

In the physical stream the single-chunk ft row sits between the public chunks and the
`z` chunks (pushed at :984–987), so the flat position of row `i` chunk `c` is `c` at
`i = 0` and `nc + 1 + (i − 1)·nc + c` beyond (the reflection layer's `streamPos`).
The stream order is behaviorally pinned: a wrong order mis-combines the polyscale
walk, and the production fixtures reject. -/

/-- Batch row of the public commitment (proof-carried claims at `nc > 1`). -/
def pubRow : Fin batchRows := ⟨0, by omega⟩

/-- Batch row of the accumulator `z`. -/
def zRow : Fin batchRows := ⟨1, by omega⟩

/-- Batch row of the `j`-th selector (order of `selGate`). -/
def selRow (j : Fin selCount) : Fin batchRows := ⟨2 + (j : ℕ), by omega⟩

/-- Batch row of witness column `c`. -/
def wRow (c : Fin wCols) : Fin batchRows := ⟨8 + (c : ℕ), by omega⟩

/-- Batch row of coefficient column `c`. -/
def cRow (c : Fin coeffCols) : Fin batchRows := ⟨23 + (c : ℕ), by omega⟩

/-- Batch row of the `i`-th σ column (first six only). -/
def sRow (i : Fin sigmaRows) : Fin batchRows := ⟨38 + (i : ℕ), by omega⟩

/-- **The 44-row chunked batch commitment assembly**, in `to_batch` order: the public
commitment, the accumulator, the six masked selectors, the 15 witness columns, the 15
coefficient columns, and the first six σ columns — each row its `nc`-chunk vector. -/
def batchC {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (comms : IndexComms (Fin nc → G)) : Fin batchRows → Fin nc → G := fun i =>
  if (i : ℕ) < 1 then pubC
  else if (i : ℕ) < 2 then zC
  else if h2 : (i : ℕ) < 8 then selComm comms ⟨(i : ℕ) - 2, by omega⟩
  else if h3 : (i : ℕ) < 23 then wC ⟨(i : ℕ) - 8, by omega⟩
  else if h4 : (i : ℕ) < 38 then comms.coefficients ⟨(i : ℕ) - 23, by omega⟩
  else comms.sigma ⟨(i : ℕ) - 38, by have := i.isLt; omega⟩

private theorem batchC_pubRow {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (comms : IndexComms (Fin nc → G)) :
    batchC wC zC pubC comms pubRow = pubC := by
  have h1 : (0 : ℕ) < 1 := by omega
  simp only [batchC, pubRow]
  rw [if_pos h1]

private theorem batchC_zRow {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (comms : IndexComms (Fin nc → G)) :
    batchC wC zC pubC comms zRow = zC := by
  have h1 : ¬ (1 : ℕ) < 1 := by omega
  have h2 : (1 : ℕ) < 2 := by omega
  simp only [batchC, zRow]
  rw [if_neg h1, if_pos h2]

private theorem batchC_selRow {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (comms : IndexComms (Fin nc → G)) (j : Fin selCount) :
    batchC wC zC pubC comms (selRow j) = selComm comms j := by
  have h1 : ¬ 2 + (j : ℕ) < 1 := by omega
  have h2 : ¬ 2 + (j : ℕ) < 2 := by omega
  have h3 : 2 + (j : ℕ) < 8 := by omega
  simp only [batchC, selRow]
  rw [if_neg h1, if_neg h2, dif_pos h3]
  congr 1
  apply Fin.ext
  show 2 + (j : ℕ) - 2 = (j : ℕ)
  omega

private theorem batchC_wRow {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (comms : IndexComms (Fin nc → G)) (c : Fin wCols) :
    batchC wC zC pubC comms (wRow c) = wC c := by
  have h1 : ¬ 8 + (c : ℕ) < 1 := by omega
  have h2 : ¬ 8 + (c : ℕ) < 2 := by omega
  have h3 : ¬ 8 + (c : ℕ) < 8 := by omega
  have h4 : 8 + (c : ℕ) < 23 := by omega
  simp only [batchC, wRow]
  rw [if_neg h1, if_neg h2, dif_neg h3, dif_pos h4]
  congr 1
  apply Fin.ext
  show 8 + (c : ℕ) - 8 = (c : ℕ)
  omega

private theorem batchC_cRow {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (comms : IndexComms (Fin nc → G)) (c : Fin coeffCols) :
    batchC wC zC pubC comms (cRow c) = comms.coefficients c := by
  have h1 : ¬ 23 + (c : ℕ) < 1 := by omega
  have h2 : ¬ 23 + (c : ℕ) < 2 := by omega
  have h3 : ¬ 23 + (c : ℕ) < 8 := by omega
  have h4 : ¬ 23 + (c : ℕ) < 23 := by omega
  have h5 : 23 + (c : ℕ) < 38 := by omega
  simp only [batchC, cRow]
  rw [if_neg h1, if_neg h2, dif_neg h3, dif_neg h4, dif_pos h5]
  congr 1
  apply Fin.ext
  show 23 + (c : ℕ) - 23 = (c : ℕ)
  omega

private theorem batchC_sRow {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (comms : IndexComms (Fin nc → G)) (i : Fin sigmaRows) :
    batchC wC zC pubC comms (sRow i) = comms.sigma (sigmaPermCol i) := by
  have h1 : ¬ 38 + (i : ℕ) < 1 := by omega
  have h2 : ¬ 38 + (i : ℕ) < 2 := by omega
  have h3 : ¬ 38 + (i : ℕ) < 8 := by omega
  have h4 : ¬ 38 + (i : ℕ) < 23 := by omega
  have h5 : ¬ 38 + (i : ℕ) < 38 := by omega
  simp only [batchC, sRow]
  rw [if_neg h1, if_neg h2, dif_neg h3, dif_neg h4, dif_neg h5]
  congr 1
  simp only [Fin.mk.injEq]
  omega

/-- On the honest chunked indexer, the `j`-th selector chunk is the per-chunk masked
commitment of the `selGate j` selector interpolant. -/
private theorem selComm_indexerOf [Field F] [AddCommGroup G] [Module F G] {n : ℕ}
    (σ : SRS G) (nc : ℕ) (idx : Index F n) (j : Fin selCount) :
    selComm (indexerOf σ nc idx) j
      = fun c : Fin nc => commitPolyMaskedChunk σ (idx.selectorPoly (selGate j)) (c : ℕ) := by
  fin_cases j <;> rfl

/-! ## The flat segment index -/

/-- The flat segment count of the 44-row chunked batch, in the whnf-friendly
multiplied form (structures indexed by the literal `∑ _ : Fin batchRows, nc` send the
elaborator into a `whnf` spiral; the product is definitionally stuck). -/
def segTotal (nc : ℕ) : ℕ := batchRows * nc

/-- The segment count is the sigma-sum `chunked_batch_soundness` ranges over. -/
theorem segTotal_eq_sum (nc : ℕ) : segTotal nc = ∑ _ : Fin batchRows, nc := by
  simp [segTotal, Finset.sum_const, Finset.card_univ, mul_comm]

/-- The flat (segment) view of a per-row-per-chunk family, along `finSigmaFinEquiv` —
the order `chunkedCombinedCommitment`/`chunkedCombinedInnerProduct` combine in. -/
def flatten {α : Type*} {m nc : ℕ} (f : Fin m → Fin nc → α) :
    Fin (∑ _ : Fin m, nc) → α :=
  fun s => f (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2

/-- `flatten` at the multiplied index form. -/
def flatSeg {α : Type*} {nc : ℕ} (f : Fin batchRows → Fin nc → α) : Fin (segTotal nc) → α :=
  fun s => flatten f (finCongr (segTotal_eq_sum nc) s)

/-! ## Assembly and combination -/

/-- The chunk polynomial's degree bound (the private upstream lemma, restated). -/
private theorem chunkPoly_deg_lt [Field F] {m : ℕ} (hm : 0 < m) (p : Polynomial F)
    (i : ℕ) : (chunkPoly m p i).natDegree < m := by
  apply lt_of_le_of_lt (natDegree_sum_le _ _)
  rw [Finset.fold_max_lt]
  exact ⟨hm, fun j hj =>
    lt_of_le_of_lt (natDegree_monomial_le _) (Finset.mem_range.mp hj)⟩

/-- A row's `nc` chunk witness vectors assembled into the one long polynomial: the
`Fin`-shaped view of `Bulletproof.assemblePoly`. This is the polynomial the row's
chunk commitments BIND — the explicit satisfying witness of the chunked conclusions. -/
noncomputable def assembledRow [Field F] (k nc : ℕ) (a : Fin nc → Fin (2 ^ k) → F) :
    Polynomial F :=
  assemblePoly (2 ^ k) nc (fun ci => if h : ci < nc then a ⟨ci, h⟩ else 0)

private theorem assembledRow_natDegree_lt [Field F] {k nc : ℕ} (hnc : 0 < nc)
    (a : Fin nc → Fin (2 ^ k) → F) :
    (assembledRow k nc a).natDegree < nc * 2 ^ k :=
  assemblePoly_natDegree_lt (Nat.two_pow_pos k) hnc _

private theorem chunkCoeffs_assembledRow [Field F] {k nc : ℕ}
    (a : Fin nc → Fin (2 ^ k) → F) (c : Fin nc) :
    chunkCoeffs (2 ^ k) (assembledRow k nc a) (c : ℕ) = a c := by
  rw [assembledRow, chunkCoeffs_assemblePoly _ c.isLt, dif_pos c.isLt]

/-- The assembled row evaluates as the `x^{2^k}`-power combination of its chunk
witnesses' inner products — `evals.combine` on bound data. -/
private theorem assembledRow_eval [Field F] {k nc : ℕ} (hnc : 0 < nc)
    (a : Fin nc → Fin (2 ^ k) → F) (x : F) :
    (assembledRow k nc a).eval x
      = ∑ c : Fin nc, (x ^ 2 ^ k) ^ (c : ℕ)
          * innerProduct (a c) (evalVector (2 ^ k) x) := by
  rw [eval_eq_sum_chunkPoly _ (assembledRow_natDegree_lt hnc a) x,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [chunkPoly_eval, chunkCoeffs_assembledRow]

/-- **Per-chunk claims against a fixed column combine to its evaluation** (unblinded
form): if each chunk claim is bound to the corresponding chunk commitment of a fixed
polynomial `p` of degree `< nc · 2^σ.k`, the `x^{2^σ.k}`-power combination of the
claims is `p.eval x` — `bound_eval_of_commitPoly`, chunk by chunk. -/
private theorem combined_eval_of_chunks [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {nc : ℕ} {p : Polynomial F} (hdeg : p.natDegree < nc * 2 ^ σ.k)
    {a : Fin nc → Fin (2 ^ σ.k) → F} {ρ : Fin nc → F}
    (hcommit : ∀ c : Fin nc, commit σ (a c) (ρ c) = commitPolyChunk σ p (c : ℕ))
    {x : F} {ev : Fin nc → F}
    (hev : ∀ c, ev c = innerProduct (a c) (evalVector (2 ^ σ.k) x)) :
    ∑ c : Fin nc, (x ^ 2 ^ σ.k) ^ (c : ℕ) * ev c = p.eval x := by
  rw [eval_eq_sum_chunkPoly _ hdeg x, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact bound_eval_of_commitPoly σ hbind (hcommit c)
    (chunkPoly_deg_lt (Nat.two_pow_pos σ.k) p (c : ℕ)) (hev c)

/-- The masked (per-chunk unit blinder) analogue, for the selector and public rows. -/
private theorem combined_eval_of_chunks_masked [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {nc : ℕ} {p : Polynomial F} (hdeg : p.natDegree < nc * 2 ^ σ.k)
    {a : Fin nc → Fin (2 ^ σ.k) → F} {ρ : Fin nc → F}
    (hcommit : ∀ c : Fin nc, commit σ (a c) (ρ c) = commitPolyMaskedChunk σ p (c : ℕ))
    {x : F} {ev : Fin nc → F}
    (hev : ∀ c, ev c = innerProduct (a c) (evalVector (2 ^ σ.k) x)) :
    ∑ c : Fin nc, (x ^ 2 ^ σ.k) ^ (c : ℕ) * ev c = p.eval x := by
  rw [eval_eq_sum_chunkPoly _ hdeg x, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact bound_eval_of_commitPolyMasked σ hbind (hcommit c)
    (chunkPoly_deg_lt (Nat.two_pow_pos σ.k) p (c : ℕ)) (hev c)

/-! ## The claimed record -/

/-- **The chunk-combined claimed record**: the `Evals` the verifier's scalar side reads
(`evals.combine(&powers_of_eval_points_for_chunks)`, verifier.rs:409), assembled from
per-chunk batch claims `E : Fin batchRows → Fin nc → Fin evalPts → F` — the `ζ`-side fields combined
at `zM = ζ^{2^σ.k}`, the `ωζ`-side at `zwM = (ωζ)^{2^σ.k}`. -/
def claimedEvals [Field F] {nc : ℕ} (zM zwM : F) (E : Fin batchRows → Fin nc → Fin evalPts → F) :
    Evals F where
  w c := ∑ ch : Fin nc, zM ^ (ch : ℕ) * E (wRow c) ch 0
  wOmega c := ∑ ch : Fin nc, zwM ^ (ch : ℕ) * E (wRow c) ch 1
  z := ∑ ch : Fin nc, zM ^ (ch : ℕ) * E zRow ch 0
  zOmega := ∑ ch : Fin nc, zwM ^ (ch : ℕ) * E zRow ch 1
  s i := ∑ ch : Fin nc, zM ^ (ch : ℕ) * E (sRow i) ch 0
  coeffs c := ∑ ch : Fin nc, zM ^ (ch : ℕ) * E (cRow c) ch 0
  genericSelector := ∑ ch : Fin nc, zM ^ (ch : ℕ) * E (selRow 0) ch 0
  poseidonSelector := ∑ ch : Fin nc, zM ^ (ch : ℕ) * E (selRow 1) ch 0
  completeAddSelector := ∑ ch : Fin nc, zM ^ (ch : ℕ) * E (selRow 2) ch 0
  mulSelector := ∑ ch : Fin nc, zM ^ (ch : ℕ) * E (selRow 3) ch 0
  emulSelector := ∑ ch : Fin nc, zM ^ (ch : ℕ) * E (selRow 4) ch 0
  endoScalarSelector := ∑ ch : Fin nc, zM ^ (ch : ℕ) * E (selRow 5) ch 0

/-- The chunk-combined public claim at `ζ` — the value `ft_eval0`'s public slot reads
(`eval_polynomial(&public_evals[0], ζ^max_poly_size)`, verifier.rs:441–443). -/
def claimedPub [Field F] {nc : ℕ} (zM : F) (E : Fin batchRows → Fin nc → Fin evalPts → F) : F :=
  ∑ ch : Fin nc, zM ^ (ch : ℕ) * E pubRow ch 0

/-! ## Soundness -/

/-- The chunked openings-interface core (`kimchiProof_sound_of_openings` at
`nc · 2^σ.k = n`): reference openings bind every batch row's chunks; the consumer
supplies, at each avoiding challenge tuple, per-chunk openings binding to the same
commitments and reproducing the per-chunk claims, plus the acceptance equation on the
chunk-COMBINED record. The satisfying table is the reference openings' own witness
rows, ASSEMBLED (`assembledRow`) into degree-`< n` polynomials. The public row's
claims are pinned to the negated public interpolant through `hpubC` — the carried
public evaluations of the `nc > 1` wire are adversarial data, believed only through
this binding. -/
theorem kimchiProof_sound_of_openings [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) {nc : ℕ} (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms (Fin nc → G)) (hvk : VKCorresponds σ nc comms idx)
    (pub : Fin idx.publicCount → F)
    (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (hpubC : ∀ c : Fin nc,
      pubC c = commitPolyMaskedChunk σ (-(idx.pubPoly pub)) (c : ℕ))
    (aw₀ : Fin batchRows → Fin nc → Fin (2 ^ σ.k) → F) (ρw₀ : Fin batchRows → Fin nc → F)
    (hbound₀ : ∀ i c, commit σ (aw₀ i c) (ρw₀ i c) = batchC wC zC pubC comms i c) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : F) (t : Polynomial F) (ζ : F)
          (E : Fin batchRows → Fin nc → Fin evalPts → F)
          (aw : Fin batchRows → Fin nc → Fin (2 ^ σ.k) → F) (ρw : Fin batchRows → Fin nc → F),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          (∀ i c, commit σ (aw i c) (ρw i c) = batchC wC zC pubC comms i c
              ∧ ∀ j : Fin evalPts,
                E i c j = innerProduct (aw i c)
                  (evalVector (2 ^ σ.k) (![ζ, idx.omega * ζ] j))) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ)
              (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ
                ζ (claimedPub (ζ ^ 2 ^ σ.k) E)
                (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)) →
          Satisfies idx pub
            (extractTable idx.omega fun col => assembledRow σ.k nc (aw₀ (wRow col))) := by
  classical
  have hvk' : comms = indexerOf σ nc idx := hvk
  subst hvk'
  -- the bound witness-column and accumulator polynomials (assembled, challenge-free)
  set W : Fin wCols → Polynomial F := fun col => assembledRow σ.k nc (aw₀ (wRow col))
    with hWdef
  set zg : Polynomial F := assembledRow σ.k nc (aw₀ zRow) with hzgdef
  have hW : ∀ col, (W col).natDegree < n := fun col => by
    simp only [hWdef]
    rw [← hk]
    exact assembledRow_natDegree_lt hnc _
  have hzdeg : zg.natDegree < n := by
    simp only [hzgdef]
    rw [← hk]
    exact assembledRow_natDegree_lt hnc _
  -- degree feeders at the CHUNKED bound `nc · 2^σ.k = n`
  have hdσ : ∀ jj : Fin permCols, (idx.sigmaPoly jj).natDegree < nc * 2 ^ σ.k := fun jj => by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hdc : ∀ cc : Fin coeffCols, (idx.coeffPoly cc).natDegree < nc * 2 ^ σ.k := fun cc => by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hdsel : ∀ gg : GateType,
      (idx.selectorPoly gg).natDegree < nc * 2 ^ σ.k := fun gg => by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hdpub : (-(idx.pubPoly pub)).natDegree < nc * 2 ^ σ.k := by
    rw [hk, natDegree_neg]
    exact columnPoly_natDegree_lt idx.omega_prim _
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    Kimchi.Protocol.sound idx pub W zg hzdeg
  refine ⟨badB, badG, badA, badZ, hbounds, ?_⟩
  intro β γ α t ζ E aw ρw hβ hγ hα hζ hζ₁ hζb ht hrow hteq
  -- cross-point uniqueness per chunk: fixed commitments bind the reference chunks
  have hwchunk : ∀ (col : Fin wCols) (c : Fin nc),
      rowPoly (aw (wRow col) c) = rowPoly (aw₀ (wRow col) c) := fun col c =>
    bound_unique σ hbind
      (((hrow (wRow col) c).1.trans
          (congrFun (batchC_wRow wC zC pubC (indexerOf σ nc idx) col) c)).trans
        (((hbound₀ (wRow col) c).trans
          (congrFun (batchC_wRow wC zC pubC (indexerOf σ nc idx) col) c)).symm))
  have hzchunk : ∀ c : Fin nc, rowPoly (aw zRow c) = rowPoly (aw₀ zRow c) := fun c =>
    bound_unique σ hbind
      ((hrow zRow c).1.trans ((hbound₀ zRow c).symm))
  -- the combined witness and accumulator claims are the assembled polynomials' values
  have hcombW : ∀ (col : Fin wCols) (j : Fin evalPts),
      (∑ ch : Fin nc, ((![ζ, idx.omega * ζ] j) ^ 2 ^ σ.k) ^ (ch : ℕ)
          * E (wRow col) ch j)
        = (W col).eval (![ζ, idx.omega * ζ] j) := by
    intro col j
    rw [hWdef, assembledRow_eval hnc]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [(hrow (wRow col) c).2 j, ← rowPoly_eval, ← rowPoly_eval, hwchunk col c]
  have hcombZ : ∀ j : Fin evalPts,
      (∑ ch : Fin nc, ((![ζ, idx.omega * ζ] j) ^ 2 ^ σ.k) ^ (ch : ℕ) * E zRow ch j)
        = zg.eval (![ζ, idx.omega * ζ] j) := by
    intro j
    rw [hzgdef, assembledRow_eval hnc]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [(hrow zRow c).2 j, ← rowPoly_eval, ← rowPoly_eval, hzchunk c]
  -- VK-row pinning: the combined σ / coefficient / selector claims are the Index's own
  have hcombS : ∀ i : Fin sigmaRows,
      (∑ ch : Fin nc, (ζ ^ 2 ^ σ.k) ^ (ch : ℕ) * E (sRow i) ch 0)
        = (idx.sigmaPoly (sigmaPermCol i)).eval ζ :=
    fun i => combined_eval_of_chunks σ hbind (hdσ _)
      (fun c => (hrow (sRow i) c).1.trans
        (congrFun (batchC_sRow wC zC pubC (indexerOf σ nc idx) i) c))
      (fun c => by simpa using (hrow (sRow i) c).2 0)
  have hcombC : ∀ cc : Fin coeffCols,
      (∑ ch : Fin nc, (ζ ^ 2 ^ σ.k) ^ (ch : ℕ) * E (cRow cc) ch 0)
        = (idx.coeffPoly cc).eval ζ :=
    fun cc => combined_eval_of_chunks σ hbind (hdc _)
      (fun c => (hrow (cRow cc) c).1.trans
        (congrFun (batchC_cRow wC zC pubC (indexerOf σ nc idx) cc) c))
      (fun c => by simpa using (hrow (cRow cc) c).2 0)
  have hcombSel : ∀ jj : Fin selCount,
      (∑ ch : Fin nc, (ζ ^ 2 ^ σ.k) ^ (ch : ℕ) * E (selRow jj) ch 0)
        = (idx.selectorPoly (selGate jj)).eval ζ :=
    fun jj => combined_eval_of_chunks_masked σ hbind (hdsel _)
      (fun c => (hrow (selRow jj) c).1.trans
        ((congrFun (batchC_selRow wC zC pubC (indexerOf σ nc idx) jj) c).trans
          (congrFun (selComm_indexerOf σ nc idx jj) c)))
      (fun c => by simpa using (hrow (selRow jj) c).2 0)
  -- the public row: the combined carried claim is the negated public evaluation
  have hcombPub : claimedPub (ζ ^ 2 ^ σ.k) E = -((idx.pubPoly pub).eval ζ) := by
    rw [show -((idx.pubPoly pub).eval ζ) = (-(idx.pubPoly pub)).eval ζ from
      (eval_neg _ _).symm]
    exact combined_eval_of_chunks_masked σ hbind hdpub
      (fun c => (hrow pubRow c).1.trans
        ((congrFun (batchC_pubRow wC zC pubC (indexerOf σ nc idx)) c).trans
          (hpubC c)))
      (fun c => by simpa using (hrow pubRow c).2 0)
  -- the combined record IS the honest record at the assembled table
  have hrec : claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E
      = evalsOf idx (extractTable idx.omega W) zg ζ := by
    refine Evals.ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · funext col
      rw [show (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E).w col
          = ∑ ch : Fin nc, (ζ ^ 2 ^ σ.k) ^ (ch : ℕ) * E (wRow col) ch 0 from rfl,
        evalsOf_extractTable_w idx W hW zg ζ col]
      simpa using hcombW col 0
    · funext col
      rw [show (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E).wOmega col
          = ∑ ch : Fin nc, ((idx.omega * ζ) ^ 2 ^ σ.k) ^ (ch : ℕ) * E (wRow col) ch 1
          from rfl,
        evalsOf_extractTable_wOmega idx W hW zg ζ col]
      simpa using hcombW col 1
    · simpa using hcombZ 0
    · simpa using hcombZ 1
    · funext i
      exact hcombS i
    · funext cc
      exact hcombC cc
    · exact hcombSel 0
    · exact hcombSel 1
    · exact hcombSel 2
    · exact hcombSel 3
    · exact hcombSel 4
    · exact hcombSel 5
  refine himp β γ α t ζ hβ hγ hα hζ hζ₁ hζb ?_
  have h := hteq
  rw [hrec, hcombPub, Index.sigmaPoly_eq_wiring idx 6] at h
  exact h

/-- **Chunked composed soundness** (`kimchiProof_sound` at `nc · 2^σ.k = n`): batched
opening acceptance on the 44-row chunked assembly, binding, and the key–index
correspondence force a satisfying witness table — the reference openings' assembled
witness columns. The transcript split (reference at `ζ₀` for the challenge-free
extraction, consumer at each `ζ`) is verbatim the `nc = 1` argument; extraction is
`Bulletproof.chunked_batch_soundness` at the uniform chunk count, consumed DIRECTLY. -/
theorem kimchiProof_sound [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) {nc : ℕ} (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms (Fin nc → G)) (hvk : VKCorresponds σ nc comms idx)
    (pub : Fin idx.publicCount → F)
    (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (hpubC : ∀ c : Fin nc,
      pubC c = commitPolyMaskedChunk σ (-(idx.pubPoly pub)) (c : ℕ))
    (ζ₀ : F)
    (E₀ : Fin batchRows → Fin nc → Fin evalPts → F)
    (ξ₀ : Fin (segTotal nc) → F) (hξ₀ : Function.Injective ξ₀)
    (r₀ : Fin evalPts → F) (hr₀ : Function.Injective r₀)
    (A₀ : Fin (segTotal nc) → Fin evalPts → Prop)
    (hFS₀ : ∀ s j,
      FiatShamirTreeB σ
        (chunkedCombinedCommitment (ξ₀ s) (batchC wC zC pubC comms))
        (combinedEvalVector (2 ^ σ.k) (r₀ j) ![ζ₀, idx.omega * ζ₀])
        (chunkedCombinedInnerProduct (ξ₀ s) (r₀ j) E₀) (A₀ s j))
    (hacc₀ : ∀ s j, A₀ s j) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F) (wTab : Fin n → Fin wCols → F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : F) (t : Polynomial F) (ζ : F)
          (E : Fin batchRows → Fin nc → Fin evalPts → F)
          (ξ : Fin (segTotal nc) → F) (r : Fin evalPts → F)
          (A : Fin (segTotal nc) → Fin evalPts → Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          Function.Injective ξ → Function.Injective r →
          (∀ s j,
            FiatShamirTreeB σ
              (chunkedCombinedCommitment (ξ s) (batchC wC zC pubC comms))
              (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
              (chunkedCombinedInnerProduct (ξ s) (r j) E) (A s j)) →
          (∀ s j, A s j) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ)
              (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ
                ζ (claimedPub (ζ ^ 2 ^ σ.k) E)
                (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)) →
          Satisfies idx pub wTab := by
  classical
  -- the index transport between the multiplied and sigma-summed segment counts
  set ι := finCongr (segTotal_eq_sum nc).symm with hι
  -- reference extraction: the assembled row polynomials, via the chunked seam
  obtain ⟨q₀, hq₀⟩ := chunked_batch_soundness σ (nc := fun _ : Fin batchRows => nc)
    (fun _ => hnc) (fun v => ξ₀ (ι v)) (hξ₀.comp ι.injective) r₀ hr₀ (by omega)
    (batchC wC zC pubC comms) ![ζ₀, idx.omega * ζ₀] E₀ (fun v j => A₀ (ι v) j)
    (fun v j => hFS₀ (ι v) j) hbind (fun v j => hacc₀ (ι v) j)
  choose ρ₀ hρ₀ using fun i => (hq₀ i).2.1
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hnc hk hbind comms hvk pub wC zC pubC hpubC
      (fun i c => chunkCoeffs (2 ^ σ.k) (q₀ i) (c : ℕ)) ρ₀ (fun i c => hρ₀ i c)
  refine ⟨badB, badG, badA, badZ,
    extractTable idx.omega
      (fun col => assembledRow σ.k nc
        (fun c => chunkCoeffs (2 ^ σ.k) (q₀ (wRow col)) (c : ℕ))),
    hbounds, ?_⟩
  intro β γ α t ζ E ξ r A hβ hγ hα hζ hζ₁ hζb ht hξ hr hFS hacc hteq
  -- consumer extraction at ζ
  obtain ⟨q, hq⟩ := chunked_batch_soundness σ (nc := fun _ : Fin batchRows => nc)
    (fun _ => hnc) (fun v => ξ (ι v)) (hξ.comp ι.injective) r hr (by omega)
    (batchC wC zC pubC comms) ![ζ, idx.omega * ζ] E (fun v j => A (ι v) j)
    (fun v j => hFS (ι v) j) hbind (fun v j => hacc (ι v) j)
  choose ρ hρ using fun i => (hq i).2.1
  exact himp β γ α t ζ E
    (fun i c => chunkCoeffs (2 ^ σ.k) (q i) (c : ℕ)) ρ
    hβ hγ hα hζ hζ₁ hζb ht
    (fun i c => ⟨hρ i c, fun j => (hq i).2.2.2 c j⟩) hteq

end Kimchi.Verifier
