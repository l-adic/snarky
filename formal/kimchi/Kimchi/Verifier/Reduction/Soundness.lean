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
correspondence as hypothesis. The quotient `t` also enters as hypothesis data in the
consumer's shape (the acceptance equation `hteq` at each `ζ`): a quotient serving every
consumed evaluation point is a transcript-prefix fact, not something this layer can
produce — its dissolution into the committed `t_comm` chunks is the `_ft` capstone's job
(`ft_identity_of_chunks`, `Capstone/Algebraic.lean`). The assembled witness polynomials
have degree `< n`, so `Kimchi.Protocol.sound` consumption never sees the SRS.
-/
open Bulletproof

namespace Kimchi.Verifier

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization
  Kimchi.Protocol.Equation Kimchi.Verifier

variable {F G : Type*}

/-! ## Cross-point uniqueness -/


/-- The six selector commitments of a verifier key, in gate enumeration order.
Generic over the commitment carrier, so the chunked reduction reuses it at
`Fin nc → G`. Public because it is what the batch reads at a selector row
(`batchC_selRow`), so a downstream statement about the verifying-key rows must name it. -/
def selComm (comms : IndexComms G) : Fin selCount → G :=
  ![comms.generic, comms.poseidon, comms.completeAdd, comms.varBaseMul,
    comms.endoMul, comms.endoScalar]

/-- The gate type of the `j`-th selector row, in the same enumeration order as
`selComm`. Public because it names the selector polynomial a verifying-key selector row
is pinned to, and that pinning is a hypothesis of the binding-free core
`kimchiProof_sound_of_openings_of_vkrep`. -/
def selGate : Fin selCount → GateType :=
  ![.generic, .poseidon, .completeAdd, .varBaseMul, .endoMul, .endoScalar]

/-! ## The batch assembly (44 logical rows)

The abstract rows are the deployed `to_batch` order (verifier.rs) with the ft row
omitted — the ft opening is consumed separately (the `_ft` terminals read it off the
run). Production's `to_batch` also pushes the recursion (`polys`, prev-challenge) rows
ahead of the public row (verifier.rs:972); those rows are absent here because recursion
(`prev_challenges`) is a declared deferral (the scope list in `Verifier/Kimchi.lean`).
The rows:

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

/-- The batch reads the verifier-computed public commitment chunks at the public row.
Public: the verifying-key row bridge (`Capstone/Reflection.lean`) names it. -/
theorem batchC_pubRow {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
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

/-- The batch reads the key's `j`-th selector commitment chunks (`selComm`) at the `j`-th
selector row. Public: the verifying-key row bridge (`Capstone/Reflection.lean`) names it. -/
theorem batchC_selRow {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
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

/-- The batch reads the key's `c`-th coefficient-column commitment chunks at the `c`-th
coefficient row. Public: the verifying-key row bridge (`Capstone/Reflection.lean`) names it. -/
theorem batchC_cRow {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
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

/-- The batch reads the key's σ-column commitment chunks at the `i`-th σ row, at the
permutation column `sigmaPermCol i`. Public: the verifying-key row bridge
(`Capstone/Reflection.lean`) names it. -/
theorem batchC_sRow {nc : ℕ} (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
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
commitment of the `selGate j` selector interpolant. Public alongside `selComm` and
`batchC_selRow`: it is the only route from the batch's selector-row read to the circuit's
own selector polynomial, so the verifying-key row bridge (`Capstone/Reflection.lean`)
cannot state its selector case without it. -/
theorem selComm_indexerOf [Field F] [AddCommGroup G] [Module F G] {n : ℕ}
    (σ : SRS G) (nc : ℕ) (idx : Index F n) (j : Fin selCount) :
    selComm (indexerOf σ nc idx) j
      = fun c : Fin nc => commitPolyMaskedChunk σ (idx.selectorPoly (selGate j)) (c : ℕ) := by
  fin_cases j <;> rfl

/-! ## The verifying-key rows of the batch, at a corresponding key

The three row families the verifying key FIXES — the six σ rows, the fifteen coefficient
rows, the six selector rows — read, under `VKCorresponds`, as the honest chunk commitment
of the presented circuit's own interpolant: unblinded on the σ and coefficient rows, and
carrying the fixed unit blinder (`mask_custom`) on the selectors. These package
`batchC_{sRow,cRow,selRow}` with the correspondence's substitution, so the downstream
layout bridge (`Capstone/Reflection.lean`) applies one lemma per family rather than
resolving the batch read and then the indexer read.

The public row is deliberately NOT here: `batchC_pubRow` returns the caller's `pubC`,
which is the commitment the VERIFIER computes from the key's Lagrange basis, not a key
entry. Its identification with the negated public interpolant's masked chunks is the
caller's `hpubC`, and downstream it comes from the correspondence's Lagrange pin. -/

/-- **The σ rows at a corresponding key**: under `VKCorresponds` the batch's `i`-th σ row,
chunk `c`, is the unblinded chunk commitment of the circuit's own `sigmaPermCol i`
permutation polynomial. -/
theorem batchC_sRow_of_corresponds [Field F] [AddCommGroup G] [Module F G] {n nc : ℕ}
    (σ : SRS G) {idx : Index F n} {comms : IndexComms (Fin nc → G)}
    (hvk : VKCorresponds σ nc comms idx)
    (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (i : Fin sigmaRows) (c : Fin nc) :
    batchC wC zC pubC comms (sRow i) c
      = commitPolyChunk σ (idx.sigmaPoly (sigmaPermCol i)) (c : ℕ) := by
  subst hvk
  rw [batchC_sRow]
  rfl

/-- **The coefficient rows at a corresponding key**: under `VKCorresponds` the batch's
`cc`-th coefficient row, chunk `c`, is the unblinded chunk commitment of the circuit's own
`cc`-th coefficient interpolant. -/
theorem batchC_cRow_of_corresponds [Field F] [AddCommGroup G] [Module F G] {n nc : ℕ}
    (σ : SRS G) {idx : Index F n} {comms : IndexComms (Fin nc → G)}
    (hvk : VKCorresponds σ nc comms idx)
    (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (cc : Fin coeffCols) (c : Fin nc) :
    batchC wC zC pubC comms (cRow cc) c = commitPolyChunk σ (idx.coeffPoly cc) (c : ℕ) := by
  subst hvk
  rw [batchC_cRow]
  rfl

/-- **The selector rows at a corresponding key**: under `VKCorresponds` the batch's `j`-th
selector row, chunk `c`, is the MASKED chunk commitment (fixed unit blinder) of the
circuit's own `selGate j` selector interpolant. -/
theorem batchC_selRow_of_corresponds [Field F] [AddCommGroup G] [Module F G] {n nc : ℕ}
    (σ : SRS G) {idx : Index F n} {comms : IndexComms (Fin nc → G)}
    (hvk : VKCorresponds σ nc comms idx)
    (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (j : Fin selCount) (c : Fin nc) :
    batchC wC zC pubC comms (selRow j) c
      = commitPolyMaskedChunk σ (idx.selectorPoly (selGate j)) (c : ℕ) := by
  subst hvk
  rw [batchC_selRow]
  exact congrFun (selComm_indexerOf σ nc idx j) c

/-! ## The flat segment index -/





/-! ## Assembly and combination -/

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

/-- **Per-chunk claims against a REPRESENTED column combine to its evaluation**
(binding-free): if the chunk witnesses backing the claims ARE the width-`2^k`
coefficient windows of a fixed polynomial `p` of degree `< nc · 2^k`, then the
`x^{2^k}`-power combination of the claims is `p.eval x`.

No commitment occurs in the statement, so the one lemma serves the unblinded rows (σ,
coefficients) and the masked rows (selectors, public) alike: masking changes a chunk
commitment's blinder, never the chunk's coefficient window.

Project-local: it is the binding-free core of the four verifying-key row pinnings inside
`kimchiProof_sound_of_openings`. The knowledge-soundness reduction runs over a key basis
where binding provably FAILS, so the pinning there must come from a representation
hypothesis (discharged, or reported as a discrete-log relation by
`dlRelation_of_chunk_rep_ne`) rather than from `hbind`. -/
theorem combined_eval_of_chunks_of_rep [Field F]
    {k nc : ℕ} {p : Polynomial F} (hdeg : p.natDegree < nc * 2 ^ k)
    {a : Fin nc → Fin (2 ^ k) → F}
    (hrep : ∀ c : Fin nc, a c = chunkCoeffs (2 ^ k) p (c : ℕ))
    {x : F} {ev : Fin nc → F}
    (hev : ∀ c, ev c = innerProduct (a c) (evalVector (2 ^ k) x)) :
    ∑ c : Fin nc, (x ^ 2 ^ k) ^ (c : ℕ) * ev c = p.eval x := by
  rw [eval_eq_sum_chunkPoly _ hdeg x, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [hev c, hrep c, ← chunkPoly_eval]

/-! ## The chunk-representation channel

What a MISMATCHED chunk representation is, when binding is unavailable: a discrete-log
relation with computed coefficients. The commitment map is linear in the
coefficient–blinder pair, so two pairs committing to one group element differ by a
relation; the honest chunk pair is `(chunkCoeffs (2^σ.k) p c, 0)` unblinded and
`(chunkCoeffs (2^σ.k) p c, 1)` masked. -/

/-- Two witness pairs committing to the same point differ by a discrete-log relation —
the `commitmentBinding_iff_no_relation` converse, isolated as a step so the chunk lemmas
below can use it without assuming binding.

Public because it is the whole seam every "representation mismatch is a relation" lemma
factors through, here and in the knowledge-soundness endpoint; it is stated with the
difference pair explicit so the extractor can emit computed coefficients. -/
theorem dlRelation_of_commit_eq [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) {a a' : Fin (2 ^ σ.k) → F} {ρ ρ' : F}
    (h : commit σ a ρ = commit σ a' ρ') : DLRelation σ (a - a') (ρ - ρ') := by
  have hlin : commit σ (a - a') (ρ - ρ') = commit σ a ρ - commit σ a' ρ' := by
    show commitₗ σ (a - a', ρ - ρ') = commitₗ σ (a, ρ) - commitₗ σ (a', ρ')
    rw [← map_sub]
    rfl
  show commit σ (a - a') (ρ - ρ') = 0
  rw [hlin, h, sub_self]

/-- A chunk commitment is the hiding commitment of the chunk's coefficient window at
blinder `0` — the shape `dlRelation_of_commit_eq` consumes. -/
private theorem chunkCommit_as_commit [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (p : Polynomial F) (c : ℕ) :
    commitPolyChunk σ p c = commit σ (chunkCoeffs (2 ^ σ.k) p c) 0 := by
  rw [commitPolyChunk, commitPoly_eq_commit]
  congr 1
  funext i
  show (chunkPoly (2 ^ σ.k) p c).coeff (i : ℕ) = p.coeff (c * 2 ^ σ.k + (i : ℕ))
  unfold chunkPoly
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single (i : ℕ)]
  · rw [if_pos rfl]
  · intro j _ hj
    exact if_neg fun h => hj h
  · intro h
    exact absurd (Finset.mem_range.mpr i.isLt) h

/-- The masked chunk commitment is the same window at blinder `1`. -/
private theorem maskedChunkCommit_as_commit [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (p : Polynomial F) (c : ℕ) :
    commitPolyMaskedChunk σ p c = commit σ (chunkCoeffs (2 ^ σ.k) p c) 1 := by
  rw [commitPolyMaskedChunk, chunkCommit_as_commit]
  simp [commit]

/-- **The break branch for a verifying-key row: a chunk representation that misses the
honest window IS a discrete-log relation** (binding-free, unblinded rows). Given a pair
`(a, ρ)` whose commitment is the `c`-th chunk commitment of `p`, the difference pair
`(a − chunkCoeffs (2^σ.k) p c, ρ − 0)` satisfies `DLRelation σ`.

The two conclusions are deliberately separate: the relation is UNCONDITIONAL (it is what
the extractor's break branch emits, with computed coefficients), while nontriviality is
the discriminator the consumer branches on. Bundling them behind an existential would be
useless downstream, where at the sampled key a relation always exists.

Project-local: this — with `dlRelation_of_chunk_rep_masked_ne` — is where
`kimchiProof_sound_of_openings` spends its binding hypothesis on the verifying-key rows,
so the knowledge-soundness reduction gets data instead of an obstruction. -/
theorem dlRelation_of_chunk_rep_ne [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F} {c : ℕ}
    (hcommit : commit σ a ρ = commitPolyChunk σ p c) :
    DLRelation σ (a - chunkCoeffs (2 ^ σ.k) p c) (ρ - 0)
      ∧ (a ≠ chunkCoeffs (2 ^ σ.k) p c → a - chunkCoeffs (2 ^ σ.k) p c ≠ 0) :=
  ⟨dlRelation_of_commit_eq σ (hcommit.trans (chunkCommit_as_commit σ p c)),
    fun hne => sub_ne_zero_of_ne hne⟩

/-- The masked analogue (selector and public rows): the honest chunk pair carries the
unit mask, so the relation is `(a − chunkCoeffs (2^σ.k) p c, ρ − 1)`. -/
theorem dlRelation_of_chunk_rep_masked_ne [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F} {c : ℕ}
    (hcommit : commit σ a ρ = commitPolyMaskedChunk σ p c) :
    DLRelation σ (a - chunkCoeffs (2 ^ σ.k) p c) (ρ - 1)
      ∧ (a ≠ chunkCoeffs (2 ^ σ.k) p c → a - chunkCoeffs (2 ^ σ.k) p c ≠ 0) :=
  ⟨dlRelation_of_commit_eq σ (hcommit.trans (maskedChunkCommit_as_commit σ p c)),
    fun hne => sub_ne_zero_of_ne hne⟩

/-- Under binding the unblinded chunk relation is trivial, so the representation IS the
honest window. The discharge half of `dlRelation_of_chunk_rep_ne`. -/
private theorem chunk_rep_of_commit [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F} {c : ℕ}
    (hcommit : commit σ a ρ = commitPolyChunk σ p c) :
    a = chunkCoeffs (2 ^ σ.k) p c := by
  obtain ⟨hrel, hnt⟩ := dlRelation_of_chunk_rep_ne σ hcommit
  by_contra hne
  exact hnt hne (hbind _ _ hrel).1

/-- The masked analogue of `chunk_rep_of_commit`. -/
private theorem chunk_rep_of_commit_masked [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F} {c : ℕ}
    (hcommit : commit σ a ρ = commitPolyMaskedChunk σ p c) :
    a = chunkCoeffs (2 ^ σ.k) p c := by
  obtain ⟨hrel, hnt⟩ := dlRelation_of_chunk_rep_masked_ne σ hcommit
  by_contra hne
  exact hnt hne (hbind _ _ hrel).1

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

/-- **The chunked openings-interface core, binding-free**: `kimchiProof_sound_of_openings`
with `hbind` deleted and its two consequences taken as hypotheses instead.

Binding is spent in the original at exactly six places, of two kinds.

*Cross-point agreement* (two places — the witness columns, the accumulator column): the
representation supplied at the challenge tuple carries the same row polynomial as the
challenge-free reference representation. Every consumer in this development passes the
SAME function on both sides, so these are discharged by `rfl`; only a hypothetical
consumer varying the representation across a challenge grid needs binding for them.

*Verifying-key row pinning* (four places — the six σ rows, the fifteen coefficient rows,
the six selector rows, the public row): the challenge-side representation of a row the
verifying key FIXES is the honest chunk window of the presented circuit's own
polynomial. This is the load-bearing use and is not removable — without it the claimed
evaluations speak about a different circuit. Here it is a hypothesis, discharged
downstream either from binding (`kimchiProof_sound_of_openings`) or, over the
knowledge-soundness game's key basis where binding fails, by reporting the mismatch as
the discrete-log relation of `dlRelation_of_chunk_rep_ne`.

Correspondingly the group-side inputs of the original — `hvk`, `hpubC`, and the
reference openings `hbound₀` — are absent: the four pinnings and the two agreements are
everything they were used for, and an unused hypothesis is a lint finding. The
conclusion (the four exclusion-set cardinality bounds and guarded satisfaction of the
assembled reference table) is unchanged. -/
theorem kimchiProof_sound_of_openings_of_vkrep [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) {nc : ℕ} (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n)
    (comms : IndexComms (Fin nc → G))
    (pub : Fin idx.publicCount → F)
    (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (aw₀ : Fin batchRows → Fin nc → Fin (2 ^ σ.k) → F) :
      ((Kimchi.Protocol.soundBadB idx
            (fun col => assembledRow σ.k nc (aw₀ (wRow col)))).card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (Kimchi.Protocol.soundBadG idx
              (fun col => assembledRow σ.k nc (aw₀ (wRow col))) β).card
            ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ, (Kimchi.Protocol.soundBadA idx pub
              (fun col => assembledRow σ.k nc (aw₀ (wRow col)))
              (assembledRow σ.k nc (aw₀ zRow)) β γ).card
            ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (Kimchi.Protocol.soundBadZ idx pub
              (fun col => assembledRow σ.k nc (aw₀ (wRow col)))
              (assembledRow σ.k nc (aw₀ zRow)) β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : F) (t : Polynomial F) (ζ : F)
          (E : Fin batchRows → Fin nc → Fin evalPts → F)
          (aw : Fin batchRows → Fin nc → Fin (2 ^ σ.k) → F) (ρw : Fin batchRows → Fin nc → F),
          β ∉ Kimchi.Protocol.soundBadB idx
              (fun col => assembledRow σ.k nc (aw₀ (wRow col))) →
          γ ∉ Kimchi.Protocol.soundBadG idx
              (fun col => assembledRow σ.k nc (aw₀ (wRow col))) β →
          α ∉ Kimchi.Protocol.soundBadA idx pub
              (fun col => assembledRow σ.k nc (aw₀ (wRow col)))
              (assembledRow σ.k nc (aw₀ zRow)) β γ →
          ζ ∉ Kimchi.Protocol.soundBadZ idx pub
              (fun col => assembledRow σ.k nc (aw₀ (wRow col)))
              (assembledRow σ.k nc (aw₀ zRow)) β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          (∀ i c, commit σ (aw i c) (ρw i c) = batchC wC zC pubC comms i c
              ∧ ∀ j : Fin evalPts,
                E i c j = innerProduct (aw i c)
                  (evalVector (2 ^ σ.k) (![ζ, idx.omega * ζ] j))) →
          (∀ (col : Fin wCols) (c : Fin nc),
            rowPoly (aw (wRow col) c) = rowPoly (aw₀ (wRow col) c)) →
          (∀ c : Fin nc, rowPoly (aw zRow c) = rowPoly (aw₀ zRow c)) →
          (∀ (i : Fin sigmaRows) (c : Fin nc),
            aw (sRow i) c
              = chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly (sigmaPermCol i)) (c : ℕ)) →
          (∀ (cc : Fin coeffCols) (c : Fin nc),
            aw (cRow cc) c = chunkCoeffs (2 ^ σ.k) (idx.coeffPoly cc) (c : ℕ)) →
          (∀ (jj : Fin selCount) (c : Fin nc),
            aw (selRow jj) c
              = chunkCoeffs (2 ^ σ.k) (idx.selectorPoly (selGate jj)) (c : ℕ)) →
          (∀ c : Fin nc,
            aw pubRow c = chunkCoeffs (2 ^ σ.k) (-(idx.pubPoly pub)) (c : ℕ)) →
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
  obtain ⟨hb1, hb2, hb3, hb4, himp⟩ :=
    Kimchi.Protocol.sound idx pub W zg hzdeg
  refine ⟨⟨hb1, hb2, hb3, hb4⟩, ?_⟩
  intro β γ α t ζ E aw ρw hβ hγ hα hζ hζ₁ hζb ht hrow
    hwchunk hzchunk hsigRep hcoeffRep hselRep hpubRep hteq
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
    fun i => combined_eval_of_chunks_of_rep (hdσ _) (hsigRep i)
      (fun c => by simpa using (hrow (sRow i) c).2 0)
  have hcombC : ∀ cc : Fin coeffCols,
      (∑ ch : Fin nc, (ζ ^ 2 ^ σ.k) ^ (ch : ℕ) * E (cRow cc) ch 0)
        = (idx.coeffPoly cc).eval ζ :=
    fun cc => combined_eval_of_chunks_of_rep (hdc _) (hcoeffRep cc)
      (fun c => by simpa using (hrow (cRow cc) c).2 0)
  have hcombSel : ∀ jj : Fin selCount,
      (∑ ch : Fin nc, (ζ ^ 2 ^ σ.k) ^ (ch : ℕ) * E (selRow jj) ch 0)
        = (idx.selectorPoly (selGate jj)).eval ζ :=
    fun jj => combined_eval_of_chunks_of_rep (hdsel _) (hselRep jj)
      (fun c => by simpa using (hrow (selRow jj) c).2 0)
  -- the public row: the combined carried claim is the negated public evaluation
  have hcombPub : claimedPub (ζ ^ 2 ^ σ.k) E = -((idx.pubPoly pub).eval ζ) := by
    rw [show -((idx.pubPoly pub).eval ζ) = (-(idx.pubPoly pub)).eval ζ from
      (eval_neg _ _).symm]
    exact combined_eval_of_chunks_of_rep hdpub hpubRep
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



end Kimchi.Verifier
