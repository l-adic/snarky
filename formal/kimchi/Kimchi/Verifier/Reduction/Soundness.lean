import Mathlib
import Bulletproof.Soundness
import Kimchi.Verifier.Reduction.Binding
import Kimchi.Protocol.Equation

/-!
# Composed soundness

Batched opening acceptance, binding, and the key–index correspondence compose into
`Satisfies idx pub wTab`: acceptance across the challenge grid forces a satisfying
witness table — the committed data itself, fixed before the challenges — for the
circuit the key commits.

Three things are assumed rather than derived. The challenge grids — over `(β, γ, α, ζ)`
and, per point, over the batch's `(ξ, r)` — stand in for Fiat–Shamir. Binding is carried
in the no-relation form, the computational discrete-log idealization. The key–index
correspondence is a hypothesis.

The batch has 43 rows: fifteen witness columns, the permutation accumulator, the first
six σ columns, fifteen coefficient columns, and six selectors. Only six σ rows appear,
since the evaluation record consumes six σ evaluations while the seventh enters the
scalar equation as a circuit-side value; the public and quotient rows are omitted, as
nothing downstream consumes their binding.

The quotient `t` enters as hypothesis data in the consumer's shape: a quotient serving
every evaluation point of the grid is a transcript-prefix fact, not something this layer
can produce.
-/
open Bulletproof

namespace Kimchi.Verifier

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization
  Kimchi.Protocol.Equation

variable {F G : Type*}

/-! ## Batch extraction

Every commitment in the batch is single-chunk — the quotient's chunks are folded into the
Maller row upstream — so the extraction specializes the chunked argument to one chunk per
row and reads the witness vectors off it. -/

/-- Batched-opening extraction at one chunk per row, presented flatly. -/
private theorem batch_openings_nc1 [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) {n m : ℕ}
    (ξ : Fin n → F) (hξ : Function.Injective ξ)
    (r : Fin m → F) (hr : Function.Injective r) (hm : 0 < m)
    (C : Fin n → G) (x : Fin m → F) (e : Fin n → Fin m → F)
    (A : Fin n → Fin m → Prop)
    (hFS : ∀ s t, FiatShamirTreeB σ (combinedCommitment (ξ s) C)
      (combinedEvalVector (2 ^ σ.k) (r t) x) (combinedInnerProduct (ξ s) (r t) e) (A s t))
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F),
      DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (hacc : ∀ s t, A s t) :
    ∃ (a : Fin n → Fin (2 ^ σ.k) → F) (ρ : Fin n → F), ∀ i,
      commit σ (a i) (ρ i) = C i
        ∧ ∀ j, e i j = innerProduct (a i) (evalVector (2 ^ σ.k) (x j)) := by
  classical
  -- the declared chunk structure: one chunk per row
  set nc : Fin n → ℕ := fun _ => 1 with hnc
  have hsum : (∑ i, nc i) = n := by simp [hnc]
  -- at `nc = 1` the segment equivalence is the identity on values
  have hsig : ∀ v : Fin (∑ i, nc i), finSigmaFinEquiv.symm v
      = (⟨finCongr hsum v, ⟨0, Nat.one_pos⟩⟩ : (i : Fin n) × Fin (nc i)) := by
    intro v
    rw [Equiv.symm_apply_eq]
    refine (Fin.ext ?_).symm
    rw [finSigmaFinEquiv_apply]
    simp [hnc]
    exact Fintype.card_fin _
  obtain ⟨q, hq⟩ := chunked_batch_soundness σ (nc := nc) (fun _ => Nat.one_pos)
    (fun v => ξ (finCongr hsum v)) (hξ.comp (finCongr hsum).injective)
    r hr hm (fun i _ => C i) x (fun i _ j => e i j)
    (fun v t => A (finCongr hsum v) t)
    (fun v t => by
      have h := hFS (finCongr hsum v) t
      have hC : chunkedCombinedCommitment (ξ (finCongr hsum v))
            (fun i (_ : Fin (nc i)) => C i)
          = combinedCommitment (ξ (finCongr hsum v)) C := by
        rw [chunkedCombinedCommitment_eq_flat, combinedCommitment, combinedCommitment]
        refine Finset.sum_equiv (finCongr hsum) (by simp) fun w _ => ?_
        rw [hsig w]
        simp [finCongr_apply]
      have hcip : chunkedCombinedInnerProduct (ξ (finCongr hsum v)) (r t)
            (fun i (_ : Fin (nc i)) j => e i j)
          = combinedInnerProduct (ξ (finCongr hsum v)) (r t) e := by
        rw [chunkedCombinedInnerProduct_eq_flat, combinedInnerProduct,
          combinedInnerProduct]
        refine Finset.sum_equiv (finCongr hsum) (by simp) fun w _ => ?_
        rw [hsig w]
        simp [finCongr_apply]
      rw [hC, hcip]
      exact h)
    hbind (fun v t => hacc (finCongr hsum v) t)
  -- read the flat witnesses off the window-0 chunks (type ascriptions coerce the
  -- `nc`-shaped conclusions to their `nc = 1` values)
  choose ρ hρ using fun i => (hq i).2.1 ⟨0, Nat.one_pos⟩
  refine ⟨fun i => chunkCoeffs (2 ^ σ.k) (q i) 0, ρ, fun i => ⟨hρ i, fun j => ?_⟩⟩
  have hdeg : (q i).natDegree < 1 * 2 ^ σ.k := (hq i).1
  have heval : (q i).eval (x j)
      = ∑ c : Fin 1, ((x j) ^ 2 ^ σ.k) ^ (c : ℕ) * e i j := (hq i).2.2.1 j
  rw [eval_eq_sum_chunkPoly (q i) hdeg, Finset.sum_range_one, pow_zero, one_mul,
    chunkPoly_eval] at heval
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul] at heval
  exact heval.symm

/-! ## Cross-point uniqueness -/

/-- **Cross-point binding uniqueness**: two extracted witness pairs committing to the
same point carry the same row polynomial. From the no-DL-relation binding hypothesis via
`commitmentBinding_iff_no_relation` (the pair equality is consumed through
`congrArg Prod.fst`, mirroring `bound_eq_of_commitPoly`). Consumed wherever a commitment
is FIXED across the challenge grid: the witness rows and, per `(β, γ)`, the accumulator
row. Shared with the chunked reduction (`Reduction/Chunked.lean`), which applies it per
chunk. -/
theorem bound_unique [Field F] [AddCommGroup G] [Module F G] (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a a' : Fin (2 ^ σ.k) → F} {ρ ρ' : F}
    (h : commit σ a ρ = commit σ a' ρ') : rowPoly a = rowPoly a' := by
  have hbd : CommitmentBinding (F := F) σ :=
    (commitmentBinding_iff_no_relation σ).mpr hbind
  have hpair := @hbd (a, ρ) (a', ρ') h
  have ha : a = a' := congrArg Prod.fst hpair
  rw [ha]

/-! ## The batch assembly

The 43-row commitment list the acceptance grids range over, with the named row indices the
claimed-evaluation record reads: rows `0–14` the witness columns, `15` the accumulator,
`16–21` the first six σ columns, `22–36` the coefficient columns, `37–42` the selectors. -/

/-- The six selector commitments of a verifier key, in gate enumeration order.
Generic over the commitment carrier, so the chunked reduction reuses it at
`Fin nc → G`. -/
def selComm (comms : IndexComms G) : Fin 6 → G :=
  ![comms.generic, comms.poseidon, comms.completeAdd, comms.varBaseMul,
    comms.endoMul, comms.endoScalar]

/-- The gate type of the `j`-th selector row, in the same enumeration order as
`selComm`. -/
def selGate : Fin 6 → GateType :=
  ![.generic, .poseidon, .completeAdd, .varBaseMul, .endoMul, .endoScalar]

/-- Batch row of witness column `c`. -/
def wRow (c : Fin 15) : Fin 43 := ⟨(c : ℕ), by omega⟩

/-- Batch row of the accumulator `z`. -/
def zRow : Fin 43 := ⟨15, by omega⟩

/-- Batch row of the `i`-th σ column (first six only — see the module preamble). -/
def sRow (i : Fin 6) : Fin 43 := ⟨16 + (i : ℕ), by omega⟩

/-- Batch row of coefficient column `c`. -/
def cRow (c : Fin 15) : Fin 43 := ⟨22 + (c : ℕ), by omega⟩

/-- Batch row of the `j`-th selector (order of `selGate`). -/
def selRow (j : Fin 6) : Fin 43 := ⟨37 + (j : ℕ), by omega⟩

/-- **The 43-row batch commitment assembly**: 15 witness columns, the accumulator, the
first six σ columns, the 15 coefficient columns, the six masked selectors. -/
def batchC (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) : Fin 43 → G := fun i =>
  if h : (i : ℕ) < 15 then wC ⟨(i : ℕ), h⟩
  else if (i : ℕ) < 16 then zC
  else if h2 : (i : ℕ) < 22 then comms.sigma ⟨(i : ℕ) - 16, by omega⟩
  else if h3 : (i : ℕ) < 37 then comms.coefficients ⟨(i : ℕ) - 22, by omega⟩
  else selComm comms ⟨(i : ℕ) - 37, by omega⟩

/-- Row extraction: a witness row holds its witness commitment. -/
private theorem batchC_wRow (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) (c : Fin 15) :
    batchC wC zC comms (wRow c) = wC c := by
  simp only [batchC, wRow]
  rw [dif_pos c.isLt]

/-- Row extraction: the accumulator row holds the accumulator commitment. -/
private theorem batchC_zRow (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) :
    batchC wC zC comms zRow = zC := by
  have h1 : ¬ (15 : ℕ) < 15 := by omega
  have h2 : (15 : ℕ) < 16 := by omega
  simp only [batchC, zRow]
  rw [dif_neg h1, if_pos h2]

/-- Row extraction: a σ row holds its verifier-key σ commitment. -/
private theorem batchC_sRow (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) (i : Fin 6) :
    batchC wC zC comms (sRow i) = comms.sigma ⟨(i : ℕ), by omega⟩ := by
  have h1 : ¬ 16 + (i : ℕ) < 15 := by omega
  have h2 : ¬ 16 + (i : ℕ) < 16 := by omega
  have h3 : 16 + (i : ℕ) < 22 := by omega
  simp only [batchC, sRow]
  rw [dif_neg h1, if_neg h2, dif_pos h3]
  congr 1
  simp only [Fin.mk.injEq]
  omega

/-- Row extraction: a coefficient row holds its verifier-key coefficient commitment. -/
private theorem batchC_cRow (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) (c : Fin 15) :
    batchC wC zC comms (cRow c) = comms.coefficients c := by
  have h1 : ¬ 22 + (c : ℕ) < 15 := by omega
  have h2 : ¬ 22 + (c : ℕ) < 16 := by omega
  have h3 : ¬ 22 + (c : ℕ) < 22 := by omega
  have h4 : 22 + (c : ℕ) < 37 := by omega
  simp only [batchC, cRow]
  rw [dif_neg h1, if_neg h2, dif_neg h3, dif_pos h4]
  congr 1
  apply Fin.ext
  show 22 + (c : ℕ) - 22 = (c : ℕ)
  omega

/-- Row extraction: a selector row holds its verifier-key selector commitment. -/
private theorem batchC_selRow (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) (j : Fin 6) :
    batchC wC zC comms (selRow j) = selComm comms j := by
  have h1 : ¬ 37 + (j : ℕ) < 15 := by omega
  have h2 : ¬ 37 + (j : ℕ) < 16 := by omega
  have h3 : ¬ 37 + (j : ℕ) < 22 := by omega
  have h4 : ¬ 37 + (j : ℕ) < 37 := by omega
  simp only [batchC, selRow]
  rw [dif_neg h1, if_neg h2, dif_neg h3, dif_neg h4]
  congr 1
  apply Fin.ext
  show 37 + (j : ℕ) - 37 = (j : ℕ)
  omega

/-- On the honest indexer, the `j`-th selector commitment is the masked commitment of
the `selGate j` selector interpolant — the shape `bound_eval_of_commitPolyMasked`
consumes. -/
private theorem selComm_indexerOf [Field F] [AddCommGroup G] [Module F G] {n : ℕ}
    (σ : SRS G) (idx : Index F n) (j : Fin 6) :
    selComm (indexerOf σ idx) j = commitPolyMasked σ (idx.selectorPoly (selGate j)) := by
  fin_cases j <;> rfl

/-! ## The claimed record -/

/-- **The claimed-evaluations record of one grid point**: the `Evals` the verifier's
scalar side reads, assembled from the batch claims `E : Fin 43 → Fin 2 → F` by row —
current-row fields at eval point `0` (= `ζ`), next-row fields at `1` (= `ωζ`). The σ,
coefficient, and selector claims at point `1` are batched but not read here. -/
def claimedEvals (E : Fin 43 → Fin 2 → F) : Evals F where
  w c := E (wRow c) 0
  wOmega c := E (wRow c) 1
  z := E zRow 0
  zOmega := E zRow 1
  s i := E (sRow i) 0
  coeffs c := E (cRow c) 0
  genericSelector := E (selRow 0) 0
  poseidonSelector := E (selRow 1) 0
  completeAddSelector := E (selRow 2) 0
  mulSelector := E (selRow 3) 0
  emulSelector := E (selRow 4) 0
  endoScalarSelector := E (selRow 5) 0

theorem evalsExt {e e' : Evals F} (h1 : e.w = e'.w) (h2 : e.wOmega = e'.wOmega)
    (h3 : e.z = e'.z) (h4 : e.zOmega = e'.zOmega) (h5 : e.s = e'.s)
    (h6 : e.coeffs = e'.coeffs) (h7 : e.genericSelector = e'.genericSelector)
    (h8 : e.poseidonSelector = e'.poseidonSelector)
    (h9 : e.completeAddSelector = e'.completeAddSelector)
    (h10 : e.mulSelector = e'.mulSelector) (h11 : e.emulSelector = e'.emulSelector)
    (h12 : e.endoScalarSelector = e'.endoScalarSelector) : e = e' := by
  cases e
  cases e'
  simp only [Evals.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- **The record congruence** (the crux of the composition): once binding has pinned
every batch claim — witness rows to a fixed polynomial family `W`, the accumulator row
to `z`, the σ/coefficient/selector rows to the Index's own interpolants — the claimed
record IS the honest record `evalsOf` at the extracted table. The witness fields go
through `evalsOf_extractTable_w`/`_wOmega`; the `z`, σ, coefficient, and selector fields
are definitional (`coeffPoly`/`coeffRow`/`sigmaPoly` unfold to the `columnPoly` forms
`evalsOf` carries). -/
private theorem claimedEvals_eq_evalsOf [Field F] {n : ℕ} [NeZero n] (idx : Index F n)
    (W : Fin 15 → Polynomial F) (hW : ∀ c, (W c).natDegree < n)
    (z : Polynomial F) (ζ : F) (E : Fin 43 → Fin 2 → F)
    (hw : ∀ (c : Fin 15) (j : Fin 2), E (wRow c) j = (W c).eval (![ζ, idx.omega * ζ] j))
    (hz : ∀ j : Fin 2, E zRow j = z.eval (![ζ, idx.omega * ζ] j))
    (hs : ∀ i : Fin 6, E (sRow i) 0 = (idx.sigmaPoly ⟨(i : ℕ), by omega⟩).eval ζ)
    (hc : ∀ c : Fin 15, E (cRow c) 0 = (idx.coeffPoly c).eval ζ)
    (hsel : ∀ j : Fin 6, E (selRow j) 0 = (idx.selectorPoly (selGate j)).eval ζ) :
    claimedEvals E = evalsOf idx (extractTable idx.omega W) z ζ := by
  refine evalsExt ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · funext c
    rw [evalsOf_extractTable_w idx W hW z ζ c]
    simpa using hw c 0
  · funext c
    rw [evalsOf_extractTable_wOmega idx W hW z ζ c]
    simpa using hw c 1
  · simpa using hz 0
  · simpa using hz 1
  · funext i
    exact hs i
  · funext c
    exact hc c
  · exact hsel 0
  · exact hsel 1
  · exact hsel 2
  · exact hsel 3
  · exact hsel 4
  · exact hsel 5

/-! ## Soundness -/

/-- The openings-interface core: the per-point transcript families replaced by per-row
openings. The reference side is pure commitment knowledge — every batch row bound to a
known witness pair — and the consumer side supplies, at each avoiding challenge tuple,
openings that bind to the same commitments and reproduce the claimed evaluations.
Extraction models that already possess opened values discharge it directly. The satisfying
table is named EXPLICITLY in the conclusion: it is the reference openings' own witness
rows, read as polynomials and evaluated over the domain — the committed data itself
satisfies the circuit, not merely some table. -/
theorem kimchiProof_sound_of_openings [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F)
    (wC : Fin 15 → G) (zC : G)
    -- REFERENCE openings: the 43 batch rows are BOUND to known witness pairs (commit pins).
    (aw₀ : Fin 43 → Fin (2 ^ σ.k) → F) (ρw₀ : Fin 43 → F)
    (hbound₀ : ∀ i, commit σ (aw₀ i) (ρw₀ i) = batchC wC zC comms i) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : F) (t : Polynomial F) (ζ : F)
          (E : Fin 43 → Fin 2 → F)
          (aw : Fin 43 → Fin (2 ^ σ.k) → F) (ρw : Fin 43 → F),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          (∀ i, commit σ (aw i) (ρw i) = batchC wC zC comms i
              ∧ ∀ j : Fin 2,
                E i j = innerProduct (aw i)
                  (evalVector (2 ^ σ.k) (![ζ, idx.omega * ζ] j))) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ
                ζ (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) →
          Satisfies idx pub
            (extractTable idx.omega fun col => rowPoly (aw₀ (wRow col))) := by
  classical
  -- the verifier key is the honest indexer's
  have hvk' : comms = indexerOf σ idx := hvk
  subst hvk'
  -- the bound witness-column and accumulator polynomials (all challenge-free)
  set W : Fin 15 → Polynomial F := fun col => rowPoly (aw₀ (wRow col)) with hWdef
  set zg : Polynomial F := rowPoly (aw₀ zRow) with hzgdef
  have hW : ∀ col, (W col).natDegree < n := by
    intro col
    simp only [hWdef]
    rw [← hk]
    exact rowPoly_natDegree_lt_two_pow _
  have hzdeg : zg.natDegree < n := by
    simp only [hzgdef]
    rw [← hk]
    exact rowPoly_natDegree_lt_two_pow _
  -- degree feeders for the VK-row pinning (challenge-free)
  have hdσ : ∀ jj : Fin 7, (idx.sigmaPoly jj).natDegree < 2 ^ σ.k := by
    intro jj
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hdc : ∀ cc : Fin 15, (idx.coeffPoly cc).natDegree < 2 ^ σ.k := by
    intro cc
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hdsel : ∀ gg : GateType, (idx.selectorPoly gg).natDegree < 2 ^ σ.k := by
    intro gg
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  -- protocol soundness (`Protocol/Equation.lean`) packages the four small bad sets over
  -- the REFERENCE-extracted witness table and quantifies them BEFORE the challenges; the
  -- commitment layer's only job is to feed its guarded `Accepts` implication `himp`.
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    Kimchi.Protocol.sound idx pub W zg hzdeg
  refine ⟨badB, badG, badA, badZ, hbounds, ?_⟩
  · -- every avoiding challenge tuple with an accepting consumer transcript yields Satisfies
    intro β γ α t ζ E aw ρw hβ hγ hα hζ hζ₁ hζb ht hrow hteq
    -- cross-point uniqueness: FIXED commitments bind the reference W, zg
    have hwpoly : ∀ col, rowPoly (aw (wRow col)) = W col := by
      intro col
      simp only [hWdef]
      exact bound_unique σ hbind
        (((hrow (wRow col)).1.trans
            (batchC_wRow wC zC (indexerOf σ idx) col)).trans
          (((hbound₀ (wRow col)).trans
            (batchC_wRow wC zC (indexerOf σ idx) col)).symm))
    have hzpoly : rowPoly (aw zRow) = zg := by
      simp only [hzgdef]
      exact bound_unique σ hbind
        ((hrow zRow).1.trans ((hbound₀ zRow).symm))
    -- the witness and accumulator claims at ζ, at both eval points
    have hwE : ∀ col (j : Fin 2),
        E (wRow col) j = (W col).eval (![ζ, idx.omega * ζ] j) := by
      intro col j
      rw [(hrow (wRow col)).2 j, ← rowPoly_eval, hwpoly col]
    have hzE : ∀ (j : Fin 2),
        E zRow j = zg.eval (![ζ, idx.omega * ζ] j) := by
      intro j
      rw [(hrow zRow).2 j, ← rowPoly_eval, hzpoly]
    -- VK-row pinning at ζ: σ, coefficient, and selector claims are the Index's own values
    have hsE : ∀ (i : Fin 6),
        E (sRow i) 0 = (idx.sigmaPoly ⟨(i : ℕ), by omega⟩).eval ζ := by
      intro i
      have hcommit : commit σ (aw (sRow i)) (ρw (sRow i))
          = commitPoly σ (idx.sigmaPoly ⟨(i : ℕ), by omega⟩) :=
        (hrow (sRow i)).1.trans (batchC_sRow wC zC (indexerOf σ idx) i)
      have h := bound_eval_of_commitPoly σ hbind hcommit (hdσ _)
        ((hrow (sRow i)).2 0)
      simpa using h
    have hcE : ∀ (cc : Fin 15),
        E (cRow cc) 0 = (idx.coeffPoly cc).eval ζ := by
      intro cc
      have hcommit : commit σ (aw (cRow cc)) (ρw (cRow cc))
          = commitPoly σ (idx.coeffPoly cc) :=
        (hrow (cRow cc)).1.trans (batchC_cRow wC zC (indexerOf σ idx) cc)
      have h := bound_eval_of_commitPoly σ hbind hcommit (hdc _)
        ((hrow (cRow cc)).2 0)
      simpa using h
    have hselE : ∀ (jj : Fin 6),
        E (selRow jj) 0 = (idx.selectorPoly (selGate jj)).eval ζ := by
      intro jj
      have hcommit : commit σ (aw (selRow jj)) (ρw (selRow jj))
          = commitPolyMasked σ (idx.selectorPoly (selGate jj)) :=
        (hrow (selRow jj)).1.trans
          ((batchC_selRow wC zC (indexerOf σ idx) jj).trans
            (selComm_indexerOf σ idx jj))
      have h := bound_eval_of_commitPolyMasked σ hbind hcommit (hdsel _)
        ((hrow (selRow jj)).2 0)
      simpa using h
    refine himp β γ α t ζ hβ hγ hα hζ hζ₁ hζb ?_
    have hrec := claimedEvals_eq_evalsOf idx W hW zg ζ E hwE hzE hsE hcE hselE
    have h := hteq
    rw [hrec, Index.sigmaPoly_eq_wiring idx 6] at h
    exact h

/-- Batched opening acceptance on the 43-row assembly, binding, and the key–index
correspondence force a satisfying witness table, the witness read off the bound
witness-column polynomials. The table is quantified WITH the bad sets, before the
challenges: one fixed assignment — the reference openings' own data — satisfies at every
avoiding accepting tuple. (It cannot be named in the statement, since the reference
openings are themselves extracted inside the proof.)

The transcript is split, and that split is the point. The claimed evaluations are
openings *at* `ζ`, so extracting the witness polynomials from the transcript at `ζ` would
let the excluded set of evaluation points depend on `ζ`, and the statement would be
vacuous. Instead a reference transcript at a separate point extracts the challenge-free
witness and accumulator polynomials; the bad sets are built from that data, with their
cardinalities bounded, and quantified *before* the challenges; only then is every
avoiding tuple quantified. A consumer transcript at `ζ` binds its own openings back to
the reference ones, so point-independence is derived from binding rather than assumed. -/
theorem kimchiProof_sound [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F)
    (wC : Fin 15 → G) (zC : G)
    -- REFERENCE transcript (single, at a reference point ζ₀): extracts the ζ-FREE W, zg.
    (ζ₀ : F)
    (E₀ : Fin 43 → Fin 2 → F)
    (ξ₀ : Fin 43 → F) (hξ₀ : Function.Injective ξ₀)
    (r₀ : Fin 2 → F) (hr₀ : Function.Injective r₀)
    (A₀ : Fin 43 → Fin 2 → Prop)
    (hFS₀ : ∀ (i : Fin 43) (j : Fin 2),
      FiatShamirTreeB σ (combinedCommitment (ξ₀ i) (batchC wC zC comms))
        (combinedEvalVector (2 ^ σ.k) (r₀ j) ![ζ₀, idx.omega * ζ₀])
        (combinedInnerProduct (ξ₀ i) (r₀ j) E₀) (A₀ i j))
    (hacc₀ : ∀ i j, A₀ i j) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F) (wTab : Fin n → Fin 15 → F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : F) (t : Polynomial F) (ζ : F)
          (E : Fin 43 → Fin 2 → F) (ξ : Fin 43 → F) (r : Fin 2 → F)
          (A : Fin 43 → Fin 2 → Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          Function.Injective ξ → Function.Injective r →
          (∀ (i : Fin 43) (j : Fin 2),
            FiatShamirTreeB σ (combinedCommitment (ξ i) (batchC wC zC comms))
              (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
              (combinedInnerProduct (ξ i) (r j) E) (A i j)) →
          (∀ i j, A i j) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ
                ζ (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) →
          Satisfies idx pub wTab := by
  obtain ⟨aw₀, ρw₀, hrow₀⟩ :=
    batch_openings_nc1 σ ξ₀ hξ₀ r₀ hr₀ (by omega)
      (batchC wC zC comms) ![ζ₀, idx.omega * ζ₀] E₀ A₀ hFS₀ hbind hacc₀
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hk hbind comms hvk pub wC zC
      aw₀ ρw₀ (fun i => (hrow₀ i).1)
  refine ⟨badB, badG, badA, badZ,
    extractTable idx.omega (fun col => rowPoly (aw₀ (wRow col))), hbounds, ?_⟩
  intro β γ α t ζ E ξ r A hβ hγ hα hζ hζ₁ hζb ht hξ hr hFS hacc hteq
  obtain ⟨aw, ρw, hrow⟩ :=
    batch_openings_nc1 σ ξ hξ r hr (by omega)
      (batchC wC zC comms) ![ζ, idx.omega * ζ] E A hFS hbind hacc
  exact himp β γ α t ζ E aw ρw hβ hγ hα hζ hζ₁ hζb ht hrow hteq

end Kimchi.Verifier
