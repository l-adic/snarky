import Mathlib
import Kimchi.Verifier.Sound
import Kimchi.Verifier.Equation

/-!
# The composed soundness headline (milestone 4.5): `kimchiProof_sound`

The milestone-4 capstone: batched IPA acceptance (`batch_soundnessA`), DL-binding, and
the verifier-key correspondence (`VKCorresponds`) compose into
`∃ wTab, Satisfies idx pub wTab` — acceptance of the whole challenge grid forces a
satisfying witness table for the modeled circuit. Everything underneath is on the shelf:
the batch extraction is `Soundness/Batch.lean`, the `rowPoly` and pinned-row kits are
`Sound.lean`, the evaluation record and the grid consumer are `Equation.lean`. This file
contributes the composition: cross-point binding uniqueness (`bound_unique`), the 43-row
batch assembly and its claimed-evaluations record (`batchC`/`claimedEvals`), the record
congruence (`claimedEvals_eq_evalsOf`), and the headline itself.

**The trust story.** The challenge grids over `(β, γ, α, ζ)` and, per grid point, over
the batch's `(ξ, r)` are the Fiat–Shamir idealization surrogate — exactly the role they
play in `batch_soundness` and `satisfies_of_verifierEquation`; milestone 5 discharges
them from rewinding the transcript tree. Binding is carried as the no-DL-relation
hypothesis, the computational discrete-log idealization (information-theoretically false
at real parameters — see the scope note of `Soundness/Batch.lean`); the per-point
`FiatShamirTreeB` family is the declared Fiat–Shamir assumption. `VKCorresponds` is
discharged constructively for honest keys (`vkCorresponds_indexerOf`) and by the fixture
MSM check for the production key (`scripts/check_vk_correspond.lean`).

**The batch.** 43 rows: the 15 witness columns (commitments FIXED across the whole
grid), the accumulator `z` (commitment per `(β, γ)`), the FIRST SIX σ columns, the 15
coefficient columns, and the six gate selectors (production's fixed-blinder masking,
`commitPolyMasked`). Only six σ rows are batched: the evaluation record consumes the six
σ *evaluations*, while σ₆ enters the scalar equation as the Index-side value
`(idx.sigmaPoly 6).eval ζ` — never as a proof claim — so a seventh row would add a claim
nothing consumes. The **public and ft rows are omitted** from the abstract batch
entirely (design decision): nothing downstream consumes their binding — the public
value is recomputed by the verifier from `pub`, and the ft row's role is carried by the
`t`-hypothesis below — and the milestone-5 wire reflection adds them back when it
connects to the deployed batch layout.

## The t deferral

Production commits the quotient chunks before `ζ` is sampled, but the verifier's
`ftComm` combination uses `ζ`, so a per-`(β, γ, α)` quotient `t` serving ALL `ζ`-points
of the grid is a transcript-prefix fact that only the Fiat–Shamir layer (milestone 5)
can supply. At this layer the quotient family `t`, its degree bound `ht`, and its scalar
equation `hteq` are hypothesis data, in exactly the consumer's shape — stated at the
claimed record and transported to the honest record by the congruence. `ft_equation`
(`Sound.lean`) documents how a single transcript's bound ft row yields one instance of
the equation; milestone 5 lifts it to the `p`-uniform family. Accordingly no
`ftComm`/`Tcomm`/ft-row data is modeled here.
-/

namespace Kimchi.Verifier

open Polynomial Kimchi.Commitment.IPA Kimchi.Index Kimchi.Verifier.Linearization
  Kimchi.Verifier.Equation

variable {F G : Type*}

/-! ## Cross-point uniqueness -/

/-- **Cross-point binding uniqueness**: two extracted witness pairs committing to the
same point carry the same row polynomial. From the no-DL-relation binding hypothesis via
`commitmentBinding_iff_no_relation` (the pair equality is consumed through
`congrArg Prod.fst`, mirroring `bound_eq_of_commitPoly`). Consumed wherever a commitment
is FIXED across the challenge grid: the witness rows and, per `(β, γ)`, the accumulator
row. -/
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

The 43-row commitment list the headline's acceptance grids range over, and the named row
indices the claimed-evaluations record reads. Layout (documented above): rows `0–14` the
witness columns, `15` the accumulator, `16–21` the first six σ columns, `22–36` the
coefficient columns, `37–42` the six selectors in `GateType` enumeration order. -/

/-- The six selector commitments of a verifier key, as a vector in `GateType`
enumeration order (the zero gate has no selector). Project-local packaging for the batch
assembly. -/
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
theorem batchC_wRow (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) (c : Fin 15) :
    batchC wC zC comms (wRow c) = wC c := by
  simp only [batchC, wRow]
  rw [dif_pos c.isLt]

/-- Row extraction: the accumulator row holds the accumulator commitment. -/
theorem batchC_zRow (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) :
    batchC wC zC comms zRow = zC := by
  have h1 : ¬ (15 : ℕ) < 15 := by omega
  have h2 : (15 : ℕ) < 16 := by omega
  simp only [batchC, zRow]
  rw [dif_neg h1, if_pos h2]

/-- Row extraction: a σ row holds its verifier-key σ commitment. -/
theorem batchC_sRow (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) (i : Fin 6) :
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
theorem batchC_cRow (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) (c : Fin 15) :
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
theorem batchC_selRow (wC : Fin 15 → G) (zC : G) (comms : IndexComms G) (j : Fin 6) :
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
theorem selComm_indexerOf [Field F] [AddCommGroup G] [Module F G] {n : ℕ}
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

private theorem evalsExt {e e' : Evals F} (h1 : e.w = e'.w) (h2 : e.wOmega = e'.wOmega)
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
theorem claimedEvals_eq_evalsOf [Field F] {n : ℕ} [NeZero n] (idx : Index F n)
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

/-! ## The headline -/

set_option linter.unusedVariables false in
/-- **The composed kimchi soundness headline (milestone 4.5), single-challenge form.**
Batched IPA acceptance on the 43-row assembly at every node of the injective challenge
grids, DL-binding, and `VKCorresponds` force a satisfying witness table:
`∃ wTab, Satisfies idx pub wTab`, with witness `extractTable idx.omega W` for the bound
witness-column polynomials `W`.

**Single-α trust story.** The former per-node α *grid axis*
(`Fin (gateAlphaCount + permAlphaCount)`, driven by an injective family + Vandermonde) is
GONE: this layer now uses the counting Schwartz–Zippel argument (`badAlphas`,
`card_badAlphas_le`). The verifier draws ONE constraint-combining challenge `α a c` per
`(β, γ)` node, together with ONE quotient `t a c`; the ζ grid and the per-point `(ξ, r)`
batch grids remain the Fiat–Shamir idealization surrogate (milestone 5 discharges them),
and `hbind` is the DL idealization.

**Quantifier order is the point.** The bad set is *extracted*, hence α-DEPENDENT-LOOKING;
to keep the statement non-vacuous the α-goodness condition lives INSIDE the conclusion as
a proved-small existential — `∃ badA`, of cardinality `≤ n · (K − 1)`
(`card_badAlphas_le`), chosen from the α-FREE extracted data (the witness/accumulator
polynomials produced by `batch_soundnessA` from `E`, `ξ`, `r`, `A`, `hFS`, `hacc`, none of
which mention `α`), and only THEN quantifying over every `α`/`t`/`hteq` that avoids it.
Because `badA` is fixed before `α` is introduced, the vacuous `badA a c := {α a c}` witness
is unavailable: the implication genuinely delivers `Satisfies` for each avoiding challenge.

Hypothesis shape (see the module preamble for the trust story):
* `hk` pins the SRS width to the domain size (`max_poly_size = n`), so every bound row
  polynomial has degree `< n` and column extraction applies;
* the ζ grid and per-point `(ξ, r)` grids with their `FiatShamirTreeB` families are the
  Fiat–Shamir idealization surrogate; `hbind` is the DL idealization;
* the claims `E` may vary with the grid point `(a, c, p)` — every needed
  point-independence is *derived* from binding (`bound_unique`), never assumed;
* `hζn` (`ζ^n ≠ 1` per point) is interface-mandated grid data — not consumed here,
  hence the silenced unused-variable linter (precedent: `ft_equation`,
  `satisfies_extractTable_of_verifierEquation`). -/
theorem kimchiProof_sound [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F)
    {NNN : ℕ}
    (ζ : Fin NNN → F) (hζ : Function.Injective ζ)
    (hζ₁ : ∀ p, ζ p ≠ 1)
    (hζb : ∀ p, ζ p ≠ idx.omega ^ (n - idx.zkRows))
    (hζn : ∀ p, (ζ p) ^ n ≠ 1)
    (hD : Index.degreeBound n < NNN)
    (wC : Fin 15 → G) (zC : G)
    (E : Fin NNN → Fin 43 → Fin 2 → F)
    (ξ : Fin NNN → Fin 43 → F)
    (hξ : ∀ p, Function.Injective (ξ p))
    (r : Fin NNN → Fin 2 → F)
    (hr : ∀ p, Function.Injective (r p))
    (A : Fin NNN → Fin 43 → Fin 2 → Prop)
    (hFS : ∀ p (i : Fin 43) (j : Fin 2),
      FiatShamirTreeB σ (combinedCommitment (ξ p i) (batchC wC zC comms))
        (combinedEvalVector (2 ^ σ.k) (r p j) ![ζ p, idx.omega * ζ p])
        (combinedInnerProduct (ξ p i) (r p j) (E p))
        (A p i j))
    (hacc : ∀ p i j, A p i j) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1)))
      ∧ ∀ (β γ α : F) (t : Polynomial F),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ →
          t.natDegree < 7 * n →
          (∀ p,
            permScalar β γ α (zkpmEval n idx.zkRows idx.omega (ζ p))
                (claimedEvals (E p))
              * (idx.sigmaPoly 6).eval (ζ p)
              - ((ζ p) ^ n - 1) * t.eval (ζ p)
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                (ζ p) (-((idx.pubPoly pub).eval (ζ p)))
                (claimedEvals (E p))) →
          ∃ wTab : Fin n → Fin 15 → F, Satisfies idx pub wTab := by
  classical
  -- the verifier key is the honest indexer's
  have hvk' : comms = indexerOf σ idx := hvk
  subst hvk'
  -- batch extraction at every ζ-grid point: one witness pair per row (challenge-free data)
  choose aw ρw hrow using fun p =>
    batch_soundnessA σ (ξ p) (hξ p) (r p) (hr p) (by omega)
      (batchC wC zC (indexerOf σ idx)) ![ζ p, idx.omega * ζ p]
      (E p) (A p) (hFS p) hbind (hacc p)
  -- a base ζ-grid point (`degreeBound < NNN` forces `NNN` positive)
  have p₀ : Fin NNN := ⟨0, by omega⟩
  -- the bound witness-column and accumulator polynomials (all challenge-free)
  set W : Fin 15 → Polynomial F := fun col => rowPoly (aw p₀ (wRow col))
    with hWdef
  set zg : Polynomial F := rowPoly (aw p₀ zRow) with hzgdef
  have hW : ∀ col, (W col).natDegree < n := by
    intro col
    simp only [hWdef]
    rw [← hk]
    exact rowPoly_natDegree_lt_two_pow _
  have hzdeg : zg.natDegree < n := by
    simp only [hzgdef]
    rw [← hk]
    exact rowPoly_natDegree_lt_two_pow _
  -- cross-point uniqueness: the FIXED commitments bind the same polynomial everywhere
  have hwpoly : ∀ p col, rowPoly (aw p (wRow col)) = W col := by
    intro p col
    simp only [hWdef]
    exact bound_unique σ hbind
      (((hrow p (wRow col)).1.trans
          (batchC_wRow wC zC (indexerOf σ idx) col)).trans
        (((hrow p₀ (wRow col)).1.trans
          (batchC_wRow wC zC (indexerOf σ idx) col)).symm))
  have hzpoly : ∀ p, rowPoly (aw p zRow) = zg := by
    intro p
    simp only [hzgdef]
    exact bound_unique σ hbind
      ((hrow p zRow).1.trans ((hrow p₀ zRow).1.symm))
  -- the witness and accumulator claims, at both eval points
  have hwE : ∀ p col (j : Fin 2),
      E p (wRow col) j = (W col).eval (![ζ p, idx.omega * ζ p] j) := by
    intro p col j
    rw [(hrow p (wRow col)).2 j, ← rowPoly_eval, hwpoly p col]
  have hzE : ∀ p (j : Fin 2),
      E p zRow j = zg.eval (![ζ p, idx.omega * ζ p] j) := by
    intro p j
    rw [(hrow p zRow).2 j, ← rowPoly_eval, hzpoly p]
  -- degree feeders for the VK-row pinning
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
  -- VK-row pinning: σ, coefficient, and selector claims are the Index's own values
  have hsE : ∀ p (i : Fin 6),
      E p (sRow i) 0 = (idx.sigmaPoly ⟨(i : ℕ), by omega⟩).eval (ζ p) := by
    intro p i
    have hcommit : commit σ (aw p (sRow i)) (ρw p (sRow i))
        = commitPoly σ (idx.sigmaPoly ⟨(i : ℕ), by omega⟩) :=
      (hrow p (sRow i)).1.trans (batchC_sRow wC zC (indexerOf σ idx) i)
    have h := bound_eval_of_commitPoly σ hbind hcommit (hdσ _)
      ((hrow p (sRow i)).2 0)
    simpa using h
  have hcE : ∀ p (cc : Fin 15),
      E p (cRow cc) 0 = (idx.coeffPoly cc).eval (ζ p) := by
    intro p cc
    have hcommit : commit σ (aw p (cRow cc)) (ρw p (cRow cc))
        = commitPoly σ (idx.coeffPoly cc) :=
      (hrow p (cRow cc)).1.trans (batchC_cRow wC zC (indexerOf σ idx) cc)
    have h := bound_eval_of_commitPoly σ hbind hcommit (hdc _)
      ((hrow p (cRow cc)).2 0)
    simpa using h
  have hselE : ∀ p (jj : Fin 6),
      E p (selRow jj) 0 = (idx.selectorPoly (selGate jj)).eval (ζ p) := by
    intro p jj
    have hcommit : commit σ (aw p (selRow jj)) (ρw p (selRow jj))
        = commitPolyMasked σ (idx.selectorPoly (selGate jj)) :=
      (hrow p (selRow jj)).1.trans
        ((batchC_selRow wC zC (indexerOf σ idx) jj).trans
          (selComm_indexerOf σ idx jj))
    have h := bound_eval_of_commitPolyMasked σ hbind hcommit (hdsel _)
      ((hrow p (selRow jj)).2 0)
    simpa using h
  -- the challenge-free (value, address) pair multisets (m₁ current-row, m₂ wired-row);
  -- both have `7 · (n − zkRows)` members, bounding the bad β/γ sets.
  set m₁ : Multiset (F × F) :=
    Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
      ((idx.permWitnessPoly (extractTable idx.omega W) c.1).eval (idx.omega ^ (c.2 : ℕ)),
        idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)) with hm₁def
  set m₂ : Multiset (F × F) :=
    Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
      ((idx.permWitnessPoly (extractTable idx.omega W) c.1).eval (idx.omega ^ (c.2 : ℕ)),
        idx.shifts (Kimchi.Quotient.Permutation.restrictCells idx.wiringPerm
              idx.wiringPerm_regionPreserving c).1
          * idx.omega ^ ((Kimchi.Quotient.Permutation.restrictCells idx.wiringPerm
              idx.wiringPerm_regionPreserving c).2 : ℕ)) with hm₂def
  -- both multisets range over `Fin 7 × Fin (n − zkRows)`, so each has `7 · (n − zkRows)`
  -- members
  have hcard : ∀ (f : Fin 7 × Fin (n - idx.zkRows) → F × F),
      Multiset.card (Finset.univ.val.map f) = 7 * (n - idx.zkRows) := by
    intro f
    rw [Multiset.card_map]
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  -- the extracted bad sets — quantified BEFORE the challenges, built from challenge-free
  -- extracted data, each provably small; only THEN quantify over β/γ/α/t
  refine ⟨Kimchi.Quotient.badBetas m₁ m₂, fun β => Kimchi.Quotient.badGammas m₁ m₂ β,
    fun β γ => Kimchi.Quotient.badAlphas
      (idx.fullFamily pub (extractTable idx.omega W) zg β γ) idx.omega n,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · -- anti-vacuity (β axis): `card_badBetas_le` bounds by `max |m₁| |m₂| = 7·(n − zkRows)`
    refine le_trans (Kimchi.Quotient.card_badBetas_le m₁ m₂) ?_
    rw [hm₁def, hm₂def, hcard, hcard]
    exact le_of_eq (max_self _)
  · -- anti-vacuity (γ axis): `card_badGammas_le` bounds by `max |m₁| |m₂| = 7·(n − zkRows)`
    intro β
    refine le_trans (Kimchi.Quotient.card_badGammas_le m₁ m₂ β) ?_
    rw [hm₁def, hm₂def, hcard, hcard]
    exact le_of_eq (max_self _)
  · -- anti-vacuity (α axis): `card_badAlphas_le` bounds the extracted bad set by `n · (K − 1)`
    intro β γ
    exact Kimchi.Quotient.card_badAlphas_le
      (idx.fullFamily pub (extractTable idx.omega W) zg β γ) idx.omega n
  · -- every avoiding challenge triple yields a satisfying witness, via the grid consumer
    intro β γ α t hβ hγ havoid ht hteq
    refine ⟨extractTable idx.omega W,
      satisfies_extractTable_of_verifierEquation idx pub W hW β γ hβ hγ zg hzdeg
        ζ hζ hζ₁ hζb α havoid t ht hD ?_⟩
    intro p
    have hrec := claimedEvals_eq_evalsOf idx W hW zg (ζ p) (E p)
      (hwE p) (hzE p) (hsE p) (hcE p) (hselE p)
    have h := hteq p
    rw [hrec, Index.sigmaPoly_eq_wiring idx 6] at h
    exact h

end Kimchi.Verifier
