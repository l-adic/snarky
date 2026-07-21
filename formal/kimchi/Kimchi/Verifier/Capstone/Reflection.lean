import Kimchi.Verifier.Capstone.Algebraic
import Kimchi.Verifier.Reflect

/-!
# The Fiat–Shamir-reflection discharge (the run-level terminal roots)

The composition that removes the extraction grid at a genuine deployed run, building on the
algebraic quotient of `Capstone/Algebraic.lean`.

**Part 1 — the FS-reflection ft opening.** `kimchi_fiat_shamir_{vesta,pallas}` re-anchor the
Fiat–Shamir axiom on the deployed verifier's OWN transcript — the warm-sponge finish
`Ipa.verifyFrom … (runWarm …) (runInput …)` a `kimchiVerify`-accepted run actually executes
(`ReflectedRun.accepts`, `Kimchi/Verifier/Reflect.lean`) — rather than the cold `Ipa.verify`
of `poseidon_fiat_shamir_*`; and `ft_opening_of_reflected` (PROVED, the transcript tree as a
hypothesis) derives the ft opening from a genuine acceptance: the constructed ft commitment
is slot 1 of the run's own accepted 45-row batch, so `ipa_soundnessA` plus the arity-generic
`eval_pins_of_opening` pin `runFtComm` to a representation whose evaluation at the run's own
`ζ` is `runFtEval0`. The curve wrappers `ft_opening_of_reflected_{vesta,pallas}` discharge the
run by reflection (`kimchiVerify_reflects`) and the tree by the new axioms, so a single
`KimchiVesta.verify … = true` yields the ft opening outright.

**Part 2 — the run-level terminal roots.** `kimchi{Vesta,Pallas}_run_sound_algebraic_ft`
derive, from ONE genuine `KimchiVesta/Pallas.verify … = true` and the algebraic prover's
representations of the run's own 45 batch rows and 7 quotient chunks, the guarded
`∃ wTab, Satisfies idx (pubView idx pub) wTab` at the run's own sponge challenges — the
quotient residue dissolved. The deployed 45-row batch is reindexed onto the abstract 43-row
`batchC` (`runReindex` and its commitment/claim faithfulness lemmas), the openings seam
`kimchiProof_sound_of_openings` is fed directly, and the ft/Maller identity is derived from
the part-1 ft opening via `ft_identity_of_chunks` — no grid, no `poseidon_fiat_shamir`: the
Fiat–Shamir content is exactly `kimchi_fiat_shamir_{vesta,pallas}` at the observed
transcript. The four VK-parameter bridges (`homega`/`hzk`/`hshift`/`hendo`) remain genuine
hypotheses, since `VKCorresponds` pins only commitments.
-/

open Bulletproof

namespace Kimchi.Verifier

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization
  Kimchi.Protocol.Equation CompElliptic.Fields.Pasta

/-! ## The FS-reflection ft opening (the Fiat–Shamir discharge, part 1)

The Fiat–Shamir assumption re-anchored on the deployed verifier's OWN transcript:
`kimchi_fiat_shamir_{vesta,pallas}` state the transcript-tree extraction over the WARM
data of a reflected run — the warm-sponge finish `Ipa.verifyFrom … (runWarm …)
(runInput …)` that `kimchiVerify` itself executes (the `ReflectedRun.accepts` field of
`Kimchi/Verifier/Reflect.lean`) — rather than the cold `Ipa.verify` of
`poseidon_fiat_shamir_*`. On top of them, `ft_opening_of_reflected` (PROVED,
tree-as-hypothesis) derives the ft opening from a genuine acceptance: the constructed
ft commitment is slot 1 of the run's own accepted 45-row batch
(`ReflectedRun.comm_eq`), so `ipa_soundnessA` extracts the batch-opening witness and
the arity-generic `eval_pins_of_opening` pins slot `(1, 0)` — the ft row at the run's
own `ζ` — to the represented row: `runFtComm` opens to a vector whose evaluation at
`ζ` is exactly `runFtEval0`. The curve wrappers `ft_opening_of_reflected_{vesta,pallas}`
discharge the run by reflection (`kimchiVerify_reflects`) and the tree by the new
axioms, so a single `KimchiVesta.verify … = true` yields the ft opening. Scope
boundary: ONLY the ft opening — reconciling the reflected 45-row layout with the
43-row `batchC` (raw vs masked selectors) is a deferred follow-on. -/

/-- `getElem!` distributes over an append when the index lands in the left part —
the `getElem!` companion of `Array.getElem_append_left`, threading the three
`getElem!`-spelled batch-array reads below through `ReflectedRun`'s append-shaped
`comm_eq`/`evals_eq`. -/
private theorem getBang_append_left {α : Type*} [Inhabited α] (as bs : Array α)
    (i : ℕ) (h : i < as.size) : (as ++ bs)[i]! = as[i]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega),
    getElem!_pos as i h, Array.getElem_append_left h]

/-- **AXIOM (Fiat–Shamir, Poseidon instantiation over the deployed run, Vesta).** A run
accepted by the deployed warm-sponge finish (`Ipa.verifyFrom … (runWarm …) (runInput …)
= true`, the `ReflectedRun.accepts` field) admits a de-blinded accepting transcript
tree over the run's own 45-row batch. This is `poseidon_fiat_shamir_vesta` re-anchored
on the OBSERVED transcript — the reflected run's batched input `runInput` and post-`ζ`
warm sponge state `runWarm` — rather than the cold `Ipa.verify`: the same declared
assumption that the Poseidon sponge provides a valid Fiat–Shamir transform, stated at
the transcript the deployed kimchi verifier actually runs. -/
axiom kimchi_fiat_shamir_vesta (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (p : KimchiVesta.Proof) (pub : Array Fp) :
  FiatShamirTreeB σ
    (combinedCommitment (runInput IpaVesta.curve σ vk p pub).polyscale
      (runInput IpaVesta.curve σ vk p pub).commitmentFn)
    (combinedEvalVector (2 ^ σ.k) (runInput IpaVesta.curve σ vk p pub).evalscale
      (runInput IpaVesta.curve σ vk p pub).pointFn)
    (Ipa.cipOf (runInput IpaVesta.curve σ vk p pub))
    (Ipa.verifyFrom IpaVesta.curve σ (runWarm IpaVesta.curve σ vk p pub)
      (runInput IpaVesta.curve σ vk p pub) = true)

/-- **AXIOM (Fiat–Shamir, Poseidon instantiation over the deployed run, Pallas).** The
Pallas-side twin of `kimchi_fiat_shamir_vesta` — see its docstring for the trust
story. -/
axiom kimchi_fiat_shamir_pallas (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (p : KimchiPallas.Proof) (pub : Array Fq) :
  FiatShamirTreeB σ
    (combinedCommitment (runInput IpaPallas.curve σ vk p pub).polyscale
      (runInput IpaPallas.curve σ vk p pub).commitmentFn)
    (combinedEvalVector (2 ^ σ.k) (runInput IpaPallas.curve σ vk p pub).evalscale
      (runInput IpaPallas.curve σ vk p pub).pointFn)
    (Ipa.cipOf (runInput IpaPallas.curve σ vk p pub))
    (Ipa.verifyFrom IpaPallas.curve σ (runWarm IpaPallas.curve σ vk p pub)
      (runInput IpaPallas.curve σ vk p pub) = true)

/-- **The ft opening from a reflected run** (tree-as-hypothesis, PROVED — no axiom):
DL-binding, a reflected accepted run, SRS-basis representations `aRef`/`ρRef` of the
run's own 45 batch rows, the run's transcript tree (the `kimchi_fiat_shamir_*` shape,
here a hypothesis), and good combination challenges yield the ft opening — a
representation of the constructed ft commitment `runFtComm` whose evaluation at the
run's own `ζ` is the computed claim `runFtEval0`. Route: `ipa_soundnessA` extracts the
batch-opening witness from the run's acceptance (`ReflectedRun.accepts`);
`eval_pins_of_opening` (at the run's 45-row arity) pins every claimed evaluation to its
represented row; slot `(1, 0)` — the ft row (`comm_eq`/`evals_eq`) at the first batch
point `ζ` — reads off both facts. The FS-reflection bridge the curve
wrappers instantiate. -/
theorem ft_opening_of_reflected {C : Ipa.CommitmentCurve} [Module C.ScalarField C.Point]
    (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C) (pub : Array C.ScalarField)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → C.ScalarField) (wh : C.ScalarField),
      DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hrun : ReflectedRun C σ vk p pub)
    (aRef : Fin (runInput C σ vk p pub).commitments.size → Fin (2 ^ σ.k)
      → C.ScalarField)
    (ρRef : Fin (runInput C σ vk p pub).commitments.size → C.ScalarField)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i) = (runInput C σ vk p pub).commitmentFn i)
    (hFS : FiatShamirTreeB σ
      (combinedCommitment (runInput C σ vk p pub).polyscale
        (runInput C σ vk p pub).commitmentFn)
      (combinedEvalVector (2 ^ σ.k) (runInput C σ vk p pub).evalscale
        (runInput C σ vk p pub).pointFn)
      (Ipa.cipOf (runInput C σ vk p pub))
      (Ipa.verifyFrom C σ (runWarm C σ vk p pub) (runInput C σ vk p pub) = true))
    (hξ : (runInput C σ vk p pub).polyscale
      ∉ badXiOf σ aRef (runInput C σ vk p pub).pointFn (runInput C σ vk p pub).evalFn)
    (hr : (runInput C σ vk p pub).evalscale
      ∉ badROf σ aRef (runInput C σ vk p pub).pointFn (runInput C σ vk p pub).evalFn
          (runInput C σ vk p pub).polyscale) :
    ∃ (aft : Fin (2 ^ σ.k) → C.ScalarField) (ρft : C.ScalarField),
      commit σ aft ρft = runFtComm C σ vk p pub
        ∧ innerProduct aft (evalVector (2 ^ σ.k) (runOracles C σ vk p pub).zeta)
            = runFtEval0 C σ vk p pub := by
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _ hFS hrun.accepts
  have hpins := eval_pins_of_opening σ hbind (runInput C σ vk p pub).commitmentFn
    (runInput C σ vk p pub).pointFn aRef ρRef hrep (runInput C σ vk p pub).evalFn
    (runInput C σ vk p pub).polyscale (runInput C σ vk p pub).evalscale hξ hr a ρ hopen
  have hsize : (runInput C σ vk p pub).commitments.size = 45 := by
    rw [hrun.comm_eq]
    simp [Array.size_append, hrun.shape_wComm, hrun.shape_coeffsComm,
      hrun.shape_sigmaComm]
  have h1m : 1 < (runInput C σ vk p pub).commitments.size := by rw [hsize]; norm_num
  refine ⟨aRef ⟨1, h1m⟩, ρRef ⟨1, h1m⟩, ?_, ?_⟩
  · -- The commitment side: slot 1 of `comm_eq` is the constructed ft commitment.
    rw [hrep ⟨1, h1m⟩]
    show (runInput C σ vk p pub).commitments[(1 : ℕ)]'h1m = runFtComm C σ vk p pub
    simp only [hrun.comm_eq]
    rw [Array.getElem_append_left (by simp [Array.size_append]; omega),
      Array.getElem_append_left (by simp [Array.size_append]; omega),
      Array.getElem_append_left (by simp)]
    rfl
  · -- The value side: the eval pin at slot `(1, 0)` reads `evals_eq` at the point `ζ`.
    have hpt : (runInput C σ vk p pub).pointFn (0 : Fin 2)
        = (runOracles C σ vk p pub).zeta := rfl
    have hpin := hpins ⟨1, h1m⟩ (0 : Fin 2)
    rw [hpt] at hpin
    rw [← hpin]
    show ((runInput C σ vk p pub).evals[(1 : ℕ)]!)[(0 : ℕ)]!
      = runFtEval0 C σ vk p pub
    rw [hrun.evals_eq, getBang_append_left, getBang_append_left, getBang_append_left]
    · rfl
    · simp
    · simp [Array.size_append]
      omega
    · simp [Array.size_append]
      omega

/-- **The ft opening of the deployed Vesta kimchi verifier** (the Vesta FS-reflection
root): a genuine acceptance `KimchiVesta.verify … = true`, DL-binding, SRS-basis
representations of the run's own batch rows, and good combination challenges yield the
ft opening — `runFtComm` opens to a vector whose evaluation at the run's own `ζ` is
`runFtEval0`. The run is reflected trust-free (`kimchiVerify_reflects`); the transcript
tree is `kimchi_fiat_shamir_vesta` at the run's own warm data — the sole axiom
consumed. The Vesta FS-reflection root. -/
theorem ft_opening_of_reflected_vesta (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (p : KimchiVesta.Proof) (pub : Array Fp)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : KimchiVesta.verify σ vk p pub = true)
    (aRef : Fin (runInput IpaVesta.curve σ vk p pub).commitments.size
      → Fin (2 ^ σ.k) → Fp)
    (ρRef : Fin (runInput IpaVesta.curve σ vk p pub).commitments.size → Fp)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput IpaVesta.curve σ vk p pub).commitmentFn i)
    (hξ : (runInput IpaVesta.curve σ vk p pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaVesta.curve σ vk p pub).pointFn
          (runInput IpaVesta.curve σ vk p pub).evalFn)
    (hr : (runInput IpaVesta.curve σ vk p pub).evalscale
      ∉ badROf σ aRef (runInput IpaVesta.curve σ vk p pub).pointFn
          (runInput IpaVesta.curve σ vk p pub).evalFn
          (runInput IpaVesta.curve σ vk p pub).polyscale) :
    ∃ (aft : Fin (2 ^ σ.k) → Fp) (ρft : Fp),
      commit σ aft ρft = runFtComm IpaVesta.curve σ vk p pub
        ∧ innerProduct aft
            (evalVector (2 ^ σ.k) (runOracles IpaVesta.curve σ vk p pub).zeta)
            = runFtEval0 IpaVesta.curve σ vk p pub :=
  ft_opening_of_reflected σ vk p pub hbind
    (kimchiVerify_reflects IpaVesta.curve σ vk p pub hacc) aRef ρRef hrep
    (kimchi_fiat_shamir_vesta σ vk p pub) hξ hr

/-- **The ft opening of the deployed Pallas kimchi verifier.** The Pallas-side twin of
`ft_opening_of_reflected_vesta`, over `Fq`/`IpaPallas` — see the Vesta docstring for
the trust story. The Pallas FS-reflection root. -/
theorem ft_opening_of_reflected_pallas (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (p : KimchiPallas.Proof) (pub : Array Fq)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : KimchiPallas.verify σ vk p pub = true)
    (aRef : Fin (runInput IpaPallas.curve σ vk p pub).commitments.size
      → Fin (2 ^ σ.k) → Fq)
    (ρRef : Fin (runInput IpaPallas.curve σ vk p pub).commitments.size → Fq)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput IpaPallas.curve σ vk p pub).commitmentFn i)
    (hξ : (runInput IpaPallas.curve σ vk p pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaPallas.curve σ vk p pub).pointFn
          (runInput IpaPallas.curve σ vk p pub).evalFn)
    (hr : (runInput IpaPallas.curve σ vk p pub).evalscale
      ∉ badROf σ aRef (runInput IpaPallas.curve σ vk p pub).pointFn
          (runInput IpaPallas.curve σ vk p pub).evalFn
          (runInput IpaPallas.curve σ vk p pub).polyscale) :
    ∃ (aft : Fin (2 ^ σ.k) → Fq) (ρft : Fq),
      commit σ aft ρft = runFtComm IpaPallas.curve σ vk p pub
        ∧ innerProduct aft
            (evalVector (2 ^ σ.k) (runOracles IpaPallas.curve σ vk p pub).zeta)
            = runFtEval0 IpaPallas.curve σ vk p pub :=
  ft_opening_of_reflected σ vk p pub hbind
    (kimchiVerify_reflects IpaPallas.curve σ vk p pub hacc) aRef ρRef hrep
    (kimchi_fiat_shamir_pallas σ vk p pub) hξ hr

/-! ## The FS-reflection run-level roots (the Fiat–Shamir discharge, part 2)

The residue-free run-level roots: from a genuine `KimchiVesta/Pallas.verify … = true`,
the AGM path delivers `∃ wTab, Satisfies idx (pubView idx pub) wTab` with the
ft/quotient residue DISSOLVED — no `t`/`hteq` hypothesis, no extraction grid. The new
content over part 1 is pure reindexing and form matching: the deployed 45-row batch of
the reflected run carries the abstract 43-row `batchC` as a sub-batch (`runReindex` /
`batchC_eq_commitmentFn` / `claimedEvals_runReindex_eq`), the verifier's barycentric
public evaluation is the interpolant form (`runPubEvals_fst_eq`), and the constructed
ft commitment is exactly the Maller combination `ft_identity_of_chunks` consumes
(`runFtComm_eq_{vesta,pallas}`). The openings seam `kimchiProof_sound_of_openings` is
fed DIRECTLY: its reference side by the algebraic prover's representations reindexed
along `runReindex`, its consumer side by the eval pins of the run's single accepted
opening (`eval_pins_of_opening` at the 45-row arity) — no `FiatShamirTreeB` grid is
ever manufactured, and the only axioms consumed are the part-1
`kimchi_fiat_shamir_{vesta,pallas}`. The quotient is the genuine degree-`< 7n`
assembly `ftChunkAssembly σ.k aT` of the prover-supplied `tComm`-chunk
representations, and the ft/Maller identity is derived from the part-1 ft opening. -/

/-- The verifier's squaring ladder computes the power: `powPow2 x k = x ^ 2 ^ k`.
The bridge between the executable `runZetaN` and the abstract `ζ ^ n`
the soundness layer speaks. -/
private theorem powPow2_eq {F : Type*} [Field F] (x : F) (k : ℕ) :
    powPow2 x k = x ^ 2 ^ k := by
  induction k with
  | zero => simp [powPow2]
  | succ m ih =>
    have hstep : powPow2 x (m + 1) = powPow2 x m * powPow2 x m := by
      simp [powPow2, List.range_succ]
    rw [hstep, ih, ← pow_add]
    congr 1
    rw [pow_succ]
    omega

/-- The deployed→abstract batch-row reindex: where each abstract 43-row `batchC` row
sits inside the reflected run's 45-row batch (`ReflectedRun.comm_eq` layout: public at
`0`, ft at `1`, `z` at `2`, the six selectors at `3–8`, the witnesses at `9–23`, the
coefficients at `24–38`, the first six σ at `39–44`). Pure layout — no masking: the
selector rows are the raw key commitments on both sides. -/
private def runReindex (C : Ipa.CommitmentCurve) (σ : SRS C.Point) (vk : KimchiVK C)
    (p : KimchiProof C) (pub : Array C.ScalarField)
    (hsize : (runInput C σ vk p pub).commitments.size = 45) :
    Fin 43 → Fin (runInput C σ vk p pub).commitments.size := fun i =>
  if _h1 : (i : ℕ) < 15 then ⟨9 + (i : ℕ), by rw [hsize]; omega⟩
  else if _h2 : (i : ℕ) < 16 then ⟨2, by rw [hsize]; omega⟩
  else if _h3 : (i : ℕ) < 22 then ⟨23 + (i : ℕ), by rw [hsize]; omega⟩
  else if _h4 : (i : ℕ) < 37 then ⟨2 + (i : ℕ), by rw [hsize]; omega⟩
  else ⟨(i : ℕ) - 34, by rw [hsize]; omega⟩

/-- **The batch reindex is commitment-faithful**: row `i` of the abstract 43-row
assembly `batchC` — at the run's own witness view `p.wComm.getD · 0`, its accumulator
`p.zComm`, and the wire key's committed columns `vk.comms` — is the `runReindex i`-th
commitment of the reflected run's deployed 45-row batch. Pure layout reading of
`ReflectedRun.comm_eq`; no key correspondence is consumed. -/
private theorem batchC_eq_commitmentFn {C : Ipa.CommitmentCurve} (σ : SRS C.Point)
    (vk : KimchiVK C) (p : KimchiProof C) (pub : Array C.ScalarField)
    (hrun : ReflectedRun C σ vk p pub)
    (hsize : (runInput C σ vk p pub).commitments.size = 45) (i : Fin 43) :
    batchC (fun c => p.wComm.getD (c : ℕ) 0) p.zComm vk.comms i
      = (runInput C σ vk p pub).commitmentFn (runReindex C σ vk p pub hsize i) := by
  have hw := hrun.shape_wComm
  have hcf := hrun.shape_coeffsComm
  have hsg := hrun.shape_sigmaComm
  obtain ⟨iv, hlt⟩ := i
  simp only [batchC, runReindex, Ipa.Input.commitmentFn, Fin.getElem_fin]
  by_cases h1 : iv < 15
  · -- the witness rows: abstract `wRow c` ↦ deployed `9 + c`
    simp only [dif_pos h1, hrun.comm_eq]
    rw [Array.getElem_append_left (by
        simp only [Array.size_append, List.size_toArray, List.length_cons,
          List.length_nil, hw, hcf]
        omega),
      Array.getElem_append_left (by
        simp only [Array.size_append, List.size_toArray, List.length_cons,
          List.length_nil, hw]
        omega),
      Array.getElem_append_right (by
        simp only [List.size_toArray, List.length_cons, List.length_nil]
        omega)]
    simp [Array.getD, hw, h1]
  · by_cases h2 : iv < 16
    · -- the accumulator row: abstract `zRow` ↦ deployed `2`
      simp only [dif_neg h1, if_pos h2, dif_pos h2, hrun.comm_eq]
      rw [Array.getElem_append_left (by
          simp only [Array.size_append, List.size_toArray, List.length_cons,
            List.length_nil, hw, hcf]
          omega),
        Array.getElem_append_left (by
          simp only [Array.size_append, List.size_toArray, List.length_cons,
            List.length_nil, hw]
          omega),
        Array.getElem_append_left (by
          simp only [List.size_toArray, List.length_cons, List.length_nil]
          omega)]
      rfl
    · by_cases h3 : iv < 22
      · -- the σ rows: abstract `sRow i` ↦ deployed `39 + i` (the `extract 0 6` tail)
        simp only [dif_neg h1, if_neg h2, dif_neg h2, dif_pos h3, hrun.comm_eq]
        rw [Array.getElem_append_right (by
            simp only [Array.size_append, List.size_toArray, List.length_cons,
              List.length_nil, hw, hcf]
            omega),
          Array.getElem_extract]
        simp only [KimchiVK.comms]
        simp [Array.getD, hw, hcf, show iv - 16 < vk.sigmaComm.size by omega]
        exact getElem_congr_idx (by omega)
      · by_cases h4 : iv < 37
        · -- the coefficient rows: abstract `cRow c` ↦ deployed `24 + c`
          simp only [dif_neg h1, if_neg h2, dif_neg h2, dif_neg h3, dif_pos h4,
            hrun.comm_eq]
          rw [Array.getElem_append_left (by
              simp only [Array.size_append, List.size_toArray, List.length_cons,
                List.length_nil, hw, hcf]
              omega),
            Array.getElem_append_right (by
              simp only [Array.size_append, List.size_toArray, List.length_cons,
                List.length_nil, hw]
              omega)]
          simp only [KimchiVK.comms]
          simp [Array.getD, hw, show iv - 22 < vk.coefficientsComm.size by omega]
          exact getElem_congr_idx (by omega)
        · -- the selector rows: abstract `selRow j` ↦ deployed `3 + j` (raw, no mask)
          simp only [dif_neg h1, if_neg h2, dif_neg h2, dif_neg h3, dif_neg h4,
            hrun.comm_eq]
          rw [Array.getElem_append_left (by
              simp only [Array.size_append, List.size_toArray, List.length_cons,
                List.length_nil, hw, hcf]
              omega),
            Array.getElem_append_left (by
              simp only [Array.size_append, List.size_toArray, List.length_cons,
                List.length_nil, hw]
              omega),
            Array.getElem_append_left (by
              simp only [List.size_toArray, List.length_cons, List.length_nil]
              omega)]
          have h37 : 37 ≤ iv := Nat.not_lt.mp h4
          interval_cases iv <;> rfl

/-- **The constructed ft commitment is the Maller combination** (Vesta): the reflected
run's `runFtComm` — the executable `f_comm − (ζⁿ − 1).val • combine(ζⁿ, t_comm)` — is
the abstract `•`-combination `pScalar • σ₆C − (ζⁿ − 1) • ∑ⱼ (ζⁿ)ʲ • tCommⱼ` that
`ft_identity_of_chunks` consumes. Stated per curve: the `.val`-collapse
`Pasta.vesta_smul_val` is `rfl` only at `Fp`. -/
private theorem runFtComm_eq_vesta (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (p : KimchiVesta.Proof) (pub : Array Fp)
    (hrun : ReflectedRun IpaVesta.curve σ vk p pub) {n : ℕ} (hn : vk.n = n) :
    runFtComm IpaVesta.curve σ vk p pub
      = runPScalar IpaVesta.curve σ vk p pub • vk.sigmaComm.getD 6 0
        - ((runOracles IpaVesta.curve σ vk p pub).zeta ^ n - 1)
            • ∑ j : Fin 7,
                ((runOracles IpaVesta.curve σ vk p pub).zeta ^ n) ^ (j : ℕ)
                  • p.tComm.getD (j : ℕ) 0 := by
  have hζN : runZetaN IpaVesta.curve σ vk p pub
      = (runOracles IpaVesta.curve σ vk p pub).zeta ^ n := by
    unfold runZetaN
    rw [powPow2_eq, ← hn]
    rfl
  unfold runFtComm runFComm
  rw [← Pasta.vesta_smul_val, ← Pasta.vesta_smul_val,
    combineCommitments_eq Pasta.vesta_smul_val, hζN]
  congr 1
  congr 1
  rw [combinedCommitment]
  refine Fintype.sum_equiv (finCongr hrun.shape_tComm) _ _ fun j => ?_
  simp only [finCongr_apply, Fin.val_cast]
  congr 1
  simp [Array.getD, j.isLt]

/-- **The constructed ft commitment is the Maller combination** (Pallas): the
Pallas-side twin of `runFtComm_eq_vesta`, over `Fq`/`IpaPallas`. -/
private theorem runFtComm_eq_pallas (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (p : KimchiPallas.Proof) (pub : Array Fq)
    (hrun : ReflectedRun IpaPallas.curve σ vk p pub) {n : ℕ} (hn : vk.n = n) :
    runFtComm IpaPallas.curve σ vk p pub
      = runPScalar IpaPallas.curve σ vk p pub • vk.sigmaComm.getD 6 0
        - ((runOracles IpaPallas.curve σ vk p pub).zeta ^ n - 1)
            • ∑ j : Fin 7,
                ((runOracles IpaPallas.curve σ vk p pub).zeta ^ n) ^ (j : ℕ)
                  • p.tComm.getD (j : ℕ) 0 := by
  have hζN : runZetaN IpaPallas.curve σ vk p pub
      = (runOracles IpaPallas.curve σ vk p pub).zeta ^ n := by
    unfold runZetaN
    rw [powPow2_eq, ← hn]
    rfl
  unfold runFtComm runFComm
  rw [← Pasta.pallas_smul_val, ← Pasta.pallas_smul_val,
    combineCommitments_eq Pasta.pallas_smul_val, hζN]
  congr 1
  congr 1
  rw [combinedCommitment]
  refine Fintype.sum_equiv (finCongr hrun.shape_tComm) _ _ fun j => ?_
  simp only [finCongr_apply, Fin.val_cast]
  congr 1
  simp [Array.getD, j.isLt]

/-- Generalized running-power fold for `pubDot`: from accumulator `acc` and running
power `pw`, the fold's first component adds the `pw·ωⁱ`-indexed barycentric summands.
The engine behind `pubDot_eq_sum`, mirroring `combineFoldl_aux`
(`Kimchi/Verifier/Reflection.lean`). -/
private theorem pubDotFoldl_aux {F : Type*} [Field F] (ω pt : F) (l : List F)
    (acc pw : F) :
    (l.foldl (fun (a : F × F) pi => (a.1 + -(pt - a.2)⁻¹ * pi * a.2, a.2 * ω))
        (acc, pw)).1
      = acc + ∑ i : Fin l.length,
          -(pt - pw * ω ^ (i : ℕ))⁻¹ * l[i] * (pw * ω ^ (i : ℕ)) := by
  induction l generalizing acc pw with
  | nil => simp
  | cons x t ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
      Fin.val_succ, Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [← add_assoc]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show pw * ω * ω ^ (i : ℕ) = pw * ω ^ ((i : ℕ) + 1) from by rw [pow_succ]; ring]

/-- The verifier's `pubDot` fold is the barycentric sum
`∑ᵢ −(pt − ωⁱ)⁻¹ · pubᵢ · ωⁱ`. The fold→sum bridge for
`runPubEvals_fst_eq`. -/
private theorem pubDot_eq_sum {F : Type*} [Field F] (ω pt : F) (pub : Array F) :
    pubDot ω pt pub
      = ∑ i : Fin pub.size, -(pt - ω ^ (i : ℕ))⁻¹ * pub[i] * ω ^ (i : ℕ) := by
  rw [pubDot, ← Array.foldl_toList, pubDotFoldl_aux]
  simp only [one_mul, zero_add]
  refine Fintype.sum_equiv (finCongr pub.length_toList) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.getElem_fin, Fin.val_cast, Array.getElem_toList]

/-- **The run's first public evaluation is the interpolant form**: at a run-`ζ` off the
domain (`ζⁿ ≠ 1`), the verifier's barycentric first `publicEvals` component equals
`−(idx.pubPoly (pubView idx pub)).eval ζ` — exactly the public value
`kimchiProof_sound_of_openings`' ft equation consumes. Via `pubDot_eq_sum` and
`barycentricPubEval_eq`; the VK-parameter bridges `homega`/`hn`/`hpub` align the wire
parameters with the Index's. -/
private theorem runPubEvals_fst_eq {C : Ipa.CommitmentCurve} (σ : SRS C.Point)
    (vk : KimchiVK C) (p : KimchiProof C) (pub : Array C.ScalarField)
    {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (homega : vk.omega = idx.omega) (hn : vk.n = n)
    (hpub : pub.size = idx.publicCount)
    (hζn : (runOracles C σ vk p pub).zeta ^ n ≠ 1) :
    (runPubEvals C σ vk p pub).1
      = -((idx.pubPoly (pubView idx pub)).eval (runOracles C σ vk p pub).zeta) := by
  rw [← barycentricPubEval_eq idx (pubView idx pub) hζn]
  have hζN : runZetaN C σ vk p pub = (runOracles C σ vk p pub).zeta ^ n := by
    unfold runZetaN
    rw [powPow2_eq, ← hn]
    rfl
  by_cases h0 : pub.size = 0
  · have hc : idx.publicCount = 0 := by omega
    haveI : IsEmpty (Fin idx.publicCount) := by
      rw [hc]
      infer_instance
    unfold runPubEvals publicEvals barycentricPubEval
    rw [if_pos h0, Finset.univ_eq_empty, Finset.sum_empty, zero_mul, zero_mul]
  · unfold runPubEvals publicEvals barycentricPubEval
    rw [if_neg h0]
    show pubDot vk.omega (runOracles C σ vk p pub).zeta pub
        * (runZetaN C σ vk p pub - 1) * ((vk.n : C.ScalarField))⁻¹ = _
    rw [hζN, hn, pubDot_eq_sum, homega]
    congr 2
    refine Fintype.sum_equiv (finCongr hpub) _ _ fun i => ?_
    simp only [finCongr_apply, Fin.val_cast]
    congr 2
    show pub[(i : ℕ)] = pub.getD (i : ℕ) 0
    simp [Array.getD, i.isLt]

/-- `getElem!` distributes over an append when the index lands in the right part — the
right-hand companion of `getBang_append_left`. -/
private theorem getBang_append_right {α : Type*} [Inhabited α] (as bs : Array α)
    (i : ℕ) (h1 : as.size ≤ i) (h2 : i - as.size < bs.size) :
    (as ++ bs)[i]! = bs[i - as.size]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega),
    getElem!_pos bs (i - as.size) h2, Array.getElem_append_right h1]

/-- Extensionality for the linearization's evaluation record — the (private, frozen)
`evalsExt` of `KimchiSound.lean`, inlined project-locally for the run-level record
matching. -/
private theorem evals_ext {F : Type*} {e e' : Evals F} (h1 : e.w = e'.w)
    (h2 : e.wOmega = e'.wOmega) (h3 : e.z = e'.z) (h4 : e.zOmega = e'.zOmega)
    (h5 : e.s = e'.s) (h6 : e.coeffs = e'.coeffs)
    (h7 : e.genericSelector = e'.genericSelector)
    (h8 : e.poseidonSelector = e'.poseidonSelector)
    (h9 : e.completeAddSelector = e'.completeAddSelector)
    (h10 : e.mulSelector = e'.mulSelector) (h11 : e.emulSelector = e'.emulSelector)
    (h12 : e.endoScalarSelector = e'.endoScalarSelector) : e = e' := by
  cases e
  cases e'
  simp only [Evals.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- `runReindex` at a witness row: deployed slot `9 + c`. -/
private theorem runReindex_val_wRow {C : Ipa.CommitmentCurve} (σ : SRS C.Point)
    (vk : KimchiVK C) (p : KimchiProof C) (pub : Array C.ScalarField)
    (hsize : (runInput C σ vk p pub).commitments.size = 45) (c : Fin 15) :
    ((runReindex C σ vk p pub hsize (wRow c)) : ℕ) = 9 + (c : ℕ) := by
  simp only [runReindex, wRow]
  rw [dif_pos c.isLt]

/-- `runReindex` at the accumulator row: deployed slot `2`. -/
private theorem runReindex_val_zRow {C : Ipa.CommitmentCurve} (σ : SRS C.Point)
    (vk : KimchiVK C) (p : KimchiProof C) (pub : Array C.ScalarField)
    (hsize : (runInput C σ vk p pub).commitments.size = 45) :
    ((runReindex C σ vk p pub hsize zRow) : ℕ) = 2 := by
  simp only [runReindex, zRow]
  rw [dif_neg (by omega), dif_pos (by omega)]

/-- `runReindex` at a σ row: deployed slot `39 + i` (the `extract 0 6` tail). -/
private theorem runReindex_val_sRow {C : Ipa.CommitmentCurve} (σ : SRS C.Point)
    (vk : KimchiVK C) (p : KimchiProof C) (pub : Array C.ScalarField)
    (hsize : (runInput C σ vk p pub).commitments.size = 45) (i : Fin 6) :
    ((runReindex C σ vk p pub hsize (sRow i)) : ℕ) = 39 + (i : ℕ) := by
  simp only [runReindex, sRow]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  show 23 + (16 + (i : ℕ)) = 39 + (i : ℕ)
  omega

/-- `runReindex` at a coefficient row: deployed slot `24 + c`. -/
private theorem runReindex_val_cRow {C : Ipa.CommitmentCurve} (σ : SRS C.Point)
    (vk : KimchiVK C) (p : KimchiProof C) (pub : Array C.ScalarField)
    (hsize : (runInput C σ vk p pub).commitments.size = 45) (c : Fin 15) :
    ((runReindex C σ vk p pub hsize (cRow c)) : ℕ) = 24 + (c : ℕ) := by
  simp only [runReindex, cRow]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  show 2 + (22 + (c : ℕ)) = 24 + (c : ℕ)
  omega

/-- `runReindex` at a selector row: deployed slot `3 + j`. -/
private theorem runReindex_val_selRow {C : Ipa.CommitmentCurve} (σ : SRS C.Point)
    (vk : KimchiVK C) (p : KimchiProof C) (pub : Array C.ScalarField)
    (hsize : (runInput C σ vk p pub).commitments.size = 45) (j : Fin 6) :
    ((runReindex C σ vk p pub hsize (selRow j)) : ℕ) = 3 + (j : ℕ) := by
  simp only [runReindex, selRow]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
  show 37 + (j : ℕ) - 34 = 3 + (j : ℕ)
  omega

/-- Reading a literal row (`0–8`: public, ft, `z`, the six selectors) of the reflected
run's evaluation matrix. -/
private theorem runEvals_read_lit {C : Ipa.CommitmentCurve} {σ : SRS C.Point}
    {vk : KimchiVK C} {p : KimchiProof C} {pub : Array C.ScalarField}
    (hrun : ReflectedRun C σ vk p pub) (k : ℕ) (hk : k < 9) :
    (runInput C σ vk p pub).evals[k]!
      = #[#[(runPubEvals C σ vk p pub).1, (runPubEvals C σ vk p pub).2],
          #[runFtEval0 C σ vk p pub, p.ftEval1],
          #[p.evals.z.zeta, p.evals.z.zetaOmega],
          #[p.evals.genericSelector.zeta, p.evals.genericSelector.zetaOmega],
          #[p.evals.poseidonSelector.zeta, p.evals.poseidonSelector.zetaOmega],
          #[p.evals.completeAddSelector.zeta, p.evals.completeAddSelector.zetaOmega],
          #[p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega],
          #[p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega],
          #[p.evals.endomulScalarSelector.zeta, p.evals.endomulScalarSelector.zetaOmega]][k]! := by
  rw [hrun.evals_eq,
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, Array.size_map, List.size_toArray,
        List.length_cons, List.length_nil, hrun.shape_w, hrun.shape_coeffs]
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, Array.size_map, List.size_toArray,
        List.length_cons, List.length_nil, hrun.shape_w]
      omega),
    getBang_append_left _ _ _ (by
      simp only [List.size_toArray, List.length_cons, List.length_nil]
      omega)]

/-- Reading a witness row (`9 + c`) of the reflected run's evaluation matrix: the
proof's own witness evaluation pair. -/
private theorem runEvals_read_w {C : Ipa.CommitmentCurve} {σ : SRS C.Point}
    {vk : KimchiVK C} {p : KimchiProof C} {pub : Array C.ScalarField}
    (hrun : ReflectedRun C σ vk p pub) (c : ℕ) (hc : c < 15) :
    (runInput C σ vk p pub).evals[9 + c]!
      = #[(p.evals.w[c]!).zeta, (p.evals.w[c]!).zetaOmega] := by
  have hw := hrun.shape_w
  rw [hrun.evals_eq,
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, Array.size_map, List.size_toArray,
        List.length_cons, List.length_nil, hw, hrun.shape_coeffs]
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, Array.size_map, List.size_toArray,
        List.length_cons, List.length_nil, hw]
      omega),
    getBang_append_right _ _ _ (by
      simp only [List.size_toArray, List.length_cons, List.length_nil]
      omega) (by
      simp only [Array.size_map, List.size_toArray, List.length_cons,
        List.length_nil, hw]
      omega)]
  simp only [List.size_toArray, List.length_cons, List.length_nil,
    Nat.add_sub_cancel_left]
  rw [getElem!_pos (p.evals.w.map fun e => #[e.zeta, e.zetaOmega]) c (by
      simp only [Array.size_map, hw]
      omega),
    Array.getElem_map, getElem!_pos p.evals.w c (by omega)]

/-- Reading a coefficient row (`24 + c`) of the reflected run's evaluation matrix. -/
private theorem runEvals_read_c {C : Ipa.CommitmentCurve} {σ : SRS C.Point}
    {vk : KimchiVK C} {p : KimchiProof C} {pub : Array C.ScalarField}
    (hrun : ReflectedRun C σ vk p pub) (c : ℕ) (hc : c < 15) :
    (runInput C σ vk p pub).evals[24 + c]!
      = #[(p.evals.coefficients[c]!).zeta, (p.evals.coefficients[c]!).zetaOmega] := by
  have hw := hrun.shape_w
  have hcf := hrun.shape_coeffs
  rw [hrun.evals_eq,
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, Array.size_map, List.size_toArray,
        List.length_cons, List.length_nil, hw, hcf]
      omega),
    getBang_append_right _ _ _ (by
      simp only [Array.size_append, Array.size_map, List.size_toArray,
        List.length_cons, List.length_nil, hw]
      omega) (by
      simp only [Array.size_append, Array.size_map, List.size_toArray,
        List.length_cons, List.length_nil, hw, hcf]
      omega)]
  simp only [Array.size_append, Array.size_map, List.size_toArray, List.length_cons,
    List.length_nil, hw, Nat.add_sub_cancel_left]
  rw [getElem!_pos (p.evals.coefficients.map fun e => #[e.zeta, e.zetaOmega]) c (by
      simp only [Array.size_map, hcf]
      omega),
    Array.getElem_map, getElem!_pos p.evals.coefficients c (by omega)]

/-- Reading a σ row (`39 + i`) of the reflected run's evaluation matrix. -/
private theorem runEvals_read_s {C : Ipa.CommitmentCurve} {σ : SRS C.Point}
    {vk : KimchiVK C} {p : KimchiProof C} {pub : Array C.ScalarField}
    (hrun : ReflectedRun C σ vk p pub) (i : ℕ) (hi : i < 6) :
    (runInput C σ vk p pub).evals[39 + i]!
      = #[(p.evals.s[i]!).zeta, (p.evals.s[i]!).zetaOmega] := by
  have hw := hrun.shape_w
  have hcf := hrun.shape_coeffs
  have hs := hrun.shape_s
  rw [hrun.evals_eq,
    getBang_append_right _ _ _ (by
      simp only [Array.size_append, Array.size_map, List.size_toArray,
        List.length_cons, List.length_nil, hw, hcf]
      omega) (by
      simp only [Array.size_append, Array.size_map, List.size_toArray,
        List.length_cons, List.length_nil, hw, hcf, hs]
      omega)]
  simp only [Array.size_append, Array.size_map, List.size_toArray, List.length_cons,
    List.length_nil, hw, hcf, Nat.add_sub_cancel_left]
  rw [getElem!_pos (p.evals.s.map fun e => #[e.zeta, e.zetaOmega]) i (by
      simp only [Array.size_map, hs]
      omega),
    Array.getElem_map, getElem!_pos p.evals.s i (by omega)]

/-- **The batch reindex is claim-faithful** (the record matching): the abstract
claimed-evaluations record read off the reflected run's deployed batch through
`runReindex` IS the proof's own evaluation record `p.linEvals` — field by field, the
deployed rows carry exactly the wire evaluation pairs the scalar side consumes. Pure
layout reading of `ReflectedRun.evals_eq`. -/
private theorem claimedEvals_runReindex_eq {C : Ipa.CommitmentCurve} (σ : SRS C.Point)
    (vk : KimchiVK C) (p : KimchiProof C) (pub : Array C.ScalarField)
    (hrun : ReflectedRun C σ vk p pub)
    (hsize : (runInput C σ vk p pub).commitments.size = 45) :
    claimedEvals (fun (i : Fin 43) (j : Fin 2) =>
        (runInput C σ vk p pub).evalFn (runReindex C σ vk p pub hsize i) j)
      = p.linEvals := by
  refine evals_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · funext c
    simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_wRow, runEvals_read_w hrun (c : ℕ) c.isLt]
    rfl
  · funext c
    simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_wRow, runEvals_read_w hrun (c : ℕ) c.isLt]
    rfl
  · simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_zRow, runEvals_read_lit hrun 2 (by omega)]
    rfl
  · simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_zRow, runEvals_read_lit hrun 2 (by omega)]
    rfl
  · funext i
    simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_sRow, runEvals_read_s hrun (i : ℕ) i.isLt]
    rfl
  · funext c
    simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_cRow, runEvals_read_c hrun (c : ℕ) c.isLt]
    rfl
  · simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_selRow]
    show ((runInput C σ vk p pub).evals[(3 : ℕ)]!)[(0 : ℕ)]! = p.evals.genericSelector.zeta
    rw [runEvals_read_lit hrun 3 (by omega)]
    rfl
  · simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_selRow]
    show ((runInput C σ vk p pub).evals[(4 : ℕ)]!)[(0 : ℕ)]! = p.evals.poseidonSelector.zeta
    rw [runEvals_read_lit hrun 4 (by omega)]
    rfl
  · simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_selRow]
    show ((runInput C σ vk p pub).evals[(5 : ℕ)]!)[(0 : ℕ)]!
      = p.evals.completeAddSelector.zeta
    rw [runEvals_read_lit hrun 5 (by omega)]
    rfl
  · simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_selRow]
    show ((runInput C σ vk p pub).evals[(6 : ℕ)]!)[(0 : ℕ)]! = p.evals.mulSelector.zeta
    rw [runEvals_read_lit hrun 6 (by omega)]
    rfl
  · simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_selRow]
    show ((runInput C σ vk p pub).evals[(7 : ℕ)]!)[(0 : ℕ)]! = p.evals.emulSelector.zeta
    rw [runEvals_read_lit hrun 7 (by omega)]
    rfl
  · simp only [claimedEvals, KimchiProof.linEvals, Ipa.Input.evalFn]
    rw [runReindex_val_selRow]
    show ((runInput C σ vk p pub).evals[(8 : ℕ)]!)[(0 : ℕ)]!
      = p.evals.endomulScalarSelector.zeta
    rw [runEvals_read_lit hrun 8 (by omega)]
    rfl

/-- **The run-level residue-free root (Vesta)**: from a genuine deployed acceptance
`KimchiVesta.verify σ vk p pub = true`, the AGM path delivers
`∃ wTab, Satisfies idx (pubView idx pub) wTab` — with the ft/quotient residue
DISSOLVED (no `t`/`hteq` hypothesis) and NO extraction grid. The algebraic prover
supplies SRS-basis representations of the run's own 45 batch rows (`aRef`/`ρRef`) and
of the 7 `tComm` chunks (`aT`/`ρT`); everything else is derived from the single
reflected run: the openings seam `kimchiProof_sound_of_openings` is fed directly
(reference side: the representations reindexed along `runReindex`; consumer side: the
eval pins of the run's one accepted opening), and the quotient
`t := ftChunkAssembly σ.k aT` with its Maller identity comes from the part-1 ft
opening through `ft_identity_of_chunks`. The four VK-parameter bridges
`homega`/`hzk`/`hshift`/`hendo` are genuine hypotheses (`VKCorresponds` pins only
commitments). Axioms consumed: `kimchi_fiat_shamir_vesta` (the Fiat–Shamir assumption
at the run's own transcript) plus the point-count-backed `Module` instance — no
`poseidon_fiat_shamir`, no grid. Bad-set bounds verbatim `of_openings`'; the
conclusion is guarded by the run challenges avoiding them, the two `ζ` degeneracies,
and the ft non-degeneracy `ζ ^ n ≠ 1`. The Vesta run-level
residue-free root. -/
theorem kimchiVesta_run_sound_algebraic_ft (σ : SRS IpaVesta.Point)
    (vk : KimchiVesta.VK) (p : KimchiVesta.Proof) (pub : Array Fp)
    {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : KimchiVesta.verify σ vk p pub = true)
    (homega : vk.omega = idx.omega) (hzk : vk.zkRows = idx.zkRows)
    (hshift : (fun i : Fin 7 => vk.shifts[(i : ℕ)]!) = idx.shifts)
    (hendo : vk.endo = idx.endoBase)
    (aRef : Fin (runInput IpaVesta.curve σ vk p pub).commitments.size
      → Fin (2 ^ σ.k) → Fp)
    (ρRef : Fin (runInput IpaVesta.curve σ vk p pub).commitments.size → Fp)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput IpaVesta.curve σ vk p pub).commitmentFn i)
    (aT : Fin 7 → Fin (2 ^ σ.k) → Fp) (ρT : Fin 7 → Fp)
    (hTC : ∀ j : Fin 7, commit σ (aT j) (ρT j) = p.tComm.getD (j : ℕ) 0)
    (hξ : (runInput IpaVesta.curve σ vk p pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaVesta.curve σ vk p pub).pointFn
          (runInput IpaVesta.curve σ vk p pub).evalFn)
    (hr : (runInput IpaVesta.curve σ vk p pub).evalscale
      ∉ badROf σ aRef (runInput IpaVesta.curve σ vk p pub).pointFn
          (runInput IpaVesta.curve σ vk p pub).evalFn
          (runInput IpaVesta.curve σ vk p pub).polyscale) :
    ∃ (badB : Finset Fp) (badG : Fp → Finset Fp) (badA : Fp → Fp → Finset Fp)
        (badZ : Fp → Fp → Fp → Polynomial Fp → Finset Fp),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fp), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ((runOracles IpaVesta.curve σ vk p pub).beta ∉ badB →
          (runOracles IpaVesta.curve σ vk p pub).gamma
            ∉ badG (runOracles IpaVesta.curve σ vk p pub).beta →
          (runOracles IpaVesta.curve σ vk p pub).alpha
            ∉ badA (runOracles IpaVesta.curve σ vk p pub).beta
                (runOracles IpaVesta.curve σ vk p pub).gamma →
          (runOracles IpaVesta.curve σ vk p pub).zeta
            ∉ badZ (runOracles IpaVesta.curve σ vk p pub).beta
                (runOracles IpaVesta.curve σ vk p pub).gamma
                (runOracles IpaVesta.curve σ vk p pub).alpha
                (ftChunkAssembly σ.k aT) →
          (runOracles IpaVesta.curve σ vk p pub).zeta ≠ 1 →
          (runOracles IpaVesta.curve σ vk p pub).zeta
            ≠ idx.omega ^ (n - idx.zkRows) →
          (runOracles IpaVesta.curve σ vk p pub).zeta ^ n ≠ 1 →
          ∃ wTab : Fin n → Fin 15 → Fp, Satisfies idx (pubView idx pub) wTab) := by
  -- (1) reflect the run; pin the batch width and the domain size
  have hrun := kimchiVerify_reflects IpaVesta.curve σ vk p pub hacc
  have hsize : (runInput IpaVesta.curve σ vk p pub).commitments.size = 45 := by
    rw [hrun.comm_eq]
    simp [Array.size_append, hrun.shape_wComm, hrun.shape_coeffsComm,
      hrun.shape_sigmaComm]
  have hn : vk.n = n := hrun.shape_srs.symm.trans hk
  -- (2) the reference openings, reindexed onto the abstract 43-row batch
  have hbound₀ : ∀ i : Fin 43,
      commit σ (aRef (runReindex IpaVesta.curve σ vk p pub hsize i))
          (ρRef (runReindex IpaVesta.curve σ vk p pub hsize i))
        = batchC (fun c => p.wComm.getD (c : ℕ) 0) p.zComm vk.comms i :=
    fun i => (hrep (runReindex IpaVesta.curve σ vk p pub hsize i)).trans
      (batchC_eq_commitmentFn σ vk p pub hrun hsize i).symm
  -- (3) the openings seam, fed directly
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hk hbind vk.comms hvk (pubView idx pub)
      (fun c => p.wComm.getD (c : ℕ) 0) p.zComm
      (fun i => aRef (runReindex IpaVesta.curve σ vk p pub hsize i))
      (fun i => ρRef (runReindex IpaVesta.curve σ vk p pub hsize i)) hbound₀
  refine ⟨badB, badG, badA, badZ, hbounds, ?_⟩
  intro hβ hγ hα hζ hζ1 hζb hζn
  -- (4) the eval pins from the run's single accepted opening (45-row arity)
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _
    (kimchi_fiat_shamir_vesta σ vk p pub) hrun.accepts
  have hpins := eval_pins_of_opening σ hbind
    (runInput IpaVesta.curve σ vk p pub).commitmentFn
    (runInput IpaVesta.curve σ vk p pub).pointFn aRef ρRef hrep
    (runInput IpaVesta.curve σ vk p pub).evalFn
    (runInput IpaVesta.curve σ vk p pub).polyscale
    (runInput IpaVesta.curve σ vk p pub).evalscale hξ hr a ρ hopen
  -- (5) the part-1 ft opening
  obtain ⟨aft, ρft, hcomm_ft, heval_ft⟩ :=
    ft_opening_of_reflected_vesta σ vk p pub hbind hacc aRef ρRef hrep hξ hr
  -- (6) the ft/Maller identity from the chunk representations
  have hCσ6 : vk.sigmaComm.getD 6 0 = commitPoly σ (idx.sigmaPoly 6) :=
    congrArg (fun cm => cm.sigma 6) hvk
  have hσ₆ : (idx.sigmaPoly 6).natDegree < 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hcommit : commit σ aft ρft
      = runPScalar IpaVesta.curve σ vk p pub • vk.sigmaComm.getD 6 0
        - ((runOracles IpaVesta.curve σ vk p pub).zeta ^ n - 1)
            • ∑ j : Fin 7,
                ((runOracles IpaVesta.curve σ vk p pub).zeta ^ n) ^ (j : ℕ)
                  • p.tComm.getD (j : ℕ) 0 :=
    hcomm_ft.trans (runFtComm_eq_vesta σ vk p pub hrun hn)
  obtain ⟨htdeg, hteq0⟩ := ft_identity_of_chunks σ hbind (idx.sigmaPoly 6) hσ₆
    (vk.sigmaComm.getD 6 0) hCσ6 (fun j => p.tComm.getD (j : ℕ) 0) aT ρT hTC
    (runPScalar IpaVesta.curve σ vk p pub)
    (runOracles IpaVesta.curve σ vk p pub).zeta
    (runFtEval0 IpaVesta.curve σ vk p pub) n hk aft ρft hcommit heval_ft
  -- (7) reconcile the derived identity into the consumer's shape
  have hce := claimedEvals_runReindex_eq σ vk p pub hrun hsize
  unfold runPScalar runFtEval0 runFtEval0P at hteq0
  rw [runPubEvals_fst_eq σ vk p pub idx homega hn hpub hζn, hn, hzk, homega, hendo,
    hshift, ← hce] at hteq0
  -- (8) the per-row pins, at the consumer's two eval points
  have hpt : (runInput IpaVesta.curve σ vk p pub).pointFn
      = ![(runOracles IpaVesta.curve σ vk p pub).zeta,
          idx.omega * (runOracles IpaVesta.curve σ vk p pub).zeta] := by
    funext j
    fin_cases j
    · rfl
    · show (runOracles IpaVesta.curve σ vk p pub).zeta * vk.omega = _
      rw [homega]
      exact mul_comm _ _
  rw [hpt] at hpins
  -- (9) feed the consumer
  exact himp (runOracles IpaVesta.curve σ vk p pub).beta
    (runOracles IpaVesta.curve σ vk p pub).gamma
    (runOracles IpaVesta.curve σ vk p pub).alpha
    (ftChunkAssembly σ.k aT)
    (runOracles IpaVesta.curve σ vk p pub).zeta
    (fun i j => (runInput IpaVesta.curve σ vk p pub).evalFn
      (runReindex IpaVesta.curve σ vk p pub hsize i) j)
    (fun i => aRef (runReindex IpaVesta.curve σ vk p pub hsize i))
    (fun i => ρRef (runReindex IpaVesta.curve σ vk p pub hsize i))
    hβ hγ hα hζ hζ1 hζb htdeg
    (fun i => ⟨hbound₀ i,
      fun j => hpins (runReindex IpaVesta.curve σ vk p pub hsize i) j⟩)
    hteq0

/-- **The run-level residue-free root (Pallas).** The Pallas-side twin of
`kimchiVesta_run_sound_algebraic_ft`, over `Fq`/`IpaPallas`, its Fiat–Shamir
assumption `kimchi_fiat_shamir_pallas` at the run's own transcript — see the Vesta
docstring for the full trust accounting. The Pallas run-level
residue-free root. -/
theorem kimchiPallas_run_sound_algebraic_ft (σ : SRS IpaPallas.Point)
    (vk : KimchiPallas.VK) (p : KimchiPallas.Proof) (pub : Array Fq)
    {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : KimchiPallas.verify σ vk p pub = true)
    (homega : vk.omega = idx.omega) (hzk : vk.zkRows = idx.zkRows)
    (hshift : (fun i : Fin 7 => vk.shifts[(i : ℕ)]!) = idx.shifts)
    (hendo : vk.endo = idx.endoBase)
    (aRef : Fin (runInput IpaPallas.curve σ vk p pub).commitments.size
      → Fin (2 ^ σ.k) → Fq)
    (ρRef : Fin (runInput IpaPallas.curve σ vk p pub).commitments.size → Fq)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput IpaPallas.curve σ vk p pub).commitmentFn i)
    (aT : Fin 7 → Fin (2 ^ σ.k) → Fq) (ρT : Fin 7 → Fq)
    (hTC : ∀ j : Fin 7, commit σ (aT j) (ρT j) = p.tComm.getD (j : ℕ) 0)
    (hξ : (runInput IpaPallas.curve σ vk p pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaPallas.curve σ vk p pub).pointFn
          (runInput IpaPallas.curve σ vk p pub).evalFn)
    (hr : (runInput IpaPallas.curve σ vk p pub).evalscale
      ∉ badROf σ aRef (runInput IpaPallas.curve σ vk p pub).pointFn
          (runInput IpaPallas.curve σ vk p pub).evalFn
          (runInput IpaPallas.curve σ vk p pub).polyscale) :
    ∃ (badB : Finset Fq) (badG : Fq → Finset Fq) (badA : Fq → Fq → Finset Fq)
        (badZ : Fq → Fq → Fq → Polynomial Fq → Finset Fq),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fq), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ((runOracles IpaPallas.curve σ vk p pub).beta ∉ badB →
          (runOracles IpaPallas.curve σ vk p pub).gamma
            ∉ badG (runOracles IpaPallas.curve σ vk p pub).beta →
          (runOracles IpaPallas.curve σ vk p pub).alpha
            ∉ badA (runOracles IpaPallas.curve σ vk p pub).beta
                (runOracles IpaPallas.curve σ vk p pub).gamma →
          (runOracles IpaPallas.curve σ vk p pub).zeta
            ∉ badZ (runOracles IpaPallas.curve σ vk p pub).beta
                (runOracles IpaPallas.curve σ vk p pub).gamma
                (runOracles IpaPallas.curve σ vk p pub).alpha
                (ftChunkAssembly σ.k aT) →
          (runOracles IpaPallas.curve σ vk p pub).zeta ≠ 1 →
          (runOracles IpaPallas.curve σ vk p pub).zeta
            ≠ idx.omega ^ (n - idx.zkRows) →
          (runOracles IpaPallas.curve σ vk p pub).zeta ^ n ≠ 1 →
          ∃ wTab : Fin n → Fin 15 → Fq, Satisfies idx (pubView idx pub) wTab) := by
  -- (1) reflect the run; pin the batch width and the domain size
  have hrun := kimchiVerify_reflects IpaPallas.curve σ vk p pub hacc
  have hsize : (runInput IpaPallas.curve σ vk p pub).commitments.size = 45 := by
    rw [hrun.comm_eq]
    simp [Array.size_append, hrun.shape_wComm, hrun.shape_coeffsComm,
      hrun.shape_sigmaComm]
  have hn : vk.n = n := hrun.shape_srs.symm.trans hk
  -- (2) the reference openings, reindexed onto the abstract 43-row batch
  have hbound₀ : ∀ i : Fin 43,
      commit σ (aRef (runReindex IpaPallas.curve σ vk p pub hsize i))
          (ρRef (runReindex IpaPallas.curve σ vk p pub hsize i))
        = batchC (fun c => p.wComm.getD (c : ℕ) 0) p.zComm vk.comms i :=
    fun i => (hrep (runReindex IpaPallas.curve σ vk p pub hsize i)).trans
      (batchC_eq_commitmentFn σ vk p pub hrun hsize i).symm
  -- (3) the openings seam, fed directly
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hk hbind vk.comms hvk (pubView idx pub)
      (fun c => p.wComm.getD (c : ℕ) 0) p.zComm
      (fun i => aRef (runReindex IpaPallas.curve σ vk p pub hsize i))
      (fun i => ρRef (runReindex IpaPallas.curve σ vk p pub hsize i)) hbound₀
  refine ⟨badB, badG, badA, badZ, hbounds, ?_⟩
  intro hβ hγ hα hζ hζ1 hζb hζn
  -- (4) the eval pins from the run's single accepted opening (45-row arity)
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _
    (kimchi_fiat_shamir_pallas σ vk p pub) hrun.accepts
  have hpins := eval_pins_of_opening σ hbind
    (runInput IpaPallas.curve σ vk p pub).commitmentFn
    (runInput IpaPallas.curve σ vk p pub).pointFn aRef ρRef hrep
    (runInput IpaPallas.curve σ vk p pub).evalFn
    (runInput IpaPallas.curve σ vk p pub).polyscale
    (runInput IpaPallas.curve σ vk p pub).evalscale hξ hr a ρ hopen
  -- (5) the part-1 ft opening
  obtain ⟨aft, ρft, hcomm_ft, heval_ft⟩ :=
    ft_opening_of_reflected_pallas σ vk p pub hbind hacc aRef ρRef hrep hξ hr
  -- (6) the ft/Maller identity from the chunk representations
  have hCσ6 : vk.sigmaComm.getD 6 0 = commitPoly σ (idx.sigmaPoly 6) :=
    congrArg (fun cm => cm.sigma 6) hvk
  have hσ₆ : (idx.sigmaPoly 6).natDegree < 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hcommit : commit σ aft ρft
      = runPScalar IpaPallas.curve σ vk p pub • vk.sigmaComm.getD 6 0
        - ((runOracles IpaPallas.curve σ vk p pub).zeta ^ n - 1)
            • ∑ j : Fin 7,
                ((runOracles IpaPallas.curve σ vk p pub).zeta ^ n) ^ (j : ℕ)
                  • p.tComm.getD (j : ℕ) 0 :=
    hcomm_ft.trans (runFtComm_eq_pallas σ vk p pub hrun hn)
  obtain ⟨htdeg, hteq0⟩ := ft_identity_of_chunks σ hbind (idx.sigmaPoly 6) hσ₆
    (vk.sigmaComm.getD 6 0) hCσ6 (fun j => p.tComm.getD (j : ℕ) 0) aT ρT hTC
    (runPScalar IpaPallas.curve σ vk p pub)
    (runOracles IpaPallas.curve σ vk p pub).zeta
    (runFtEval0 IpaPallas.curve σ vk p pub) n hk aft ρft hcommit heval_ft
  -- (7) reconcile the derived identity into the consumer's shape
  have hce := claimedEvals_runReindex_eq σ vk p pub hrun hsize
  unfold runPScalar runFtEval0 runFtEval0P at hteq0
  rw [runPubEvals_fst_eq σ vk p pub idx homega hn hpub hζn, hn, hzk, homega, hendo,
    hshift, ← hce] at hteq0
  -- (8) the per-row pins, at the consumer's two eval points
  have hpt : (runInput IpaPallas.curve σ vk p pub).pointFn
      = ![(runOracles IpaPallas.curve σ vk p pub).zeta,
          idx.omega * (runOracles IpaPallas.curve σ vk p pub).zeta] := by
    funext j
    fin_cases j
    · rfl
    · show (runOracles IpaPallas.curve σ vk p pub).zeta * vk.omega = _
      rw [homega]
      exact mul_comm _ _
  rw [hpt] at hpins
  -- (9) feed the consumer
  exact himp (runOracles IpaPallas.curve σ vk p pub).beta
    (runOracles IpaPallas.curve σ vk p pub).gamma
    (runOracles IpaPallas.curve σ vk p pub).alpha
    (ftChunkAssembly σ.k aT)
    (runOracles IpaPallas.curve σ vk p pub).zeta
    (fun i j => (runInput IpaPallas.curve σ vk p pub).evalFn
      (runReindex IpaPallas.curve σ vk p pub hsize i) j)
    (fun i => aRef (runReindex IpaPallas.curve σ vk p pub hsize i))
    (fun i => ρRef (runReindex IpaPallas.curve σ vk p pub hsize i))
    hβ hγ hα hζ hζ1 hζb htdeg
    (fun i => ⟨hbound₀ i,
      fun j => hpins (runReindex IpaPallas.curve σ vk p pub hsize i) j⟩)
    hteq0

end Kimchi.Verifier
