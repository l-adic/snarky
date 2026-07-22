import Kimchi.Verifier.Capstone.Algebraic
import Kimchi.Verifier.Reflect

/-!
# The Fiat–Shamir-reflection discharge: ft opening and the terminal roots

The Fiat–Shamir axiom anchored on the deployed verifier's own transcript:
`kimchi_fiat_shamir_{vesta,pallas}` state the transcript-tree extraction over the warm
data of a reflected run — the warm-sponge finish `Ipa.verifyFrom … (runWarm …)
(runInput …)` that `kimchiVerify` itself executes (`ReflectedRun.accepts`,
`Verifier/Reflect.lean`), at the flat segment stream of `44·nc + 1` batch rows. The
independence criterion: each says only that the Poseidon sponge provides a valid
Fiat–Shamir transform at the transcript the deployed verifier actually runs; no
arithmetic content, no reference to the abstract batch.

`ft_opening_of_reflected` (PROVED, tree-as-hypothesis) derives the ft opening from a
genuine acceptance: the constructed ft commitment is the single-chunk ft row of
the run's own accepted flat stream — flat position `nc` (after the public row's `nc`
chunks) — so `ipa_soundnessA` plus the arity-generic `eval_pins_of_opening` pin
`runFtComm` to a representation whose evaluation at the run's own `ζ` is `runFtEval0`.

The terminal roots `kimchi{Vesta,Pallas}_run_sound_algebraic_ft` then feed the
openings seam (`kimchiProof_sound_of_openings`) directly: the deployed flat stream is
read onto the 44-row `batchC` at the stream positions, the public row is bound through
`publicCommitment_corresponds` and the key's Lagrange chunk pin, and the Maller
identity comes from the ft opening via `ft_identity_of_chunks` at the double
`ζ^{2^σ.k}` collapse.
-/

open Bulletproof

namespace Kimchi.Verifier

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization
  Kimchi.Protocol.Equation CompElliptic.Fields.Pasta Kimchi.Verifier

/-! ## The chunked Fiat–Shamir axioms -/

/-- **AXIOM (Fiat–Shamir, Poseidon instantiation over the deployed chunked run,
Vesta).** A run accepted by the deployed chunked warm-sponge finish
(`Ipa.verifyFrom … (runWarm …) (runInput …) = true`, the `ReflectedRun.accepts` field
of the CHUNKED reflection) admits a de-blinded accepting transcript tree over the run's
own flat segment batch. This restates `kimchi_fiat_shamir_vesta` at the chunked
transcript shape — same declared assumption (the Poseidon sponge provides a valid
Fiat–Shamir transform), stated at the transcript the deployed chunked verifier actually
runs; the statement mentions only the run's own wire data. -/
axiom kimchi_fiat_shamir_vesta (σ : SRS IpaVesta.Point) {nc : ℕ}
    (cvk : KimchiVK IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc) (pub : Array Fp) :
  FiatShamirTreeB σ
    (combinedCommitment (runInput IpaVesta.curve σ cvk cp pub).polyscale
      (runInput IpaVesta.curve σ cvk cp pub).commitmentFn)
    (combinedEvalVector (2 ^ σ.k) (runInput IpaVesta.curve σ cvk cp pub).evalscale
      (runInput IpaVesta.curve σ cvk cp pub).pointFn)
    (Ipa.cipOf (runInput IpaVesta.curve σ cvk cp pub))
    (Ipa.verifyFrom IpaVesta.curve σ (runWarm IpaVesta.curve σ cvk cp pub)
      (runInput IpaVesta.curve σ cvk cp pub) = true)

/-- **AXIOM (Fiat–Shamir, Poseidon instantiation over the deployed chunked run,
Pallas).** The Pallas-side twin of `kimchi_fiat_shamir_vesta`. -/
axiom kimchi_fiat_shamir_pallas (σ : SRS IpaPallas.Point) {nc : ℕ}
    (cvk : KimchiVK IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc) (pub : Array Fq) :
  FiatShamirTreeB σ
    (combinedCommitment (runInput IpaPallas.curve σ cvk cp pub).polyscale
      (runInput IpaPallas.curve σ cvk cp pub).commitmentFn)
    (combinedEvalVector (2 ^ σ.k) (runInput IpaPallas.curve σ cvk cp pub).evalscale
      (runInput IpaPallas.curve σ cvk cp pub).pointFn)
    (Ipa.cipOf (runInput IpaPallas.curve σ cvk cp pub))
    (Ipa.verifyFrom IpaPallas.curve σ (runWarm IpaPallas.curve σ cvk cp pub)
      (runInput IpaPallas.curve σ cvk cp pub) = true)

/-! ## Reading the ft slot of the flat stream -/

variable (C : Ipa.CommitmentCurve)

/-- The wire point carrier is inhabited by the group zero — for the `getElem!` reads
of the flat stream. -/
private instance : Inhabited C.Point := ⟨0⟩

/-- `getElem!` through an append, left part (the `Reflect.lean` helper, local copy). -/
private theorem getBang_append_left {α : Type*} [Inhabited α] (as bs : Array α)
    (i : ℕ) (h : i < as.size) : (as ++ bs)[i]! = as[i]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega),
    getElem!_pos as i h, Array.getElem_append_left h]

/-- `getElem!` through an append, right part, at an offset index. -/
private theorem getBang_append_right {α : Type*} [Inhabited α] (as bs : Array α)
    (i : ℕ) (h : i < bs.size) : (as ++ bs)[as.size + i]! = bs[i]! := by
  have hgr := Array.getElem_append_right' (i := i) as h
  rw [getElem!_pos (as ++ bs) _ (by rw [Array.size_append]; omega),
    getElem!_pos bs i h, hgr]
  congr 1
  omega

/-- `getBang_append_right` with the index supplied as an equation (avoids rewriting
occurrences of the index elsewhere in the goal). -/
private theorem getBang_append_at {α : Type*} [Inhabited α] (as bs : Array α)
    (i j : ℕ) (hij : i = as.size + j) (h : j < bs.size) :
    (as ++ bs)[i]! = bs[j]! := by
  subst hij
  exact getBang_append_right as bs j h

/-- `getElem!` through a map, in range. -/
private theorem getBang_map {α β : Type*} [Inhabited α] [Inhabited β] (g : α → β)
    (as : Array α) (i : ℕ) (h : i < as.size) : (as.map g)[i]! = g as[i]! := by
  rw [getElem!_pos (as.map g) i (by rw [Array.size_map]; omega), getElem!_pos as i h,
    Array.getElem_map]

/-- The flat position of the single-chunk ft row: `nc` (right after the public row's
`nc` chunks). Reads the triple off `flatRows (runLogicalP …)`. -/
private theorem flatRows_ft_read (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc)
    (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)) :
    (flatRows C (runLogicalP C σ cvk cp pub pe))[(nc : ℕ)]!
      = (runFtComm C σ cvk cp pub,
          runFtEval0P C σ cvk cp pub
            (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray),
          cp.ftEval1) := by
  have hApub : (Array.map
        (fun ce : C.Point × C.ScalarField × C.ScalarField => (ce.1, ce.2.1, ce.2.2))
        ((publicCommitment C σ cvk pub).toArray.zip
          (pe.zeta.toArray.zip pe.zetaOmega.toArray))).size
      = nc := by
    simp [Array.size_zip]
  have hAft : Array.map
        (fun ce : C.Point × C.ScalarField × C.ScalarField => (ce.1, ce.2.1, ce.2.2))
        (#[runFtComm C σ cvk cp pub].zip
          (#[runFtEval0P C σ cvk cp pub
              (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)].zip
            #[cp.ftEval1]))
      = #[(runFtComm C σ cvk cp pub,
          runFtEval0P C σ cvk cp pub
            (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray),
          cp.ftEval1)] := by
    simp [Array.zip]
  unfold flatRows runLogicalP
  rw [Array.flatMap_append, Array.flatMap_append, Array.flatMap_append]
  rw [show (#[((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray, pe.zetaOmega.toArray),
      (#[runFtComm C σ cvk cp pub],
        #[runFtEval0P C σ cvk cp pub
            (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
        #[cp.ftEval1]),
      (cp.zComm.toArray, cp.evals.z.zeta.toArray, cp.evals.z.zetaOmega.toArray),
      (cvk.genericComm.toArray, cp.evals.genericSelector.zeta.toArray,
        cp.evals.genericSelector.zetaOmega.toArray),
      (cvk.poseidonComm.toArray, cp.evals.poseidonSelector.zeta.toArray,
        cp.evals.poseidonSelector.zetaOmega.toArray),
      (cvk.completeAddComm.toArray, cp.evals.completeAddSelector.zeta.toArray,
        cp.evals.completeAddSelector.zetaOmega.toArray),
      (cvk.mulComm.toArray, cp.evals.mulSelector.zeta.toArray,
        cp.evals.mulSelector.zetaOmega.toArray),
      (cvk.emulComm.toArray, cp.evals.emulSelector.zeta.toArray,
        cp.evals.emulSelector.zetaOmega.toArray),
      (cvk.endomulScalarComm.toArray, cp.evals.endomulScalarSelector.zeta.toArray,
        cp.evals.endomulScalarSelector.zetaOmega.toArray)]
    : Array (Array C.Point × Array C.ScalarField × Array C.ScalarField))
      = #[((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray, pe.zetaOmega.toArray)]
        ++ #[(#[runFtComm C σ cvk cp pub],
        #[runFtEval0P C σ cvk cp pub
            (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
        #[cp.ftEval1])]
        ++ #[      (cp.zComm.toArray, cp.evals.z.zeta.toArray, cp.evals.z.zetaOmega.toArray),
      (cvk.genericComm.toArray, cp.evals.genericSelector.zeta.toArray,
        cp.evals.genericSelector.zetaOmega.toArray),
      (cvk.poseidonComm.toArray, cp.evals.poseidonSelector.zeta.toArray,
        cp.evals.poseidonSelector.zetaOmega.toArray),
      (cvk.completeAddComm.toArray, cp.evals.completeAddSelector.zeta.toArray,
        cp.evals.completeAddSelector.zetaOmega.toArray),
      (cvk.mulComm.toArray, cp.evals.mulSelector.zeta.toArray,
        cp.evals.mulSelector.zetaOmega.toArray),
      (cvk.emulComm.toArray, cp.evals.emulSelector.zeta.toArray,
        cp.evals.emulSelector.zetaOmega.toArray),
      (cvk.endomulScalarComm.toArray, cp.evals.endomulScalarSelector.zeta.toArray,
        cp.evals.endomulScalarSelector.zetaOmega.toArray)] from rfl]
  rw [Array.flatMap_append, Array.flatMap_append]
  simp only [Array.flatMap_singleton]
  rw [getBang_append_left _ _ _ (by
    simp only [Array.size_append, hApub, hAft, List.size_toArray, List.length_cons,
      List.length_nil]
    omega)]
  rw [getBang_append_left _ _ _ (by
    simp only [Array.size_append, hApub, hAft, List.size_toArray, List.length_cons,
      List.length_nil]
    omega)]
  rw [getBang_append_left _ _ _ (by
    simp only [Array.size_append, hApub, hAft, List.size_toArray, List.length_cons,
      List.length_nil]
    omega)]
  rw [getBang_append_left _ _ _ (by
    simp only [Array.size_append, hApub, hAft, List.size_toArray, List.length_cons,
      List.length_nil]
    omega)]
  rw [getBang_append_at _ _ _ 0 (by rw [hApub, Nat.add_zero]) (by rw [hAft]; simp)]
  rw [hAft]
  rw [getElem!_pos _ 0 (by simp)]
  rfl

/-- The flat stream has more than `nc` rows (the public block plus the ft singleton). -/
private theorem flatRows_size_lt (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc)
    (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)) :
    (nc : ℕ) < (flatRows C (runLogicalP C σ cvk cp pub pe)).size := by
  have hApub : (Array.map
        (fun ce : C.Point × C.ScalarField × C.ScalarField => (ce.1, ce.2.1, ce.2.2))
        ((publicCommitment C σ cvk pub).toArray.zip
          (pe.zeta.toArray.zip pe.zetaOmega.toArray))).size
      = nc := by
    simp [Array.size_zip]
  unfold flatRows runLogicalP
  rw [Array.flatMap_append, Array.flatMap_append, Array.flatMap_append]
  rw [show (#[((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray, pe.zetaOmega.toArray),
      (#[runFtComm C σ cvk cp pub],
        #[runFtEval0P C σ cvk cp pub
            (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
        #[cp.ftEval1]),
      (cp.zComm.toArray, cp.evals.z.zeta.toArray, cp.evals.z.zetaOmega.toArray),
      (cvk.genericComm.toArray, cp.evals.genericSelector.zeta.toArray,
        cp.evals.genericSelector.zetaOmega.toArray),
      (cvk.poseidonComm.toArray, cp.evals.poseidonSelector.zeta.toArray,
        cp.evals.poseidonSelector.zetaOmega.toArray),
      (cvk.completeAddComm.toArray, cp.evals.completeAddSelector.zeta.toArray,
        cp.evals.completeAddSelector.zetaOmega.toArray),
      (cvk.mulComm.toArray, cp.evals.mulSelector.zeta.toArray,
        cp.evals.mulSelector.zetaOmega.toArray),
      (cvk.emulComm.toArray, cp.evals.emulSelector.zeta.toArray,
        cp.evals.emulSelector.zetaOmega.toArray),
      (cvk.endomulScalarComm.toArray, cp.evals.endomulScalarSelector.zeta.toArray,
        cp.evals.endomulScalarSelector.zetaOmega.toArray)]
    : Array (Array C.Point × Array C.ScalarField × Array C.ScalarField))
      = #[((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray, pe.zetaOmega.toArray)]
        ++ #[(#[runFtComm C σ cvk cp pub],
        #[runFtEval0P C σ cvk cp pub
            (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
        #[cp.ftEval1])]
        ++ #[      (cp.zComm.toArray, cp.evals.z.zeta.toArray, cp.evals.z.zetaOmega.toArray),
      (cvk.genericComm.toArray, cp.evals.genericSelector.zeta.toArray,
        cp.evals.genericSelector.zetaOmega.toArray),
      (cvk.poseidonComm.toArray, cp.evals.poseidonSelector.zeta.toArray,
        cp.evals.poseidonSelector.zetaOmega.toArray),
      (cvk.completeAddComm.toArray, cp.evals.completeAddSelector.zeta.toArray,
        cp.evals.completeAddSelector.zetaOmega.toArray),
      (cvk.mulComm.toArray, cp.evals.mulSelector.zeta.toArray,
        cp.evals.mulSelector.zetaOmega.toArray),
      (cvk.emulComm.toArray, cp.evals.emulSelector.zeta.toArray,
        cp.evals.emulSelector.zetaOmega.toArray),
      (cvk.endomulScalarComm.toArray, cp.evals.endomulScalarSelector.zeta.toArray,
        cp.evals.endomulScalarSelector.zetaOmega.toArray)] from rfl]
  rw [Array.flatMap_append, Array.flatMap_append]
  simp only [Array.flatMap_singleton]
  simp only [Array.size_append, hApub]
  have h1 : 0 < (Array.map
      (fun ce : C.Point × C.ScalarField × C.ScalarField => (ce.1, ce.2.1, ce.2.2))
      (#[runFtComm C σ cvk cp pub].zip
        (#[runFtEval0P C σ cvk cp pub
            (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)].zip
          #[cp.ftEval1]))).size := by
    simp [Array.zip]
  omega

/-- **The ft opening from a chunked reflected run** (tree-as-hypothesis, PROVED):
DL-binding, a reflected accepted chunked run, SRS-basis representations of the run's
own flat batch rows, the run's transcript tree (the chunked `kimchi_fiat_shamir_*`
shape, here a hypothesis), and good combination challenges yield the ft opening — a
representation of the constructed ft commitment `runFtComm` (the DOUBLE collapse at
`ζ^{2^σ.k}`) whose evaluation at the run's own `ζ` is the computed claim `runFtEval0`.
The ft row sits at flat position `nc`, right after the public row's chunks
(`flatRows_ft_read`). -/
private theorem ft_opening_of_reflected {C : Ipa.CommitmentCurve} [Module C.ScalarField C.Point]
    (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → C.ScalarField) (wh : C.ScalarField),
      DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : Ipa.verifyFrom C σ (runWarm C σ cvk cp pub)
      (runInput C σ cvk cp pub) = true)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size → Fin (2 ^ σ.k)
      → C.ScalarField)
    (ρRef : Fin (runInput C σ cvk cp pub).commitments.size → C.ScalarField)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i) = (runInput C σ cvk cp pub).commitmentFn i)
    (hFS : FiatShamirTreeB σ
      (combinedCommitment (runInput C σ cvk cp pub).polyscale
        (runInput C σ cvk cp pub).commitmentFn)
      (combinedEvalVector (2 ^ σ.k) (runInput C σ cvk cp pub).evalscale
        (runInput C σ cvk cp pub).pointFn)
      (Ipa.cipOf (runInput C σ cvk cp pub))
      (Ipa.verifyFrom C σ (runWarm C σ cvk cp pub) (runInput C σ cvk cp pub) = true))
    (hξ : (runInput C σ cvk cp pub).polyscale
      ∉ badXiOf σ aRef (runInput C σ cvk cp pub).pointFn (runInput C σ cvk cp pub).evalFn)
    (hr : (runInput C σ cvk cp pub).evalscale
      ∉ badROf σ aRef (runInput C σ cvk cp pub).pointFn (runInput C σ cvk cp pub).evalFn
          (runInput C σ cvk cp pub).polyscale) :
    ∃ (aft : Fin (2 ^ σ.k) → C.ScalarField) (ρft : C.ScalarField),
      commit σ aft ρft = runFtComm C σ cvk cp pub
        ∧ innerProduct aft (evalVector (2 ^ σ.k) (runOracles C σ cvk cp pub).zeta)
            = runFtEval0 C σ cvk cp pub := by
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _ hFS hacc
  have hpins := eval_pins_of_opening σ hbind (runInput C σ cvk cp pub).commitmentFn
    (runInput C σ cvk cp pub).pointFn aRef ρRef hrep (runInput C σ cvk cp pub).evalFn
    (runInput C σ cvk cp pub).polyscale (runInput C σ cvk cp pub).evalscale hξ hr a ρ hopen
  have hread := flatRows_ft_read C σ cvk cp pub (runPubEvals C σ cvk cp pub)
  have hflt := flatRows_size_lt C σ cvk cp pub (runPubEvals C σ cvk cp pub)
  have hsz : (nc : ℕ) < (runInput C σ cvk cp pub).commitments.size := by
    show (nc : ℕ)
      < ((flatRows C (runLogicalP C σ cvk cp pub (runPubEvals C σ cvk cp pub))).map
          (·.1)).size
    rw [Array.size_map]
    exact hflt
  refine ⟨aRef ⟨nc, hsz⟩, ρRef ⟨nc, hsz⟩, ?_, ?_⟩
  · rw [hrep ⟨nc, hsz⟩]
    show (runInput C σ cvk cp pub).commitments[(nc : ℕ)]'hsz
      = runFtComm C σ cvk cp pub
    rw [← getElem!_pos (runInput C σ cvk cp pub).commitments (nc : ℕ) hsz]
    show ((flatRows C (runLogicalP C σ cvk cp pub (runPubEvals C σ cvk cp pub))).map
        (·.1))[(nc : ℕ)]! = runFtComm C σ cvk cp pub
    rw [getBang_map _ _ _ hflt, hread]
  · have hpin := hpins ⟨nc, hsz⟩ (0 : Fin 2)
    have hpt : (runInput C σ cvk cp pub).pointFn (0 : Fin 2)
        = (runOracles C σ cvk cp pub).zeta := rfl
    rw [hpt] at hpin
    rw [← hpin]
    show ((runInput C σ cvk cp pub).evals[(nc : ℕ)]!)[(0 : ℕ)]!
      = runFtEval0 C σ cvk cp pub
    show (((flatRows C (runLogicalP C σ cvk cp pub (runPubEvals C σ cvk cp pub))).map
        (fun r => #[r.2.1, r.2.2]))[(nc : ℕ)]!)[(0 : ℕ)]!
      = runFtEval0 C σ cvk cp pub
    rw [getBang_map _ _ _ hflt, hread]
    rfl

/-- **The ft opening of the deployed chunked Vesta verifier**: a genuine
`KimchiVesta.verify … = true`, DL-binding, representations of the run's own
flat batch rows, and good combination challenges yield the ft opening. The run is
reflected trust-free (`kimchiVerify_reflects`); the transcript tree is
`kimchi_fiat_shamir_vesta` at the run's own warm data — the sole axiom
consumed. The chunked Vesta FS-reflection root. -/
theorem ft_opening_of_reflected_vesta (σ : SRS IpaVesta.Point) {nc : ℕ}
    (cvk : KimchiVK IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc)
    (pub : Array Fp)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : Ipa.verifyFrom IpaVesta.curve σ (runWarm IpaVesta.curve σ cvk cp pub)
      (runInput IpaVesta.curve σ cvk cp pub) = true)
    (aRef : Fin (runInput IpaVesta.curve σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → Fp)
    (ρRef : Fin (runInput IpaVesta.curve σ cvk cp pub).commitments.size → Fp)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput IpaVesta.curve σ cvk cp pub).commitmentFn i)
    (hξ : (runInput IpaVesta.curve σ cvk cp pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaVesta.curve σ cvk cp pub).pointFn
          (runInput IpaVesta.curve σ cvk cp pub).evalFn)
    (hr : (runInput IpaVesta.curve σ cvk cp pub).evalscale
      ∉ badROf σ aRef (runInput IpaVesta.curve σ cvk cp pub).pointFn
          (runInput IpaVesta.curve σ cvk cp pub).evalFn
          (runInput IpaVesta.curve σ cvk cp pub).polyscale) :
    ∃ (aft : Fin (2 ^ σ.k) → Fp) (ρft : Fp),
      commit σ aft ρft = runFtComm IpaVesta.curve σ cvk cp pub
        ∧ innerProduct aft
            (evalVector (2 ^ σ.k) (runOracles IpaVesta.curve σ cvk cp pub).zeta)
            = runFtEval0 IpaVesta.curve σ cvk cp pub :=
  ft_opening_of_reflected σ cvk cp pub hbind hacc aRef ρRef hrep
    (kimchi_fiat_shamir_vesta σ cvk cp pub) hξ hr

/-- **The ft opening of the deployed chunked Pallas verifier.** The Pallas twin. -/
theorem ft_opening_of_reflected_pallas (σ : SRS IpaPallas.Point) {nc : ℕ}
    (cvk : KimchiVK IpaPallas.curve nc) (cp : KimchiProof IpaPallas.curve nc)
    (pub : Array Fq)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : Ipa.verifyFrom IpaPallas.curve σ (runWarm IpaPallas.curve σ cvk cp pub)
      (runInput IpaPallas.curve σ cvk cp pub) = true)
    (aRef : Fin (runInput IpaPallas.curve σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → Fq)
    (ρRef : Fin (runInput IpaPallas.curve σ cvk cp pub).commitments.size → Fq)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput IpaPallas.curve σ cvk cp pub).commitmentFn i)
    (hξ : (runInput IpaPallas.curve σ cvk cp pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaPallas.curve σ cvk cp pub).pointFn
          (runInput IpaPallas.curve σ cvk cp pub).evalFn)
    (hr : (runInput IpaPallas.curve σ cvk cp pub).evalscale
      ∉ badROf σ aRef (runInput IpaPallas.curve σ cvk cp pub).pointFn
          (runInput IpaPallas.curve σ cvk cp pub).evalFn
          (runInput IpaPallas.curve σ cvk cp pub).polyscale) :
    ∃ (aft : Fin (2 ^ σ.k) → Fq) (ρft : Fq),
      commit σ aft ρft = runFtComm IpaPallas.curve σ cvk cp pub
        ∧ innerProduct aft
            (evalVector (2 ^ σ.k) (runOracles IpaPallas.curve σ cvk cp pub).zeta)
            = runFtEval0 IpaPallas.curve σ cvk cp pub :=
  ft_opening_of_reflected σ cvk cp pub hbind hacc aRef ρRef hrep
    (kimchi_fiat_shamir_pallas σ cvk cp pub) hξ hr

/-! ## The uniform-block read toolkit

The flat segment stream is a `flatMap` of per-row chunk blocks; every block except the
ft singleton has exactly `nc` entries. Reads at `q·nc + r` land in block `q` at offset
`r`. -/

private theorem list_uniform_length {α β : Type*} (L : List α) (g : α → List β)
    (nc : ℕ) (h : ∀ a ∈ L, (g a).length = nc) :
    (L.flatMap g).length = L.length * nc := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.flatMap_cons, List.length_append, h hd (by simp),
      ih (fun a ha => h a (by simp [ha])), List.length_cons]
    ring

private theorem list_uniform_read {α β : Type*} [Inhabited α] [Inhabited β]
    (L : List α) (g : α → List β) (nc : ℕ)
    (h : ∀ a ∈ L, (g a).length = nc)
    (q r : ℕ) (hq : q < L.length) (hr : r < nc) :
    (L.flatMap g)[q * nc + r]! = (g L[q]!)[r]! := by
  induction L generalizing q with
  | nil => simp at hq
  | cons hd tl ih =>
    have hhd : (g hd).length = nc := h hd (by simp)
    have htl : (tl.flatMap g).length = tl.length * nc :=
      list_uniform_length tl g nc (fun a ha => h a (by simp [ha]))
    rw [List.flatMap_cons]
    cases q with
    | zero =>
      have h0 : (hd :: tl)[(0 : ℕ)]! = hd := by
        rw [getElem!_pos (hd :: tl) 0 (by simp)]
        simp
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [h0, getElem!_pos (g hd ++ tl.flatMap g) r
          (by rw [List.length_append]; omega),
        List.getElem_append_left (by omega),
        ← getElem!_pos (g hd) r (by omega)]
    | succ q' =>
      have hq' : q' < tl.length := by simpa using hq
      have hbound : q' * nc + r < (tl.flatMap g).length := by
        rw [htl]
        have : (q' + 1) * nc ≤ tl.length * nc := Nat.mul_le_mul_right _ (by omega)
        have h2 : q' * nc + r < (q' + 1) * nc := by
          rw [Nat.succ_mul]
          omega
        omega
      have hpos : (q' + 1) * nc + r = (g hd).length + (q' * nc + r) := by
        rw [hhd, Nat.succ_mul]
        ring
      have hsucc : (hd :: tl)[(q' + 1 : ℕ)]! = tl[q']! := by
        rw [getElem!_pos (hd :: tl) (q' + 1) (by simpa using hq),
          getElem!_pos tl q' hq']
        simp
      rw [hpos, hsucc,
        getElem!_pos (g hd ++ tl.flatMap g) _
          (by rw [List.length_append]; omega),
        List.getElem_append_right (by omega),
        ← getElem!_pos (tl.flatMap g) _
          (by
            have : (g hd).length + (q' * nc + r) - (g hd).length = q' * nc + r := by
              omega
            omega),
        show (g hd).length + (q' * nc + r) - (g hd).length = q' * nc + r from by omega,
        ih (fun a ha => h a (by simp [ha])) q' hq']

/-- Uniform-block read through an array `flatMap`: with every block of size `nc`,
position `q·nc + r` is block `q` at offset `r`. -/
private theorem flatMap_uniform_read {α β : Type*} [Inhabited α] [Inhabited β]
    (A : Array α) (f : α → Array β) (nc : ℕ)
    (h : ∀ a ∈ A, (f a).size = nc)
    (q r : ℕ) (hq : q < A.size) (hr : r < nc) :
    (A.flatMap f)[q * nc + r]! = (f A[q]!)[r]! := by
  rw [← Array.getElem!_toList, Array.toList_flatMap,
    list_uniform_read A.toList (fun a => (f a).toList) nc
      (fun a ha => by
        rw [Array.length_toList]
        exact h a (by simpa using ha))
      q r (by rwa [Array.length_toList]) hr,
    Array.getElem!_toList, Array.getElem!_toList]

/-- The size of a uniform-block array `flatMap`. -/
private theorem flatMap_uniform_size {α β : Type*} (A : Array α) (f : α → Array β)
    (nc : ℕ) (h : ∀ a ∈ A, (f a).size = nc) :
    (A.flatMap f).size = A.size * nc := by
  rw [show (A.flatMap f).size = (A.flatMap f).toList.length from
      Array.length_toList.symm,
    Array.toList_flatMap,
    list_uniform_length A.toList (fun a => (f a).toList) nc
      (fun a ha => by
        rw [Array.length_toList]
        exact h a (by simpa using ha)),
    Array.length_toList]

/-- `combineAt`'s fold, from a running accumulator and power. -/
private theorem combineAt_aux {F : Type*} [Field F] (xM : F) (l : List F) (acc pw : F) :
    (l.foldl (fun (a : F × F) c => (a.1 + a.2 * c, a.2 * xM)) (acc, pw)).1
      = acc + ∑ i : Fin l.length, pw * xM ^ (i : ℕ) * l[i] := by
  induction l generalizing acc pw with
  | nil => simp
  | cons x t ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
      Fin.val_succ, Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [← add_assoc]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- The verifier's chunk combination is the indexed power sum. -/
private theorem combineAt_eq_sum {F : Type*} [Field F] (xM : F) (v : Array F) :
    combineAt xM v = ∑ i : Fin v.size, xM ^ (i : ℕ) * v[i] := by
  rw [combineAt, ← Array.foldl_toList, combineAt_aux]
  simp only [one_mul, zero_add]
  refine Fintype.sum_equiv (finCongr v.length_toList) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.getElem_fin, Fin.val_cast, Array.getElem_toList]

/-- The flat stream position of abstract batch row `i`, chunk `c`. The abstract rows
are the deployed `to_batch` order with the single-chunk ft row interposed at flat
position `nc`, so the public row's chunks come first and every later row `i` starts at
`nc + 1 + (i − 1)·nc`. -/
private def streamPos (nc : ℕ) (i : Fin 44) (c : ℕ) : ℕ :=
  if (i : ℕ) < 1 then c else nc + 1 + ((i : ℕ) - 1) * nc + c

section StreamRead

variable {σ : SRS C.Point} {nc : ℕ} {cvk : KimchiVK C nc}
  {cp : KimchiProof C nc} {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)}

/-- The row-triple flattener of the stream. -/
private def rowF : Array C.Point × Array C.ScalarField × Array C.ScalarField
    → Array (C.Point × C.ScalarField × C.ScalarField) :=
  fun r => (r.1.zip (r.2.1.zip r.2.2)).map (fun ce => (ce.1, ce.2.1, ce.2.2))

/-- The zip-map row triple of a checked commitment/evaluation pair. -/
private def zipRow {nc : ℕ} :
    Vector C.Point nc × Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)
    → Array C.Point × Array C.ScalarField × Array C.ScalarField :=
  fun x => (x.1.toArray, x.2.zeta.toArray, x.2.zetaOmega.toArray)

/-- The literal seven-row block of the decomposition, named for the region reads. -/
private def litRows {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) :
    Array (Array C.Point × Array C.ScalarField × Array C.ScalarField) :=
  #[(cp.zComm.toArray, cp.evals.z.zeta.toArray, cp.evals.z.zetaOmega.toArray),
    (cvk.genericComm.toArray, cp.evals.genericSelector.zeta.toArray,
      cp.evals.genericSelector.zetaOmega.toArray),
    (cvk.poseidonComm.toArray, cp.evals.poseidonSelector.zeta.toArray,
      cp.evals.poseidonSelector.zetaOmega.toArray),
    (cvk.completeAddComm.toArray, cp.evals.completeAddSelector.zeta.toArray,
      cp.evals.completeAddSelector.zetaOmega.toArray),
    (cvk.mulComm.toArray, cp.evals.mulSelector.zeta.toArray,
      cp.evals.mulSelector.zetaOmega.toArray),
    (cvk.emulComm.toArray, cp.evals.emulSelector.zeta.toArray,
      cp.evals.emulSelector.zetaOmega.toArray),
    (cvk.endomulScalarComm.toArray, cp.evals.endomulScalarSelector.zeta.toArray,
      cp.evals.endomulScalarSelector.zetaOmega.toArray)]

/-- **The stream decomposition**: the flat rows of the run's 45 logical rows are the
six-region append tree — the public block, the ft singleton, the seven literal rows
(`z` + six selectors), then the witness / coefficient / σ zip blocks. -/
private theorem stream_decomp (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)) :
    flatRows C (runLogicalP C σ cvk cp pub pe)
      = ((((rowF C ((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray,
              pe.zetaOmega.toArray)
            ++ rowF C (#[runFtComm C σ cvk cp pub],
              #[runFtEval0P C σ cvk cp pub
                  (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
              #[cp.ftEval1]))
          ++ Array.flatMap (rowF C) (litRows C cvk cp))
        ++ Array.flatMap (rowF C) ((cp.wComm.zip cp.evals.w).toArray.map (zipRow C)))
      ++ Array.flatMap (rowF C)
          ((cvk.coefficientsComm.zip cp.evals.coefficients).toArray.map (zipRow C)))
      ++ Array.flatMap (rowF C)
          (((cvk.sigmaComm.take 6).zip cp.evals.s).toArray.map (zipRow C)) := by
  unfold flatRows runLogicalP
  rw [Array.flatMap_append, Array.flatMap_append, Array.flatMap_append]
  rw [show (#[((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray,
        pe.zetaOmega.toArray),
      (#[runFtComm C σ cvk cp pub],
        #[runFtEval0P C σ cvk cp pub
            (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
        #[cp.ftEval1]),
      (cp.zComm.toArray, cp.evals.z.zeta.toArray, cp.evals.z.zetaOmega.toArray),
      (cvk.genericComm.toArray, cp.evals.genericSelector.zeta.toArray,
        cp.evals.genericSelector.zetaOmega.toArray),
      (cvk.poseidonComm.toArray, cp.evals.poseidonSelector.zeta.toArray,
        cp.evals.poseidonSelector.zetaOmega.toArray),
      (cvk.completeAddComm.toArray, cp.evals.completeAddSelector.zeta.toArray,
        cp.evals.completeAddSelector.zetaOmega.toArray),
      (cvk.mulComm.toArray, cp.evals.mulSelector.zeta.toArray,
        cp.evals.mulSelector.zetaOmega.toArray),
      (cvk.emulComm.toArray, cp.evals.emulSelector.zeta.toArray,
        cp.evals.emulSelector.zetaOmega.toArray),
      (cvk.endomulScalarComm.toArray, cp.evals.endomulScalarSelector.zeta.toArray,
        cp.evals.endomulScalarSelector.zetaOmega.toArray)]
    : Array (Array C.Point × Array C.ScalarField × Array C.ScalarField))
      = #[((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray,
          pe.zetaOmega.toArray)]
        ++ #[(#[runFtComm C σ cvk cp pub],
          #[runFtEval0P C σ cvk cp pub
              (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
          #[cp.ftEval1])]
        ++ #[(cp.zComm.toArray, cp.evals.z.zeta.toArray, cp.evals.z.zetaOmega.toArray),
      (cvk.genericComm.toArray, cp.evals.genericSelector.zeta.toArray,
        cp.evals.genericSelector.zetaOmega.toArray),
      (cvk.poseidonComm.toArray, cp.evals.poseidonSelector.zeta.toArray,
        cp.evals.poseidonSelector.zetaOmega.toArray),
      (cvk.completeAddComm.toArray, cp.evals.completeAddSelector.zeta.toArray,
        cp.evals.completeAddSelector.zetaOmega.toArray),
      (cvk.mulComm.toArray, cp.evals.mulSelector.zeta.toArray,
        cp.evals.mulSelector.zetaOmega.toArray),
      (cvk.emulComm.toArray, cp.evals.emulSelector.zeta.toArray,
        cp.evals.emulSelector.zetaOmega.toArray),
      (cvk.endomulScalarComm.toArray, cp.evals.endomulScalarSelector.zeta.toArray,
        cp.evals.endomulScalarSelector.zetaOmega.toArray)] from rfl]
  rw [Array.flatMap_append, Array.flatMap_append]
  simp only [Array.flatMap_singleton]
  rfl

/-- A zip-map row of an `m`-chunk triple flattens to `m` entries. -/
private theorem rowF_size {A : Array C.Point} {B D : Array C.ScalarField} {m : ℕ}
    (hA : A.size = m) (hB : B.size = m) (hD : D.size = m) :
    (rowF C (A, B, D)).size = m := by
  simp [rowF, Array.size_zip, hA, hB, hD]

/-- Reading a zip-map row's flattened chunk `c`: the component chunks. -/
private theorem rowF_read {A : Array C.Point} {B D : Array C.ScalarField} {m c : ℕ}
    (hA : A.size = m) (hB : B.size = m) (hD : D.size = m) (hc : c < m) :
    (rowF C (A, B, D))[c]! = (A[c]!, B[c]!, D[c]!) := by
  have hzz : c < (B.zip D).size := by
    simp only [Array.size_zip, hB, hD]
    omega
  have hz : c < (A.zip (B.zip D)).size := by
    simp only [Array.size_zip, hA, hB, hD]
    omega
  show ((A.zip (B.zip D)).map (fun ce => (ce.1, ce.2.1, ce.2.2)))[c]! = _
  rw [getBang_map _ _ _ hz, getElem!_pos _ c hz,
    getElem!_pos A c (by omega), getElem!_pos B c (by omega),
    getElem!_pos D c (by omega)]
  simp [Array.getElem_zip]

end StreamRead

section RegionReads

variable {σ : SRS C.Point} {nc : ℕ} {cvk : KimchiVK C nc}
  {cp : KimchiProof C nc} {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)}

/-- Blocks stay inside their region: `q·nc + c < Q·nc`. -/
private theorem block_lt {q Q c nc : ℕ} (hq : q < Q) (hc : c < nc) :
    q * nc + c < Q * nc := by
  calc q * nc + c < (q + 1) * nc := by rw [Nat.succ_mul]; omega
    _ ≤ Q * nc := Nat.mul_le_mul_right nc hq

/-- A zip-map block array is uniformly `nc`-chunked: every flattened row has `nc`
entries — a type fact of the checked records. -/
private theorem zipBlock_uniform {m : ℕ} {A : Vector (Vector C.Point nc) m}
    {B : Vector (Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)) m} :
    ∀ a ∈ (A.zip B).toArray.map (zipRow C), (rowF C a).size = nc := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Array.exists_of_mem_map ha
  exact rowF_size C (by simp) (by simp) (by simp)

/-- The seven literal rows (`z` + six selectors) are uniformly `nc`-chunked. -/
private theorem litBlock_uniform :
    ∀ a ∈ litRows C cvk cp, (rowF C a).size = nc := by
  intro a ha
  simp only [litRows, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact rowF_size C (by simp) (by simp) (by simp)

/-- **Witness-region read**: the flat stream at `nc + 1 + (7+q)·nc + c` is witness
column `q`'s chunk `c` with its claims. -/
private theorem stream_read_w (q c : ℕ) (hq : q < 15) (hc : c < nc) :
    (flatRows C (runLogicalP C σ cvk cp pub pe))[nc + 1 + (7 + q) * nc + c]!
      = ((cp.wComm[q]).toArray[c]!, (cp.evals.w[q]).zeta.toArray[c]!,
          (cp.evals.w[q]).zetaOmega.toArray[c]!) := by
  rw [stream_decomp]
  have hsPub : (rowF C ((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray,
      pe.zetaOmega.toArray)).size = nc :=
    rowF_size C (by simp) (by simp) (by simp)
  have hsFt : (rowF C (#[runFtComm C σ cvk cp pub],
      #[runFtEval0P C σ cvk cp pub
          (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
      #[cp.ftEval1])).size = 1 := rowF_size C rfl rfl rfl
  have hs7 : (Array.flatMap (rowF C) (litRows C cvk cp)).size = 7 * nc := by
    rw [flatMap_uniform_size _ _ nc (litBlock_uniform C)]
    simp [litRows]
  have hzipW : ((cp.wComm.zip cp.evals.w).toArray.map (zipRow C)).size = 15 := by
    simp
  have hsW : (Array.flatMap (rowF C)
      ((cp.wComm.zip cp.evals.w).toArray.map (zipRow C))).size = 15 * nc := by
    rw [flatMap_uniform_size _ _ nc (zipBlock_uniform C), hzipW]
  rw [getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7, hsW]
      have h2 : (7 + q) * nc = 7 * nc + q * nc := by ring
      have := block_lt hq hc
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7, hsW]
      have h2 : (7 + q) * nc = 7 * nc + q * nc := by ring
      have := block_lt hq hc
      omega),
    getBang_append_at _ _ _ (q * nc + c) (by
      simp only [Array.size_append, hsPub, hsFt, hs7]
      have h2 : (7 + q) * nc = 7 * nc + q * nc := by ring
      omega)
      (by
        rw [hsW]
        exact block_lt hq hc),
    flatMap_uniform_read _ _ nc (zipBlock_uniform C) q c
      (by rw [hzipW]; omega) hc]
  have hread : ((cp.wComm.zip cp.evals.w).toArray.map (zipRow C))[q]!
      = zipRow C (cp.wComm[q], cp.evals.w[q]) := by
    rw [getBang_map _ _ _ (by simp; omega), getElem!_pos _ q (by simp; omega)]
    congr 1
    simp
  rw [hread]
  exact rowF_read C (by simp) (by simp) (by simp) hc

/-- **Literal-region read** (`z` + the six selectors): the flat stream at
`nc + 1 + k·nc + c` is literal row `k`'s chunk `c`. -/
private theorem stream_read_lit (k c : ℕ) (hk : k < 7) (hc : c < nc) :
    (flatRows C (runLogicalP C σ cvk cp pub pe))[nc + 1 + k * nc + c]!
      = (((litRows C cvk cp)[k]!).1[c]!, ((litRows C cvk cp)[k]!).2.1[c]!,
          ((litRows C cvk cp)[k]!).2.2[c]!) := by
  rw [stream_decomp]
  have hsPub : (rowF C ((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray,
      pe.zetaOmega.toArray)).size = nc :=
    rowF_size C (by simp) (by simp) (by simp)
  have hsFt : (rowF C (#[runFtComm C σ cvk cp pub],
      #[runFtEval0P C σ cvk cp pub
          (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
      #[cp.ftEval1])).size = 1 := rowF_size C rfl rfl rfl
  have hs7 : (Array.flatMap (rowF C) (litRows C cvk cp)).size = 7 * nc := by
    rw [flatMap_uniform_size _ _ nc (litBlock_uniform C)]
    simp [litRows]
  rw [getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7]
      have := block_lt hk hc
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7]
      have := block_lt hk hc
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7]
      have := block_lt hk hc
      omega),
    getBang_append_at _ _ _ (k * nc + c) (by
      simp only [Array.size_append, hsPub, hsFt]
      omega)
      (by
        rw [hs7]
        exact block_lt hk hc),
    flatMap_uniform_read _ _ nc (litBlock_uniform C) k c
      (by simp [litRows]; omega) hc]
  have hkm : k < (litRows C cvk cp).size := by simp [litRows]; omega
  have hcomp : ((((litRows C cvk cp)[k]!).1.size = nc
      ∧ ((litRows C cvk cp)[k]!).2.1.size = nc)
      ∧ ((litRows C cvk cp)[k]!).2.2.size = nc) := by
    rw [getElem!_pos _ k hkm]
    interval_cases k <;> refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [litRows]
  have := rowF_read C hcomp.1.1 hcomp.1.2 hcomp.2 hc
    (A := ((litRows C cvk cp)[k]!).1) (B := ((litRows C cvk cp)[k]!).2.1)
    (D := ((litRows C cvk cp)[k]!).2.2)
  rw [show ((litRows C cvk cp)[k]!
      : Array C.Point × Array C.ScalarField × Array C.ScalarField)
      = (((litRows C cvk cp)[k]!).1, ((litRows C cvk cp)[k]!).2.1,
          ((litRows C cvk cp)[k]!).2.2) from rfl]
  exact this

/-- **Coefficient-region read**: the flat stream at `nc + 1 + (22+q)·nc + c`. -/
private theorem stream_read_c (q c : ℕ) (hq : q < 15) (hc : c < nc) :
    (flatRows C (runLogicalP C σ cvk cp pub pe))[nc + 1 + (22 + q) * nc + c]!
      = ((cvk.coefficientsComm[q]).toArray[c]!,
          (cp.evals.coefficients[q]).zeta.toArray[c]!,
          (cp.evals.coefficients[q]).zetaOmega.toArray[c]!) := by
  rw [stream_decomp]
  have hsPub : (rowF C ((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray,
      pe.zetaOmega.toArray)).size = nc :=
    rowF_size C (by simp) (by simp) (by simp)
  have hsFt : (rowF C (#[runFtComm C σ cvk cp pub],
      #[runFtEval0P C σ cvk cp pub
          (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
      #[cp.ftEval1])).size = 1 := rowF_size C rfl rfl rfl
  have hs7 : (Array.flatMap (rowF C) (litRows C cvk cp)).size = 7 * nc := by
    rw [flatMap_uniform_size _ _ nc (litBlock_uniform C)]
    simp [litRows]
  have hsW : (Array.flatMap (rowF C)
      ((cp.wComm.zip cp.evals.w).toArray.map (zipRow C))).size = 15 * nc := by
    rw [flatMap_uniform_size _ _ nc (zipBlock_uniform C)]
    simp
  have hzipC : ((cvk.coefficientsComm.zip cp.evals.coefficients).toArray.map
      (zipRow C)).size = 15 := by
    simp
  have hsC : (Array.flatMap (rowF C)
      ((cvk.coefficientsComm.zip cp.evals.coefficients).toArray.map
        (zipRow C))).size = 15 * nc := by
    rw [flatMap_uniform_size _ _ nc (zipBlock_uniform C), hzipC]
  rw [getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7, hsW, hsC]
      have h2 : (22 + q) * nc = 22 * nc + q * nc := by ring
      have := block_lt hq hc
      omega),
    getBang_append_at _ _ _ (q * nc + c) (by
      simp only [Array.size_append, hsPub, hsFt, hs7, hsW]
      have h2 : (22 + q) * nc = 7 * nc + 15 * nc + q * nc := by ring
      omega)
      (by
        rw [hsC]
        exact block_lt hq hc),
    flatMap_uniform_read _ _ nc (zipBlock_uniform C) q c
      (by rw [hzipC]; omega) hc]
  have hread : ((cvk.coefficientsComm.zip cp.evals.coefficients).toArray.map
      (zipRow C))[q]!
      = zipRow C (cvk.coefficientsComm[q], cp.evals.coefficients[q]) := by
    rw [getBang_map _ _ _ (by simp; omega), getElem!_pos _ q (by simp; omega)]
    congr 1
    simp
  rw [hread]
  exact rowF_read C (by simp) (by simp) (by simp) hc

/-- **σ-region read**: the flat stream at `nc + 1 + (37+q)·nc + c`. -/
private theorem stream_read_s (q c : ℕ) (hq : q < 6) (hc : c < nc) :
    (flatRows C (runLogicalP C σ cvk cp pub pe))[nc + 1 + (37 + q) * nc + c]!
      = ((cvk.sigmaComm[q]).toArray[c]!, (cp.evals.s[q]).zeta.toArray[c]!,
          (cp.evals.s[q]).zetaOmega.toArray[c]!) := by
  rw [stream_decomp]
  have hsPub : (rowF C ((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray,
      pe.zetaOmega.toArray)).size = nc :=
    rowF_size C (by simp) (by simp) (by simp)
  have hsFt : (rowF C (#[runFtComm C σ cvk cp pub],
      #[runFtEval0P C σ cvk cp pub
          (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
      #[cp.ftEval1])).size = 1 := rowF_size C rfl rfl rfl
  have hs7 : (Array.flatMap (rowF C) (litRows C cvk cp)).size = 7 * nc := by
    rw [flatMap_uniform_size _ _ nc (litBlock_uniform C)]
    simp [litRows]
  have hsW : (Array.flatMap (rowF C)
      ((cp.wComm.zip cp.evals.w).toArray.map (zipRow C))).size = 15 * nc := by
    rw [flatMap_uniform_size _ _ nc (zipBlock_uniform C)]
    simp
  have hsC : (Array.flatMap (rowF C)
      ((cvk.coefficientsComm.zip cp.evals.coefficients).toArray.map
        (zipRow C))).size = 15 * nc := by
    rw [flatMap_uniform_size _ _ nc (zipBlock_uniform C)]
    simp
  have hzipS : (((cvk.sigmaComm.take 6).zip cp.evals.s).toArray.map
      (zipRow C)).size = 6 := by
    simp
  rw [getBang_append_at _ _ _ (q * nc + c) (by
      simp only [Array.size_append, hsPub, hsFt, hs7, hsW, hsC]
      have h2 : (37 + q) * nc = 7 * nc + 15 * nc + 15 * nc + q * nc := by ring
      omega)
      (by
        rw [flatMap_uniform_size _ _ nc (zipBlock_uniform C), hzipS]
        exact block_lt hq hc),
    flatMap_uniform_read _ _ nc (zipBlock_uniform C) q c
      (by rw [hzipS]; omega) hc]
  have hread : ((((cvk.sigmaComm.take 6).zip cp.evals.s).toArray.map
      (zipRow C)))[q]!
      = zipRow C (cvk.sigmaComm[q], cp.evals.s[q]) := by
    rw [getBang_map _ _ _ (by simp; omega), getElem!_pos _ q (by simp; omega)]
    congr 1
    simp
    rfl
  rw [hread]
  exact rowF_read C (by simp) (by simp) (by simp) hc

/-- **Public-region read**: the flat stream at `c` is public chunk `c`. -/
private theorem stream_read_pub (c : ℕ) (hc : c < nc) :
    (flatRows C (runLogicalP C σ cvk cp pub pe))[c]!
      = ((publicCommitment C σ cvk pub).toArray[c]!, pe.zeta.toArray[c]!,
          pe.zetaOmega.toArray[c]!) := by
  rw [stream_decomp]
  have hsPub : (rowF C ((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray,
      pe.zetaOmega.toArray)).size = nc :=
    rowF_size C (by simp) (by simp) (by simp)
  rw [getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub]
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub]
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub]
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub]
      omega),
    getBang_append_left _ _ _ (by rw [hsPub]; omega)]
  exact rowF_read C (by simp) (by simp) (by simp) hc

/-- **The stream size**: the flat stream has `44·nc + 1` rows. -/
private theorem stream_size :
    (flatRows C (runLogicalP C σ cvk cp pub pe)).size = 44 * nc + 1 := by
  rw [stream_decomp]
  have hsPub : (rowF C ((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray,
      pe.zetaOmega.toArray)).size = nc :=
    rowF_size C (by simp) (by simp) (by simp)
  have hsFt : (rowF C (#[runFtComm C σ cvk cp pub],
      #[runFtEval0P C σ cvk cp pub
          (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
      #[cp.ftEval1])).size = 1 := rowF_size C rfl rfl rfl
  have hs7 : (Array.flatMap (rowF C) (litRows C cvk cp)).size = 7 * nc := by
    rw [flatMap_uniform_size _ _ nc (litBlock_uniform C)]
    simp [litRows]
  have hsW : (Array.flatMap (rowF C)
      ((cp.wComm.zip cp.evals.w).toArray.map (zipRow C))).size = 15 * nc := by
    rw [flatMap_uniform_size _ _ nc (zipBlock_uniform C)]
    simp
  have hsC : (Array.flatMap (rowF C)
      ((cvk.coefficientsComm.zip cp.evals.coefficients).toArray.map
        (zipRow C))).size = 15 * nc := by
    rw [flatMap_uniform_size _ _ nc (zipBlock_uniform C)]
    simp
  have hsS : (Array.flatMap (rowF C)
      (((cvk.sigmaComm.take 6).zip cp.evals.s).toArray.map (zipRow C))).size
      = 6 * nc := by
    rw [flatMap_uniform_size _ _ nc (zipBlock_uniform C)]
    simp
  simp only [Array.size_append, hsPub, hsFt, hs7, hsW, hsC, hsS]
  ring

end RegionReads

/-! ## The chunked wire correspondence and the public-commitment link -/

/-- Chunk windows are additive in the polynomial. -/
private theorem chunkPoly_add {F : Type*} [Field F] (m : ℕ) (p q : Polynomial F)
    (i : ℕ) : chunkPoly m (p + q) i = chunkPoly m p i + chunkPoly m q i := by
  unfold chunkPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_add, map_add]

/-- Chunk windows commute with scalar multiplication. -/
private theorem chunkPoly_smul {F : Type*} [Field F] (m : ℕ) (a : F) (p : Polynomial F)
    (i : ℕ) : chunkPoly m (a • p) i = a • chunkPoly m p i := by
  unfold chunkPoly
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_smul, Polynomial.smul_monomial]

/-- The unblinded commitment is additive in the polynomial. -/
private theorem commitPoly_add {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (p q : Polynomial F) :
    commitPoly σ (p + q) = commitPoly σ p + commitPoly σ q := by
  unfold commitPoly commitGen
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.coeff_add, add_smul]

/-- The unblinded commitment commutes with scalar multiplication. -/
private theorem commitPoly_smul {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (a : F) (p : Polynomial F) :
    commitPoly σ (a • p) = a • commitPoly σ p := by
  unfold commitPoly commitGen
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.coeff_smul, smul_eq_mul, mul_smul]

/-- Chunk commitments distribute over scalar-weighted polynomial sums. -/
private theorem commitPolyChunk_sum {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] (σ : SRS G) {ι : Type*} (s : Finset ι) (a : ι → F)
    (q : ι → Polynomial F) (c : ℕ) :
    commitPolyChunk σ (∑ j ∈ s, a j • q j) c
      = ∑ j ∈ s, a j • commitPolyChunk σ (q j) c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold commitPolyChunk chunkPoly
    simp [commitPoly, commitGen]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, ← ih]
    unfold commitPolyChunk
    rw [chunkPoly_add, commitPoly_add, chunkPoly_smul, commitPoly_smul]

/-- Group-valued left folds accumulate to sums. -/
private theorem addFoldl_aux {α G : Type*} [AddCommMonoid G] (f : α → G) (l : List α)
    (acc : G) :
    (l.foldl (fun a x => a + f x) acc) = acc + ∑ i : Fin l.length, f l[i] := by
  induction l generalizing acc with
  | nil => simp
  | cons x t ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [add_assoc]

/-- **The checked key–index correspondence**: the committed chunk columns are the
circuit's own (`VKCorresponds`, through the total `comms` view), the scalar-side
parameters match (the domain generator, the zero-knowledge row count, the shifts, the
`ft_eval0` endo coefficient, and the Poseidon MDS — read off the fr-sponge table), AND
the Lagrange-basis chunk commitments over the public region are the basis polynomials'
own chunk commitments. The Lagrange pin is what binds the proof-carried public
evaluations (the public batch row) to the circuit's public input: the verifier
COMPUTES the public commitment from these key entries. Adjudicated numerically, per
chunk, by `check_vk_correspond`. -/
def KimchiVK.Corresponds {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] {nc : ℕ} {n : ℕ}
    (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (idx : Index C.ScalarField n) : Prop :=
  VKCorresponds σ nc cvk.comms idx
    ∧ cvk.omega = idx.omega
    ∧ cvk.zkRows = idx.zkRows
    ∧ (fun i : Fin 7 => cvk.shifts[i]) = idx.shifts
    ∧ cvk.endo = idx.endoBase
    ∧ mdsOfParams cvk.frParams = idx.mds
    ∧ ∀ (j : Fin n), (j : ℕ) < idx.publicCount →
        ∀ (hj : (j : ℕ) < cvk.lagrangeBasis.size) (c : Fin nc),
          (cvk.lagrangeBasis[(j : ℕ)]'hj)[c]
            = commitPolyChunk σ
                (columnPoly idx.omega (Kimchi.Permutation.rowIndicator j)) (c : ℕ)

/-- **The public commitment corresponds**: under the Lagrange chunk pin, the deployed
verifier's per-chunk public commitment is the per-chunk masked commitment of the
NEGATED public interpolant — the `pubC` feed of the reduction. The `.val`-scalar
collapse is supplied per curve (`hsmul`). -/
private theorem publicCommitment_corresponds [Module C.ScalarField C.Point]
    (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) {n : ℕ}
    [NeZero n] (idx : Index C.ScalarField n)
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a.val • P = a • P)
    (hlag : ∀ (j : Fin n), (j : ℕ) < idx.publicCount →
      ∀ (hj : (j : ℕ) < cvk.lagrangeBasis.size) (c : Fin nc),
        (cvk.lagrangeBasis[(j : ℕ)]'hj)[c]
          = commitPolyChunk σ
              (columnPoly idx.omega (Kimchi.Permutation.rowIndicator j)) (c : ℕ))
    (hlagsz : pub.size ≤ cvk.lagrangeBasis.size)
    (hpub : pub.size = idx.publicCount)
    (c : Fin nc) :
    (publicCommitment C σ cvk pub)[c]
      = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hω := idx.omega_prim
  have hpc : idx.publicCount ≤ n := idx.public_le.trans (Nat.sub_le _ _)
  -- the negated interpolant as a Lagrange-basis combination
  have hpoly : -(idx.pubPoly (pubView idx pub))
      = ∑ j : Fin n, (-(pubAt idx (pubView idx pub) j))
          • columnPoly idx.omega (Kimchi.Permutation.rowIndicator j) := by
    rw [show idx.pubPoly (pubView idx pub)
        = columnPoly idx.omega (pubAt idx (pubView idx pub)) from rfl,
      Kimchi.Permutation.columnPoly_eq_sum_indicator hω hn,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => (neg_smul _ _).symm
  unfold commitPolyMaskedChunk
  rw [hpoly, commitPolyChunk_sum]
  unfold publicCommitment
  by_cases h0 : pub.size = 0
  · rw [if_pos h0]
    have hzero : ∀ j : Fin n, (-(pubAt idx (pubView idx pub) j))
        • commitPolyChunk σ
            (columnPoly idx.omega (Kimchi.Permutation.rowIndicator j)) (c : ℕ)
          = 0 := by
      intro j
      have hz : pubAt idx (pubView idx pub) j = 0 := by
        unfold pubAt
        rw [dif_neg (by omega)]
      rw [hz, neg_zero, zero_smul]
    rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero, zero_add]
    simp
  · rw [if_neg h0]
    rw [show (Vector.ofFn (fun (c : Fin nc) =>
        ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).foldl
          (fun acc Pp => acc + (-Pp.2).val • Pp.1[c]) 0 + σ.h))[c]
      = ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).foldl
          (fun acc Pp => acc + (-Pp.2).val • Pp.1[c]) 0 + σ.h from by
        simp]
    congr 1
    rw [← Array.foldl_toList, addFoldl_aux, zero_add]
    have hzipsz : ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).size
        = pub.size := by
      simp only [Array.size_zip, Array.size_extract]
      omega
    have hlen : ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList.length
        = pub.size := by
      rw [Array.length_toList, hzipsz]
    -- both sides as `range`-indexed sums of total functions of the row number
    calc (∑ i : Fin ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList.length,
          (-(((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList[i]).2).val
            • (((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList[i]).1[c])
        = ∑ i : Fin ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList.length,
            (fun m => (-(pub.getD m 0)).val
              • ((cvk.lagrangeBasis.getD m (Vector.replicate nc 0))[c])) (i : ℕ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hilt : (i : ℕ) < pub.size := by
            have := i.isLt
            omega
          have hie : (i : ℕ)
              < ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).size := by omega
          have hextr : (i : ℕ) < (cvk.lagrangeBasis.extract 0 pub.size).size := by
            rw [Array.size_extract]
            omega
          have hentry : ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList[i]
              = ((cvk.lagrangeBasis.extract 0 pub.size)[(i : ℕ)]'hextr,
                pub[(i : ℕ)]'hilt) := by
            rw [show ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList[i]
                = ((cvk.lagrangeBasis.extract 0 pub.size).zip pub)[(i : ℕ)]'hie from
              Array.getElem_toList _]
            exact Array.getElem_zip
          rw [hentry]
          have hib : (i : ℕ) < cvk.lagrangeBasis.size := by omega
          have hlagread : (cvk.lagrangeBasis.extract 0 pub.size)[(i : ℕ)]'hextr
              = cvk.lagrangeBasis.getD (i : ℕ) (Vector.replicate nc 0) := by
            rw [Array.getElem_extract,
              show cvk.lagrangeBasis.getD (i : ℕ) (Vector.replicate nc 0)
                = cvk.lagrangeBasis[(i : ℕ)]'hib from by simp [Array.getD, hib]]
            congr 1
            omega
          rw [hlagread, show pub[(i : ℕ)]'hilt = pub.getD (i : ℕ) 0 from by
            simp [Array.getD, hilt]]
      _ = ∑ m ∈ Finset.range pub.size,
            (-(pub.getD m 0)).val
              • ((cvk.lagrangeBasis.getD m (Vector.replicate nc 0))[c]) := by
          rw [Fin.sum_univ_eq_sum_range
            (fun m => (-(pub.getD m 0)).val
              • ((cvk.lagrangeBasis.getD m (Vector.replicate nc 0))[c]))
            (((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList.length), hlen]
      _ = ∑ m ∈ Finset.range pub.size,
            (if h : m < n then (-(pubAt idx (pubView idx pub) ⟨m, h⟩))
              • commitPolyChunk σ (columnPoly idx.omega
                  (Kimchi.Permutation.rowIndicator ⟨m, h⟩)) (c : ℕ) else 0) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          have hmlt : m < pub.size := Finset.mem_range.mp hm
          have hmn : m < n := by omega
          rw [dif_pos hmn]
          have hjp : ((⟨m, hmn⟩ : Fin n) : ℕ) < idx.publicCount := by
            show m < idx.publicCount
            omega
          have hjl : ((⟨m, hmn⟩ : Fin n) : ℕ) < cvk.lagrangeBasis.size := by
            show m < cvk.lagrangeBasis.size
            omega
          have hpubAt : pubAt idx (pubView idx pub) ⟨m, hmn⟩ = pub.getD m 0 := by
            unfold pubAt
            rw [dif_pos hjp]
            rfl
          rw [hpubAt, ← hlag ⟨m, hmn⟩ hjp hjl c, hsmul]
          congr 2
          simp [Array.getD, hjl]
      _ = ∑ m ∈ Finset.range n,
            (if h : m < n then (-(pubAt idx (pubView idx pub) ⟨m, h⟩))
              • commitPolyChunk σ (columnPoly idx.omega
                  (Kimchi.Permutation.rowIndicator ⟨m, h⟩)) (c : ℕ) else 0) := by
          have hsub : Finset.range pub.size ⊆ Finset.range n := by
            intro x hx
            have := Finset.mem_range.mp hx
            exact Finset.mem_range.mpr (by omega)
          refine Finset.sum_subset hsub ?_
          intro m hmn hmp
          have hmn' : m < n := Finset.mem_range.mp hmn
          have hmp' : ¬ m < pub.size := fun h => hmp (Finset.mem_range.mpr h)
          rw [dif_pos hmn']
          have hz : pubAt idx (pubView idx pub) ⟨m, hmn'⟩ = 0 := by
            unfold pubAt
            rw [dif_neg (by show ¬ m < idx.publicCount; omega)]
          rw [hz, neg_zero, zero_smul]
      _ = ∑ j : Fin n, (fun m => if h : m < n then
            (-(pubAt idx (pubView idx pub) ⟨m, h⟩))
              • commitPolyChunk σ (columnPoly idx.omega
                  (Kimchi.Permutation.rowIndicator ⟨m, h⟩)) (c : ℕ) else 0) (j : ℕ) :=
          (Fin.sum_univ_eq_sum_range
            (fun m => if h : m < n then (-(pubAt idx (pubView idx pub) ⟨m, h⟩))
              • commitPolyChunk σ (columnPoly idx.omega
                  (Kimchi.Permutation.rowIndicator ⟨m, h⟩)) (c : ℕ) else 0) n).symm
      _ = ∑ j : Fin n, (-(pubAt idx (pubView idx pub) j))
            • commitPolyChunk σ (columnPoly idx.omega
                (Kimchi.Permutation.rowIndicator j)) (c : ℕ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          beta_reduce
          rw [dif_pos j.isLt]

/-! ## The scalar-side reconciliations: the run's claims are the abstract batch's -/

section ScalarReconcile

variable {σ : SRS C.Point} {nc : ℕ} {cvk : KimchiVK C nc}
  {cp : KimchiProof C nc} {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)}
  {v u : C.ScalarField}

/-- The verifier's squaring ladder computes the power: `powPow2 x k = x ^ 2 ^ k`. -/
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

/-- Extensionality for the linearization's evaluation record. -/
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

/-- Every stream position lies inside the `44·nc + 1` flat rows. -/
private theorem streamPos_lt (nc : ℕ) (i : Fin 44) (c : ℕ) (hc : c < nc) :
    streamPos nc i c < 44 * nc + 1 := by
  have hi := i.isLt
  unfold streamPos
  split_ifs with h1
  · omega
  · have := block_lt (show (i : ℕ) - 1 < 43 by omega) hc
    omega

/-- `streamPos` at the public row. -/
private theorem streamPos_pubRow (nc : ℕ) (ch : ℕ) :
    streamPos nc pubRow ch = ch := by
  simp only [streamPos, pubRow]
  rw [if_pos (by omega)]

/-- `streamPos` at the accumulator row (`0·nc` kept for the region-read shape). -/
private theorem streamPos_zRow (nc : ℕ) (ch : ℕ) :
    streamPos nc zRow ch = nc + 1 + 0 * nc + ch := by
  simp only [streamPos, zRow]
  rw [if_neg (by omega), show (1 : ℕ) - 1 = 0 from rfl]

/-- `streamPos` at a selector row. -/
private theorem streamPos_selRow (nc : ℕ) (j : Fin 6) (ch : ℕ) :
    streamPos nc (selRow j) ch = nc + 1 + (1 + (j : ℕ)) * nc + ch := by
  simp only [streamPos, selRow]
  rw [if_neg (by omega), show 2 + (j : ℕ) - 1 = 1 + (j : ℕ) from by omega]

/-- `streamPos` at a witness row. -/
private theorem streamPos_wRow (nc : ℕ) (q : Fin 15) (ch : ℕ) :
    streamPos nc (wRow q) ch = nc + 1 + (7 + (q : ℕ)) * nc + ch := by
  simp only [streamPos, wRow]
  rw [if_neg (by omega), show 8 + (q : ℕ) - 1 = 7 + (q : ℕ) from by omega]

/-- `streamPos` at a coefficient row. -/
private theorem streamPos_cRow (nc : ℕ) (q : Fin 15) (ch : ℕ) :
    streamPos nc (cRow q) ch = nc + 1 + (22 + (q : ℕ)) * nc + ch := by
  simp only [streamPos, cRow]
  rw [if_neg (by omega), show 23 + (q : ℕ) - 1 = 22 + (q : ℕ) from by omega]

/-- `streamPos` at a σ row. -/
private theorem streamPos_sRow (nc : ℕ) (i : Fin 6) (ch : ℕ) :
    streamPos nc (sRow i) ch = nc + 1 + (37 + (i : ℕ)) * nc + ch := by
  simp only [streamPos, sRow]
  rw [if_neg (by omega), show 38 + (i : ℕ) - 1 = 37 + (i : ℕ) from by omega]

/-- Reading the run input's evaluation matrix at a stream position: the flat row's
claim pair. -/
private theorem runEvals_read (i : Fin 44) (c : ℕ) (hc : c < nc) :
    (runInputP C σ cvk cp pub pe v u).evals[streamPos nc i c]!
      = #[((flatRows C (runLogicalP C σ cvk cp pub pe))[streamPos nc i c]!).2.1,
          ((flatRows C (runLogicalP C σ cvk cp pub pe))[streamPos nc i c]!).2.2] := by
  show ((flatRows C (runLogicalP C σ cvk cp pub pe)).map
      (fun r => #[r.2.1, r.2.2]))[streamPos nc i c]! = _
  rw [getBang_map _ _ _ (by
    rw [stream_size C]
    exact streamPos_lt _ i c hc)]

/-- A `Fin nc`-indexed power sum whose entries read an `nc`-sized array is that
array's chunk combination. -/
private theorem sum_readsTo (xM : C.ScalarField) (w : Array C.ScalarField)
    (hw : w.size = nc) (f : Fin nc → C.ScalarField)
    (hf : ∀ ch : Fin nc, f ch = w[(ch : ℕ)]!) :
    (∑ ch : Fin nc, xM ^ (ch : ℕ) * f ch) = combineAt xM w := by
  rw [combineAt_eq_sum]
  refine (Fintype.sum_equiv (finCongr hw) _ _ fun i => ?_).symm
  rw [hf (finCongr hw i)]
  simp only [finCongr_apply, Fin.val_cast, Fin.getElem_fin]
  rw [getElem!_pos w (i : ℕ) i.isLt]

/-- **The chunk-combined claimed record is the run's own** (`evals.combine`): the
abstract `claimedEvals`, fed the run's flat claims at the stream positions, IS the
verifier's combined record `cp.linEvals` at the run's combination powers. Pure layout
reading through the region reads. -/
private theorem claimedEvals_run_eq :
    claimedEvals (runZetaM C σ cvk cp pub) (runZetaOmegaM C σ cvk cp pub)
        (fun (i : Fin 44) (ch : Fin nc) (j : Fin 2) =>
          ((runInputP C σ cvk cp pub pe v u).evals[streamPos nc i
              (ch : ℕ)]!)[(j : ℕ)]!)
      = cp.linEvals (runZetaM C σ cvk cp pub) (runZetaOmegaM C σ cvk cp pub) := by
  refine evals_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · funext col
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (wRow col) (ch : ℕ) ch.isLt, streamPos_wRow,
      stream_read_w C (col : ℕ) (ch : ℕ) col.isLt ch.isLt]
    rfl
  · funext col
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (wRow col) (ch : ℕ) ch.isLt, streamPos_wRow,
      stream_read_w C (col : ℕ) (ch : ℕ) col.isLt ch.isLt]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C zRow (ch : ℕ) ch.isLt, streamPos_zRow,
      stream_read_lit C 0 (ch : ℕ) (by omega) ch.isLt]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C zRow (ch : ℕ) ch.isLt, streamPos_zRow,
      stream_read_lit C 0 (ch : ℕ) (by omega) ch.isLt]
    rfl
  · funext i
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (sRow i) (ch : ℕ) ch.isLt, streamPos_sRow,
      stream_read_s C (i : ℕ) (ch : ℕ) i.isLt ch.isLt]
    rfl
  · funext col
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (cRow col) (ch : ℕ) ch.isLt, streamPos_cRow,
      stream_read_c C (col : ℕ) (ch : ℕ) col.isLt ch.isLt]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 0) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C (1 + ((0 : Fin 6) : ℕ)) (ch : ℕ) (by decide) ch.isLt]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 1) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C (1 + ((1 : Fin 6) : ℕ)) (ch : ℕ) (by decide) ch.isLt]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 2) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C (1 + ((2 : Fin 6) : ℕ)) (ch : ℕ) (by decide) ch.isLt]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 3) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C (1 + ((3 : Fin 6) : ℕ)) (ch : ℕ) (by decide) ch.isLt]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 4) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C (1 + ((4 : Fin 6) : ℕ)) (ch : ℕ) (by decide) ch.isLt]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 5) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C (1 + ((5 : Fin 6) : ℕ)) (ch : ℕ) (by decide) ch.isLt]
    rfl

/-- **The combined public claim is the run's own**: `claimedPub` at the stream's
public-row claims is the verifier's chunk-combined public evaluation. -/
private theorem claimedPub_run_eq :
    claimedPub (runZetaM C σ cvk cp pub)
        (fun (i : Fin 44) (ch : Fin nc) (j : Fin 2) =>
          ((runInputP C σ cvk cp pub pe v u).evals[streamPos nc i
              (ch : ℕ)]!)[(j : ℕ)]!)
      = combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray := by
  refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
  beta_reduce
  rw [runEvals_read C pubRow (ch : ℕ) ch.isLt, streamPos_pubRow,
    stream_read_pub C (ch : ℕ) ch.isLt]
  rfl

/-- **The constructed ft commitment is the double Maller collapse** (generic in the
`.val`-scalar bridge): the executable `runFtComm` — `combine(ζ^max, f_comm) −
(ζⁿ − 1).val • combine(ζ^max, t_comm)` — is the abstract `•`-combination
`ft_identity_of_chunks` consumes: `pScalar • ∑_c (ζ^max)^c • σ₆C_c
− (ζⁿ − 1) • ∑_j (ζ^max)^j • tCommⱼ`. -/
private theorem runFtComm_eq [Module C.ScalarField C.Point]
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a • P = a.val • P)
    {n : ℕ} (hn : cvk.n = n) :
    runFtComm C σ cvk cp pub
      = runPScalar C σ cvk cp pub
          • ∑ c : Fin nc,
              ((runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • (cvk.sigmaComm[6])[c]
        - ((runOracles C σ cvk cp pub).zeta ^ n - 1)
            • ∑ j : Fin cp.tComm.size,
                ((runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (j : ℕ)
                  • cp.tComm.getD (j : ℕ) 0 := by
  have hζM : runZetaM C σ cvk cp pub = (runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k := by
    unfold runZetaM
    rw [powPow2_eq]
  have hζN : runZetaN C σ cvk cp pub = (runOracles C σ cvk cp pub).zeta ^ n := by
    unfold runZetaN
    rw [powPow2_eq, ← hn]
    rfl
  unfold runFtComm runFComm
  rw [combineCommitments_eq hsmul, combineCommitments_eq hsmul, ← hsmul, hζM, hζN]
  congr 1
  · rw [combinedCommitment, Finset.smul_sum]
    have hmapsz : ((cvk.sigmaComm[6].map
        (fun P => (runPScalar C σ cvk cp pub).val • P)).toArray).size = nc := by
      simp
    refine Fintype.sum_equiv (finCongr hmapsz) _ _ fun i => ?_
    simp only [finCongr_apply, Fin.val_cast, Fin.getElem_fin, Vector.getElem_toArray,
      Vector.getElem_map]
    rw [← hsmul, ← mul_smul, ← mul_smul, mul_comm]
  · congr 1
    rw [combinedCommitment]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [Array.getD, j.isLt]

end ScalarReconcile

/-! ## The group-side reconciliation: the flat stream carries the abstract batch -/

section GroupReconcile

variable {σ : SRS C.Point} {nc : ℕ} {cvk : KimchiVK C nc}
  {cp : KimchiProof C nc} {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)}

/-- **The abstract 44-row chunked batch is the flat stream's commitment column**: at
every batch row and chunk, `batchC` — fed the checked witness/accumulator/public chunk
reads and the key's `comms` view — is the flat stream's commitment at the row's stream
position. The layout bridge `hbound₀` consumes. -/
private theorem batchC_eq_flat (i : Fin 44) (c : Fin nc) :
    batchC (fun (col : Fin 15) (c : Fin nc) => (cp.wComm[col])[c])
        (fun c => cp.zComm[c])
        (fun c => (publicCommitment C σ cvk pub)[c])
        cvk.comms i c
      = ((flatRows C (runLogicalP C σ cvk cp pub pe))[streamPos nc i
          (c : ℕ)]!).1 := by
  have hbr : ∀ (w : Vector C.Point nc), w.toArray[(c : ℕ)]! = w[c] := fun w => by
    rw [getElem!_pos w.toArray (c : ℕ) (by simp)]
    simp
  by_cases h1 : (i : ℕ) < 1
  · rw [show streamPos nc i (c : ℕ) = (c : ℕ) from by
        unfold streamPos
        rw [if_pos h1],
      stream_read_pub C (c : ℕ) c.isLt]
    simp only [batchC]
    rw [if_pos h1]
    exact (hbr _).symm
  · by_cases h2 : (i : ℕ) < 2
    · rw [show streamPos nc i (c : ℕ)
          = nc + 1 + 0 * nc + (c : ℕ) from by
            unfold streamPos
            rw [if_neg h1, show (i : ℕ) - 1 = 0 from by omega],
        stream_read_lit C 0 (c : ℕ) (by omega) c.isLt]
      simp only [batchC]
      rw [if_neg h1, if_pos h2]
      exact (hbr _).symm
    · by_cases h3 : (i : ℕ) < 8
      · rw [show streamPos nc i (c : ℕ)
            = nc + 1 + (1 + ((i : ℕ) - 2)) * nc + (c : ℕ) from by
              unfold streamPos
              rw [if_neg h1, show (i : ℕ) - 1 = 1 + ((i : ℕ) - 2) from by omega],
          stream_read_lit C (1 + ((i : ℕ) - 2)) (c : ℕ) (by omega) c.isLt]
        simp only [batchC]
        rw [if_neg h1, if_neg h2, dif_pos h3]
        obtain ⟨iv, hivlt⟩ := i
        have hlo : 2 ≤ iv := Nat.not_lt.mp h2
        have hhi : iv < 8 := h3
        interval_cases iv <;> exact (hbr _).symm
      · by_cases h4 : (i : ℕ) < 23
        · rw [show streamPos nc i (c : ℕ)
              = nc + 1 + (7 + ((i : ℕ) - 8)) * nc + (c : ℕ) from by
                unfold streamPos
                rw [if_neg h1, show (i : ℕ) - 1 = 7 + ((i : ℕ) - 8) from by omega],
            stream_read_w C ((i : ℕ) - 8) (c : ℕ) (by omega) c.isLt]
          simp only [batchC]
          rw [if_neg h1, if_neg h2, dif_neg h3, dif_pos h4]
          exact (hbr _).symm
        · by_cases h5 : (i : ℕ) < 38
          · rw [show streamPos nc i (c : ℕ)
                = nc + 1 + (22 + ((i : ℕ) - 23)) * nc + (c : ℕ) from by
                  unfold streamPos
                  rw [if_neg h1,
                    show (i : ℕ) - 1 = 22 + ((i : ℕ) - 23) from by omega],
              stream_read_c C ((i : ℕ) - 23) (c : ℕ) (by omega) c.isLt]
            simp only [batchC]
            rw [if_neg h1, if_neg h2, dif_neg h3, dif_neg h4, dif_pos h5]
            exact (hbr _).symm
          · rw [show streamPos nc i (c : ℕ)
                = nc + 1 + (37 + ((i : ℕ) - 38)) * nc + (c : ℕ) from by
                  unfold streamPos
                  rw [if_neg h1,
                    show (i : ℕ) - 1 = 37 + ((i : ℕ) - 38) from by
                      have := i.isLt
                      omega],
              stream_read_s C ((i : ℕ) - 38) (c : ℕ) (by
                have := i.isLt
                omega) c.isLt]
            simp only [batchC]
            rw [if_neg h1, if_neg h2, dif_neg h3, dif_neg h4, dif_neg h5]
            exact (hbr _).symm

end GroupReconcile

/-! ## The chunked run-level terminal roots -/

private instance : Inhabited IpaVesta.Point := ⟨0⟩
private instance : Inhabited IpaPallas.Point := ⟨0⟩

/-- **The run-level residue-free root (Vesta)**: from a genuine acceptance
`kimchiVerify σ cvk cp pub = true` of the checked records at production chunking
`nc · 2^σ.k = n`, the AGM path delivers the guarded
`Satisfies idx (pubView idx pub) wTab` — the assembled witness table of the algebraic
prover's own per-chunk representations. A deployed run reaches this root through the
wire boundary: the client parses with `Wire.{KimchiVK,KimchiProof}.check` (a checked
record cannot hold a ragged proof) and calls `kimchiVerify` on the result. The prover
supplies SRS-basis representations of the run's `44·nc + 1` flat segment rows
(`aRef`/`ρRef`) and of the `tComm` chunks (`aT`/`ρT`); everything else is derived
from the single reflected run: the openings seam `kimchiProof_sound_of_openings` is
fed directly (reference side: the representations at the stream positions; consumer
side: the eval pins of the run's one accepted opening), the public row is pinned
through `publicCommitment_corresponds` and the key's Lagrange chunk pin, and the
quotient `t := ftChunkAssembly σ.k cp.tComm.size aT` with its Maller identity comes
from the ft opening through `ft_identity_of_chunks` at the DOUBLE `ζ^{2^σ.k}`
collapse. The key–index hypothesis is the checked `KimchiVK.Corresponds` —
per-chunk `VKCorresponds`, the scalar pins, and the Lagrange pin. Axioms consumed:
`kimchi_fiat_shamir_vesta` plus the point-count-backed `Module` instance. No
`ζⁿ ≠ 1` guard: the public claims are proof-carried batch data, believed only
through binding — no barycentric reconciliation. The Vesta run-level root. -/
theorem kimchiVesta_run_sound_algebraic_ft (σ : SRS IpaVesta.Point) {nc : ℕ}
    (cvk : KimchiVK IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc)
    (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n) (hn : cvk.n = n)
    (hvk : cvk.Corresponds σ idx)
    (hpub : pub.size = idx.publicCount)
    (htpos : 0 < cp.tComm.size)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : kimchiVerify IpaVesta.curve σ cvk cp pub = true)
    (aRef : Fin (runInput IpaVesta.curve σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → Fp)
    (ρRef : Fin (runInput IpaVesta.curve σ cvk cp pub).commitments.size → Fp)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput IpaVesta.curve σ cvk cp pub).commitmentFn i)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → Fp) (ρT : Fin cp.tComm.size → Fp)
    (hTC : ∀ j : Fin cp.tComm.size, commit σ (aT j) (ρT j) = cp.tComm.getD (j : ℕ) 0)
    (hξ : (runInput IpaVesta.curve σ cvk cp pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaVesta.curve σ cvk cp pub).pointFn
          (runInput IpaVesta.curve σ cvk cp pub).evalFn)
    (hr : (runInput IpaVesta.curve σ cvk cp pub).evalscale
      ∉ badROf σ aRef (runInput IpaVesta.curve σ cvk cp pub).pointFn
          (runInput IpaVesta.curve σ cvk cp pub).evalFn
          (runInput IpaVesta.curve σ cvk cp pub).polyscale) :
    ∃ (badB : Finset Fp) (badG : Fp → Finset Fp) (badA : Fp → Fp → Finset Fp)
        (badZ : Fp → Fp → Fp → Polynomial Fp → Finset Fp)
        (wTab : Fin n → Fin 15 → Fp),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fp), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ((runOracles IpaVesta.curve σ cvk cp pub).beta ∉ badB →
          (runOracles IpaVesta.curve σ cvk cp pub).gamma
            ∉ badG (runOracles IpaVesta.curve σ cvk cp pub).beta →
          (runOracles IpaVesta.curve σ cvk cp pub).alpha
            ∉ badA (runOracles IpaVesta.curve σ cvk cp pub).beta
                (runOracles IpaVesta.curve σ cvk cp pub).gamma →
          (runOracles IpaVesta.curve σ cvk cp pub).zeta
            ∉ badZ (runOracles IpaVesta.curve σ cvk cp pub).beta
                (runOracles IpaVesta.curve σ cvk cp pub).gamma
                (runOracles IpaVesta.curve σ cvk cp pub).alpha
                (ftChunkAssembly σ.k cp.tComm.size aT) →
          (runOracles IpaVesta.curve σ cvk cp pub).zeta ≠ 1 →
          (runOracles IpaVesta.curve σ cvk cp pub).zeta
            ≠ idx.omega ^ (n - idx.zkRows) →
          Satisfies idx (pubView idx pub) wTab) := by
  obtain ⟨hvkc, homega, hzk, hshift, hendo, hmds, hlag⟩ := hvk
  -- (1) the body reflection: the guards and the warm acceptance
  obtain ⟨hlagsz, hpubn, haccept⟩ :=
    kimchiVerify_reflects IpaVesta.curve σ cvk cp pub hacc
  have hlt : ∀ (i : Fin 44) (c : Fin (nc)),
      streamPos (nc) i (c : ℕ)
        < (runInput IpaVesta.curve σ cvk cp pub).commitments.size := by
    intro i c
    show streamPos (nc) i (c : ℕ)
      < ((flatRows IpaVesta.curve (runLogicalP IpaVesta.curve σ cvk cp pub
          (runPubEvals IpaVesta.curve σ cvk cp pub))).map (·.1)).size
    rw [Array.size_map, stream_size IpaVesta.curve]
    exact streamPos_lt _ i _ c.isLt
  -- (2) the reference openings at the stream positions bind the abstract batch
  have hbound₀ : ∀ (i : Fin 44) (c : Fin (nc)),
      commit σ (aRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
          (ρRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
        = batchC (fun col c => (cp.wComm[col])[c]) (fun c => cp.zComm[c])
            (fun c => (publicCommitment IpaVesta.curve σ cvk pub)[c])
            cvk.comms i c := by
    intro i c
    rw [hrep ⟨streamPos (nc) i (c : ℕ), hlt i c⟩]
    show (runInput IpaVesta.curve σ cvk cp pub).commitments[streamPos
        (nc) i (c : ℕ)]'(hlt i c) = _
    rw [← getElem!_pos (runInput IpaVesta.curve σ cvk cp pub).commitments
      (streamPos (nc) i (c : ℕ)) (hlt i c)]
    show ((flatRows IpaVesta.curve (runLogicalP IpaVesta.curve σ cvk cp pub
        (runPubEvals IpaVesta.curve σ cvk cp pub))).map
          (·.1))[streamPos (nc) i (c : ℕ)]! = _
    rw [getBang_map _ _ _ (by
      rw [stream_size IpaVesta.curve]
      exact streamPos_lt _ i _ c.isLt)]
    exact (batchC_eq_flat IpaVesta.curve i c).symm
  -- (3) the public row pinned through the Lagrange chunk pin
  have hpubC : ∀ c : Fin (nc),
      (publicCommitment IpaVesta.curve σ cvk pub)[c]
        = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ) :=
    fun c => publicCommitment_corresponds IpaVesta.curve σ cvk pub idx
      (fun a P => (Pasta.vesta_smul_val a P).symm) hlag hlagsz hpub c
  -- (4) the openings seam, fed directly
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hnc hk hbind cvk.comms hvkc (pubView idx pub)
      (fun col c => (cp.wComm[col])[c]) (fun c => cp.zComm[c])
      (fun c => (publicCommitment IpaVesta.curve σ cvk pub)[c])
      hpubC
      (fun i c => aRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
      (fun i c => ρRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
      hbound₀
  refine ⟨badB, badG, badA, badZ,
    extractTable idx.omega (fun col => assembledRow σ.k (nc)
      (fun c => aRef ⟨streamPos (nc) (wRow col) (c : ℕ),
        hlt (wRow col) c⟩)),
    hbounds, ?_⟩
  intro hβ hγ hα hζ hζ1 hζb
  -- (5) the eval pins from the run's single accepted opening (flat arity)
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _
    (kimchi_fiat_shamir_vesta σ cvk cp pub) haccept
  have hpins := eval_pins_of_opening σ hbind
    (runInput IpaVesta.curve σ cvk cp pub).commitmentFn
    (runInput IpaVesta.curve σ cvk cp pub).pointFn aRef ρRef hrep
    (runInput IpaVesta.curve σ cvk cp pub).evalFn
    (runInput IpaVesta.curve σ cvk cp pub).polyscale
    (runInput IpaVesta.curve σ cvk cp pub).evalscale hξ hr a ρ hopen
  -- (6) the ft opening and the Maller identity at the double collapse
  obtain ⟨aft, ρft, hcomm_ft, heval_ft⟩ :=
    ft_opening_of_reflected_vesta σ cvk cp pub hbind haccept aRef ρRef hrep hξ hr
  have hCσ6 : ∀ c : Fin (nc),
      (cvk.sigmaComm[6])[c] = commitPolyChunk σ (idx.sigmaPoly 6) (c : ℕ) :=
    fun c => congrFun (congrArg (fun cm => cm.sigma 6) hvkc) c
  have hσ₆ : (idx.sigmaPoly 6).natDegree
      < nc * 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hcommit : commit σ aft ρft
      = runPScalar IpaVesta.curve σ cvk cp pub
          • ∑ c : Fin (nc),
              ((runOracles IpaVesta.curve σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • (cvk.sigmaComm[6])[c]
        - ((runOracles IpaVesta.curve σ cvk cp pub).zeta ^ n - 1)
            • ∑ j : Fin cp.tComm.size,
                ((runOracles IpaVesta.curve σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (j : ℕ)
                  • cp.tComm.getD (j : ℕ) 0 :=
    hcomm_ft.trans (runFtComm_eq IpaVesta.curve Pasta.vesta_smul_val hn)
  obtain ⟨htdeg, hteq0⟩ := ft_identity_of_chunks σ hbind (idx.sigmaPoly 6) hσ₆
    (fun c => (cvk.sigmaComm[6])[c]) hCσ6 htpos cp.tComm_le
    (fun j => cp.tComm.getD (j : ℕ) 0) aT ρT hTC
    (runPScalar IpaVesta.curve σ cvk cp pub)
    (runOracles IpaVesta.curve σ cvk cp pub).zeta
    (runFtEval0 IpaVesta.curve σ cvk cp pub) n hk aft ρft hcommit heval_ft
  -- (7) reconcile the derived identity into the consumer's shape
  have hce := claimedEvals_run_eq IpaVesta.curve (σ := σ) (cvk := cvk) (cp := cp)
    (pub := pub) (pe := runPubEvals IpaVesta.curve σ cvk cp pub)
    (v := (runVU IpaVesta.curve σ cvk cp pub).1)
    (u := (runVU IpaVesta.curve σ cvk cp pub).2)
  have hcpe := claimedPub_run_eq IpaVesta.curve (σ := σ) (cvk := cvk) (cp := cp)
    (pub := pub) (pe := runPubEvals IpaVesta.curve σ cvk cp pub)
    (v := (runVU IpaVesta.curve σ cvk cp pub).1)
    (u := (runVU IpaVesta.curve σ cvk cp pub).2)
  have hζM : runZetaM IpaVesta.curve σ cvk cp pub
      = (runOracles IpaVesta.curve σ cvk cp pub).zeta ^ 2 ^ σ.k := by
    unfold runZetaM
    rw [powPow2_eq]
  have hζwM : runZetaOmegaM IpaVesta.curve σ cvk cp pub
      = (idx.omega * (runOracles IpaVesta.curve σ cvk cp pub).zeta) ^ 2 ^ σ.k := by
    unfold runZetaOmegaM runZetaOmega
    rw [powPow2_eq, homega, mul_comm]
  unfold runPScalar runFtEval0 runFtEval0P runPubEval0 runLinEvals at hteq0
  rw [← hce, ← hcpe, hζM, hζwM, hn, hzk, homega, hendo, hmds, hshift] at hteq0
  -- (8) the per-row pins, at the consumer's two eval points
  have hpt : (runInput IpaVesta.curve σ cvk cp pub).pointFn
      = ![(runOracles IpaVesta.curve σ cvk cp pub).zeta,
          idx.omega * (runOracles IpaVesta.curve σ cvk cp pub).zeta] := by
    funext j
    fin_cases j
    · rfl
    · show (runOracles IpaVesta.curve σ cvk cp pub).zeta * cvk.omega = _
      rw [homega]
      exact mul_comm _ _
  rw [hpt] at hpins
  -- (9) feed the consumer
  exact himp (runOracles IpaVesta.curve σ cvk cp pub).beta
    (runOracles IpaVesta.curve σ cvk cp pub).gamma
    (runOracles IpaVesta.curve σ cvk cp pub).alpha
    (ftChunkAssembly σ.k cp.tComm.size aT)
    (runOracles IpaVesta.curve σ cvk cp pub).zeta
    (fun (i : Fin 44) (ch : Fin (nc)) (j : Fin 2) =>
      ((runInputP IpaVesta.curve σ cvk cp pub
          (runPubEvals IpaVesta.curve σ cvk cp pub)
          (runVU IpaVesta.curve σ cvk cp pub).1
          (runVU IpaVesta.curve σ cvk cp pub).2).evals[streamPos
            (nc) i (ch : ℕ)]!)[(j : ℕ)]!)
    (fun i c => aRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
    (fun i c => ρRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
    hβ hγ hα hζ hζ1 hζb htdeg
    (fun i c => ⟨hbound₀ i c,
      fun j => hpins ⟨streamPos (nc) i (c : ℕ), hlt i c⟩ j⟩)
    hteq0

/-- **The run-level residue-free root (Pallas).** The Pallas-side twin of
`kimchiVesta_run_sound_algebraic_ft`, over `Fq`/`IpaPallas`, its Fiat–Shamir
assumption `kimchi_fiat_shamir_pallas`. -/
theorem kimchiPallas_run_sound_algebraic_ft (σ : SRS IpaPallas.Point) {nc : ℕ}
    (cvk : KimchiVK IpaPallas.curve nc) (cp : KimchiProof IpaPallas.curve nc)
    (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n) (hn : cvk.n = n)
    (hvk : cvk.Corresponds σ idx)
    (hpub : pub.size = idx.publicCount)
    (htpos : 0 < cp.tComm.size)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : kimchiVerify IpaPallas.curve σ cvk cp pub = true)
    (aRef : Fin (runInput IpaPallas.curve σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → Fq)
    (ρRef : Fin (runInput IpaPallas.curve σ cvk cp pub).commitments.size → Fq)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput IpaPallas.curve σ cvk cp pub).commitmentFn i)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → Fq) (ρT : Fin cp.tComm.size → Fq)
    (hTC : ∀ j : Fin cp.tComm.size, commit σ (aT j) (ρT j) = cp.tComm.getD (j : ℕ) 0)
    (hξ : (runInput IpaPallas.curve σ cvk cp pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaPallas.curve σ cvk cp pub).pointFn
          (runInput IpaPallas.curve σ cvk cp pub).evalFn)
    (hr : (runInput IpaPallas.curve σ cvk cp pub).evalscale
      ∉ badROf σ aRef (runInput IpaPallas.curve σ cvk cp pub).pointFn
          (runInput IpaPallas.curve σ cvk cp pub).evalFn
          (runInput IpaPallas.curve σ cvk cp pub).polyscale) :
    ∃ (badB : Finset Fq) (badG : Fq → Finset Fq) (badA : Fq → Fq → Finset Fq)
        (badZ : Fq → Fq → Fq → Polynomial Fq → Finset Fq)
        (wTab : Fin n → Fin 15 → Fq),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fq), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ((runOracles IpaPallas.curve σ cvk cp pub).beta ∉ badB →
          (runOracles IpaPallas.curve σ cvk cp pub).gamma
            ∉ badG (runOracles IpaPallas.curve σ cvk cp pub).beta →
          (runOracles IpaPallas.curve σ cvk cp pub).alpha
            ∉ badA (runOracles IpaPallas.curve σ cvk cp pub).beta
                (runOracles IpaPallas.curve σ cvk cp pub).gamma →
          (runOracles IpaPallas.curve σ cvk cp pub).zeta
            ∉ badZ (runOracles IpaPallas.curve σ cvk cp pub).beta
                (runOracles IpaPallas.curve σ cvk cp pub).gamma
                (runOracles IpaPallas.curve σ cvk cp pub).alpha
                (ftChunkAssembly σ.k cp.tComm.size aT) →
          (runOracles IpaPallas.curve σ cvk cp pub).zeta ≠ 1 →
          (runOracles IpaPallas.curve σ cvk cp pub).zeta
            ≠ idx.omega ^ (n - idx.zkRows) →
          Satisfies idx (pubView idx pub) wTab) := by
  obtain ⟨hvkc, homega, hzk, hshift, hendo, hmds, hlag⟩ := hvk
  -- (1) the body reflection: the guards and the warm acceptance
  obtain ⟨hlagsz, hpubn, haccept⟩ :=
    kimchiVerify_reflects IpaPallas.curve σ cvk cp pub hacc
  have hlt : ∀ (i : Fin 44) (c : Fin (nc)),
      streamPos (nc) i (c : ℕ)
        < (runInput IpaPallas.curve σ cvk cp pub).commitments.size := by
    intro i c
    show streamPos (nc) i (c : ℕ)
      < ((flatRows IpaPallas.curve (runLogicalP IpaPallas.curve σ cvk cp pub
          (runPubEvals IpaPallas.curve σ cvk cp pub))).map (·.1)).size
    rw [Array.size_map, stream_size IpaPallas.curve]
    exact streamPos_lt _ i _ c.isLt
  -- (2) the reference openings at the stream positions bind the abstract batch
  have hbound₀ : ∀ (i : Fin 44) (c : Fin (nc)),
      commit σ (aRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
          (ρRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
        = batchC (fun col c => (cp.wComm[col])[c]) (fun c => cp.zComm[c])
            (fun c => (publicCommitment IpaPallas.curve σ cvk pub)[c])
            cvk.comms i c := by
    intro i c
    rw [hrep ⟨streamPos (nc) i (c : ℕ), hlt i c⟩]
    show (runInput IpaPallas.curve σ cvk cp pub).commitments[streamPos
        (nc) i (c : ℕ)]'(hlt i c) = _
    rw [← getElem!_pos (runInput IpaPallas.curve σ cvk cp pub).commitments
      (streamPos (nc) i (c : ℕ)) (hlt i c)]
    show ((flatRows IpaPallas.curve (runLogicalP IpaPallas.curve σ cvk cp pub
        (runPubEvals IpaPallas.curve σ cvk cp pub))).map
          (·.1))[streamPos (nc) i (c : ℕ)]! = _
    rw [getBang_map _ _ _ (by
      rw [stream_size IpaPallas.curve]
      exact streamPos_lt _ i _ c.isLt)]
    exact (batchC_eq_flat IpaPallas.curve i c).symm
  -- (3) the public row pinned through the Lagrange chunk pin
  have hpubC : ∀ c : Fin (nc),
      (publicCommitment IpaPallas.curve σ cvk pub)[c]
        = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ) :=
    fun c => publicCommitment_corresponds IpaPallas.curve σ cvk pub idx
      (fun a P => (Pasta.pallas_smul_val a P).symm) hlag hlagsz hpub c
  -- (4) the openings seam, fed directly
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hnc hk hbind cvk.comms hvkc (pubView idx pub)
      (fun col c => (cp.wComm[col])[c]) (fun c => cp.zComm[c])
      (fun c => (publicCommitment IpaPallas.curve σ cvk pub)[c])
      hpubC
      (fun i c => aRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
      (fun i c => ρRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
      hbound₀
  refine ⟨badB, badG, badA, badZ,
    extractTable idx.omega (fun col => assembledRow σ.k (nc)
      (fun c => aRef ⟨streamPos (nc) (wRow col) (c : ℕ),
        hlt (wRow col) c⟩)),
    hbounds, ?_⟩
  intro hβ hγ hα hζ hζ1 hζb
  -- (5) the eval pins from the run's single accepted opening (flat arity)
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _
    (kimchi_fiat_shamir_pallas σ cvk cp pub) haccept
  have hpins := eval_pins_of_opening σ hbind
    (runInput IpaPallas.curve σ cvk cp pub).commitmentFn
    (runInput IpaPallas.curve σ cvk cp pub).pointFn aRef ρRef hrep
    (runInput IpaPallas.curve σ cvk cp pub).evalFn
    (runInput IpaPallas.curve σ cvk cp pub).polyscale
    (runInput IpaPallas.curve σ cvk cp pub).evalscale hξ hr a ρ hopen
  -- (6) the ft opening and the Maller identity at the double collapse
  obtain ⟨aft, ρft, hcomm_ft, heval_ft⟩ :=
    ft_opening_of_reflected_pallas σ cvk cp pub hbind haccept aRef ρRef hrep hξ hr
  have hCσ6 : ∀ c : Fin (nc),
      (cvk.sigmaComm[6])[c] = commitPolyChunk σ (idx.sigmaPoly 6) (c : ℕ) :=
    fun c => congrFun (congrArg (fun cm => cm.sigma 6) hvkc) c
  have hσ₆ : (idx.sigmaPoly 6).natDegree
      < nc * 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hcommit : commit σ aft ρft
      = runPScalar IpaPallas.curve σ cvk cp pub
          • ∑ c : Fin (nc),
              ((runOracles IpaPallas.curve σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • (cvk.sigmaComm[6])[c]
        - ((runOracles IpaPallas.curve σ cvk cp pub).zeta ^ n - 1)
            • ∑ j : Fin cp.tComm.size,
                ((runOracles IpaPallas.curve σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (j : ℕ)
                  • cp.tComm.getD (j : ℕ) 0 :=
    hcomm_ft.trans (runFtComm_eq IpaPallas.curve Pasta.pallas_smul_val hn)
  obtain ⟨htdeg, hteq0⟩ := ft_identity_of_chunks σ hbind (idx.sigmaPoly 6) hσ₆
    (fun c => (cvk.sigmaComm[6])[c]) hCσ6 htpos cp.tComm_le
    (fun j => cp.tComm.getD (j : ℕ) 0) aT ρT hTC
    (runPScalar IpaPallas.curve σ cvk cp pub)
    (runOracles IpaPallas.curve σ cvk cp pub).zeta
    (runFtEval0 IpaPallas.curve σ cvk cp pub) n hk aft ρft hcommit heval_ft
  -- (7) reconcile the derived identity into the consumer's shape
  have hce := claimedEvals_run_eq IpaPallas.curve (σ := σ) (cvk := cvk) (cp := cp)
    (pub := pub) (pe := runPubEvals IpaPallas.curve σ cvk cp pub)
    (v := (runVU IpaPallas.curve σ cvk cp pub).1)
    (u := (runVU IpaPallas.curve σ cvk cp pub).2)
  have hcpe := claimedPub_run_eq IpaPallas.curve (σ := σ) (cvk := cvk) (cp := cp)
    (pub := pub) (pe := runPubEvals IpaPallas.curve σ cvk cp pub)
    (v := (runVU IpaPallas.curve σ cvk cp pub).1)
    (u := (runVU IpaPallas.curve σ cvk cp pub).2)
  have hζM : runZetaM IpaPallas.curve σ cvk cp pub
      = (runOracles IpaPallas.curve σ cvk cp pub).zeta ^ 2 ^ σ.k := by
    unfold runZetaM
    rw [powPow2_eq]
  have hζwM : runZetaOmegaM IpaPallas.curve σ cvk cp pub
      = (idx.omega * (runOracles IpaPallas.curve σ cvk cp pub).zeta) ^ 2 ^ σ.k := by
    unfold runZetaOmegaM runZetaOmega
    rw [powPow2_eq, homega, mul_comm]
  unfold runPScalar runFtEval0 runFtEval0P runPubEval0 runLinEvals at hteq0
  rw [← hce, ← hcpe, hζM, hζwM, hn, hzk, homega, hendo, hmds, hshift] at hteq0
  -- (8) the per-row pins, at the consumer's two eval points
  have hpt : (runInput IpaPallas.curve σ cvk cp pub).pointFn
      = ![(runOracles IpaPallas.curve σ cvk cp pub).zeta,
          idx.omega * (runOracles IpaPallas.curve σ cvk cp pub).zeta] := by
    funext j
    fin_cases j
    · rfl
    · show (runOracles IpaPallas.curve σ cvk cp pub).zeta * cvk.omega = _
      rw [homega]
      exact mul_comm _ _
  rw [hpt] at hpins
  -- (9) feed the consumer
  exact himp (runOracles IpaPallas.curve σ cvk cp pub).beta
    (runOracles IpaPallas.curve σ cvk cp pub).gamma
    (runOracles IpaPallas.curve σ cvk cp pub).alpha
    (ftChunkAssembly σ.k cp.tComm.size aT)
    (runOracles IpaPallas.curve σ cvk cp pub).zeta
    (fun (i : Fin 44) (ch : Fin (nc)) (j : Fin 2) =>
      ((runInputP IpaPallas.curve σ cvk cp pub
          (runPubEvals IpaPallas.curve σ cvk cp pub)
          (runVU IpaPallas.curve σ cvk cp pub).1
          (runVU IpaPallas.curve σ cvk cp pub).2).evals[streamPos
            (nc) i (ch : ℕ)]!)[(j : ℕ)]!)
    (fun i c => aRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
    (fun i c => ρRef ⟨streamPos (nc) i (c : ℕ), hlt i c⟩)
    hβ hγ hα hζ hζ1 hζb htdeg
    (fun i c => ⟨hbound₀ i c,
      fun j => hpins ⟨streamPos (nc) i (c : ℕ), hlt i c⟩ j⟩)
    hteq0

end Kimchi.Verifier
