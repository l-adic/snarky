import Kimchi.Verifier.Capstone.AlgebraicChunked
import Kimchi.Verifier.ReflectChunked

/-!
# The chunked Fiat–Shamir-reflection discharge (part 1: the ft opening)

The chunked re-anchoring of the Fiat–Shamir axiom on the deployed CHUNKED verifier's
own transcript: `Chunked.kimchi_fiat_shamir_{vesta,pallas}` state the transcript-tree
extraction over the warm data of a chunked reflected run — the warm-sponge finish
`Ipa.verifyFrom … (Chunked.runWarm …) (Chunked.runInput …)` that `Chunked.kimchiVerify`
itself executes (`ReflectedRun.accepts`, `Verifier/ReflectChunked.lean`). These
RESTATE the `nc = 1` `kimchi_fiat_shamir_*` axioms at the chunked transcript shape —
the flat segment stream of `44·nc + 1` batch rows — and carry the same independence
criterion: each says only that the Poseidon sponge provides a valid Fiat–Shamir
transform at the transcript the deployed verifier actually runs; no arithmetic content,
no reference to the abstract batch.

`ft_opening_of_reflected` (PROVED, tree-as-hypothesis) derives the ft opening from a
genuine chunked acceptance: the constructed ft commitment is the single-chunk ft row of
the run's own accepted flat stream — flat position `nc` (after the public row's `nc`
chunks) — so `ipa_soundnessA` plus the arity-generic `eval_pins_of_opening` pin
`runFtComm` to a representation whose evaluation at the run's own `ζ` is `runFtEval0`.
The curve wrappers discharge the run by reflection and the tree by the new axioms.

Part 2 — the run-level terminal roots (the deployed flat stream reindexed onto the
44-row chunked `batchC`, the openings seam fed directly, the Maller identity from this
ft opening via `ft_identity_of_chunks`) — is the follow-on.
-/

open Bulletproof

namespace Kimchi.Verifier.Chunked

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
axiom kimchi_fiat_shamir_vesta (σ : SRS IpaVesta.Point) (vk : Chunked.KimchiVesta.VK)
    (p : Chunked.KimchiVesta.Proof) (pub : Array Fp) :
  FiatShamirTreeB σ
    (combinedCommitment (runInput IpaVesta.curve σ vk p pub).polyscale
      (runInput IpaVesta.curve σ vk p pub).commitmentFn)
    (combinedEvalVector (2 ^ σ.k) (runInput IpaVesta.curve σ vk p pub).evalscale
      (runInput IpaVesta.curve σ vk p pub).pointFn)
    (Ipa.cipOf (runInput IpaVesta.curve σ vk p pub))
    (Ipa.verifyFrom IpaVesta.curve σ (runWarm IpaVesta.curve σ vk p pub)
      (runInput IpaVesta.curve σ vk p pub) = true)

/-- **AXIOM (Fiat–Shamir, Poseidon instantiation over the deployed chunked run,
Pallas).** The Pallas-side twin of `Chunked.kimchi_fiat_shamir_vesta`. -/
axiom kimchi_fiat_shamir_pallas (σ : SRS IpaPallas.Point) (vk : Chunked.KimchiPallas.VK)
    (p : Chunked.KimchiPallas.Proof) (pub : Array Fq) :
  FiatShamirTreeB σ
    (combinedCommitment (runInput IpaPallas.curve σ vk p pub).polyscale
      (runInput IpaPallas.curve σ vk p pub).commitmentFn)
    (combinedEvalVector (2 ^ σ.k) (runInput IpaPallas.curve σ vk p pub).evalscale
      (runInput IpaPallas.curve σ vk p pub).pointFn)
    (Ipa.cipOf (runInput IpaPallas.curve σ vk p pub))
    (Ipa.verifyFrom IpaPallas.curve σ (runWarm IpaPallas.curve σ vk p pub)
      (runInput IpaPallas.curve σ vk p pub) = true)

/-! ## Reading the ft slot of the flat stream -/

variable (C : Ipa.CommitmentCurve)

/-- The wire point carrier is inhabited by the group zero — for the `getElem!` reads
of the flat stream. -/
private instance : Inhabited C.Point := ⟨0⟩

/-- The public commitment always has exactly `nc` chunks. -/
private theorem publicCommitment_size (σ : SRS C.Point) (vk : KimchiVK C) (nc : ℕ)
    (pub : Array C.ScalarField) : (publicCommitment C σ vk nc pub).size = nc := by
  unfold publicCommitment
  split
  · simp
  · simp

/-- The run's public evaluation chunk vectors have exactly `runNc` chunks (from the
shape guard: proof-carried vectors are guard-checked; the barycentric fallback is a
singleton and the guard pins `runNc = 1`). -/
private theorem runPubEvals_size (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    (runPubEvals C σ vk p pub).zeta.size = runNc C σ vk
      ∧ (runPubEvals C σ vk p pub).zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hpub : (!(match p.pubEvals with
      | some pe => pe.zeta.size == runNc C σ vk && pe.zetaOmega.size == runNc C σ vk
      | none => runNc C σ vk == 1)) = false := h.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false'] at hpub
  cases hm : p.pubEvals with
  | some pe =>
    rw [hm] at hpub
    simp only [Bool.and_eq_true, beq_iff_eq] at hpub
    simp only [runPubEvals, publicEvalChunks, hm]
    exact hpub
  | none =>
    rw [hm] at hpub
    simp only [beq_iff_eq] at hpub
    simp only [runPubEvals, publicEvalChunks, hm]
    simp [hpub]

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
private theorem flatRows_ft_read (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Array C.ScalarField))
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk) :
    (flatRows C (runLogicalP C σ vk p pub pe))[(runNc C σ vk : ℕ)]!
      = (runFtComm C σ vk p pub,
          runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta),
          p.ftEval1) := by
  set nc := runNc C σ vk with hnc
  have hpubsize := publicCommitment_size C σ vk nc pub
  have hApub : (Array.map
        (fun ce : C.Point × C.ScalarField × C.ScalarField => (ce.1, ce.2.1, ce.2.2))
        ((publicCommitment C σ vk nc pub).zip (pe.zeta.zip pe.zetaOmega))).size
      = nc := by
    simp [Array.size_zip, hpubsize, hpe0, hpe1]
  have hAft : Array.map
        (fun ce : C.Point × C.ScalarField × C.ScalarField => (ce.1, ce.2.1, ce.2.2))
        (#[runFtComm C σ vk p pub].zip
          (#[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)].zip
            #[p.ftEval1]))
      = #[(runFtComm C σ vk p pub,
          runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta),
          p.ftEval1)] := by
    simp [Array.zip]
  unfold flatRows runLogicalP
  rw [Array.flatMap_append, Array.flatMap_append, Array.flatMap_append]
  rw [show (#[(publicCommitment C σ vk nc pub, pe.zeta, pe.zetaOmega),
      (#[runFtComm C σ vk p pub],
        #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
        #[p.ftEval1]),
      (p.zComm, p.evals.z.zeta, p.evals.z.zetaOmega),
      (vk.genericComm, p.evals.genericSelector.zeta,
        p.evals.genericSelector.zetaOmega),
      (vk.poseidonComm, p.evals.poseidonSelector.zeta,
        p.evals.poseidonSelector.zetaOmega),
      (vk.completeAddComm, p.evals.completeAddSelector.zeta,
        p.evals.completeAddSelector.zetaOmega),
      (vk.mulComm, p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega),
      (vk.emulComm, p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega),
      (vk.endomulScalarComm, p.evals.endomulScalarSelector.zeta,
        p.evals.endomulScalarSelector.zetaOmega)]
    : Array (Array C.Point × Array C.ScalarField × Array C.ScalarField))
      = #[(publicCommitment C σ vk nc pub, pe.zeta, pe.zetaOmega)]
        ++ #[(#[runFtComm C σ vk p pub],
          #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
          #[p.ftEval1])]
        ++ #[(p.zComm, p.evals.z.zeta, p.evals.z.zetaOmega),
      (vk.genericComm, p.evals.genericSelector.zeta,
        p.evals.genericSelector.zetaOmega),
      (vk.poseidonComm, p.evals.poseidonSelector.zeta,
        p.evals.poseidonSelector.zetaOmega),
      (vk.completeAddComm, p.evals.completeAddSelector.zeta,
        p.evals.completeAddSelector.zetaOmega),
      (vk.mulComm, p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega),
      (vk.emulComm, p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega),
      (vk.endomulScalarComm, p.evals.endomulScalarSelector.zeta,
        p.evals.endomulScalarSelector.zetaOmega)] from rfl]
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
private theorem flatRows_size_lt (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Array C.ScalarField))
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk) :
    (runNc C σ vk : ℕ) < (flatRows C (runLogicalP C σ vk p pub pe)).size := by
  set nc := runNc C σ vk with hnc
  have hpubsize := publicCommitment_size C σ vk nc pub
  have hApub : (Array.map
        (fun ce : C.Point × C.ScalarField × C.ScalarField => (ce.1, ce.2.1, ce.2.2))
        ((publicCommitment C σ vk nc pub).zip (pe.zeta.zip pe.zetaOmega))).size
      = nc := by
    simp [Array.size_zip, hpubsize, hpe0, hpe1]
  have hAft : Array.map
        (fun ce : C.Point × C.ScalarField × C.ScalarField => (ce.1, ce.2.1, ce.2.2))
        (#[runFtComm C σ vk p pub].zip
          (#[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)].zip
            #[p.ftEval1]))
      = #[(runFtComm C σ vk p pub,
          runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta),
          p.ftEval1)] := by
    simp [Array.zip]
  unfold flatRows runLogicalP
  rw [Array.flatMap_append, Array.flatMap_append, Array.flatMap_append]
  rw [show (#[(publicCommitment C σ vk nc pub, pe.zeta, pe.zetaOmega),
      (#[runFtComm C σ vk p pub],
        #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
        #[p.ftEval1]),
      (p.zComm, p.evals.z.zeta, p.evals.z.zetaOmega),
      (vk.genericComm, p.evals.genericSelector.zeta,
        p.evals.genericSelector.zetaOmega),
      (vk.poseidonComm, p.evals.poseidonSelector.zeta,
        p.evals.poseidonSelector.zetaOmega),
      (vk.completeAddComm, p.evals.completeAddSelector.zeta,
        p.evals.completeAddSelector.zetaOmega),
      (vk.mulComm, p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega),
      (vk.emulComm, p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega),
      (vk.endomulScalarComm, p.evals.endomulScalarSelector.zeta,
        p.evals.endomulScalarSelector.zetaOmega)]
    : Array (Array C.Point × Array C.ScalarField × Array C.ScalarField))
      = #[(publicCommitment C σ vk nc pub, pe.zeta, pe.zetaOmega)]
        ++ #[(#[runFtComm C σ vk p pub],
          #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
          #[p.ftEval1])]
        ++ #[(p.zComm, p.evals.z.zeta, p.evals.z.zetaOmega),
      (vk.genericComm, p.evals.genericSelector.zeta,
        p.evals.genericSelector.zetaOmega),
      (vk.poseidonComm, p.evals.poseidonSelector.zeta,
        p.evals.poseidonSelector.zetaOmega),
      (vk.completeAddComm, p.evals.completeAddSelector.zeta,
        p.evals.completeAddSelector.zetaOmega),
      (vk.mulComm, p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega),
      (vk.emulComm, p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega),
      (vk.endomulScalarComm, p.evals.endomulScalarSelector.zeta,
        p.evals.endomulScalarSelector.zetaOmega)] from rfl]
  rw [Array.flatMap_append, Array.flatMap_append]
  simp only [Array.flatMap_singleton]
  simp only [Array.size_append, hApub, hAft, List.size_toArray, List.length_cons,
    List.length_nil]
  omega

/-! ## The ft opening from a chunked reflected run -/

/-- **The ft opening from a chunked reflected run** (tree-as-hypothesis, PROVED):
DL-binding, a reflected accepted chunked run, SRS-basis representations of the run's
own flat batch rows, the run's transcript tree (the chunked `kimchi_fiat_shamir_*`
shape, here a hypothesis), and good combination challenges yield the ft opening — a
representation of the constructed ft commitment `runFtComm` (the DOUBLE collapse at
`ζ^{2^σ.k}`) whose evaluation at the run's own `ζ` is the computed claim `runFtEval0`.
The ft row sits at flat position `nc`, right after the public row's chunks
(`flatRows_ft_read`). -/
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
  have hpe := runPubEvals_size C σ vk p pub hrun.shape
  have hread := flatRows_ft_read C σ vk p pub (runPubEvals C σ vk p pub) hpe.1 hpe.2
  have hflt := flatRows_size_lt C σ vk p pub (runPubEvals C σ vk p pub) hpe.1 hpe.2
  have hsz : (runNc C σ vk : ℕ) < (runInput C σ vk p pub).commitments.size := by
    show (runNc C σ vk : ℕ)
      < ((flatRows C (runLogicalP C σ vk p pub (runPubEvals C σ vk p pub))).map
          (·.1)).size
    rw [Array.size_map]
    exact hflt
  refine ⟨aRef ⟨runNc C σ vk, hsz⟩, ρRef ⟨runNc C σ vk, hsz⟩, ?_, ?_⟩
  · rw [hrep ⟨runNc C σ vk, hsz⟩]
    show (runInput C σ vk p pub).commitments[(runNc C σ vk : ℕ)]'hsz
      = runFtComm C σ vk p pub
    rw [← getElem!_pos (runInput C σ vk p pub).commitments (runNc C σ vk : ℕ) hsz]
    show ((flatRows C (runLogicalP C σ vk p pub (runPubEvals C σ vk p pub))).map
        (·.1))[(runNc C σ vk : ℕ)]! = runFtComm C σ vk p pub
    rw [getBang_map _ _ _ hflt, hread]
  · have hpin := hpins ⟨runNc C σ vk, hsz⟩ (0 : Fin 2)
    have hpt : (runInput C σ vk p pub).pointFn (0 : Fin 2)
        = (runOracles C σ vk p pub).zeta := rfl
    rw [hpt] at hpin
    rw [← hpin]
    show ((runInput C σ vk p pub).evals[(runNc C σ vk : ℕ)]!)[(0 : ℕ)]!
      = runFtEval0 C σ vk p pub
    show (((flatRows C (runLogicalP C σ vk p pub (runPubEvals C σ vk p pub))).map
        (fun r => #[r.2.1, r.2.2]))[(runNc C σ vk : ℕ)]!)[(0 : ℕ)]!
      = runFtEval0 C σ vk p pub
    rw [getBang_map _ _ _ hflt, hread]
    rfl

/-- **The ft opening of the deployed chunked Vesta verifier**: a genuine
`Chunked.KimchiVesta.verify … = true`, DL-binding, representations of the run's own
flat batch rows, and good combination challenges yield the ft opening. The run is
reflected trust-free (`Chunked.kimchiVerify_reflects`); the transcript tree is
`Chunked.kimchi_fiat_shamir_vesta` at the run's own warm data — the sole axiom
consumed. The chunked Vesta FS-reflection root. -/
theorem ft_opening_of_reflected_vesta (σ : SRS IpaVesta.Point)
    (vk : Chunked.KimchiVesta.VK) (p : Chunked.KimchiVesta.Proof) (pub : Array Fp)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : Chunked.KimchiVesta.verify σ vk p pub = true)
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

/-- **The ft opening of the deployed chunked Pallas verifier.** The Pallas twin. -/
theorem ft_opening_of_reflected_pallas (σ : SRS IpaPallas.Point)
    (vk : Chunked.KimchiPallas.VK) (p : Chunked.KimchiPallas.Proof) (pub : Array Fq)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : Chunked.KimchiPallas.verify σ vk p pub = true)
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

/-! ## The run shapes, extracted from the guard -/

/-- The shape facts of an accepted chunked run, as membership-form size statements —
extracted once from `shapeBad = false` (the 30-clause guard conjunction). -/
structure RunShapes (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Prop where
  wCommSize : p.wComm.size = 15
  wCommChunks : ∀ a ∈ p.wComm, a.size = runNc C σ vk
  zCommSize : p.zComm.size = runNc C σ vk
  tCommSize : p.tComm.size ≤ 7 * runNc C σ vk
  wSize : p.evals.w.size = 15
  sSize : p.evals.s.size = 6
  coeffSize : p.evals.coefficients.size = 15
  wChunks : ∀ e ∈ p.evals.w,
    e.zeta.size = runNc C σ vk ∧ e.zetaOmega.size = runNc C σ vk
  sChunks : ∀ e ∈ p.evals.s,
    e.zeta.size = runNc C σ vk ∧ e.zetaOmega.size = runNc C σ vk
  coeffChunks : ∀ e ∈ p.evals.coefficients,
    e.zeta.size = runNc C σ vk ∧ e.zetaOmega.size = runNc C σ vk
  zChunks : p.evals.z.zeta.size = runNc C σ vk
    ∧ p.evals.z.zetaOmega.size = runNc C σ vk
  genChunks : p.evals.genericSelector.zeta.size = runNc C σ vk
    ∧ p.evals.genericSelector.zetaOmega.size = runNc C σ vk
  posChunks : p.evals.poseidonSelector.zeta.size = runNc C σ vk
    ∧ p.evals.poseidonSelector.zetaOmega.size = runNc C σ vk
  addChunks : p.evals.completeAddSelector.zeta.size = runNc C σ vk
    ∧ p.evals.completeAddSelector.zetaOmega.size = runNc C σ vk
  mulChunks : p.evals.mulSelector.zeta.size = runNc C σ vk
    ∧ p.evals.mulSelector.zetaOmega.size = runNc C σ vk
  emulChunks : p.evals.emulSelector.zeta.size = runNc C σ vk
    ∧ p.evals.emulSelector.zetaOmega.size = runNc C σ vk
  endoChunks : p.evals.endomulScalarSelector.zeta.size = runNc C σ vk
    ∧ p.evals.endomulScalarSelector.zetaOmega.size = runNc C σ vk
  sigmaCommSize : vk.sigmaComm.size = 7
  sigmaCommChunks : ∀ a ∈ vk.sigmaComm, a.size = runNc C σ vk
  coeffCommSize : vk.coefficientsComm.size = 15
  coeffCommChunks : ∀ a ∈ vk.coefficientsComm, a.size = runNc C σ vk
  genCommSize : vk.genericComm.size = runNc C σ vk
  posCommSize : vk.poseidonComm.size = runNc C σ vk
  addCommSize : vk.completeAddComm.size = runNc C σ vk
  mulCommSize : vk.mulComm.size = runNc C σ vk
  emulCommSize : vk.emulComm.size = runNc C σ vk
  endoCommSize : vk.endomulScalarComm.size = runNc C σ vk
  shiftsSize : vk.shifts.size = 7
  lagSize : pub.size ≤ vk.lagrangeBasis.size
  lagChunks : ∀ a ∈ vk.lagrangeBasis.extract 0 pub.size, a.size = runNc C σ vk
  pubSize : pub.size ≤ vk.n
  srsLe : σ.k ≤ vk.domainLog2

private theorem shape_wCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.wComm.size = 15 := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at hx
  exact hx.1

private theorem shape_wCommChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    ∀ a ∈ p.wComm, a.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at hx
  exact hx.2

private theorem shape_zCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.zComm.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', beq_iff_eq] at hx
  exact hx

private theorem shape_tCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.tComm.size ≤ 7 * (runNc C σ vk) := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hx
  show p.tComm.size ≤ 7 * 2 ^ (vk.domainLog2 - σ.k)
  omega

private theorem shape_wSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.evals.w.size = 15 := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [bne_eq_false_iff_eq] at hx
  exact hx

private theorem shape_sSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.evals.s.size = 6 := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [bne_eq_false_iff_eq] at hx
  exact hx

private theorem shape_coeffSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.evals.coefficients.size = 15 := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [bne_eq_false_iff_eq] at hx
  exact hx

private theorem shape_wChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    ∀ e ∈ p.evals.w, e.zeta.size = runNc C σ vk ∧ e.zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at hx
  exact hx

private theorem shape_sChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    ∀ e ∈ p.evals.s, e.zeta.size = runNc C σ vk ∧ e.zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at hx
  exact hx

private theorem shape_coeffChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    ∀ e ∈ p.evals.coefficients, e.zeta.size = runNc C σ vk ∧ e.zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at hx
  exact hx

private theorem shape_zChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.evals.z.zeta.size = runNc C σ vk
      ∧ p.evals.z.zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hx
  exact hx

private theorem shape_genChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.evals.genericSelector.zeta.size = runNc C σ vk
      ∧ p.evals.genericSelector.zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hx
  exact hx

private theorem shape_posChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.evals.poseidonSelector.zeta.size = runNc C σ vk
      ∧ p.evals.poseidonSelector.zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hx
  exact hx

private theorem shape_addChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.evals.completeAddSelector.zeta.size = runNc C σ vk
      ∧ p.evals.completeAddSelector.zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hx
  exact hx

private theorem shape_mulChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.evals.mulSelector.zeta.size = runNc C σ vk
      ∧ p.evals.mulSelector.zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hx
  exact hx

private theorem shape_emulChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.evals.emulSelector.zeta.size = runNc C σ vk
      ∧ p.evals.emulSelector.zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hx
  exact hx

private theorem shape_endoChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    p.evals.endomulScalarSelector.zeta.size = runNc C σ vk
      ∧ p.evals.endomulScalarSelector.zetaOmega.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hx
  exact hx

private theorem shape_sigmaCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    vk.sigmaComm.size = 7 := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at hx
  exact hx.1

private theorem shape_sigmaCommChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    ∀ a ∈ vk.sigmaComm, a.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at hx
  exact hx.2

private theorem shape_coeffCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    vk.coefficientsComm.size = 15 := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at hx
  exact hx.1

private theorem shape_coeffCommChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    ∀ a ∈ vk.coefficientsComm, a.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at hx
  exact hx.2

private theorem shape_genCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    vk.genericComm.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', beq_iff_eq] at hx
  exact hx

private theorem shape_posCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    vk.poseidonComm.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', beq_iff_eq] at hx
  exact hx

private theorem shape_addCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    vk.completeAddComm.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', beq_iff_eq] at hx
  exact hx

private theorem shape_mulCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    vk.mulComm.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.2
  simp only [Bool.not_eq_false', beq_iff_eq] at hx
  exact hx

private theorem shape_emulCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    vk.emulComm.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.2
  simp only [Bool.not_eq_false', beq_iff_eq] at hx
  exact hx

private theorem shape_endoCommSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    vk.endomulScalarComm.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.2
  simp only [Bool.not_eq_false', beq_iff_eq] at hx
  exact hx

private theorem shape_shiftsSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    vk.shifts.size = 7 := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.2
  simp only [bne_eq_false_iff_eq] at hx
  exact hx

private theorem shape_lagSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    pub.size ≤ vk.lagrangeBasis.size := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.2
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hx
  omega

private theorem shape_lagChunks (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    ∀ a ∈ vk.lagrangeBasis.extract 0 pub.size, a.size = runNc C σ vk := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.2
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at hx
  exact hx

private theorem shape_pubSize (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    pub.size ≤ vk.n := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.2
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hx
  omega

private theorem shape_srsLe (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    σ.k ≤ vk.domainLog2 := by
  have h := hshape
  simp only [shapeBad, Bool.or_eq_false_iff] at h
  have hx := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hx
  exact hx

/-- The extraction: `shapeBad = false` gives every run shape. -/
theorem runShapes_of_shape (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hshape : shapeBad C σ vk p pub = false) :
    RunShapes C σ vk p pub :=
  { wCommSize := shape_wCommSize C σ vk p pub hshape
    wCommChunks := shape_wCommChunks C σ vk p pub hshape
    zCommSize := shape_zCommSize C σ vk p pub hshape
    tCommSize := shape_tCommSize C σ vk p pub hshape
    wSize := shape_wSize C σ vk p pub hshape
    sSize := shape_sSize C σ vk p pub hshape
    coeffSize := shape_coeffSize C σ vk p pub hshape
    wChunks := shape_wChunks C σ vk p pub hshape
    sChunks := shape_sChunks C σ vk p pub hshape
    coeffChunks := shape_coeffChunks C σ vk p pub hshape
    zChunks := shape_zChunks C σ vk p pub hshape
    genChunks := shape_genChunks C σ vk p pub hshape
    posChunks := shape_posChunks C σ vk p pub hshape
    addChunks := shape_addChunks C σ vk p pub hshape
    mulChunks := shape_mulChunks C σ vk p pub hshape
    emulChunks := shape_emulChunks C σ vk p pub hshape
    endoChunks := shape_endoChunks C σ vk p pub hshape
    sigmaCommSize := shape_sigmaCommSize C σ vk p pub hshape
    sigmaCommChunks := shape_sigmaCommChunks C σ vk p pub hshape
    coeffCommSize := shape_coeffCommSize C σ vk p pub hshape
    coeffCommChunks := shape_coeffCommChunks C σ vk p pub hshape
    genCommSize := shape_genCommSize C σ vk p pub hshape
    posCommSize := shape_posCommSize C σ vk p pub hshape
    addCommSize := shape_addCommSize C σ vk p pub hshape
    mulCommSize := shape_mulCommSize C σ vk p pub hshape
    emulCommSize := shape_emulCommSize C σ vk p pub hshape
    endoCommSize := shape_endoCommSize C σ vk p pub hshape
    shiftsSize := shape_shiftsSize C σ vk p pub hshape
    lagSize := shape_lagSize C σ vk p pub hshape
    lagChunks := shape_lagChunks C σ vk p pub hshape
    pubSize := shape_pubSize C σ vk p pub hshape
    srsLe := shape_srsLe C σ vk p pub hshape }

/-! ## The stream positions and the decomposition -/

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

/-- The flat stream position of abstract batch row `i`, chunk `c` — the `to_batch`
layout of the deployed stream: the public row's chunks first, the ft singleton at `nc`,
then per logical row `nc` consecutive chunks (`z`, the six selectors, `w`,
coefficients, `σ[0..6)`). -/
def streamPos (nc : ℕ) (i : Fin 44) (c : ℕ) : ℕ :=
  if (i : ℕ) < 15 then nc + 1 + (7 + (i : ℕ)) * nc + c
  else if (i : ℕ) < 16 then nc + 1 + c
  else if (i : ℕ) < 22 then nc + 1 + (37 + ((i : ℕ) - 16)) * nc + c
  else if (i : ℕ) < 37 then nc + 1 + (22 + ((i : ℕ) - 22)) * nc + c
  else if (i : ℕ) < 43 then nc + 1 + (1 + ((i : ℕ) - 37)) * nc + c
  else c

section StreamRead

variable {σ : SRS C.Point} {vk : KimchiVK C} {p : KimchiProof C}
  {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Array C.ScalarField)}

/-- The row-triple flattener of the stream. -/
private def rowF : Array C.Point × Array C.ScalarField × Array C.ScalarField
    → Array (C.Point × C.ScalarField × C.ScalarField) :=
  fun r => (r.1.zip (r.2.1.zip r.2.2)).map (fun ce => (ce.1, ce.2.1, ce.2.2))

/-- The zip-map row triple of a commitment/evaluation pair. -/
private def zipRow :
    Array C.Point × Kimchi.Verifier.PointEvaluations (Array C.ScalarField)
    → Array C.Point × Array C.ScalarField × Array C.ScalarField :=
  fun x => (x.1, x.2.zeta, x.2.zetaOmega)

/-- The literal seven-row block of the decomposition, named for the region reads. -/
private def litRows (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C) :
    Array (Array C.Point × Array C.ScalarField × Array C.ScalarField) :=
  #[(p.zComm, p.evals.z.zeta, p.evals.z.zetaOmega),
    (vk.genericComm, p.evals.genericSelector.zeta,
      p.evals.genericSelector.zetaOmega),
    (vk.poseidonComm, p.evals.poseidonSelector.zeta,
      p.evals.poseidonSelector.zetaOmega),
    (vk.completeAddComm, p.evals.completeAddSelector.zeta,
      p.evals.completeAddSelector.zetaOmega),
    (vk.mulComm, p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega),
    (vk.emulComm, p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega),
    (vk.endomulScalarComm, p.evals.endomulScalarSelector.zeta,
      p.evals.endomulScalarSelector.zetaOmega)]

/-- **The stream decomposition**: the flat rows of the run's 45 logical rows are the
six-region append tree — the public block, the ft singleton, the seven literal rows
(`z` + six selectors), then the witness / coefficient / σ zip blocks. -/
private theorem stream_decomp (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Array C.ScalarField)) :
    flatRows C (runLogicalP C σ vk p pub pe)
      = ((((rowF C (publicCommitment C σ vk (runNc C σ vk) pub, pe.zeta, pe.zetaOmega)
            ++ rowF C (#[runFtComm C σ vk p pub],
              #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
              #[p.ftEval1]))
          ++ Array.flatMap (rowF C) (litRows C σ vk p))
        ++ Array.flatMap (rowF C) ((p.wComm.zip p.evals.w).map (zipRow C)))
      ++ Array.flatMap (rowF C) ((vk.coefficientsComm.zip p.evals.coefficients).map
          (zipRow C)))
      ++ Array.flatMap (rowF C) (((vk.sigmaComm.extract 0 6).zip p.evals.s).map
          (zipRow C)) := by
  unfold flatRows runLogicalP
  rw [Array.flatMap_append, Array.flatMap_append, Array.flatMap_append]
  rw [show (#[(publicCommitment C σ vk (runNc C σ vk) pub, pe.zeta, pe.zetaOmega),
      (#[runFtComm C σ vk p pub],
        #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
        #[p.ftEval1]),
      (p.zComm, p.evals.z.zeta, p.evals.z.zetaOmega),
      (vk.genericComm, p.evals.genericSelector.zeta,
        p.evals.genericSelector.zetaOmega),
      (vk.poseidonComm, p.evals.poseidonSelector.zeta,
        p.evals.poseidonSelector.zetaOmega),
      (vk.completeAddComm, p.evals.completeAddSelector.zeta,
        p.evals.completeAddSelector.zetaOmega),
      (vk.mulComm, p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega),
      (vk.emulComm, p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega),
      (vk.endomulScalarComm, p.evals.endomulScalarSelector.zeta,
        p.evals.endomulScalarSelector.zetaOmega)]
    : Array (Array C.Point × Array C.ScalarField × Array C.ScalarField))
      = #[(publicCommitment C σ vk (runNc C σ vk) pub, pe.zeta, pe.zetaOmega)]
        ++ #[(#[runFtComm C σ vk p pub],
          #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
          #[p.ftEval1])]
        ++ #[(p.zComm, p.evals.z.zeta, p.evals.z.zetaOmega),
      (vk.genericComm, p.evals.genericSelector.zeta,
        p.evals.genericSelector.zetaOmega),
      (vk.poseidonComm, p.evals.poseidonSelector.zeta,
        p.evals.poseidonSelector.zetaOmega),
      (vk.completeAddComm, p.evals.completeAddSelector.zeta,
        p.evals.completeAddSelector.zetaOmega),
      (vk.mulComm, p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega),
      (vk.emulComm, p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega),
      (vk.endomulScalarComm, p.evals.endomulScalarSelector.zeta,
        p.evals.endomulScalarSelector.zetaOmega)] from rfl]
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

variable {σ : SRS C.Point} {vk : KimchiVK C} {p : KimchiProof C}
  {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Array C.ScalarField)}

/-- Blocks stay inside their region: `q·nc + c < Q·nc`. -/
private theorem block_lt {q Q c nc : ℕ} (hq : q < Q) (hc : c < nc) :
    q * nc + c < Q * nc := by
  calc q * nc + c < (q + 1) * nc := by rw [Nat.succ_mul]; omega
    _ ≤ Q * nc := Nat.mul_le_mul_right nc hq

/-- A zip-map block array is uniformly `nc`-chunked (witness form): every flattened
row has `runNc` entries. -/
private theorem zipBlock_uniform {A : Array (Array C.Point)}
    {B : Array (Kimchi.Verifier.PointEvaluations (Array C.ScalarField))}
    (hA : ∀ a ∈ A, a.size = runNc C σ vk)
    (hB : ∀ e ∈ B, e.zeta.size = runNc C σ vk ∧ e.zetaOmega.size = runNc C σ vk) :
    ∀ a ∈ (A.zip B).map (zipRow C), (rowF C a).size = runNc C σ vk := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Array.exists_of_mem_map ha
  obtain ⟨hx1, hx2⟩ := Array.of_mem_zip hx
  exact rowF_size C (hA _ hx1) (hB _ hx2).1 (hB _ hx2).2

/-- The seven literal rows (`z` + six selectors) are uniformly `nc`-chunked. -/
private theorem litBlock_uniform (hsh : RunShapes C σ vk p pub) :
    ∀ a ∈ litRows C σ vk p, (rowF C a).size = runNc C σ vk := by
  intro a ha
  simp only [litRows, Array.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowF_size C hsh.zCommSize hsh.zChunks.1 hsh.zChunks.2
  · exact rowF_size C hsh.genCommSize hsh.genChunks.1 hsh.genChunks.2
  · exact rowF_size C hsh.posCommSize hsh.posChunks.1 hsh.posChunks.2
  · exact rowF_size C hsh.addCommSize hsh.addChunks.1 hsh.addChunks.2
  · exact rowF_size C hsh.mulCommSize hsh.mulChunks.1 hsh.mulChunks.2
  · exact rowF_size C hsh.emulCommSize hsh.emulChunks.1 hsh.emulChunks.2
  · exact rowF_size C hsh.endoCommSize hsh.endoChunks.1 hsh.endoChunks.2

/-- **Witness-region read**: the flat stream at `nc + 1 + (7+q)·nc + c` is witness
column `q`'s chunk `c` with its claims. -/
private theorem stream_read_w (hsh : RunShapes C σ vk p pub)
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk)
    (q c : ℕ) (hq : q < 15) (hc : c < runNc C σ vk) :
    (flatRows C (runLogicalP C σ vk p pub pe))[runNc C σ vk + 1
        + (7 + q) * runNc C σ vk + c]!
      = ((p.wComm[q]!)[c]!, (p.evals.w[q]!).zeta[c]!, (p.evals.w[q]!).zetaOmega[c]!) := by
  rw [stream_decomp]
  have hsPub : (rowF C (publicCommitment C σ vk (runNc C σ vk) pub, pe.zeta, pe.zetaOmega)).size
      = (runNc C σ vk) := rowF_size C (publicCommitment_size C σ vk (runNc C σ vk) pub) hpe0 hpe1
  have hsFt : (rowF C (#[runFtComm C σ vk p pub],
      #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
      #[p.ftEval1])).size = 1 := rowF_size C rfl rfl rfl
  have hs7 : (Array.flatMap (rowF C) (litRows C σ vk p)).size
      = 7 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk) (litBlock_uniform C hsh)]
    simp [litRows]
  have hzipW : ((p.wComm.zip p.evals.w).map (zipRow C)).size = 15 := by
    simp [Array.size_map, Array.size_zip, hsh.wCommSize, hsh.wSize]
  have hsW : (Array.flatMap (rowF C)
      ((p.wComm.zip p.evals.w).map (zipRow C))).size = 15 * (runNc C σ vk) := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk) (zipBlock_uniform C hsh.wCommChunks hsh.wChunks),
      hzipW]
  -- peel the σ and coefficient regions, land in the witness region
  rw [getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7, hsW]
      have h1 := block_lt hq hc
      have h2 : (7 + q) * runNc C σ vk
          = 7 * runNc C σ vk + q * runNc C σ vk := by ring
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7, hsW]
      have h1 := block_lt hq hc
      have h2 : (7 + q) * runNc C σ vk
          = 7 * runNc C σ vk + q * runNc C σ vk := by ring
      omega),
    getBang_append_at _ _ _ (q * (runNc C σ vk) + c) (by
      simp only [Array.size_append, hsPub, hsFt, hs7]
      have : (7 + q) * (runNc C σ vk) = 7 * (runNc C σ vk) + q * (runNc C σ vk) := by ring
      omega)
      (by
        rw [hsW]
        exact block_lt hq hc),
    flatMap_uniform_read _ _ (runNc C σ vk) (zipBlock_uniform C hsh.wCommChunks hsh.wChunks) q c
      (by rw [hzipW]; omega) hc]
  have hqz : q < (p.wComm.zip p.evals.w).size := by
    simp only [Array.size_zip, hsh.wCommSize, hsh.wSize]
    omega
  have hread : ((p.wComm.zip p.evals.w).map (zipRow C))[q]!
      = (p.wComm[q]!, (p.evals.w[q]!).zeta, (p.evals.w[q]!).zetaOmega) := by
    rw [getBang_map _ _ _ hqz, getElem!_pos _ q hqz,
      getElem!_pos p.wComm q (by rw [hsh.wCommSize]; omega),
      getElem!_pos p.evals.w q (by rw [hsh.wSize]; omega)]
    simp [zipRow, Array.getElem_zip]
  rw [hread]
  exact rowF_read C
    (hsh.wCommChunks _ (by
      rw [getElem!_pos p.wComm q (by rw [hsh.wCommSize]; omega)]
      exact Array.getElem_mem _))
    ((hsh.wChunks _ (by
      rw [getElem!_pos p.evals.w q (by rw [hsh.wSize]; omega)]
      exact Array.getElem_mem _)).1)
    ((hsh.wChunks _ (by
      rw [getElem!_pos p.evals.w q (by rw [hsh.wSize]; omega)]
      exact Array.getElem_mem _)).2)
    hc

/-- **Literal-region read** (`z` + the six selectors): the flat stream at
`nc + 1 + k·nc + c` is literal row `k`'s chunk `c`. -/
private theorem stream_read_lit (hsh : RunShapes C σ vk p pub)
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk)
    (k c : ℕ) (hk : k < 7) (hc : c < runNc C σ vk) :
    (flatRows C (runLogicalP C σ vk p pub pe))[runNc C σ vk + 1
        + k * runNc C σ vk + c]!
      = (((litRows C σ vk p)[k]!).1[c]!, ((litRows C σ vk p)[k]!).2.1[c]!,
          ((litRows C σ vk p)[k]!).2.2[c]!) := by
  rw [stream_decomp]
  have hsPub : (rowF C (publicCommitment C σ vk (runNc C σ vk) pub,
      pe.zeta, pe.zetaOmega)).size = runNc C σ vk :=
    rowF_size C (publicCommitment_size C σ vk (runNc C σ vk) pub) hpe0 hpe1
  have hsFt : (rowF C (#[runFtComm C σ vk p pub],
      #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
      #[p.ftEval1])).size = 1 := rowF_size C rfl rfl rfl
  have hs7 : (Array.flatMap (rowF C) (litRows C σ vk p)).size
      = 7 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk) (litBlock_uniform C hsh)]
    simp [litRows]
  rw [getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7]
      have h1 := block_lt hk hc
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7]
      have h1 := block_lt hk hc
      omega),
    getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7]
      have h1 := block_lt hk hc
      omega),
    getBang_append_at _ _ _ (k * runNc C σ vk + c) (by
      simp only [Array.size_append, hsPub, hsFt]
      omega)
      (by
        rw [hs7]
        exact block_lt hk hc),
    flatMap_uniform_read _ _ (runNc C σ vk) (litBlock_uniform C hsh) k c
      (by simp [litRows]; omega) hc]
  have hkm : k < (litRows C σ vk p).size := by
    simp only [litRows, List.size_toArray, List.length_cons, List.length_nil]
    omega
  have hmem : (litRows C σ vk p)[k]! ∈ litRows C σ vk p := by
    rw [getElem!_pos _ k hkm]
    exact Array.getElem_mem _
  have hsz := litBlock_uniform C hsh _ hmem
  have hcomp1 : ((litRows C σ vk p)[k]!).1.size = runNc C σ vk := by
    interval_cases k <;>
      first
        | exact hsh.zCommSize | exact hsh.genCommSize | exact hsh.posCommSize
        | exact hsh.addCommSize | exact hsh.mulCommSize | exact hsh.emulCommSize
        | exact hsh.endoCommSize
  have hcomp2 : ((litRows C σ vk p)[k]!).2.1.size = runNc C σ vk := by
    interval_cases k <;>
      first
        | exact hsh.zChunks.1 | exact hsh.genChunks.1 | exact hsh.posChunks.1
        | exact hsh.addChunks.1 | exact hsh.mulChunks.1 | exact hsh.emulChunks.1
        | exact hsh.endoChunks.1
  have hcomp3 : ((litRows C σ vk p)[k]!).2.2.size = runNc C σ vk := by
    interval_cases k <;>
      first
        | exact hsh.zChunks.2 | exact hsh.genChunks.2 | exact hsh.posChunks.2
        | exact hsh.addChunks.2 | exact hsh.mulChunks.2 | exact hsh.emulChunks.2
        | exact hsh.endoChunks.2
  have hread := rowF_read C hcomp1 hcomp2 hcomp3 hc
  rw [show ((litRows C σ vk p)[k]!
      : Array C.Point × Array C.ScalarField × Array C.ScalarField)
      = (((litRows C σ vk p)[k]!).1, ((litRows C σ vk p)[k]!).2.1,
          ((litRows C σ vk p)[k]!).2.2) from rfl]
  exact hread

/-- The first six σ chunk arrays are `nc`-chunked (through the `extract`). -/
private theorem sigmaExtract_chunks (hsh : RunShapes C σ vk p pub) :
    ∀ a ∈ vk.sigmaComm.extract 0 6, a.size = runNc C σ vk := by
  intro a ha
  rw [Array.mem_extract_iff_getElem] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact hsh.sigmaCommChunks _ (Array.getElem_mem _)

/-- **Coefficient-region read**: the flat stream at `nc + 1 + (22+q)·nc + c`. -/
private theorem stream_read_c (hsh : RunShapes C σ vk p pub)
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk)
    (q c : ℕ) (hq : q < 15) (hc : c < runNc C σ vk) :
    (flatRows C (runLogicalP C σ vk p pub pe))[runNc C σ vk + 1
        + (22 + q) * runNc C σ vk + c]!
      = ((vk.coefficientsComm[q]!)[c]!, (p.evals.coefficients[q]!).zeta[c]!,
          (p.evals.coefficients[q]!).zetaOmega[c]!) := by
  rw [stream_decomp]
  have hsPub : (rowF C (publicCommitment C σ vk (runNc C σ vk) pub,
      pe.zeta, pe.zetaOmega)).size = runNc C σ vk :=
    rowF_size C (publicCommitment_size C σ vk (runNc C σ vk) pub) hpe0 hpe1
  have hsFt : (rowF C (#[runFtComm C σ vk p pub],
      #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
      #[p.ftEval1])).size = 1 := rowF_size C rfl rfl rfl
  have hs7 : (Array.flatMap (rowF C) (litRows C σ vk p)).size
      = 7 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk) (litBlock_uniform C hsh)]
    simp [litRows]
  have hzipW : ((p.wComm.zip p.evals.w).map (zipRow C)).size = 15 := by
    simp [Array.size_map, Array.size_zip, hsh.wCommSize, hsh.wSize]
  have hsW : (Array.flatMap (rowF C)
      ((p.wComm.zip p.evals.w).map (zipRow C))).size = 15 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk)
        (zipBlock_uniform C hsh.wCommChunks hsh.wChunks), hzipW]
  have hzipC : ((vk.coefficientsComm.zip p.evals.coefficients).map
      (zipRow C)).size = 15 := by
    simp [Array.size_map, Array.size_zip, hsh.coeffCommSize, hsh.coeffSize]
  have hsC : (Array.flatMap (rowF C)
      ((vk.coefficientsComm.zip p.evals.coefficients).map (zipRow C))).size
      = 15 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk)
        (zipBlock_uniform C hsh.coeffCommChunks hsh.coeffChunks), hzipC]
  rw [getBang_append_left _ _ _ (by
      simp only [Array.size_append, hsPub, hsFt, hs7, hsW, hsC]
      have h1 := block_lt hq hc
      have h2 : (22 + q) * runNc C σ vk
          = 22 * runNc C σ vk + q * runNc C σ vk := by ring
      omega),
    getBang_append_at _ _ _ (q * runNc C σ vk + c) (by
      simp only [Array.size_append, hsPub, hsFt, hs7, hsW]
      have h2 : (22 + q) * runNc C σ vk
          = 22 * runNc C σ vk + q * runNc C σ vk := by ring
      omega)
      (by
        rw [hsC]
        exact block_lt hq hc),
    flatMap_uniform_read _ _ (runNc C σ vk)
      (zipBlock_uniform C hsh.coeffCommChunks hsh.coeffChunks) q c
      (by rw [hzipC]; omega) hc]
  have hqz : q < (vk.coefficientsComm.zip p.evals.coefficients).size := by
    simp only [Array.size_zip, hsh.coeffCommSize, hsh.coeffSize]
    omega
  have hread : ((vk.coefficientsComm.zip p.evals.coefficients).map (zipRow C))[q]!
      = (vk.coefficientsComm[q]!, (p.evals.coefficients[q]!).zeta,
          (p.evals.coefficients[q]!).zetaOmega) := by
    rw [getBang_map _ _ _ hqz, getElem!_pos _ q hqz,
      getElem!_pos vk.coefficientsComm q (by rw [hsh.coeffCommSize]; omega),
      getElem!_pos p.evals.coefficients q (by rw [hsh.coeffSize]; omega)]
    simp [zipRow, Array.getElem_zip]
  rw [hread]
  exact rowF_read C
    (hsh.coeffCommChunks _ (by
      rw [getElem!_pos vk.coefficientsComm q (by rw [hsh.coeffCommSize]; omega)]
      exact Array.getElem_mem _))
    ((hsh.coeffChunks _ (by
      rw [getElem!_pos p.evals.coefficients q (by rw [hsh.coeffSize]; omega)]
      exact Array.getElem_mem _)).1)
    ((hsh.coeffChunks _ (by
      rw [getElem!_pos p.evals.coefficients q (by rw [hsh.coeffSize]; omega)]
      exact Array.getElem_mem _)).2)
    hc

/-- **σ-region read**: the flat stream at `nc + 1 + (37+q)·nc + c`. -/
private theorem stream_read_s (hsh : RunShapes C σ vk p pub)
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk)
    (q c : ℕ) (hq : q < 6) (hc : c < runNc C σ vk) :
    (flatRows C (runLogicalP C σ vk p pub pe))[runNc C σ vk + 1
        + (37 + q) * runNc C σ vk + c]!
      = ((vk.sigmaComm[q]!)[c]!, (p.evals.s[q]!).zeta[c]!,
          (p.evals.s[q]!).zetaOmega[c]!) := by
  rw [stream_decomp]
  have hsPub : (rowF C (publicCommitment C σ vk (runNc C σ vk) pub,
      pe.zeta, pe.zetaOmega)).size = runNc C σ vk :=
    rowF_size C (publicCommitment_size C σ vk (runNc C σ vk) pub) hpe0 hpe1
  have hsFt : (rowF C (#[runFtComm C σ vk p pub],
      #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
      #[p.ftEval1])).size = 1 := rowF_size C rfl rfl rfl
  have hs7 : (Array.flatMap (rowF C) (litRows C σ vk p)).size
      = 7 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk) (litBlock_uniform C hsh)]
    simp [litRows]
  have hzipW : ((p.wComm.zip p.evals.w).map (zipRow C)).size = 15 := by
    simp [Array.size_map, Array.size_zip, hsh.wCommSize, hsh.wSize]
  have hsW : (Array.flatMap (rowF C)
      ((p.wComm.zip p.evals.w).map (zipRow C))).size = 15 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk)
        (zipBlock_uniform C hsh.wCommChunks hsh.wChunks), hzipW]
  have hzipC : ((vk.coefficientsComm.zip p.evals.coefficients).map
      (zipRow C)).size = 15 := by
    simp [Array.size_map, Array.size_zip, hsh.coeffCommSize, hsh.coeffSize]
  have hsC : (Array.flatMap (rowF C)
      ((vk.coefficientsComm.zip p.evals.coefficients).map (zipRow C))).size
      = 15 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk)
        (zipBlock_uniform C hsh.coeffCommChunks hsh.coeffChunks), hzipC]
  have hzipS : (((vk.sigmaComm.extract 0 6).zip p.evals.s).map (zipRow C)).size
      = 6 := by
    simp [Array.size_map, Array.size_zip, Array.size_extract, hsh.sigmaCommSize,
      hsh.sSize]
  rw [getBang_append_at _ _ _ (q * runNc C σ vk + c) (by
      simp only [Array.size_append, hsPub, hsFt, hs7, hsW, hsC]
      have h2 : (37 + q) * runNc C σ vk
          = 37 * runNc C σ vk + q * runNc C σ vk := by ring
      omega)
      (by
        rw [flatMap_uniform_size _ _ (runNc C σ vk)
            (zipBlock_uniform C (sigmaExtract_chunks C hsh) hsh.sChunks), hzipS]
        exact block_lt hq hc),
    flatMap_uniform_read _ _ (runNc C σ vk)
      (zipBlock_uniform C (sigmaExtract_chunks C hsh) hsh.sChunks) q c
      (by rw [hzipS]; omega) hc]
  have hqe : q < (vk.sigmaComm.extract 0 6).size := by
    simp only [Array.size_extract, hsh.sigmaCommSize]
    omega
  have hqz : q < ((vk.sigmaComm.extract 0 6).zip p.evals.s).size := by
    simp only [Array.size_zip, Array.size_extract, hsh.sigmaCommSize, hsh.sSize]
    omega
  have hext : (vk.sigmaComm.extract 0 6)[q]! = vk.sigmaComm[q]! := by
    rw [getElem!_pos _ q hqe,
      getElem!_pos vk.sigmaComm q (by rw [hsh.sigmaCommSize]; omega),
      Array.getElem_extract]
    congr 1
    omega
  have hread : (((vk.sigmaComm.extract 0 6).zip p.evals.s).map (zipRow C))[q]!
      = ((vk.sigmaComm.extract 0 6)[q]!, (p.evals.s[q]!).zeta,
          (p.evals.s[q]!).zetaOmega) := by
    rw [getBang_map _ _ _ hqz, getElem!_pos _ q hqz,
      getElem!_pos (vk.sigmaComm.extract 0 6) q hqe,
      getElem!_pos p.evals.s q (by rw [hsh.sSize]; omega)]
    simp [zipRow, Array.getElem_zip]
  rw [hread, hext]
  exact rowF_read C
    (hsh.sigmaCommChunks _ (by
      rw [getElem!_pos vk.sigmaComm q (by rw [hsh.sigmaCommSize]; omega)]
      exact Array.getElem_mem _))
    ((hsh.sChunks _ (by
      rw [getElem!_pos p.evals.s q (by rw [hsh.sSize]; omega)]
      exact Array.getElem_mem _)).1)
    ((hsh.sChunks _ (by
      rw [getElem!_pos p.evals.s q (by rw [hsh.sSize]; omega)]
      exact Array.getElem_mem _)).2)
    hc

/-- **Public-region read**: the flat stream at `c` is the public row's chunk `c`. -/
private theorem stream_read_pub (hsh : RunShapes C σ vk p pub)
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk)
    (c : ℕ) (hc : c < runNc C σ vk) :
    (flatRows C (runLogicalP C σ vk p pub pe))[c]!
      = ((publicCommitment C σ vk (runNc C σ vk) pub)[c]!, pe.zeta[c]!,
          pe.zetaOmega[c]!) := by
  rw [stream_decomp]
  have hsPub : (rowF C (publicCommitment C σ vk (runNc C σ vk) pub,
      pe.zeta, pe.zetaOmega)).size = runNc C σ vk :=
    rowF_size C (publicCommitment_size C σ vk (runNc C σ vk) pub) hpe0 hpe1
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
  exact rowF_read C (publicCommitment_size C σ vk (runNc C σ vk) pub) hpe0 hpe1 hc

/-- **The stream size**: the flat stream has `44·nc + 1` rows. -/
private theorem stream_size (hsh : RunShapes C σ vk p pub)
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk) :
    (flatRows C (runLogicalP C σ vk p pub pe)).size = 44 * runNc C σ vk + 1 := by
  rw [stream_decomp]
  have hsPub : (rowF C (publicCommitment C σ vk (runNc C σ vk) pub,
      pe.zeta, pe.zetaOmega)).size = runNc C σ vk :=
    rowF_size C (publicCommitment_size C σ vk (runNc C σ vk) pub) hpe0 hpe1
  have hsFt : (rowF C (#[runFtComm C σ vk p pub],
      #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
      #[p.ftEval1])).size = 1 := rowF_size C rfl rfl rfl
  have hs7 : (Array.flatMap (rowF C) (litRows C σ vk p)).size
      = 7 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk) (litBlock_uniform C hsh)]
    simp [litRows]
  have hzipW : ((p.wComm.zip p.evals.w).map (zipRow C)).size = 15 := by
    simp [Array.size_map, Array.size_zip, hsh.wCommSize, hsh.wSize]
  have hsW : (Array.flatMap (rowF C)
      ((p.wComm.zip p.evals.w).map (zipRow C))).size = 15 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk)
        (zipBlock_uniform C hsh.wCommChunks hsh.wChunks), hzipW]
  have hzipC : ((vk.coefficientsComm.zip p.evals.coefficients).map
      (zipRow C)).size = 15 := by
    simp [Array.size_map, Array.size_zip, hsh.coeffCommSize, hsh.coeffSize]
  have hsC : (Array.flatMap (rowF C)
      ((vk.coefficientsComm.zip p.evals.coefficients).map (zipRow C))).size
      = 15 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk)
        (zipBlock_uniform C hsh.coeffCommChunks hsh.coeffChunks), hzipC]
  have hzipS : (((vk.sigmaComm.extract 0 6).zip p.evals.s).map (zipRow C)).size
      = 6 := by
    simp [Array.size_map, Array.size_zip, Array.size_extract, hsh.sigmaCommSize,
      hsh.sSize]
  have hsS : (Array.flatMap (rowF C)
      (((vk.sigmaComm.extract 0 6).zip p.evals.s).map (zipRow C))).size
      = 6 * runNc C σ vk := by
    rw [flatMap_uniform_size _ _ (runNc C σ vk)
        (zipBlock_uniform C (sigmaExtract_chunks C hsh) hsh.sChunks), hzipS]
  simp only [Array.size_append, hsPub, hsFt, hs7, hsW, hsC, hsS]
  ring

end RegionReads

end Kimchi.Verifier.Chunked
