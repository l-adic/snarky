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

/-- **The chunked wire key–index correspondence**: the committed chunk columns are the
circuit's own (`Chunked.VKCorresponds`, through the `comms` view at the run's chunk
count), the scalar-side parameters match (the domain generator, the zero-knowledge row
count, the shifts, the `ft_eval0` endo coefficient, and the Poseidon MDS — read off
the fr-sponge table), AND the Lagrange-basis chunk commitments over the public region
are the basis polynomials' own chunk commitments. The Lagrange pin is NEW against the
`nc = 1` correspondence: with the public row IN the batch, the verifier COMPUTES the
public commitment from these key entries, and their correspondence is what binds the
proof-carried public evaluations to the circuit's public input. Adjudicated
numerically, per chunk, by `check_vk_correspond_chunked`. -/
def KimchiVK.Corresponds [Module C.ScalarField C.Point] {n : ℕ}
    (σ : SRS C.Point) (vk : KimchiVK C) (idx : Index C.ScalarField n) : Prop :=
  VKCorresponds σ (runNc C σ vk) (vk.comms (runNc C σ vk)) idx
    ∧ vk.omega = idx.omega
    ∧ vk.zkRows = idx.zkRows
    ∧ (fun i : Fin 7 => vk.shifts[(i : ℕ)]!) = idx.shifts
    ∧ vk.endo = idx.endoBase
    ∧ mdsOfParams vk.frParams = idx.mds
    ∧ ∀ (j : Fin n), (j : ℕ) < idx.publicCount → ∀ c : ℕ, c < runNc C σ vk →
        (vk.lagrangeBasis.getD (j : ℕ) #[]).getD c 0
          = commitPolyChunk σ
              (columnPoly idx.omega (Kimchi.Permutation.rowIndicator j)) c

/-- **The public commitment corresponds**: under the Lagrange chunk pin, the deployed
verifier's per-chunk public commitment is the per-chunk masked commitment of the
NEGATED public interpolant — the `pubC` feed of the chunked reduction. The
`.val`-scalar collapse is supplied per curve (`hsmul`). -/
theorem publicCommitment_corresponds [Module C.ScalarField C.Point]
    (σ : SRS C.Point) (vk : KimchiVK C) (pub : Array C.ScalarField) {n : ℕ}
    [NeZero n] (idx : Index C.ScalarField n)
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a.val • P = a • P)
    (hlag : ∀ (j : Fin n), (j : ℕ) < idx.publicCount → ∀ c : ℕ, c < runNc C σ vk →
      (vk.lagrangeBasis.getD (j : ℕ) #[]).getD c 0
        = commitPolyChunk σ
            (columnPoly idx.omega (Kimchi.Permutation.rowIndicator j)) c)
    (hlagsz : pub.size ≤ vk.lagrangeBasis.size)
    (hpub : pub.size = idx.publicCount)
    (c : ℕ) (hc : c < runNc C σ vk) :
    (publicCommitment C σ vk (runNc C σ vk) pub).getD c 0
      = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) c := by
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
            (columnPoly idx.omega (Kimchi.Permutation.rowIndicator j)) c = 0 := by
      intro j
      have hz : pubAt idx (pubView idx pub) j = 0 := by
        unfold pubAt
        rw [dif_neg (by omega)]
      rw [hz, neg_zero, zero_smul]
    rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero, zero_add]
    simp [Array.getD, hc]
  · rw [if_neg h0]
    rw [show ((Array.range (runNc C σ vk)).map (fun c =>
        ((vk.lagrangeBasis.extract 0 pub.size).zip pub).foldl
          (fun acc Pp => acc + (-Pp.2).val • Pp.1.getD c 0) 0 + σ.h)).getD c 0
      = ((vk.lagrangeBasis.extract 0 pub.size).zip pub).foldl
          (fun acc Pp => acc + (-Pp.2).val • Pp.1.getD c 0) 0 + σ.h from by
        simp [Array.getD, hc]]
    congr 1
    rw [← Array.foldl_toList, addFoldl_aux, zero_add]
    have hzipsz : ((vk.lagrangeBasis.extract 0 pub.size).zip pub).size = pub.size := by
      simp only [Array.size_zip, Array.size_extract]
      omega
    have hlen : ((vk.lagrangeBasis.extract 0 pub.size).zip pub).toList.length
        = pub.size := by
      rw [Array.length_toList, hzipsz]
    -- both sides as `range`-indexed sums of total functions of the row number
    calc (∑ i : Fin ((vk.lagrangeBasis.extract 0 pub.size).zip pub).toList.length,
          (-(((vk.lagrangeBasis.extract 0 pub.size).zip pub).toList[i]).2).val
            • (((vk.lagrangeBasis.extract 0 pub.size).zip pub).toList[i]).1.getD c 0)
        = ∑ i : Fin ((vk.lagrangeBasis.extract 0 pub.size).zip pub).toList.length,
            (fun m => (-(pub.getD m 0)).val
              • ((vk.lagrangeBasis.getD m #[]).getD c 0)) (i : ℕ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hilt : (i : ℕ) < pub.size := by
            have := i.isLt
            omega
          have hie : (i : ℕ)
              < ((vk.lagrangeBasis.extract 0 pub.size).zip pub).size := by omega
          have hix : (i : ℕ) < min pub.size vk.lagrangeBasis.size := by omega
          have hextr : (i : ℕ) < (vk.lagrangeBasis.extract 0 pub.size).size := by
            rw [Array.size_extract]
            omega
          have hentry : ((vk.lagrangeBasis.extract 0 pub.size).zip pub).toList[i]
              = ((vk.lagrangeBasis.extract 0 pub.size)[(i : ℕ)]'hextr,
                pub[(i : ℕ)]'hilt) := by
            rw [show ((vk.lagrangeBasis.extract 0 pub.size).zip pub).toList[i]
                = ((vk.lagrangeBasis.extract 0 pub.size).zip pub)[(i : ℕ)]'hie from
              Array.getElem_toList _]
            exact Array.getElem_zip
          rw [hentry]
          have hib : (i : ℕ) < vk.lagrangeBasis.size := by omega
          have hlagread : (vk.lagrangeBasis.extract 0 pub.size)[(i : ℕ)]'hextr
              = vk.lagrangeBasis.getD (i : ℕ) #[] := by
            rw [Array.getElem_extract,
              show vk.lagrangeBasis.getD (i : ℕ) #[]
                = vk.lagrangeBasis[(i : ℕ)]'hib from by simp [Array.getD, hib]]
            congr 1
            omega
          rw [hlagread, show pub[(i : ℕ)]'hilt = pub.getD (i : ℕ) 0 from by
            simp [Array.getD, hilt]]
      _ = ∑ m ∈ Finset.range pub.size,
            (-(pub.getD m 0)).val • ((vk.lagrangeBasis.getD m #[]).getD c 0) := by
          rw [Fin.sum_univ_eq_sum_range
            (fun m => (-(pub.getD m 0)).val
              • ((vk.lagrangeBasis.getD m #[]).getD c 0))
            (((vk.lagrangeBasis.extract 0 pub.size).zip pub).toList.length), hlen]
      _ = ∑ m ∈ Finset.range pub.size,
            (if h : m < n then (-(pubAt idx (pubView idx pub) ⟨m, h⟩))
              • commitPolyChunk σ (columnPoly idx.omega
                  (Kimchi.Permutation.rowIndicator ⟨m, h⟩)) c else 0) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          have hmlt : m < pub.size := Finset.mem_range.mp hm
          have hmn : m < n := by omega
          rw [dif_pos hmn]
          have hjp : ((⟨m, hmn⟩ : Fin n) : ℕ) < idx.publicCount := by
            show m < idx.publicCount
            omega
          have hpubAt : pubAt idx (pubView idx pub) ⟨m, hmn⟩ = pub.getD m 0 := by
            unfold pubAt
            rw [dif_pos hjp]
            rfl
          rw [hpubAt, ← hlag ⟨m, hmn⟩ hjp c hc, hsmul]
      _ = ∑ m ∈ Finset.range n,
            (if h : m < n then (-(pubAt idx (pubView idx pub) ⟨m, h⟩))
              • commitPolyChunk σ (columnPoly idx.omega
                  (Kimchi.Permutation.rowIndicator ⟨m, h⟩)) c else 0) := by
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
                  (Kimchi.Permutation.rowIndicator ⟨m, h⟩)) c else 0) (j : ℕ) :=
          (Fin.sum_univ_eq_sum_range
            (fun m => if h : m < n then (-(pubAt idx (pubView idx pub) ⟨m, h⟩))
              • commitPolyChunk σ (columnPoly idx.omega
                  (Kimchi.Permutation.rowIndicator ⟨m, h⟩)) c else 0) n).symm
      _ = ∑ j : Fin n, (-(pubAt idx (pubView idx pub) j))
            • commitPolyChunk σ (columnPoly idx.omega
                (Kimchi.Permutation.rowIndicator j)) c := by
          refine Finset.sum_congr rfl fun j _ => ?_
          beta_reduce
          rw [dif_pos j.isLt]

/-! ## The scalar-side reconciliations: the run's claims are the abstract batch's -/

section ScalarReconcile

variable {σ : SRS C.Point} {vk : KimchiVK C} {p : KimchiProof C}
  {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Array C.ScalarField)}
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
  split_ifs with h1 h2 h3 h4 h5
  · have := block_lt (show 7 + (i : ℕ) < 43 by omega) hc
    omega
  · omega
  · have := block_lt (show 37 + ((i : ℕ) - 16) < 43 by omega) hc
    omega
  · have := block_lt (show 22 + ((i : ℕ) - 22) < 43 by omega) hc
    omega
  · have := block_lt (show 1 + ((i : ℕ) - 37) < 43 by omega) hc
    omega
  · omega

/-- `streamPos` at a witness row. -/
private theorem streamPos_wRow (nc : ℕ) (q : Fin 15) (ch : ℕ) :
    streamPos nc (wRow q) ch = nc + 1 + (7 + (q : ℕ)) * nc + ch := by
  simp only [streamPos, wRow]
  rw [if_pos q.isLt]

/-- `streamPos` at the accumulator row (`0·nc` kept for the region-read shape). -/
private theorem streamPos_zRow (nc : ℕ) (ch : ℕ) :
    streamPos nc zRow ch = nc + 1 + 0 * nc + ch := by
  simp only [streamPos, zRow]
  rw [if_neg (by omega), if_pos (by omega)]
  omega

/-- `streamPos` at a σ row. -/
private theorem streamPos_sRow (nc : ℕ) (i : Fin 6) (ch : ℕ) :
    streamPos nc (sRow i) ch = nc + 1 + (37 + (i : ℕ)) * nc + ch := by
  simp only [streamPos, sRow]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]

/-- `streamPos` at a coefficient row. -/
private theorem streamPos_cRow (nc : ℕ) (q : Fin 15) (ch : ℕ) :
    streamPos nc (cRow q) ch = nc + 1 + (22 + (q : ℕ)) * nc + ch := by
  simp only [streamPos, cRow]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]

/-- `streamPos` at a selector row. -/
private theorem streamPos_selRow (nc : ℕ) (j : Fin 6) (ch : ℕ) :
    streamPos nc (selRow j) ch = nc + 1 + (1 + (j : ℕ)) * nc + ch := by
  simp only [streamPos, selRow]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), Nat.add_sub_cancel_left]

/-- `streamPos` at the public row. -/
private theorem streamPos_pubRow (nc : ℕ) (ch : ℕ) :
    streamPos nc pubRow ch = ch := by
  simp only [streamPos, pubRow]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- Reading the run input's evaluation matrix at a stream position: the flat row's
claim pair. -/
private theorem runEvals_read (hsh : RunShapes C σ vk p pub)
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk)
    (i : Fin 44) (c : ℕ) (hc : c < runNc C σ vk) :
    (runInputP C σ vk p pub pe v u).evals[streamPos (runNc C σ vk) i c]!
      = #[((flatRows C (runLogicalP C σ vk p pub pe))[streamPos (runNc C σ vk)
            i c]!).2.1,
          ((flatRows C (runLogicalP C σ vk p pub pe))[streamPos (runNc C σ vk)
            i c]!).2.2] := by
  show ((flatRows C (runLogicalP C σ vk p pub pe)).map
      (fun r => #[r.2.1, r.2.2]))[streamPos (runNc C σ vk) i c]! = _
  rw [getBang_map _ _ _ (by
    rw [stream_size C hsh hpe0 hpe1]
    exact streamPos_lt _ i c hc)]

/-- A `Fin nc`-indexed power sum whose entries read an `nc`-sized array is that
array's chunk combination. -/
private theorem sum_readsTo (xM : C.ScalarField) (w : Array C.ScalarField)
    (hw : w.size = runNc C σ vk) (f : Fin (runNc C σ vk) → C.ScalarField)
    (hf : ∀ ch : Fin (runNc C σ vk), f ch = w[(ch : ℕ)]!) :
    (∑ ch : Fin (runNc C σ vk), xM ^ (ch : ℕ) * f ch) = combineAt xM w := by
  rw [combineAt_eq_sum]
  refine (Fintype.sum_equiv (finCongr hw) _ _ fun i => ?_).symm
  rw [hf (finCongr hw i)]
  simp only [finCongr_apply, Fin.val_cast, Fin.getElem_fin]
  rw [getElem!_pos w (i : ℕ) i.isLt]

/-- **The chunk-combined claimed record is the run's own** (`evals.combine`): the
abstract `claimedEvals`, fed the run's flat claims at the stream positions, IS the
verifier's combined record `p.linEvals` at the run's combination powers. Pure layout
reading through the region reads. -/
private theorem claimedEvals_run_eq (hsh : RunShapes C σ vk p pub)
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk) :
    claimedEvals (runZetaM C σ vk p pub) (runZetaOmegaM C σ vk p pub)
        (fun (i : Fin 44) (ch : Fin (runNc C σ vk)) (j : Fin 2) =>
          ((runInputP C σ vk p pub pe v u).evals[streamPos (runNc C σ vk) i
              (ch : ℕ)]!)[(j : ℕ)]!)
      = p.linEvals (runZetaM C σ vk p pub) (runZetaOmegaM C σ vk p pub) := by
  refine evals_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · funext col
    refine sum_readsTo C _ _ ?_ _ fun ch => ?_
    · rw [getElem!_pos p.evals.w (col : ℕ) (by rw [hsh.wSize]; exact col.isLt)]
      exact (hsh.wChunks _ (Array.getElem_mem _)).1
    · beta_reduce
      rw [runEvals_read C hsh hpe0 hpe1 (wRow col) (ch : ℕ) ch.isLt, streamPos_wRow,
        stream_read_w C hsh hpe0 hpe1 (col : ℕ) (ch : ℕ) col.isLt ch.isLt]
      rfl
  · funext col
    refine sum_readsTo C _ _ ?_ _ fun ch => ?_
    · rw [getElem!_pos p.evals.w (col : ℕ) (by rw [hsh.wSize]; exact col.isLt)]
      exact (hsh.wChunks _ (Array.getElem_mem _)).2
    · beta_reduce
      rw [runEvals_read C hsh hpe0 hpe1 (wRow col) (ch : ℕ) ch.isLt, streamPos_wRow,
        stream_read_w C hsh hpe0 hpe1 (col : ℕ) (ch : ℕ) col.isLt ch.isLt]
      rfl
  · refine sum_readsTo C _ _ hsh.zChunks.1 _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C hsh hpe0 hpe1 zRow (ch : ℕ) ch.isLt, streamPos_zRow,
      stream_read_lit C hsh hpe0 hpe1 0 (ch : ℕ) (by omega) ch.isLt]
    rfl
  · refine sum_readsTo C _ _ hsh.zChunks.2 _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C hsh hpe0 hpe1 zRow (ch : ℕ) ch.isLt, streamPos_zRow,
      stream_read_lit C hsh hpe0 hpe1 0 (ch : ℕ) (by omega) ch.isLt]
    rfl
  · funext i
    refine sum_readsTo C _ _ ?_ _ fun ch => ?_
    · rw [getElem!_pos p.evals.s (i : ℕ) (by rw [hsh.sSize]; exact i.isLt)]
      exact (hsh.sChunks _ (Array.getElem_mem _)).1
    · beta_reduce
      rw [runEvals_read C hsh hpe0 hpe1 (sRow i) (ch : ℕ) ch.isLt, streamPos_sRow,
        stream_read_s C hsh hpe0 hpe1 (i : ℕ) (ch : ℕ) i.isLt ch.isLt]
      rfl
  · funext col
    refine sum_readsTo C _ _ ?_ _ fun ch => ?_
    · rw [getElem!_pos p.evals.coefficients (col : ℕ) (by
        rw [hsh.coeffSize]
        exact col.isLt)]
      exact (hsh.coeffChunks _ (Array.getElem_mem _)).1
    · beta_reduce
      rw [runEvals_read C hsh hpe0 hpe1 (cRow col) (ch : ℕ) ch.isLt, streamPos_cRow,
        stream_read_c C hsh hpe0 hpe1 (col : ℕ) (ch : ℕ) col.isLt ch.isLt]
      rfl
  · refine sum_readsTo C _ _ hsh.genChunks.1 _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C hsh hpe0 hpe1 (selRow 0) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C hsh hpe0 hpe1 (1 + ((0 : Fin 6) : ℕ)) (ch : ℕ) (by decide)
        ch.isLt]
    rfl
  · refine sum_readsTo C _ _ hsh.posChunks.1 _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C hsh hpe0 hpe1 (selRow 1) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C hsh hpe0 hpe1 (1 + ((1 : Fin 6) : ℕ)) (ch : ℕ) (by decide)
        ch.isLt]
    rfl
  · refine sum_readsTo C _ _ hsh.addChunks.1 _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C hsh hpe0 hpe1 (selRow 2) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C hsh hpe0 hpe1 (1 + ((2 : Fin 6) : ℕ)) (ch : ℕ) (by decide)
        ch.isLt]
    rfl
  · refine sum_readsTo C _ _ hsh.mulChunks.1 _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C hsh hpe0 hpe1 (selRow 3) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C hsh hpe0 hpe1 (1 + ((3 : Fin 6) : ℕ)) (ch : ℕ) (by decide)
        ch.isLt]
    rfl
  · refine sum_readsTo C _ _ hsh.emulChunks.1 _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C hsh hpe0 hpe1 (selRow 4) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C hsh hpe0 hpe1 (1 + ((4 : Fin 6) : ℕ)) (ch : ℕ) (by decide)
        ch.isLt]
    rfl
  · refine sum_readsTo C _ _ hsh.endoChunks.1 _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C hsh hpe0 hpe1 (selRow 5) (ch : ℕ) ch.isLt, streamPos_selRow,
      stream_read_lit C hsh hpe0 hpe1 (1 + ((5 : Fin 6) : ℕ)) (ch : ℕ) (by decide)
        ch.isLt]
    rfl

/-- **The combined public claim is the run's own**: `claimedPub` at the stream's
public-row claims is the verifier's chunk-combined public evaluation. -/
private theorem claimedPub_run_eq (hsh : RunShapes C σ vk p pub)
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk) :
    claimedPub (runZetaM C σ vk p pub)
        (fun (i : Fin 44) (ch : Fin (runNc C σ vk)) (j : Fin 2) =>
          ((runInputP C σ vk p pub pe v u).evals[streamPos (runNc C σ vk) i
              (ch : ℕ)]!)[(j : ℕ)]!)
      = combineAt (runZetaM C σ vk p pub) pe.zeta := by
  refine sum_readsTo C _ _ hpe0 _ fun ch => ?_
  beta_reduce
  rw [runEvals_read C hsh hpe0 hpe1 pubRow (ch : ℕ) ch.isLt, streamPos_pubRow,
    stream_read_pub C hsh hpe0 hpe1 (ch : ℕ) ch.isLt]
  rfl

/-- **The constructed ft commitment is the double Maller collapse** (generic in the
`.val`-scalar bridge): the executable `runFtComm` — `combine(ζ^max, f_comm) −
(ζⁿ − 1).val • combine(ζ^max, t_comm)` — is the abstract `•`-combination
`ft_identity_of_chunks` consumes: `pScalar • ∑_c (ζ^max)^c • σ₆C_c
− (ζⁿ − 1) • ∑_j (ζ^max)^j • tCommⱼ`. -/
private theorem runFtComm_eq [Module C.ScalarField C.Point]
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a • P = a.val • P)
    (hsh : RunShapes C σ vk p pub) {n : ℕ} (hn : vk.n = n) :
    runFtComm C σ vk p pub
      = runPScalar C σ vk p pub
          • ∑ c : Fin (runNc C σ vk),
              ((runOracles C σ vk p pub).zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • (vk.sigmaComm.getD 6 #[]).getD (c : ℕ) 0
        - ((runOracles C σ vk p pub).zeta ^ n - 1)
            • ∑ j : Fin p.tComm.size,
                ((runOracles C σ vk p pub).zeta ^ 2 ^ σ.k) ^ (j : ℕ)
                  • p.tComm.getD (j : ℕ) 0 := by
  have hζM : runZetaM C σ vk p pub = (runOracles C σ vk p pub).zeta ^ 2 ^ σ.k := by
    unfold runZetaM
    rw [powPow2_eq]
  have hζN : runZetaN C σ vk p pub = (runOracles C σ vk p pub).zeta ^ n := by
    unfold runZetaN
    rw [powPow2_eq, ← hn]
    rfl
  have h6lt : 6 < vk.sigmaComm.size := by
    rw [hsh.sigmaCommSize]
    omega
  have hσ6 : vk.sigmaComm.getD 6 #[] = vk.sigmaComm[6] := by
    simp [Array.getD, h6lt]
  have hσ6sz : (vk.sigmaComm.getD 6 #[]).size = runNc C σ vk := by
    rw [hσ6]
    exact hsh.sigmaCommChunks _ (Array.getElem_mem _)
  unfold runFtComm runFComm
  rw [combineCommitments_eq hsmul, combineCommitments_eq hsmul, ← hsmul, hζM, hζN]
  congr 1
  · rw [combinedCommitment, Finset.smul_sum, hσ6]
    have hmapsz : ((vk.sigmaComm[6]'h6lt).map
        (fun P => (runPScalar C σ vk p pub).val • P)).size = runNc C σ vk := by
      rw [Array.size_map, ← hσ6, hσ6sz]
    refine Fintype.sum_equiv (finCongr hmapsz) _ _ fun i => ?_
    simp only [finCongr_apply, Fin.val_cast, Fin.getElem_fin, Array.getElem_map]
    rw [← hsmul, ← mul_smul, ← mul_smul, mul_comm]
    congr 1
    have hib : (i : ℕ) < (vk.sigmaComm[6]'h6lt).size := by
      have := i.isLt
      simp only [Array.size_map] at this
      omega
    simp [Array.getD, hib]
  · congr 1
    rw [combinedCommitment]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [Array.getD, j.isLt]

end ScalarReconcile

/-! ## The group-side reconciliation: the flat stream carries the abstract batch -/

section GroupReconcile

variable {σ : SRS C.Point} {vk : KimchiVK C} {p : KimchiProof C}
  {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Array C.ScalarField)}

/-- **The abstract 44-row chunked batch is the flat stream's commitment column**: at
every batch row and chunk, `batchC` — fed the wire witness/accumulator/public chunk
reads and the key's `comms` view — is the flat stream's commitment at the row's stream
position. The layout bridge `hbound₀` consumes. -/
private theorem batchC_eq_flat (hsh : RunShapes C σ vk p pub)
    (hpe0 : pe.zeta.size = runNc C σ vk) (hpe1 : pe.zetaOmega.size = runNc C σ vk)
    (i : Fin 44) (c : Fin (runNc C σ vk)) :
    batchC (fun (col : Fin 15) (c : Fin (runNc C σ vk)) =>
          (p.wComm[(col : ℕ)]!)[(c : ℕ)]!)
        (fun c => p.zComm[(c : ℕ)]!)
        (fun c => (publicCommitment C σ vk (runNc C σ vk) pub)[(c : ℕ)]!)
        (vk.comms (runNc C σ vk)) i c
      = ((flatRows C (runLogicalP C σ vk p pub pe))[streamPos (runNc C σ vk) i
          (c : ℕ)]!).1 := by
  by_cases h1 : (i : ℕ) < 15
  · rw [show streamPos (runNc C σ vk) i (c : ℕ)
        = runNc C σ vk + 1 + (7 + (i : ℕ)) * runNc C σ vk + (c : ℕ) from by
          unfold streamPos
          rw [if_pos h1],
      stream_read_w C hsh hpe0 hpe1 (i : ℕ) (c : ℕ) h1 c.isLt]
    simp only [batchC]
    rw [dif_pos h1]
  · by_cases h2 : (i : ℕ) < 16
    · rw [show streamPos (runNc C σ vk) i (c : ℕ)
          = runNc C σ vk + 1 + 0 * runNc C σ vk + (c : ℕ) from by
            unfold streamPos
            rw [if_neg h1, if_pos h2]
            omega,
        stream_read_lit C hsh hpe0 hpe1 0 (c : ℕ) (by omega) c.isLt]
      simp only [batchC]
      rw [dif_neg h1, if_pos h2]
      rfl
    · by_cases h3 : (i : ℕ) < 22
      · rw [show streamPos (runNc C σ vk) i (c : ℕ)
            = runNc C σ vk + 1 + (37 + ((i : ℕ) - 16)) * runNc C σ vk + (c : ℕ) from by
              unfold streamPos
              rw [if_neg h1, if_neg h2, if_pos h3],
          stream_read_s C hsh hpe0 hpe1 ((i : ℕ) - 16) (c : ℕ) (by omega) c.isLt]
        simp only [batchC]
        rw [dif_neg h1, if_neg h2, dif_pos h3]
        show (vk.sigmaComm.getD ((i : ℕ) - 16) #[]).getD (c : ℕ) 0
          = (vk.sigmaComm[(i : ℕ) - 16]!)[(c : ℕ)]!
        have hb1 : (i : ℕ) - 16 < vk.sigmaComm.size := by
          rw [hsh.sigmaCommSize]
          omega
        rw [getElem!_pos vk.sigmaComm ((i : ℕ) - 16) hb1]
        have hb2 : (c : ℕ) < (vk.sigmaComm[(i : ℕ) - 16]'hb1).size := by
          rw [hsh.sigmaCommChunks _ (Array.getElem_mem _)]
          exact c.isLt
        rw [getElem!_pos (vk.sigmaComm[(i : ℕ) - 16]'hb1) (c : ℕ) hb2]
        simp [Array.getD, hb1, hb2]
      · by_cases h4 : (i : ℕ) < 37
        · rw [show streamPos (runNc C σ vk) i (c : ℕ)
              = runNc C σ vk + 1 + (22 + ((i : ℕ) - 22)) * runNc C σ vk + (c : ℕ)
              from by
                unfold streamPos
                rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4],
            stream_read_c C hsh hpe0 hpe1 ((i : ℕ) - 22) (c : ℕ) (by omega) c.isLt]
          simp only [batchC]
          rw [dif_neg h1, if_neg h2, dif_neg h3, dif_pos h4]
          show (vk.coefficientsComm.getD ((i : ℕ) - 22) #[]).getD (c : ℕ) 0
            = (vk.coefficientsComm[(i : ℕ) - 22]!)[(c : ℕ)]!
          have hb1 : (i : ℕ) - 22 < vk.coefficientsComm.size := by
            rw [hsh.coeffCommSize]
            omega
          rw [getElem!_pos vk.coefficientsComm ((i : ℕ) - 22) hb1]
          have hb2 : (c : ℕ) < (vk.coefficientsComm[(i : ℕ) - 22]'hb1).size := by
            rw [hsh.coeffCommChunks _ (Array.getElem_mem _)]
            exact c.isLt
          rw [getElem!_pos (vk.coefficientsComm[(i : ℕ) - 22]'hb1) (c : ℕ) hb2]
          simp [Array.getD, hb1, hb2]
        · by_cases h5 : (i : ℕ) < 43
          · rw [show streamPos (runNc C σ vk) i (c : ℕ)
                = runNc C σ vk + 1 + (1 + ((i : ℕ) - 37)) * runNc C σ vk + (c : ℕ)
                from by
                  unfold streamPos
                  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5],
              stream_read_lit C hsh hpe0 hpe1 (1 + ((i : ℕ) - 37)) (c : ℕ) (by omega)
                c.isLt]
            simp only [batchC]
            rw [dif_neg h1, if_neg h2, dif_neg h3, dif_neg h4, dif_pos h5]
            obtain ⟨iv, hivlt⟩ := i
            have h37 : 37 ≤ iv := Nat.not_lt.mp h4
            have h43 : iv < 43 := h5
            have hgen : (c : ℕ) < vk.genericComm.size := by
              rw [hsh.genCommSize]
              exact c.isLt
            have hpos : (c : ℕ) < vk.poseidonComm.size := by
              rw [hsh.posCommSize]
              exact c.isLt
            have hadd : (c : ℕ) < vk.completeAddComm.size := by
              rw [hsh.addCommSize]
              exact c.isLt
            have hmul : (c : ℕ) < vk.mulComm.size := by
              rw [hsh.mulCommSize]
              exact c.isLt
            have hemul : (c : ℕ) < vk.emulComm.size := by
              rw [hsh.emulCommSize]
              exact c.isLt
            have hendo : (c : ℕ) < vk.endomulScalarComm.size := by
              rw [hsh.endoCommSize]
              exact c.isLt
            interval_cases iv
            · show vk.genericComm.getD (c : ℕ) 0 = vk.genericComm[(c : ℕ)]!
              rw [getElem!_pos vk.genericComm (c : ℕ) hgen]
              simp [Array.getD, hgen]
            · show vk.poseidonComm.getD (c : ℕ) 0 = vk.poseidonComm[(c : ℕ)]!
              rw [getElem!_pos vk.poseidonComm (c : ℕ) hpos]
              simp [Array.getD, hpos]
            · show vk.completeAddComm.getD (c : ℕ) 0 = vk.completeAddComm[(c : ℕ)]!
              rw [getElem!_pos vk.completeAddComm (c : ℕ) hadd]
              simp [Array.getD, hadd]
            · show vk.mulComm.getD (c : ℕ) 0 = vk.mulComm[(c : ℕ)]!
              rw [getElem!_pos vk.mulComm (c : ℕ) hmul]
              simp [Array.getD, hmul]
            · show vk.emulComm.getD (c : ℕ) 0 = vk.emulComm[(c : ℕ)]!
              rw [getElem!_pos vk.emulComm (c : ℕ) hemul]
              simp [Array.getD, hemul]
            · show vk.endomulScalarComm.getD (c : ℕ) 0
                = vk.endomulScalarComm[(c : ℕ)]!
              rw [getElem!_pos vk.endomulScalarComm (c : ℕ) hendo]
              simp [Array.getD, hendo]
          · rw [show streamPos (runNc C σ vk) i (c : ℕ) = (c : ℕ) from by
                unfold streamPos
                rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5],
              stream_read_pub C hsh hpe0 hpe1 (c : ℕ) c.isLt]
            simp only [batchC]
            rw [dif_neg h1, if_neg h2, dif_neg h3, dif_neg h4, dif_neg h5]

end GroupReconcile

/-! ## The chunked run-level terminal roots -/

private instance : Inhabited IpaVesta.Point := ⟨0⟩
private instance : Inhabited IpaPallas.Point := ⟨0⟩

/-- **The chunked run-level residue-free root (Vesta)**: from a genuine deployed
CHUNKED acceptance `Chunked.KimchiVesta.verify σ vk p pub = true` at production
chunking `nc · 2^σ.k = n`, the AGM path delivers the guarded
`Satisfies idx (pubView idx pub) wTab` — the assembled witness table of the algebraic
prover's own per-chunk representations. The prover supplies SRS-basis representations
of the run's `44·nc + 1` flat segment rows (`aRef`/`ρRef`) and of the `tComm` chunks
(`aT`/`ρT`); everything else is derived from the single reflected run: the openings
seam `Chunked.kimchiProof_sound_of_openings` is fed directly (reference side: the
representations at the stream positions; consumer side: the eval pins of the run's one
accepted opening), the public row is pinned through `publicCommitment_corresponds` and
the key's Lagrange chunk pin, and the quotient `t := ftChunkAssembly σ.k p.tComm.size
aT` with its Maller identity comes from the part-1 ft opening through
`ft_identity_of_chunks` at the DOUBLE `ζ^{2^σ.k}` collapse. The key–index hypothesis
is the chunked `KimchiVK.Corresponds` — per-chunk `VKCorresponds`, the scalar pins,
and the Lagrange pin. Axioms consumed: `Chunked.kimchi_fiat_shamir_vesta` plus the
point-count-backed `Module` instance. No `ζⁿ ≠ 1` guard: at the chunked wire the
public claims are proof-carried batch data, believed only through binding — no
barycentric reconciliation. The Vesta chunked run-level root. -/
theorem kimchiVesta_run_sound_algebraic_ft (σ : SRS IpaVesta.Point)
    (vk : Chunked.KimchiVesta.VK) (p : Chunked.KimchiVesta.Proof) (pub : Array Fp)
    {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hn : vk.n = n) (hvk : KimchiVK.Corresponds IpaVesta.curve σ vk idx)
    (hpub : pub.size = idx.publicCount)
    (htpos : 0 < p.tComm.size)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : Chunked.KimchiVesta.verify σ vk p pub = true)
    (aRef : Fin (runInput IpaVesta.curve σ vk p pub).commitments.size
      → Fin (2 ^ σ.k) → Fp)
    (ρRef : Fin (runInput IpaVesta.curve σ vk p pub).commitments.size → Fp)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput IpaVesta.curve σ vk p pub).commitmentFn i)
    (aT : Fin p.tComm.size → Fin (2 ^ σ.k) → Fp) (ρT : Fin p.tComm.size → Fp)
    (hTC : ∀ j : Fin p.tComm.size, commit σ (aT j) (ρT j) = p.tComm.getD (j : ℕ) 0)
    (hξ : (runInput IpaVesta.curve σ vk p pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaVesta.curve σ vk p pub).pointFn
          (runInput IpaVesta.curve σ vk p pub).evalFn)
    (hr : (runInput IpaVesta.curve σ vk p pub).evalscale
      ∉ badROf σ aRef (runInput IpaVesta.curve σ vk p pub).pointFn
          (runInput IpaVesta.curve σ vk p pub).evalFn
          (runInput IpaVesta.curve σ vk p pub).polyscale) :
    ∃ (badB : Finset Fp) (badG : Fp → Finset Fp) (badA : Fp → Fp → Finset Fp)
        (badZ : Fp → Fp → Fp → Polynomial Fp → Finset Fp)
        (wTab : Fin n → Fin 15 → Fp),
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
                (ftChunkAssembly σ.k p.tComm.size aT) →
          (runOracles IpaVesta.curve σ vk p pub).zeta ≠ 1 →
          (runOracles IpaVesta.curve σ vk p pub).zeta
            ≠ idx.omega ^ (n - idx.zkRows) →
          Satisfies idx (pubView idx pub) wTab) := by
  obtain ⟨hvkc, homega, hzk, hshift, hendo, hmds, hlag⟩ := hvk
  -- (1) reflect the run; shapes, chunk arithmetic, and the batch width
  have hrun := kimchiVerify_reflects IpaVesta.curve σ vk p pub hacc
  have hsh := runShapes_of_shape IpaVesta.curve σ vk p pub hrun.shape
  have hpe := runPubEvals_size IpaVesta.curve σ vk p pub hrun.shape
  have hnc : 0 < runNc IpaVesta.curve σ vk := Nat.two_pow_pos _
  have hk : runNc IpaVesta.curve σ vk * 2 ^ σ.k = n := by
    unfold runNc
    rw [← pow_add]
    have := hsh.srsLe
    rw [show vk.domainLog2 - σ.k + σ.k = vk.domainLog2 from by omega]
    exact hn
  have hlt : ∀ (i : Fin 44) (c : Fin (runNc IpaVesta.curve σ vk)),
      streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ)
        < (runInput IpaVesta.curve σ vk p pub).commitments.size := by
    intro i c
    show streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ)
      < ((flatRows IpaVesta.curve (runLogicalP IpaVesta.curve σ vk p pub
          (runPubEvals IpaVesta.curve σ vk p pub))).map (·.1)).size
    rw [Array.size_map, stream_size IpaVesta.curve hsh hpe.1 hpe.2]
    exact streamPos_lt _ i _ c.isLt
  -- (2) the reference openings at the stream positions bind the abstract batch
  have hbound₀ : ∀ (i : Fin 44) (c : Fin (runNc IpaVesta.curve σ vk)),
      commit σ (aRef ⟨streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ), hlt i c⟩)
          (ρRef ⟨streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ), hlt i c⟩)
        = batchC (fun col c => (p.wComm[(col : ℕ)]!)[(c : ℕ)]!)
            (fun c => p.zComm[(c : ℕ)]!)
            (fun c => (publicCommitment IpaVesta.curve σ vk
                (runNc IpaVesta.curve σ vk) pub)[(c : ℕ)]!)
            (vk.comms (runNc IpaVesta.curve σ vk)) i c := by
    intro i c
    rw [hrep ⟨streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ), hlt i c⟩]
    show (runInput IpaVesta.curve σ vk p pub).commitments[streamPos
        (runNc IpaVesta.curve σ vk) i (c : ℕ)]'(hlt i c) = _
    rw [← getElem!_pos (runInput IpaVesta.curve σ vk p pub).commitments
      (streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ)) (hlt i c)]
    show ((flatRows IpaVesta.curve (runLogicalP IpaVesta.curve σ vk p pub
        (runPubEvals IpaVesta.curve σ vk p pub))).map
          (·.1))[streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ)]! = _
    rw [getBang_map _ _ _ (by
      rw [stream_size IpaVesta.curve hsh hpe.1 hpe.2]
      exact streamPos_lt _ i _ c.isLt)]
    exact (batchC_eq_flat IpaVesta.curve hsh hpe.1 hpe.2 i c).symm
  -- (3) the public row pinned through the Lagrange chunk pin
  have hpubC : ∀ c : Fin (runNc IpaVesta.curve σ vk),
      (publicCommitment IpaVesta.curve σ vk (runNc IpaVesta.curve σ vk)
          pub)[(c : ℕ)]!
        = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ) := by
    intro c
    have hb : (c : ℕ) < (publicCommitment IpaVesta.curve σ vk
        (runNc IpaVesta.curve σ vk) pub).size := by
      rw [publicCommitment_size]
      exact c.isLt
    rw [getElem!_pos (publicCommitment IpaVesta.curve σ vk
        (runNc IpaVesta.curve σ vk) pub) (c : ℕ) hb,
      show (publicCommitment IpaVesta.curve σ vk (runNc IpaVesta.curve σ vk)
          pub)[(c : ℕ)]'hb
        = (publicCommitment IpaVesta.curve σ vk (runNc IpaVesta.curve σ vk)
            pub).getD (c : ℕ) 0 from by simp [Array.getD, hb]]
    exact publicCommitment_corresponds IpaVesta.curve σ vk pub idx
      (fun a P => (Pasta.vesta_smul_val a P).symm) hlag hsh.lagSize hpub
      (c : ℕ) c.isLt
  -- (4) the openings seam, fed directly
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hnc hk hbind
      (vk.comms (runNc IpaVesta.curve σ vk)) hvkc (pubView idx pub)
      (fun col c => (p.wComm[(col : ℕ)]!)[(c : ℕ)]!)
      (fun c => p.zComm[(c : ℕ)]!)
      (fun c => (publicCommitment IpaVesta.curve σ vk
          (runNc IpaVesta.curve σ vk) pub)[(c : ℕ)]!)
      hpubC
      (fun i c => aRef ⟨streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ), hlt i c⟩)
      (fun i c => ρRef ⟨streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ), hlt i c⟩)
      hbound₀
  refine ⟨badB, badG, badA, badZ,
    extractTable idx.omega (fun col => assembledRow σ.k (runNc IpaVesta.curve σ vk)
      (fun c => aRef ⟨streamPos (runNc IpaVesta.curve σ vk) (wRow col) (c : ℕ),
        hlt (wRow col) c⟩)),
    hbounds, ?_⟩
  intro hβ hγ hα hζ hζ1 hζb
  -- (5) the eval pins from the run's single accepted opening (flat arity)
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _
    (kimchi_fiat_shamir_vesta σ vk p pub) hrun.accepts
  have hpins := eval_pins_of_opening σ hbind
    (runInput IpaVesta.curve σ vk p pub).commitmentFn
    (runInput IpaVesta.curve σ vk p pub).pointFn aRef ρRef hrep
    (runInput IpaVesta.curve σ vk p pub).evalFn
    (runInput IpaVesta.curve σ vk p pub).polyscale
    (runInput IpaVesta.curve σ vk p pub).evalscale hξ hr a ρ hopen
  -- (6) the part-1 ft opening and the Maller identity at the double collapse
  obtain ⟨aft, ρft, hcomm_ft, heval_ft⟩ :=
    ft_opening_of_reflected_vesta σ vk p pub hbind hacc aRef ρRef hrep hξ hr
  have hCσ6 : ∀ c : Fin (runNc IpaVesta.curve σ vk),
      (vk.sigmaComm.getD 6 #[]).getD (c : ℕ) 0
        = commitPolyChunk σ (idx.sigmaPoly 6) (c : ℕ) :=
    fun c => congrFun (congrArg (fun cm => cm.sigma 6) hvkc) c
  have hσ₆ : (idx.sigmaPoly 6).natDegree < runNc IpaVesta.curve σ vk * 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hcommit : commit σ aft ρft
      = runPScalar IpaVesta.curve σ vk p pub
          • ∑ c : Fin (runNc IpaVesta.curve σ vk),
              ((runOracles IpaVesta.curve σ vk p pub).zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • (vk.sigmaComm.getD 6 #[]).getD (c : ℕ) 0
        - ((runOracles IpaVesta.curve σ vk p pub).zeta ^ n - 1)
            • ∑ j : Fin p.tComm.size,
                ((runOracles IpaVesta.curve σ vk p pub).zeta ^ 2 ^ σ.k) ^ (j : ℕ)
                  • p.tComm.getD (j : ℕ) 0 :=
    hcomm_ft.trans (runFtComm_eq IpaVesta.curve Pasta.vesta_smul_val hsh hn)
  obtain ⟨htdeg, hteq0⟩ := ft_identity_of_chunks σ hbind (idx.sigmaPoly 6) hσ₆
    (fun c => (vk.sigmaComm.getD 6 #[]).getD (c : ℕ) 0) hCσ6 htpos hsh.tCommSize
    (fun j => p.tComm.getD (j : ℕ) 0) aT ρT hTC
    (runPScalar IpaVesta.curve σ vk p pub)
    (runOracles IpaVesta.curve σ vk p pub).zeta
    (runFtEval0 IpaVesta.curve σ vk p pub) n hk aft ρft hcommit heval_ft
  -- (7) reconcile the derived identity into the consumer's shape
  have hce := claimedEvals_run_eq IpaVesta.curve
    (v := (runVU IpaVesta.curve σ vk p pub).1)
    (u := (runVU IpaVesta.curve σ vk p pub).2) hsh hpe.1 hpe.2
  have hcp := claimedPub_run_eq IpaVesta.curve
    (v := (runVU IpaVesta.curve σ vk p pub).1)
    (u := (runVU IpaVesta.curve σ vk p pub).2) hsh hpe.1 hpe.2
  have hζM : runZetaM IpaVesta.curve σ vk p pub
      = (runOracles IpaVesta.curve σ vk p pub).zeta ^ 2 ^ σ.k := by
    unfold runZetaM
    rw [powPow2_eq]
  have hζwM : runZetaOmegaM IpaVesta.curve σ vk p pub
      = (idx.omega * (runOracles IpaVesta.curve σ vk p pub).zeta) ^ 2 ^ σ.k := by
    unfold runZetaOmegaM runZetaOmega
    rw [powPow2_eq, homega, mul_comm]
  unfold runPScalar runFtEval0 runFtEval0P runPubEval0 runLinEvals at hteq0
  rw [← hce, ← hcp, hζM, hζwM, hn, hzk, homega, hendo, hmds, hshift] at hteq0
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
    (ftChunkAssembly σ.k p.tComm.size aT)
    (runOracles IpaVesta.curve σ vk p pub).zeta
    (fun (i : Fin 44) (ch : Fin (runNc IpaVesta.curve σ vk)) (j : Fin 2) =>
      ((runInputP IpaVesta.curve σ vk p pub
          (runPubEvals IpaVesta.curve σ vk p pub)
          (runVU IpaVesta.curve σ vk p pub).1
          (runVU IpaVesta.curve σ vk p pub).2).evals[streamPos
            (runNc IpaVesta.curve σ vk) i (ch : ℕ)]!)[(j : ℕ)]!)
    (fun i c => aRef ⟨streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ), hlt i c⟩)
    (fun i c => ρRef ⟨streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ), hlt i c⟩)
    hβ hγ hα hζ hζ1 hζb htdeg
    (fun i c => ⟨hbound₀ i c,
      fun j => hpins ⟨streamPos (runNc IpaVesta.curve σ vk) i (c : ℕ), hlt i c⟩ j⟩)
    hteq0

/-- **The chunked run-level residue-free root (Pallas).** The Pallas-side twin of
`Chunked.kimchiVesta_run_sound_algebraic_ft`, over `Fq`/`IpaPallas`, its
Fiat–Shamir assumption `Chunked.kimchi_fiat_shamir_pallas`. -/
theorem kimchiPallas_run_sound_algebraic_ft (σ : SRS IpaPallas.Point)
    (vk : Chunked.KimchiPallas.VK) (p : Chunked.KimchiPallas.Proof) (pub : Array Fq)
    {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hn : vk.n = n) (hvk : KimchiVK.Corresponds IpaPallas.curve σ vk idx)
    (hpub : pub.size = idx.publicCount)
    (htpos : 0 < p.tComm.size)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : Chunked.KimchiPallas.verify σ vk p pub = true)
    (aRef : Fin (runInput IpaPallas.curve σ vk p pub).commitments.size
      → Fin (2 ^ σ.k) → Fq)
    (ρRef : Fin (runInput IpaPallas.curve σ vk p pub).commitments.size → Fq)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput IpaPallas.curve σ vk p pub).commitmentFn i)
    (aT : Fin p.tComm.size → Fin (2 ^ σ.k) → Fq) (ρT : Fin p.tComm.size → Fq)
    (hTC : ∀ j : Fin p.tComm.size, commit σ (aT j) (ρT j) = p.tComm.getD (j : ℕ) 0)
    (hξ : (runInput IpaPallas.curve σ vk p pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaPallas.curve σ vk p pub).pointFn
          (runInput IpaPallas.curve σ vk p pub).evalFn)
    (hr : (runInput IpaPallas.curve σ vk p pub).evalscale
      ∉ badROf σ aRef (runInput IpaPallas.curve σ vk p pub).pointFn
          (runInput IpaPallas.curve σ vk p pub).evalFn
          (runInput IpaPallas.curve σ vk p pub).polyscale) :
    ∃ (badB : Finset Fq) (badG : Fq → Finset Fq) (badA : Fq → Fq → Finset Fq)
        (badZ : Fq → Fq → Fq → Polynomial Fq → Finset Fq)
        (wTab : Fin n → Fin 15 → Fq),
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
                (ftChunkAssembly σ.k p.tComm.size aT) →
          (runOracles IpaPallas.curve σ vk p pub).zeta ≠ 1 →
          (runOracles IpaPallas.curve σ vk p pub).zeta
            ≠ idx.omega ^ (n - idx.zkRows) →
          Satisfies idx (pubView idx pub) wTab) := by
  obtain ⟨hvkc, homega, hzk, hshift, hendo, hmds, hlag⟩ := hvk
  -- (1) reflect the run; shapes, chunk arithmetic, and the batch width
  have hrun := kimchiVerify_reflects IpaPallas.curve σ vk p pub hacc
  have hsh := runShapes_of_shape IpaPallas.curve σ vk p pub hrun.shape
  have hpe := runPubEvals_size IpaPallas.curve σ vk p pub hrun.shape
  have hnc : 0 < runNc IpaPallas.curve σ vk := Nat.two_pow_pos _
  have hk : runNc IpaPallas.curve σ vk * 2 ^ σ.k = n := by
    unfold runNc
    rw [← pow_add]
    have := hsh.srsLe
    rw [show vk.domainLog2 - σ.k + σ.k = vk.domainLog2 from by omega]
    exact hn
  have hlt : ∀ (i : Fin 44) (c : Fin (runNc IpaPallas.curve σ vk)),
      streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ)
        < (runInput IpaPallas.curve σ vk p pub).commitments.size := by
    intro i c
    show streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ)
      < ((flatRows IpaPallas.curve (runLogicalP IpaPallas.curve σ vk p pub
          (runPubEvals IpaPallas.curve σ vk p pub))).map (·.1)).size
    rw [Array.size_map, stream_size IpaPallas.curve hsh hpe.1 hpe.2]
    exact streamPos_lt _ i _ c.isLt
  -- (2) the reference openings at the stream positions bind the abstract batch
  have hbound₀ : ∀ (i : Fin 44) (c : Fin (runNc IpaPallas.curve σ vk)),
      commit σ (aRef ⟨streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ), hlt i c⟩)
          (ρRef ⟨streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ), hlt i c⟩)
        = batchC (fun col c => (p.wComm[(col : ℕ)]!)[(c : ℕ)]!)
            (fun c => p.zComm[(c : ℕ)]!)
            (fun c => (publicCommitment IpaPallas.curve σ vk
                (runNc IpaPallas.curve σ vk) pub)[(c : ℕ)]!)
            (vk.comms (runNc IpaPallas.curve σ vk)) i c := by
    intro i c
    rw [hrep ⟨streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ), hlt i c⟩]
    show (runInput IpaPallas.curve σ vk p pub).commitments[streamPos
        (runNc IpaPallas.curve σ vk) i (c : ℕ)]'(hlt i c) = _
    rw [← getElem!_pos (runInput IpaPallas.curve σ vk p pub).commitments
      (streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ)) (hlt i c)]
    show ((flatRows IpaPallas.curve (runLogicalP IpaPallas.curve σ vk p pub
        (runPubEvals IpaPallas.curve σ vk p pub))).map
          (·.1))[streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ)]! = _
    rw [getBang_map _ _ _ (by
      rw [stream_size IpaPallas.curve hsh hpe.1 hpe.2]
      exact streamPos_lt _ i _ c.isLt)]
    exact (batchC_eq_flat IpaPallas.curve hsh hpe.1 hpe.2 i c).symm
  -- (3) the public row pinned through the Lagrange chunk pin
  have hpubC : ∀ c : Fin (runNc IpaPallas.curve σ vk),
      (publicCommitment IpaPallas.curve σ vk (runNc IpaPallas.curve σ vk)
          pub)[(c : ℕ)]!
        = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ) := by
    intro c
    have hb : (c : ℕ) < (publicCommitment IpaPallas.curve σ vk
        (runNc IpaPallas.curve σ vk) pub).size := by
      rw [publicCommitment_size]
      exact c.isLt
    rw [getElem!_pos (publicCommitment IpaPallas.curve σ vk
        (runNc IpaPallas.curve σ vk) pub) (c : ℕ) hb,
      show (publicCommitment IpaPallas.curve σ vk (runNc IpaPallas.curve σ vk)
          pub)[(c : ℕ)]'hb
        = (publicCommitment IpaPallas.curve σ vk (runNc IpaPallas.curve σ vk)
            pub).getD (c : ℕ) 0 from by simp [Array.getD, hb]]
    exact publicCommitment_corresponds IpaPallas.curve σ vk pub idx
      (fun a P => (Pasta.pallas_smul_val a P).symm) hlag hsh.lagSize hpub
      (c : ℕ) c.isLt
  -- (4) the openings seam, fed directly
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hnc hk hbind
      (vk.comms (runNc IpaPallas.curve σ vk)) hvkc (pubView idx pub)
      (fun col c => (p.wComm[(col : ℕ)]!)[(c : ℕ)]!)
      (fun c => p.zComm[(c : ℕ)]!)
      (fun c => (publicCommitment IpaPallas.curve σ vk
          (runNc IpaPallas.curve σ vk) pub)[(c : ℕ)]!)
      hpubC
      (fun i c => aRef ⟨streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ), hlt i c⟩)
      (fun i c => ρRef ⟨streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ), hlt i c⟩)
      hbound₀
  refine ⟨badB, badG, badA, badZ,
    extractTable idx.omega (fun col => assembledRow σ.k (runNc IpaPallas.curve σ vk)
      (fun c => aRef ⟨streamPos (runNc IpaPallas.curve σ vk) (wRow col) (c : ℕ),
        hlt (wRow col) c⟩)),
    hbounds, ?_⟩
  intro hβ hγ hα hζ hζ1 hζb
  -- (5) the eval pins from the run's single accepted opening (flat arity)
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _
    (kimchi_fiat_shamir_pallas σ vk p pub) hrun.accepts
  have hpins := eval_pins_of_opening σ hbind
    (runInput IpaPallas.curve σ vk p pub).commitmentFn
    (runInput IpaPallas.curve σ vk p pub).pointFn aRef ρRef hrep
    (runInput IpaPallas.curve σ vk p pub).evalFn
    (runInput IpaPallas.curve σ vk p pub).polyscale
    (runInput IpaPallas.curve σ vk p pub).evalscale hξ hr a ρ hopen
  -- (6) the part-1 ft opening and the Maller identity at the double collapse
  obtain ⟨aft, ρft, hcomm_ft, heval_ft⟩ :=
    ft_opening_of_reflected_pallas σ vk p pub hbind hacc aRef ρRef hrep hξ hr
  have hCσ6 : ∀ c : Fin (runNc IpaPallas.curve σ vk),
      (vk.sigmaComm.getD 6 #[]).getD (c : ℕ) 0
        = commitPolyChunk σ (idx.sigmaPoly 6) (c : ℕ) :=
    fun c => congrFun (congrArg (fun cm => cm.sigma 6) hvkc) c
  have hσ₆ : (idx.sigmaPoly 6).natDegree < runNc IpaPallas.curve σ vk * 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hcommit : commit σ aft ρft
      = runPScalar IpaPallas.curve σ vk p pub
          • ∑ c : Fin (runNc IpaPallas.curve σ vk),
              ((runOracles IpaPallas.curve σ vk p pub).zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • (vk.sigmaComm.getD 6 #[]).getD (c : ℕ) 0
        - ((runOracles IpaPallas.curve σ vk p pub).zeta ^ n - 1)
            • ∑ j : Fin p.tComm.size,
                ((runOracles IpaPallas.curve σ vk p pub).zeta ^ 2 ^ σ.k) ^ (j : ℕ)
                  • p.tComm.getD (j : ℕ) 0 :=
    hcomm_ft.trans (runFtComm_eq IpaPallas.curve Pasta.pallas_smul_val hsh hn)
  obtain ⟨htdeg, hteq0⟩ := ft_identity_of_chunks σ hbind (idx.sigmaPoly 6) hσ₆
    (fun c => (vk.sigmaComm.getD 6 #[]).getD (c : ℕ) 0) hCσ6 htpos hsh.tCommSize
    (fun j => p.tComm.getD (j : ℕ) 0) aT ρT hTC
    (runPScalar IpaPallas.curve σ vk p pub)
    (runOracles IpaPallas.curve σ vk p pub).zeta
    (runFtEval0 IpaPallas.curve σ vk p pub) n hk aft ρft hcommit heval_ft
  -- (7) reconcile the derived identity into the consumer's shape
  have hce := claimedEvals_run_eq IpaPallas.curve
    (v := (runVU IpaPallas.curve σ vk p pub).1)
    (u := (runVU IpaPallas.curve σ vk p pub).2) hsh hpe.1 hpe.2
  have hcp := claimedPub_run_eq IpaPallas.curve
    (v := (runVU IpaPallas.curve σ vk p pub).1)
    (u := (runVU IpaPallas.curve σ vk p pub).2) hsh hpe.1 hpe.2
  have hζM : runZetaM IpaPallas.curve σ vk p pub
      = (runOracles IpaPallas.curve σ vk p pub).zeta ^ 2 ^ σ.k := by
    unfold runZetaM
    rw [powPow2_eq]
  have hζwM : runZetaOmegaM IpaPallas.curve σ vk p pub
      = (idx.omega * (runOracles IpaPallas.curve σ vk p pub).zeta) ^ 2 ^ σ.k := by
    unfold runZetaOmegaM runZetaOmega
    rw [powPow2_eq, homega, mul_comm]
  unfold runPScalar runFtEval0 runFtEval0P runPubEval0 runLinEvals at hteq0
  rw [← hce, ← hcp, hζM, hζwM, hn, hzk, homega, hendo, hmds, hshift] at hteq0
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
    (ftChunkAssembly σ.k p.tComm.size aT)
    (runOracles IpaPallas.curve σ vk p pub).zeta
    (fun (i : Fin 44) (ch : Fin (runNc IpaPallas.curve σ vk)) (j : Fin 2) =>
      ((runInputP IpaPallas.curve σ vk p pub
          (runPubEvals IpaPallas.curve σ vk p pub)
          (runVU IpaPallas.curve σ vk p pub).1
          (runVU IpaPallas.curve σ vk p pub).2).evals[streamPos
            (runNc IpaPallas.curve σ vk) i (ch : ℕ)]!)[(j : ℕ)]!)
    (fun i c => aRef ⟨streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ), hlt i c⟩)
    (fun i c => ρRef ⟨streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ), hlt i c⟩)
    hβ hγ hα hζ hζ1 hζb htdeg
    (fun i c => ⟨hbound₀ i c,
      fun j => hpins ⟨streamPos (runNc IpaPallas.curve σ vk) i (c : ℕ), hlt i c⟩ j⟩)
    hteq0

end Kimchi.Verifier.Chunked
