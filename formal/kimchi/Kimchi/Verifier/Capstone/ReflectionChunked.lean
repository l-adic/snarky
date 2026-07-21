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

end Kimchi.Verifier.Chunked
