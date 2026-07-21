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

end Kimchi.Verifier.Chunked
