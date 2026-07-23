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

`ft_opening_of_reflected` (tree-as-hypothesis) derives the ft opening from a
genuine acceptance: the constructed ft commitment is the single-chunk ft row of
the run's own accepted flat stream — flat position `nc` (after the public row's `nc`
chunks) — so `ipa_soundnessA` plus the arity-generic `eval_pins_of_opening` pin
`runFtComm` to a representation whose evaluation at the run's own `ζ` is `runFtEval0`.

The terminal roots `kimchi{Vesta,Pallas}_run_sound_algebraic_ft` — thin wrappers of
the curve-generic `run_sound_algebraic_ft`, each consuming exactly one Fiat–Shamir
axiom instance — feed the openings seam (`kimchiProof_sound_of_openings`) directly:
the deployed flat stream is read onto the 44-row `batchC` at the stream positions,
the public row is bound through `publicCommitment_corresponds` and the key's Lagrange
chunk pin, and the Maller identity comes from the ft opening via
`ft_identity_of_chunks` at the double `ζ^{2^σ.k}` collapse.
-/

open Bulletproof

namespace Kimchi.Verifier

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization
  Kimchi.Protocol.Equation CompElliptic.Fields.Pasta Kimchi.Verifier

/-! ## The Fiat–Shamir axioms -/

/-- **AXIOM (Fiat–Shamir, Poseidon instantiation over the deployed run, Vesta).**
A run accepted by the deployed warm-sponge finish
(`Ipa.verifyFrom … (runWarm …) (runInput …) = true`, the `ReflectedRun.accepts` field
of the reflection) admits a de-blinded accepting transcript tree over the run's own
flat segment batch. The idealized transcript is the deployed one: the fq-sponge
absorb/squeeze schedule of `oracles` (verifier.rs:156–283 — the index digest, the
public, witness, `z` and `t` commitments absorbed, with `β`, `γ`, `α`, `ζ` squeezed
between), whose warm final state seeds the opening verification
(`BatchEvaluationProof { sponge: fq_sponge, … }`, verifier.rs:1185–1193). The declared
assumption is exactly that the Poseidon sponge provides a valid Fiat–Shamir transform
at this transcript; the statement mentions only the run's own wire data — no
arithmetic content, no reference to the abstract batch. What would discharge it is
the program already stated for `Bulletproof.poseidon_fiat_shamir_*`: the sponge
itself is definitional and fixture-validated, and the axiom packages the remaining
rewinding/forking extraction against its random-oracle behaviour. -/
axiom kimchi_fiat_shamir_vesta (σ : SRS IpaVesta.Point) {nc : ℕ}
    (cvk : KimchiVK IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc σ.k) (pub : Array Fp) :
  FiatShamirTreeB σ
    (combinedCommitment (runInput IpaVesta.curve σ cvk cp pub).polyscale
      (runInput IpaVesta.curve σ cvk cp pub).commitmentFn)
    (combinedEvalVector (2 ^ σ.k) (runInput IpaVesta.curve σ cvk cp pub).evalscale
      (runInput IpaVesta.curve σ cvk cp pub).pointFn)
    (Ipa.cipOf (runInput IpaVesta.curve σ cvk cp pub))
    (Ipa.verifyFrom IpaVesta.curve σ (runWarm IpaVesta.curve σ cvk cp pub)
      (runInput IpaVesta.curve σ cvk cp pub) = true)

/-- **AXIOM (Fiat–Shamir, Poseidon instantiation over the deployed run, Pallas).**
The Pallas-side twin of `kimchi_fiat_shamir_vesta` — the same idealized transcript
(the `oracles` schedule, verifier.rs:156–283, seeding the opening verification at
verifier.rs:1185–1193) and the same discharge program (definitional
fixture-validated sponge plus the rewinding/forking extraction). -/
axiom kimchi_fiat_shamir_pallas (σ : SRS IpaPallas.Point) {nc : ℕ}
    (cvk : KimchiVK IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc σ.k) (pub : Array Fq) :
  FiatShamirTreeB σ
    (combinedCommitment (runInput IpaPallas.curve σ cvk cp pub).polyscale
      (runInput IpaPallas.curve σ cvk cp pub).commitmentFn)
    (combinedEvalVector (2 ^ σ.k) (runInput IpaPallas.curve σ cvk cp pub).evalscale
      (runInput IpaPallas.curve σ cvk cp pub).pointFn)
    (Ipa.cipOf (runInput IpaPallas.curve σ cvk cp pub))
    (Ipa.verifyFrom IpaPallas.curve σ (runWarm IpaPallas.curve σ cvk cp pub)
      (runInput IpaPallas.curve σ cvk cp pub) = true)

variable (C : Ipa.CommitmentCurve)

/-! ## The stream reads

`runStreamP` is three `Vector` appends — the public block, the ft singleton, and the
flattened 43-row tail — so every segment read is `Vector.getElem_append` dispatch plus
one `flatten_read`. Every read is total: the shapes are type-level. -/

section StreamReads

variable {σ : SRS C.Point} {nc : ℕ} {cvk : KimchiVK C nc}
  {cp : KimchiProof C nc σ.k} {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)}

/-- Blocks stay inside their region: `q·nc + c < Q·nc`. -/
private theorem block_lt {q Q c nc : ℕ} (hq : q < Q) (hc : c < nc) :
    q * nc + c < Q * nc := by
  calc q * nc + c < (q + 1) * nc := by rw [Nat.succ_mul]; omega
    _ ≤ Q * nc := Nat.mul_le_mul_right nc hq

/-- **Public-region read**: position `c` is public chunk `c`. -/
private theorem stream_pub_read (c : ℕ) (hc : c < nc) :
    (runStreamP C σ cvk cp pub pe)[c]'(by omega)
      = ((publicCommitment C σ cvk pub)[c]'hc, pe.zeta[c]'hc, pe.zetaOmega[c]'hc) := by
  unfold runStreamP
  rw [Vector.getElem_append, dif_pos (by omega : c < nc + 1),
    Vector.getElem_append, dif_pos hc, Vector.getElem_ofFn]
  rfl

/-- **The ft read**: position `nc` is the constructed single-chunk ft row. -/
private theorem stream_ft_read :
    (runStreamP C σ cvk cp pub pe)[(nc : ℕ)]'(by omega)
      = (runFtComm C σ cvk cp pub,
         runFtEval0P C σ cvk cp pub
           (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray),
         cp.ftEval1) := by
  unfold runStreamP
  rw [Vector.getElem_append, dif_pos (by omega : (nc : ℕ) < nc + 1),
    Vector.getElem_append, dif_neg (by omega : ¬ (nc : ℕ) < nc)]
  simp only [Nat.sub_self]
  rfl

/-- **The tail read**: position `nc + 1 + q·nc + c` is tail row `q`'s chunk `c` — one
`flatten_read`. -/
private theorem stream_tail_read (q c : ℕ) (hq : q < tailRowCount) (hc : c < nc) :
    (runStreamP C σ cvk cp pub pe)[nc + 1 + q * nc + c]'(by
        have := block_lt hq hc
        omega)
      = ((tailRowsOf C cvk cp)[q]'hq)[c]'hc := by
  unfold runStreamP
  rw [Vector.getElem_append, dif_neg (by omega : ¬ nc + 1 + q * nc + c < nc + 1)]
  simp only [show nc + 1 + q * nc + c - (nc + 1) = q * nc + c from by omega]
  exact flatten_read _ q c hq hc

/-- Tail row `j < 7` is the `j`-th literal row (`z` + the six selectors). -/
private theorem tailRows_read_lit (j : ℕ) (hj : j < litRowCount) :
    (tailRowsOf C cvk cp)[j]'(by omega)
      = ((⟨#[zipSeg C cp.zComm cp.evals.z,
            zipSeg C cvk.genericComm cp.evals.genericSelector,
            zipSeg C cvk.poseidonComm cp.evals.poseidonSelector,
            zipSeg C cvk.completeAddComm cp.evals.completeAddSelector,
            zipSeg C cvk.mulComm cp.evals.mulSelector,
            zipSeg C cvk.emulComm cp.evals.emulSelector,
            zipSeg C cvk.endomulScalarComm cp.evals.endomulScalarSelector], rfl⟩
          : Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) litRowCount)[j]'hj) := by
  show ((⟨#[zipSeg C cp.zComm cp.evals.z,
        zipSeg C cvk.genericComm cp.evals.genericSelector,
        zipSeg C cvk.poseidonComm cp.evals.poseidonSelector,
        zipSeg C cvk.completeAddComm cp.evals.completeAddSelector,
        zipSeg C cvk.mulComm cp.evals.mulSelector,
        zipSeg C cvk.emulComm cp.evals.emulSelector,
        zipSeg C cvk.endomulScalarComm cp.evals.endomulScalarSelector], rfl⟩
          : Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) litRowCount)
      ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
      ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
      ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map
        (fun x => zipSeg C x.1 x.2))[j]'(by omega) = _
  rw [Vector.getElem_append, dif_pos (by omega), Vector.getElem_append,
    dif_pos (by omega), Vector.getElem_append, dif_pos hj]

/-- Tail row `7 + q` is witness column `q`'s row. -/
private theorem tailRows_read_w (q : ℕ) (hq : q < wCols) :
    (tailRowsOf C cvk cp)[7 + q]'(by omega)
      = zipSeg C (cp.wComm[q]'hq) (cp.evals.w[q]'hq) := by
  show ((⟨#[zipSeg C cp.zComm cp.evals.z,
        zipSeg C cvk.genericComm cp.evals.genericSelector,
        zipSeg C cvk.poseidonComm cp.evals.poseidonSelector,
        zipSeg C cvk.completeAddComm cp.evals.completeAddSelector,
        zipSeg C cvk.mulComm cp.evals.mulSelector,
        zipSeg C cvk.emulComm cp.evals.emulSelector,
        zipSeg C cvk.endomulScalarComm cp.evals.endomulScalarSelector], rfl⟩
          : Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) litRowCount)
      ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
      ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
      ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map
        (fun x => zipSeg C x.1 x.2))[7 + q]'(by omega) = _
  rw [Vector.getElem_append, dif_pos (by omega), Vector.getElem_append,
    dif_pos (by omega), Vector.getElem_append, dif_neg (by omega)]
  simp only [show 7 + q - 7 = q from by omega, Vector.getElem_map, Vector.getElem_zip]

/-- Tail row `22 + q` is coefficient column `q`'s row. -/
private theorem tailRows_read_c (q : ℕ) (hq : q < coeffCols) :
    (tailRowsOf C cvk cp)[22 + q]'(by omega)
      = zipSeg C (cvk.coefficientsComm[q]'hq) (cp.evals.coefficients[q]'hq) := by
  show ((⟨#[zipSeg C cp.zComm cp.evals.z,
        zipSeg C cvk.genericComm cp.evals.genericSelector,
        zipSeg C cvk.poseidonComm cp.evals.poseidonSelector,
        zipSeg C cvk.completeAddComm cp.evals.completeAddSelector,
        zipSeg C cvk.mulComm cp.evals.mulSelector,
        zipSeg C cvk.emulComm cp.evals.emulSelector,
        zipSeg C cvk.endomulScalarComm cp.evals.endomulScalarSelector], rfl⟩
          : Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) litRowCount)
      ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
      ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
      ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map
        (fun x => zipSeg C x.1 x.2))[22 + q]'(by omega) = _
  rw [Vector.getElem_append, dif_pos (by omega), Vector.getElem_append,
    dif_neg (by omega)]
  simp only [show 22 + q - (7 + 15) = q from by omega, Vector.getElem_map,
    Vector.getElem_zip]

/-- Tail row `37 + q` is the `q`-th σ row. -/
private theorem tailRows_read_s (q : ℕ) (hq : q < sigmaRows) :
    (tailRowsOf C cvk cp)[37 + q]'(by omega)
      = zipSeg C (cvk.sigmaComm[q]'(by omega)) (cp.evals.s[q]'hq) := by
  show ((⟨#[zipSeg C cp.zComm cp.evals.z,
        zipSeg C cvk.genericComm cp.evals.genericSelector,
        zipSeg C cvk.poseidonComm cp.evals.poseidonSelector,
        zipSeg C cvk.completeAddComm cp.evals.completeAddSelector,
        zipSeg C cvk.mulComm cp.evals.mulSelector,
        zipSeg C cvk.emulComm cp.evals.emulSelector,
        zipSeg C cvk.endomulScalarComm cp.evals.endomulScalarSelector], rfl⟩
          : Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) litRowCount)
      ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
      ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
      ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map
        (fun x => zipSeg C x.1 x.2))[37 + q]'(by omega) = _
  rw [Vector.getElem_append, dif_neg (by omega)]
  simp only [show 37 + q - (7 + 15 + 15) = q from by omega, Vector.getElem_map,
    Vector.getElem_zip, Vector.getElem_take]
  rfl

end StreamReads

/-! ## The stream positions

The flat position of every abstract batch row's chunk, `Fin`-typed at the stream
length: the abstract rows are the deployed `to_batch` order with the single-chunk ft
row interposed at flat position `nc`, and every position lies inside the `44·nc + 1`
flat rows by construction. The per-region value lemmas below feed the reads. -/

/-- The flat stream position of abstract batch row `i`, chunk `c`. The public row's
chunks come first and every later row `i` starts at `nc + 1 + (i − 1)·nc`. -/
private def streamPos (nc : ℕ) (i : Fin batchRows) (c : Fin nc) :
    Fin (nc + 1 + tailRowCount * nc) :=
  ⟨if (i : ℕ) < 1 then (c : ℕ) else nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ), by
    have hc := c.isLt
    split
    · omega
    · have := block_lt (show (i : ℕ) - 1 < tailRowCount from by
        have := i.isLt
        omega) hc
      omega⟩

/-- `streamPos` at the public row. -/
private theorem streamPos_pubRow (nc : ℕ) (ch : Fin nc) :
    (streamPos nc pubRow ch : ℕ) = (ch : ℕ) := rfl

/-- `streamPos` at the accumulator row (`0·nc` kept for the region-read shape). -/
private theorem streamPos_zRow (nc : ℕ) (ch : Fin nc) :
    (streamPos nc zRow ch : ℕ) = nc + 1 + 0 * nc + (ch : ℕ) := rfl

/-- `streamPos` at a selector row. -/
private theorem streamPos_selRow (nc : ℕ) (j : Fin selCount) (ch : Fin nc) :
    (streamPos nc (selRow j) ch : ℕ) = nc + 1 + (1 + (j : ℕ)) * nc + (ch : ℕ) := by
  show (if 2 + (j : ℕ) < 1 then (ch : ℕ)
      else nc + 1 + (2 + (j : ℕ) - 1) * nc + (ch : ℕ)) = _
  rw [if_neg (by omega), show 2 + (j : ℕ) - 1 = 1 + (j : ℕ) from by omega]

/-- `streamPos` at a witness row. -/
private theorem streamPos_wRow (nc : ℕ) (q : Fin wCols) (ch : Fin nc) :
    (streamPos nc (wRow q) ch : ℕ) = nc + 1 + (7 + (q : ℕ)) * nc + (ch : ℕ) := by
  show (if 8 + (q : ℕ) < 1 then (ch : ℕ)
      else nc + 1 + (8 + (q : ℕ) - 1) * nc + (ch : ℕ)) = _
  rw [if_neg (by omega), show 8 + (q : ℕ) - 1 = 7 + (q : ℕ) from by omega]

/-- `streamPos` at a coefficient row. -/
private theorem streamPos_cRow (nc : ℕ) (q : Fin coeffCols) (ch : Fin nc) :
    (streamPos nc (cRow q) ch : ℕ) = nc + 1 + (22 + (q : ℕ)) * nc + (ch : ℕ) := by
  show (if 23 + (q : ℕ) < 1 then (ch : ℕ)
      else nc + 1 + (23 + (q : ℕ) - 1) * nc + (ch : ℕ)) = _
  rw [if_neg (by omega), show 23 + (q : ℕ) - 1 = 22 + (q : ℕ) from by omega]

/-- `streamPos` at a σ row. -/
private theorem streamPos_sRow (nc : ℕ) (i : Fin sigmaRows) (ch : Fin nc) :
    (streamPos nc (sRow i) ch : ℕ) = nc + 1 + (37 + (i : ℕ)) * nc + (ch : ℕ) := by
  show (if 38 + (i : ℕ) < 1 then (ch : ℕ)
      else nc + 1 + (38 + (i : ℕ) - 1) * nc + (ch : ℕ)) = _
  rw [if_neg (by omega), show 38 + (i : ℕ) - 1 = 37 + (i : ℕ) from by omega]

section StreamReads

variable {σ : SRS C.Point} {nc : ℕ} {cvk : KimchiVK C nc}
  {cp : KimchiProof C nc σ.k} {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)}

/-- **Public-row read** at its stream position. -/
private theorem stream_read_pub (c : Fin nc) :
    (runStreamP C σ cvk cp pub pe)[(streamPos nc pubRow c : ℕ)]'
        ((streamPos nc pubRow c).isLt)
      = ((publicCommitment C σ cvk pub)[c], pe.zeta[c], pe.zetaOmega[c]) := by
  rw [getElem_congr_idx (streamPos_pubRow nc c)]
  exact stream_pub_read C (c : ℕ) c.isLt

/-- **Accumulator-row read** at its stream position: `z`'s chunk `c`. -/
private theorem stream_read_z (c : Fin nc) :
    (runStreamP C σ cvk cp pub pe)[(streamPos nc zRow c : ℕ)]'
        ((streamPos nc zRow c).isLt)
      = (cp.zComm[c], cp.evals.z.zeta[c], cp.evals.z.zetaOmega[c]) := by
  rw [getElem_congr_idx (streamPos_zRow nc c),
    stream_tail_read C 0 (c : ℕ) (by omega) c.isLt, tailRows_read_lit C 0 (by omega)]
  show (Vector.ofFn _)[(c : ℕ)]'c.isLt = _
  rw [Vector.getElem_ofFn]

/-- **Selector-row read** at its stream position: selector `j` is tail row `1 + j`. -/
private theorem stream_read_sel (j : Fin selCount) (c : Fin nc) :
    (runStreamP C σ cvk cp pub pe)[(streamPos nc (selRow j) c : ℕ)]'
        ((streamPos nc (selRow j) c).isLt)
      = ((tailRowsOf C cvk cp)[1 + (j : ℕ)]'(by omega))[c] := by
  rw [getElem_congr_idx (streamPos_selRow nc j c)]
  exact stream_tail_read C (1 + (j : ℕ)) (c : ℕ) (by omega) c.isLt

/-- **Witness-row read** at its stream position: witness column `q`'s chunk `c`. -/
private theorem stream_read_w (q : Fin wCols) (c : Fin nc) :
    (runStreamP C σ cvk cp pub pe)[(streamPos nc (wRow q) c : ℕ)]'
        ((streamPos nc (wRow q) c).isLt)
      = ((cp.wComm[q])[c], (cp.evals.w[q]).zeta[c], (cp.evals.w[q]).zetaOmega[c]) := by
  rw [getElem_congr_idx (streamPos_wRow nc q c),
    stream_tail_read C (7 + (q : ℕ)) (c : ℕ) (by omega) c.isLt,
    tailRows_read_w C (q : ℕ) q.isLt]
  show (Vector.ofFn _)[(c : ℕ)]'c.isLt = _
  rw [Vector.getElem_ofFn]
  rfl

/-- **Coefficient-row read** at its stream position: coefficient `q`'s chunk `c`. -/
private theorem stream_read_c (q : Fin coeffCols) (c : Fin nc) :
    (runStreamP C σ cvk cp pub pe)[(streamPos nc (cRow q) c : ℕ)]'
        ((streamPos nc (cRow q) c).isLt)
      = ((cvk.coefficientsComm[q])[c], (cp.evals.coefficients[q]).zeta[c],
          (cp.evals.coefficients[q]).zetaOmega[c]) := by
  rw [getElem_congr_idx (streamPos_cRow nc q c),
    stream_tail_read C (22 + (q : ℕ)) (c : ℕ) (by omega) c.isLt,
    tailRows_read_c C (q : ℕ) q.isLt]
  show (Vector.ofFn _)[(c : ℕ)]'c.isLt = _
  rw [Vector.getElem_ofFn]
  rfl

/-- **σ-row read** at its stream position: the `q`-th σ row's chunk `c`. -/
private theorem stream_read_s (q : Fin sigmaRows) (c : Fin nc) :
    (runStreamP C σ cvk cp pub pe)[(streamPos nc (sRow q) c : ℕ)]'
        ((streamPos nc (sRow q) c).isLt)
      = ((cvk.sigmaComm[(q : ℕ)]'(by omega))[c], (cp.evals.s[q]).zeta[c],
          (cp.evals.s[q]).zetaOmega[c]) := by
  rw [getElem_congr_idx (streamPos_sRow nc q c),
    stream_tail_read C (37 + (q : ℕ)) (c : ℕ) (by omega) c.isLt,
    tailRows_read_s C (q : ℕ) q.isLt]
  show (Vector.ofFn _)[(c : ℕ)]'c.isLt = _
  rw [Vector.getElem_ofFn]
  rfl

end StreamReads

/-! ## The ft opening from the reflected run -/

/-- **The ft opening from a chunked reflected run** (tree-as-hypothesis):
DL-binding, a reflected accepted chunked run, SRS-basis representations of the run's
own flat batch rows, the run's transcript tree (the chunked `kimchi_fiat_shamir_*`
shape, here a hypothesis), and good combination challenges yield the ft opening — a
representation of the constructed ft commitment `runFtComm` (the DOUBLE collapse at
`ζ^{2^σ.k}`) whose evaluation at the run's own `ζ` is the computed claim `runFtEval0`.
The ft row sits at flat position `nc`, right after the public row's chunks
(`stream_ft_read`). -/
private theorem ft_opening_of_reflected {C : Ipa.CommitmentCurve} [Module C.ScalarField C.Point]
    (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
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
  have hsz : (nc : ℕ) < (runInput C σ cvk cp pub).commitments.size := by
    show (nc : ℕ) < nc + 1 + tailRowCount * nc
    omega
  refine ⟨aRef ⟨nc, hsz⟩, ρRef ⟨nc, hsz⟩, ?_, ?_⟩
  · rw [hrep ⟨nc, hsz⟩]
    show ((runStreamP C σ cvk cp pub (runPubEvals C σ cvk cp pub)).map
        (·.1))[(nc : ℕ)]'(by
          show (nc : ℕ) < nc + 1 + tailRowCount * nc
          omega)
      = runFtComm C σ cvk cp pub
    rw [Vector.getElem_map, stream_ft_read C]
  · have hpin := hpins ⟨nc, hsz⟩ (0 : Fin evalPts)
    have hpt : (runInput C σ cvk cp pub).pointFn (0 : Fin evalPts)
        = (runOracles C σ cvk cp pub).zeta := rfl
    rw [hpt] at hpin
    rw [← hpin]
    show (((runStreamP C σ cvk cp pub (runPubEvals C σ cvk cp pub)).map
        (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector C.ScalarField evalPts)))[(nc : ℕ)]'(by
          show (nc : ℕ) < nc + 1 + tailRowCount * nc
          omega)
        : Vector C.ScalarField evalPts)[(0 : ℕ)]
      = runFtEval0 C σ cvk cp pub
    rw [Vector.getElem_map, stream_ft_read C]
    rfl

/-- **The ft opening of the deployed chunked Vesta verifier**: a genuine
`KimchiVesta.verify … = true`, DL-binding, representations of the run's own
flat batch rows, and good combination challenges yield the ft opening. The run is
reflected trust-free (`kimchiVerify_reflects`); the transcript tree is
`kimchi_fiat_shamir_vesta` at the run's own warm data — the sole axiom
consumed. The chunked Vesta FS-reflection root. -/
theorem ft_opening_of_reflected_vesta (σ : SRS IpaVesta.Point) {nc : ℕ}
    (cvk : KimchiVK IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc σ.k)
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
    (cvk : KimchiVK IpaPallas.curve nc) (cp : KimchiProof IpaPallas.curve nc σ.k)
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

/-! ## The chunk combination as an indexed power sum -/

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
    ∧ (fun i : Fin permCols => cvk.shifts[i]) = idx.shifts
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
  {cp : KimchiProof C nc σ.k} {pub : Array C.ScalarField}
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

/-- Reading the run input's evaluation matrix at a stream position: the flat row's
claim pair. -/
private theorem runEvals_read (i : Fin batchRows) (c : Fin nc) :
    (runInputP C σ cvk cp pub pe v u).evals[(streamPos nc i c : ℕ)]'
        ((streamPos nc i c).isLt)
      = ⟨#[((runStreamP C σ cvk cp pub pe)[(streamPos nc i c : ℕ)]'
              ((streamPos nc i c).isLt)).2.1,
          ((runStreamP C σ cvk cp pub pe)[(streamPos nc i c : ℕ)]'
              ((streamPos nc i c).isLt)).2.2],
         rfl⟩ := by
  show ((runStreamP C σ cvk cp pub pe).map
      (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector C.ScalarField evalPts)))[(streamPos
        nc i c : ℕ)]'((streamPos nc i c).isLt) = _
  rw [Vector.getElem_map]

/-- A `Fin nc`-indexed power sum whose entries read an `nc`-sized array is that
array's chunk combination. -/
private theorem sum_readsTo (xM : C.ScalarField) (w : Array C.ScalarField)
    (hw : w.size = nc) (f : Fin nc → C.ScalarField)
    (hf : ∀ ch : Fin nc, f ch = w[(ch : ℕ)]'(lt_of_lt_of_eq ch.isLt hw.symm)) :
    (∑ ch : Fin nc, xM ^ (ch : ℕ) * f ch) = combineAt xM w := by
  rw [combineAt_eq_sum]
  refine (Fintype.sum_equiv (finCongr hw) _ _ fun i => ?_).symm
  rw [hf (finCongr hw i)]
  simp only [finCongr_apply, Fin.val_cast, Fin.getElem_fin]

/-- **The chunk-combined claimed record is the run's own** (`evals.combine`): the
abstract `claimedEvals`, fed the run's flat claims at the stream positions, IS the
verifier's combined record `cp.linEvals` at the run's combination powers. Pure layout
reading through the region reads. -/
private theorem claimedEvals_run_eq :
    claimedEvals (runZetaM C σ cvk cp pub) (runZetaOmegaM C σ cvk cp pub)
        (fun (i : Fin batchRows) (ch : Fin nc) (j : Fin evalPts) =>
          ((runInputP C σ cvk cp pub pe v u).evals[(streamPos nc i ch : ℕ)]'
              ((streamPos nc i ch).isLt))[(j : ℕ)]'j.isLt)
      = cp.linEvals (runZetaM C σ cvk cp pub) (runZetaOmegaM C σ cvk cp pub) := by
  refine evals_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · funext col
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (wRow col) ch, stream_read_w C col ch]
    rfl
  · funext col
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (wRow col) ch, stream_read_w C col ch]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C zRow ch, stream_read_z C ch]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C zRow ch, stream_read_z C ch]
    rfl
  · funext i
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (sRow i) ch, stream_read_s C i ch]
    rfl
  · funext col
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (cRow col) ch, stream_read_c C col ch]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 0) ch, stream_read_sel C 0 ch,
      tailRows_read_lit C (1 + ((0 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 1) ch, stream_read_sel C 1 ch,
      tailRows_read_lit C (1 + ((1 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 2) ch, stream_read_sel C 2 ch,
      tailRows_read_lit C (1 + ((2 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 3) ch, stream_read_sel C 3 ch,
      tailRows_read_lit C (1 + ((3 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 4) ch, stream_read_sel C 4 ch,
      tailRows_read_lit C (1 + ((4 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [runEvals_read C (selRow 5) ch, stream_read_sel C 5 ch,
      tailRows_read_lit C (1 + ((5 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl

/-- **The combined public claim is the run's own**: `claimedPub` at the stream's
public-row claims is the verifier's chunk-combined public evaluation. -/
private theorem claimedPub_run_eq :
    claimedPub (runZetaM C σ cvk cp pub)
        (fun (i : Fin batchRows) (ch : Fin nc) (j : Fin evalPts) =>
          ((runInputP C σ cvk cp pub pe v u).evals[(streamPos nc i ch : ℕ)]'
              ((streamPos nc i ch).isLt))[(j : ℕ)]'j.isLt)
      = combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray := by
  refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
  beta_reduce
  rw [runEvals_read C pubRow ch, stream_read_pub C ch]
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
                  • cp.tComm[j] := by
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

end ScalarReconcile

/-! ## The group-side reconciliation: the flat stream carries the abstract batch -/

section GroupReconcile

variable {σ : SRS C.Point} {nc : ℕ} {cvk : KimchiVK C nc}
  {cp : KimchiProof C nc σ.k} {pub : Array C.ScalarField}
  {pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)}

/-- **The abstract 44-row chunked batch is the flat stream's commitment column**: at
every batch row and chunk, `batchC` — fed the checked witness/accumulator/public chunk
reads and the key's `comms` view — is the flat stream's commitment at the row's stream
position. The layout bridge `hbound₀` consumes. -/
private theorem batchC_eq_flat (i : Fin batchRows) (c : Fin nc) :
    batchC (fun (col : Fin wCols) (c : Fin nc) => (cp.wComm[col])[c])
        (fun c => cp.zComm[c])
        (fun c => (publicCommitment C σ cvk pub)[c])
        cvk.comms i c
      = ((runStreamP C σ cvk cp pub pe)[(streamPos nc i c : ℕ)]'
          ((streamPos nc i c).isLt)).1 := by
  by_cases h1 : (i : ℕ) < 1
  · rw [getElem_congr_idx (show (streamPos nc i c : ℕ) = (c : ℕ) from by
        show (if (i : ℕ) < 1 then (c : ℕ)
            else nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ)) = _
        rw [if_pos h1]),
      stream_pub_read C (c : ℕ) c.isLt]
    simp only [batchC]
    rw [if_pos h1]
    rfl
  · by_cases h2 : (i : ℕ) < 2
    · rw [getElem_congr_idx (show (streamPos nc i c : ℕ)
            = nc + 1 + 0 * nc + (c : ℕ) from by
          show (if (i : ℕ) < 1 then (c : ℕ)
              else nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ)) = _
          rw [if_neg h1, show (i : ℕ) - 1 = 0 from by omega]),
        stream_tail_read C 0 (c : ℕ) (by omega) c.isLt,
        tailRows_read_lit C 0 (by omega)]
      simp only [batchC]
      rw [if_neg h1, if_pos h2]
      show _ = ((Vector.ofFn _)[(c : ℕ)]'c.isLt
          : C.Point × C.ScalarField × C.ScalarField).1
      rw [Vector.getElem_ofFn]
    · by_cases h3 : (i : ℕ) < 8
      · rw [getElem_congr_idx (show (streamPos nc i c : ℕ)
              = nc + 1 + (1 + ((i : ℕ) - 2)) * nc + (c : ℕ) from by
            show (if (i : ℕ) < 1 then (c : ℕ)
                else nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ)) = _
            rw [if_neg h1, show (i : ℕ) - 1 = 1 + ((i : ℕ) - 2) from by omega]),
          stream_tail_read C (1 + ((i : ℕ) - 2)) (c : ℕ) (by omega) c.isLt,
          tailRows_read_lit C (1 + ((i : ℕ) - 2)) (by omega)]
        simp only [batchC]
        rw [if_neg h1, if_neg h2, dif_pos h3]
        obtain ⟨iv, hivlt⟩ := i
        have hlo : 2 ≤ iv := Nat.not_lt.mp h2
        have hhi : iv < 8 := h3
        interval_cases iv <;>
          (show _ = ((Vector.ofFn _)[(c : ℕ)]'c.isLt
              : C.Point × C.ScalarField × C.ScalarField).1
           rw [Vector.getElem_ofFn]
           rfl)
      · by_cases h4 : (i : ℕ) < 23
        · rw [getElem_congr_idx (show (streamPos nc i c : ℕ)
                = nc + 1 + (7 + ((i : ℕ) - 8)) * nc + (c : ℕ) from by
              show (if (i : ℕ) < 1 then (c : ℕ)
                  else nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ)) = _
              rw [if_neg h1, show (i : ℕ) - 1 = 7 + ((i : ℕ) - 8) from by omega]),
            stream_tail_read C (7 + ((i : ℕ) - 8)) (c : ℕ) (by omega) c.isLt,
            tailRows_read_w C ((i : ℕ) - 8) (by omega)]
          simp only [batchC]
          rw [if_neg h1, if_neg h2, dif_neg h3, dif_pos h4]
          show _ = ((Vector.ofFn _)[(c : ℕ)]'c.isLt
              : C.Point × C.ScalarField × C.ScalarField).1
          rw [Vector.getElem_ofFn]
          rfl
        · by_cases h5 : (i : ℕ) < 38
          · rw [getElem_congr_idx (show (streamPos nc i c : ℕ)
                  = nc + 1 + (22 + ((i : ℕ) - 23)) * nc + (c : ℕ) from by
                show (if (i : ℕ) < 1 then (c : ℕ)
                    else nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ)) = _
                rw [if_neg h1,
                  show (i : ℕ) - 1 = 22 + ((i : ℕ) - 23) from by omega]),
              stream_tail_read C (22 + ((i : ℕ) - 23)) (c : ℕ) (by omega) c.isLt,
              tailRows_read_c C ((i : ℕ) - 23) (by omega)]
            simp only [batchC]
            rw [if_neg h1, if_neg h2, dif_neg h3, dif_neg h4, dif_pos h5]
            show _ = ((Vector.ofFn _)[(c : ℕ)]'c.isLt
                : C.Point × C.ScalarField × C.ScalarField).1
            rw [Vector.getElem_ofFn]
            rfl
          · rw [getElem_congr_idx (show (streamPos nc i c : ℕ)
                  = nc + 1 + (37 + ((i : ℕ) - 38)) * nc + (c : ℕ) from by
                show (if (i : ℕ) < 1 then (c : ℕ)
                    else nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ)) = _
                rw [if_neg h1,
                  show (i : ℕ) - 1 = 37 + ((i : ℕ) - 38) from by
                    have := i.isLt
                    omega]),
              stream_tail_read C (37 + ((i : ℕ) - 38)) (c : ℕ) (by
                have := i.isLt
                omega) c.isLt,
              tailRows_read_s C ((i : ℕ) - 38) (by
                have := i.isLt
                omega)]
            simp only [batchC]
            rw [if_neg h1, if_neg h2, dif_neg h3, dif_neg h4, dif_neg h5]
            show _ = ((Vector.ofFn _)[(c : ℕ)]'c.isLt
                : C.Point × C.ScalarField × C.ScalarField).1
            rw [Vector.getElem_ofFn]
            rfl

end GroupReconcile

/-! ## The chunked run-level terminal roots -/

/-- **The run-level residue-free root, curve-generically**: from a genuine acceptance
`kimchiVerify σ cvk cp pub = true` of the checked records at production chunking
`nc · 2^σ.k = n`, the AGM path delivers the guarded
`Satisfies idx (pubView idx pub) wTab` — the assembled witness table of the algebraic
prover's own per-chunk representations. The two curve-specific facts enter as
hypotheses: `hsmul`, the `.val`-scalar collapse of the point-count-backed `Module`
instance, and `hFS`, the Fiat–Shamir transcript tree at the run's own warm data —
taken ONCE and threaded to both consumers (the flat eval pins at step (5) and
`ft_opening_of_reflected` at step (6)). The public roots
`kimchi{Vesta,Pallas}_run_sound_algebraic_ft` are thin wrappers applying exactly one
`kimchi_fiat_shamir_*` instance each.

The hypothesis surface carried by the statement: the algebraic prover's SRS-basis
representations of the run's `44·nc + 1` flat segment rows (`aRef`/`ρRef`) and of the
`tComm` chunks (`aT`/`ρT`); the good-combination-challenge guards `hξ`/`hr` (the
counting-SZ bad sets `badXiOf`/`badROf`); the checked key–index correspondence
`KimchiVK.Corresponds`; and DL-binding `hbind` — no nontrivial discrete-log relation
among the SRS generators. `hbind` is the computational assumption of the
development: information-theoretically false at real parameters and meaningful only
computationally — see the `hbind` scope note in the `Bulletproof/Soundness.lean`
module docstring (the file of `chunked_batch_soundness`). -/
private theorem run_sound_algebraic_ft {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a • P = a.val • P)
    (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n) (hn : cvk.n = n)
    (hvk : cvk.Corresponds σ idx)
    (hpub : pub.size = idx.publicCount)
    (htpos : 0 < cp.tComm.size)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → C.ScalarField) (wh : C.ScalarField),
      DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : kimchiVerify C σ cvk cp pub = true)
    (hFS : FiatShamirTreeB σ
      (combinedCommitment (runInput C σ cvk cp pub).polyscale
        (runInput C σ cvk cp pub).commitmentFn)
      (combinedEvalVector (2 ^ σ.k) (runInput C σ cvk cp pub).evalscale
        (runInput C σ cvk cp pub).pointFn)
      (Ipa.cipOf (runInput C σ cvk cp pub))
      (Ipa.verifyFrom C σ (runWarm C σ cvk cp pub) (runInput C σ cvk cp pub) = true))
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → C.ScalarField)
    (ρRef : Fin (runInput C σ cvk cp pub).commitments.size → C.ScalarField)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput C σ cvk cp pub).commitmentFn i)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField)
    (ρT : Fin cp.tComm.size → C.ScalarField)
    (hTC : ∀ j : Fin cp.tComm.size, commit σ (aT j) (ρT j) = cp.tComm[j])
    (hξ : (runInput C σ cvk cp pub).polyscale
      ∉ badXiOf σ aRef (runInput C σ cvk cp pub).pointFn
          (runInput C σ cvk cp pub).evalFn)
    (hr : (runInput C σ cvk cp pub).evalscale
      ∉ badROf σ aRef (runInput C σ cvk cp pub).pointFn
          (runInput C σ cvk cp pub).evalFn
          (runInput C σ cvk cp pub).polyscale) :
    ∃ (badB : Finset C.ScalarField) (badG : C.ScalarField → Finset C.ScalarField)
        (badA : C.ScalarField → C.ScalarField → Finset C.ScalarField)
        (badZ : C.ScalarField → C.ScalarField → C.ScalarField
          → Polynomial C.ScalarField → Finset C.ScalarField)
        (wTab : Fin n → Fin wCols → C.ScalarField),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial C.ScalarField), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ((runOracles C σ cvk cp pub).beta ∉ badB →
          (runOracles C σ cvk cp pub).gamma
            ∉ badG (runOracles C σ cvk cp pub).beta →
          (runOracles C σ cvk cp pub).alpha
            ∉ badA (runOracles C σ cvk cp pub).beta
                (runOracles C σ cvk cp pub).gamma →
          (runOracles C σ cvk cp pub).zeta
            ∉ badZ (runOracles C σ cvk cp pub).beta
                (runOracles C σ cvk cp pub).gamma
                (runOracles C σ cvk cp pub).alpha
                (ftChunkAssembly σ.k cp.tComm.size aT) →
          (runOracles C σ cvk cp pub).zeta ≠ 1 →
          (runOracles C σ cvk cp pub).zeta
            ≠ idx.omega ^ (n - idx.zkRows) →
          Satisfies idx (pubView idx pub) wTab) := by
  obtain ⟨hvkc, homega, hzk, hshift, hendo, hmds, hlag⟩ := hvk
  -- (1) the body reflection: the guards and the warm acceptance
  obtain ⟨hlagsz, _hpubn, haccept⟩ :=
    kimchiVerify_reflects C σ cvk cp pub hacc
  have hlt : ∀ (i : Fin batchRows) (c : Fin nc),
      (streamPos nc i c : ℕ) < (runInput C σ cvk cp pub).commitments.size :=
    fun i c => (streamPos nc i c).isLt
  -- (2) the reference openings at the stream positions bind the abstract batch
  have hbound₀ : ∀ (i : Fin batchRows) (c : Fin nc),
      commit σ (aRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
          (ρRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
        = batchC (fun col c => (cp.wComm[col])[c]) (fun c => cp.zComm[c])
            (fun c => (publicCommitment C σ cvk pub)[c])
            cvk.comms i c := by
    intro i c
    rw [hrep ⟨(streamPos nc i c : ℕ), hlt i c⟩]
    show ((runStreamP C σ cvk cp pub
        (runPubEvals C σ cvk cp pub)).map
          (·.1))[(streamPos nc i c : ℕ)]'(hlt i c) = _
    rw [Vector.getElem_map]
    exact (batchC_eq_flat C i c).symm
  -- (3) the public row pinned through the Lagrange chunk pin
  have hpubC : ∀ c : Fin nc,
      (publicCommitment C σ cvk pub)[c]
        = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ) :=
    fun c => publicCommitment_corresponds C σ cvk pub idx
      (fun a P => (hsmul a P).symm) hlag hlagsz hpub c
  -- (4) the openings seam, fed directly
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hnc hk hbind cvk.comms hvkc (pubView idx pub)
      (fun col c => (cp.wComm[col])[c]) (fun c => cp.zComm[c])
      (fun c => (publicCommitment C σ cvk pub)[c])
      hpubC
      (fun i c => aRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
      (fun i c => ρRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
      hbound₀
  refine ⟨badB, badG, badA, badZ,
    extractTable idx.omega (fun col => assembledRow σ.k nc
      (fun c => aRef ⟨(streamPos nc (wRow col) c : ℕ), hlt (wRow col) c⟩)),
    hbounds, ?_⟩
  intro hβ hγ hα hζ hζ1 hζb
  -- (5) the eval pins from the run's single accepted opening (flat arity)
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _ hFS haccept
  have hpins := eval_pins_of_opening σ hbind
    (runInput C σ cvk cp pub).commitmentFn
    (runInput C σ cvk cp pub).pointFn aRef ρRef hrep
    (runInput C σ cvk cp pub).evalFn
    (runInput C σ cvk cp pub).polyscale
    (runInput C σ cvk cp pub).evalscale hξ hr a ρ hopen
  -- (6) the ft opening and the Maller identity at the double collapse
  obtain ⟨aft, ρft, hcomm_ft, heval_ft⟩ :=
    ft_opening_of_reflected σ cvk cp pub hbind haccept aRef ρRef hrep hFS hξ hr
  have hCσ6 : ∀ c : Fin nc,
      (cvk.sigmaComm[6])[c] = commitPolyChunk σ (idx.sigmaPoly 6) (c : ℕ) :=
    fun c => congrFun (congrArg (fun cm => cm.sigma 6) hvkc) c
  have hσ₆ : (idx.sigmaPoly 6).natDegree
      < nc * 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hcommit : commit σ aft ρft
      = runPScalar C σ cvk cp pub
          • ∑ c : Fin nc,
              ((runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • (cvk.sigmaComm[6])[c]
        - ((runOracles C σ cvk cp pub).zeta ^ n - 1)
            • ∑ j : Fin cp.tComm.size,
                ((runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (j : ℕ)
                  • cp.tComm[j] :=
    hcomm_ft.trans (runFtComm_eq C hsmul hn)
  obtain ⟨htdeg, hteq0⟩ := ft_identity_of_chunks σ hbind (idx.sigmaPoly 6) hσ₆
    (fun c => (cvk.sigmaComm[6])[c]) hCσ6 htpos cp.tComm_le
    (fun j => cp.tComm[j]) aT ρT hTC
    (runPScalar C σ cvk cp pub)
    (runOracles C σ cvk cp pub).zeta
    (runFtEval0 C σ cvk cp pub) n hk aft ρft hcommit heval_ft
  -- (7) reconcile the derived identity into the consumer's shape
  have hce := claimedEvals_run_eq C (σ := σ) (cvk := cvk) (cp := cp)
    (pub := pub) (pe := runPubEvals C σ cvk cp pub)
    (v := (runVU C σ cvk cp pub).1)
    (u := (runVU C σ cvk cp pub).2)
  have hcpe := claimedPub_run_eq C (σ := σ) (cvk := cvk) (cp := cp)
    (pub := pub) (pe := runPubEvals C σ cvk cp pub)
    (v := (runVU C σ cvk cp pub).1)
    (u := (runVU C σ cvk cp pub).2)
  have hζM : runZetaM C σ cvk cp pub
      = (runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k := by
    unfold runZetaM
    rw [powPow2_eq]
  have hζwM : runZetaOmegaM C σ cvk cp pub
      = (idx.omega * (runOracles C σ cvk cp pub).zeta) ^ 2 ^ σ.k := by
    unfold runZetaOmegaM runZetaOmega
    rw [powPow2_eq, homega, mul_comm]
  unfold runPScalar runFtEval0 runFtEval0P runPubEval0 runLinEvals at hteq0
  rw [← hce, ← hcpe, hζM, hζwM, hn, hzk, homega, hendo, hmds, hshift] at hteq0
  -- (8) the per-row pins, at the consumer's two eval points
  have hpt : (runInput C σ cvk cp pub).pointFn
      = ![(runOracles C σ cvk cp pub).zeta,
          idx.omega * (runOracles C σ cvk cp pub).zeta] := by
    funext j
    fin_cases j
    · rfl
    · show (runOracles C σ cvk cp pub).zeta * cvk.omega = _
      rw [homega]
      exact mul_comm _ _
  rw [hpt] at hpins
  -- (9) feed the consumer
  exact himp (runOracles C σ cvk cp pub).beta
    (runOracles C σ cvk cp pub).gamma
    (runOracles C σ cvk cp pub).alpha
    (ftChunkAssembly σ.k cp.tComm.size aT)
    (runOracles C σ cvk cp pub).zeta
    (fun (i : Fin batchRows) (ch : Fin nc) (j : Fin evalPts) =>
      ((runInputP C σ cvk cp pub
          (runPubEvals C σ cvk cp pub)
          (runVU C σ cvk cp pub).1
          (runVU C σ cvk cp pub).2).evals[(streamPos nc i ch : ℕ)]'
            ((streamPos nc i ch).isLt))[(j : ℕ)]'j.isLt)
    (fun i c => aRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
    (fun i c => ρRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
    hβ hγ hα hζ hζ1 hζb htdeg
    (fun i c => ⟨hbound₀ i c,
      fun j => hpins ⟨(streamPos nc i c : ℕ), hlt i c⟩ j⟩)
    hteq0

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
per-chunk `VKCorresponds`, the scalar pins, and the Lagrange pin.

The trust surface. Axiom consumed: `kimchi_fiat_shamir_vesta` (once, threaded
through `run_sound_algebraic_ft` to both the flat eval pins and the ft opening), on
top of the point-count-backed `Module` instance. The computational hypotheses stay
in the statement: the AGM representations `aRef`/`ρRef`/`aT`/`ρT`, the good-challenge
guards `hξ`/`hr`, and DL-binding `hbind` — the assumption that no nontrivial
discrete-log relation among the SRS generators is known. `hbind` is
information-theoretically false at real parameters and meaningful only as a
computational assumption — see the `hbind` scope note in the
`Bulletproof/Soundness.lean` module docstring (the file of
`chunked_batch_soundness`). No `ζⁿ ≠ 1` guard: the public claims are proof-carried
batch data, believed only through binding — no barycentric reconciliation. The Vesta
run-level root. -/
theorem kimchiVesta_run_sound_algebraic_ft (σ : SRS IpaVesta.Point) {nc : ℕ}
    (cvk : KimchiVK IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc σ.k)
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
    (hTC : ∀ j : Fin cp.tComm.size, commit σ (aT j) (ρT j) = cp.tComm[j])
    (hξ : (runInput IpaVesta.curve σ cvk cp pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaVesta.curve σ cvk cp pub).pointFn
          (runInput IpaVesta.curve σ cvk cp pub).evalFn)
    (hr : (runInput IpaVesta.curve σ cvk cp pub).evalscale
      ∉ badROf σ aRef (runInput IpaVesta.curve σ cvk cp pub).pointFn
          (runInput IpaVesta.curve σ cvk cp pub).evalFn
          (runInput IpaVesta.curve σ cvk cp pub).polyscale) :
    ∃ (badB : Finset Fp) (badG : Fp → Finset Fp) (badA : Fp → Fp → Finset Fp)
        (badZ : Fp → Fp → Fp → Polynomial Fp → Finset Fp)
        (wTab : Fin n → Fin wCols → Fp),
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
          Satisfies idx (pubView idx pub) wTab) :=
  run_sound_algebraic_ft σ cvk cp pub idx Pasta.vesta_smul_val hnc hk hn hvk hpub
    htpos hbind hacc (kimchi_fiat_shamir_vesta σ cvk cp pub) aRef ρRef hrep aT ρT
    hTC hξ hr

/-- **The run-level residue-free root (Pallas).** The Pallas-side twin of
`kimchiVesta_run_sound_algebraic_ft`, over `Fq`/`IpaPallas`. The same trust surface:
the sole axiom consumed is its Fiat–Shamir assumption `kimchi_fiat_shamir_pallas`
(once, through `run_sound_algebraic_ft`), and the computational hypotheses — the AGM
representations `aRef`/`ρRef`/`aT`/`ρT`, the good-challenge guards `hξ`/`hr`, and
DL-binding `hbind` (see the `hbind` scope note in the `Bulletproof/Soundness.lean`
module docstring) — stay in the statement. -/
theorem kimchiPallas_run_sound_algebraic_ft (σ : SRS IpaPallas.Point) {nc : ℕ}
    (cvk : KimchiVK IpaPallas.curve nc) (cp : KimchiProof IpaPallas.curve nc σ.k)
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
    (hTC : ∀ j : Fin cp.tComm.size, commit σ (aT j) (ρT j) = cp.tComm[j])
    (hξ : (runInput IpaPallas.curve σ cvk cp pub).polyscale
      ∉ badXiOf σ aRef (runInput IpaPallas.curve σ cvk cp pub).pointFn
          (runInput IpaPallas.curve σ cvk cp pub).evalFn)
    (hr : (runInput IpaPallas.curve σ cvk cp pub).evalscale
      ∉ badROf σ aRef (runInput IpaPallas.curve σ cvk cp pub).pointFn
          (runInput IpaPallas.curve σ cvk cp pub).evalFn
          (runInput IpaPallas.curve σ cvk cp pub).polyscale) :
    ∃ (badB : Finset Fq) (badG : Fq → Finset Fq) (badA : Fq → Fq → Finset Fq)
        (badZ : Fq → Fq → Fq → Polynomial Fq → Finset Fq)
        (wTab : Fin n → Fin wCols → Fq),
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
          Satisfies idx (pubView idx pub) wTab) :=
  run_sound_algebraic_ft σ cvk cp pub idx Pasta.pallas_smul_val hnc hk hn hvk hpub
    htpos hbind hacc (kimchi_fiat_shamir_pallas σ cvk cp pub) aRef ρRef hrep aT ρT
    hTC hξ hr

end Kimchi.Verifier
