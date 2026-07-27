import Bulletproof.Reflection
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

/-- Blocks stay inside their region: `q·nc + c < Q·nc`. Public because it is the bound
`streamPos` carries, and downstream layers (the knowledge-soundness game) index the run's
flat commitment stream through it rather than re-deriving the arithmetic. -/
theorem block_lt {q Q c nc : ℕ} (hq : q < Q) (hc : c < nc) :
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

end StreamReads

/-! ## The stream positions

The flat position of every abstract batch row's chunk, `Fin`-typed at the stream
length: the abstract rows are the deployed `to_batch` order with the single-chunk ft
row interposed at flat position `nc`, and every position lies inside the `44·nc + 1`
flat rows by construction. The per-region value lemmas below feed the reads. -/

/-- The flat stream position of abstract batch row `i`, chunk `c`. The public row's
chunks come first and every later row `i` starts at `nc + 1 + (i − 1)·nc`. Public
because it is the layout the downstream knowledge-soundness statement must name: the
group-element side of "the family's verifying-key representations are honest" lives on
the run's flat commitment stream, and this map is what says which flat entry a given
abstract batch row and chunk occupies. -/
def streamPos (nc : ℕ) (i : Fin batchRows) (c : Fin nc) :
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

/-- **The `ft` row's commitment, at its own flat position**: the run's opening-argument
input carries, at flat position `nc` (immediately after the public row's `nc` chunks), the
constructed single-chunk `ft` commitment `runFtComm`. Public because a consumer that wants
to *name* the `ft` representation — rather than merely receive it existentially from
`ft_opening_of_pins` — needs the position identity separately. -/
theorem commitmentFn_ftPos {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (hsz : (nc : ℕ) < (runInput C σ cvk cp pub).commitments.size) :
    (runInput C σ cvk cp pub).commitmentFn ⟨nc, hsz⟩ = runFtComm C σ cvk cp pub := by
  show ((runStreamP C σ cvk cp pub (runPubEvals C σ cvk cp pub)).map
      (·.1))[(nc : ℕ)]'(by
        show (nc : ℕ) < nc + 1 + tailRowCount * nc
        omega)
    = runFtComm C σ cvk cp pub
  rw [Vector.getElem_map, stream_ft_read C]

/-- **The `ft` row's claimed evaluation, at its own flat position**: the run's claimed
evaluation at flat position `nc` and the zeroth evaluation point IS the computed `ft`
claim `runFtEval0`. The companion of `commitmentFn_ftPos`; together they let a consumer
pin the `ft` representation to `aRef ⟨nc, _⟩` by name. -/
theorem evalFn_ftPos {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (hsz : (nc : ℕ) < (runInput C σ cvk cp pub).commitments.size) :
    (runInput C σ cvk cp pub).evalFn ⟨nc, hsz⟩ (0 : Fin evalPts)
      = runFtEval0 C σ cvk cp pub := by
  show (((runStreamP C σ cvk cp pub (runPubEvals C σ cvk cp pub)).map
      (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector C.ScalarField evalPts)))[(nc : ℕ)]'(by
        show (nc : ℕ) < nc + 1 + tailRowCount * nc
        omega)
      : Vector C.ScalarField evalPts)[(0 : ℕ)]
    = runFtEval0 C σ cvk cp pub
  rw [Vector.getElem_map, stream_ft_read C]
  rfl

/-- **The ft opening from the eval pins alone** (transcript-free): SRS-basis
representations of the run's own flat batch rows together with the *eval pins* —
verbatim `eval_pins_of_opening`'s conclusion at the run's own data, i.e. every claimed
evaluation `evalFn i j` equals the represented row's true evaluation at `pointFn j` —
yield the ft opening. The ft row sits at flat position `nc`, right after the public
row's chunks (`stream_ft_read`): its commitment equation is `hrep` at index `nc`, and
its value equation is the pin at `(i, j) = (nc, 0)`, the run's zeroth evaluation point
being its own `ζ`.

This is `ft_opening_of_reflected` with DL-binding, the transcript tree and the two
good-combination guards deleted from the statement: the tree is used there ONLY to
manufacture these pins (via `ipa_soundnessA` then `eval_pins_of_opening`), so taking
the pins as the hypothesis isolates the transcript at a single seam. The
knowledge-soundness game reaches the same pins from its forking extractor's accepted
opening and so never touches the Fiat–Shamir axioms. -/
theorem ft_opening_of_pins {C : Ipa.CommitmentCurve} [Module C.ScalarField C.Point]
    (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size → Fin (2 ^ σ.k)
      → C.ScalarField)
    (ρRef : Fin (runInput C σ cvk cp pub).commitments.size → C.ScalarField)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i) = (runInput C σ cvk cp pub).commitmentFn i)
    (hpins : ∀ (i : Fin (runInput C σ cvk cp pub).commitments.size) (j : Fin evalPts),
      (runInput C σ cvk cp pub).evalFn i j
        = innerProduct (aRef i)
            (evalVector (2 ^ σ.k) ((runInput C σ cvk cp pub).pointFn j))) :
    ∃ (aft : Fin (2 ^ σ.k) → C.ScalarField) (ρft : C.ScalarField),
      commit σ aft ρft = runFtComm C σ cvk cp pub
        ∧ innerProduct aft (evalVector (2 ^ σ.k) (runOracles C σ cvk cp pub).zeta)
            = runFtEval0 C σ cvk cp pub := by
  have hsz : (nc : ℕ) < (runInput C σ cvk cp pub).commitments.size := by
    show (nc : ℕ) < nc + 1 + tailRowCount * nc
    omega
  refine ⟨aRef ⟨nc, hsz⟩, ρRef ⟨nc, hsz⟩, ?_, ?_⟩
  · rw [hrep ⟨nc, hsz⟩]
    exact commitmentFn_ftPos σ cvk cp pub hsz
  · have hpin := hpins ⟨nc, hsz⟩ (0 : Fin evalPts)
    have hpt : (runInput C σ cvk cp pub).pointFn (0 : Fin evalPts)
        = (runOracles C σ cvk cp pub).zeta := rfl
    rw [hpt] at hpin
    rw [← hpin]
    exact evalFn_ftPos σ cvk cp pub hsz

/-- **The ft opening from a chunked reflected run** (tree-as-hypothesis):
DL-binding, a reflected accepted chunked run, SRS-basis representations of the run's
own flat batch rows, the run's transcript tree (the chunked `kimchi_fiat_shamir_*`
shape, here a hypothesis), and good combination challenges yield the ft opening — a
representation of the constructed ft commitment `runFtComm` (the DOUBLE collapse at
`ζ^{2^σ.k}`) whose evaluation at the run's own `ζ` is the computed claim `runFtEval0`.
The ft row sits at flat position `nc`, right after the public row's chunks
(`stream_ft_read`). The tree is spent here on the two-step composite `ipa_soundnessA`
then `eval_pins_of_opening`; everything downstream of the resulting eval pins is
`ft_opening_of_pins`. -/
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
  exact ft_opening_of_pins σ cvk cp pub aRef ρRef hrep
    (eval_pins_of_opening σ hbind (runInput C σ cvk cp pub).commitmentFn
      (runInput C σ cvk cp pub).pointFn aRef ρRef hrep (runInput C σ cvk cp pub).evalFn
      (runInput C σ cvk cp pub).polyscale (runInput C σ cvk cp pub).evalscale hξ hr
      a ρ hopen)

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

/-- **The public commitment corresponds**: under the Lagrange chunk pin, the deployed
verifier's per-chunk public commitment is the per-chunk masked commitment of the
NEGATED public interpolant — the `pubC` feed of the reduction. The `.val`-scalar
collapse is supplied per curve (`hsmul`).

Public because the knowledge-soundness layer needs the public row of the verifying-key
honesty predicate: its claim is assembled at the oracle table's own challenges, so it
cannot route through `commitmentFn_streamPos_pubRow_eq_commit` (which is stated at
`runInput`) and must compose this chunk pin with the layout bridge itself. -/
theorem publicCommitment_corresponds [Module C.ScalarField C.Point]
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

/-- Reading a flat stream's evaluation matrix at a batch stream position: the flat row's
claim pair. Stated for ANY stream `S` agreeing with `runStreamP` at the batch positions
(`hS`) — the challenge-generic claim of the knowledge-soundness game differs from the
sponge-driven one only in the `ft` slot, which no batch position reads. -/
private theorem stream_evals_read
    (S : Vector (C.Point × C.ScalarField × C.ScalarField) (nc + 1 + tailRowCount * nc))
    (hS : ∀ (i : Fin batchRows) (c : Fin nc),
      S[(streamPos nc i c : ℕ)]'((streamPos nc i c).isLt)
        = (runStreamP C σ cvk cp pub pe)[(streamPos nc i c : ℕ)]'
            ((streamPos nc i c).isLt))
    (i : Fin batchRows) (c : Fin nc) :
    (S.map (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector C.ScalarField evalPts)))[
        (streamPos nc i c : ℕ)]'((streamPos nc i c).isLt)
      = ⟨#[((runStreamP C σ cvk cp pub pe)[(streamPos nc i c : ℕ)]'
              ((streamPos nc i c).isLt)).2.1,
          ((runStreamP C σ cvk cp pub pe)[(streamPos nc i c : ℕ)]'
              ((streamPos nc i c).isLt)).2.2],
         rfl⟩ := by
  rw [Vector.getElem_map, hS i c]

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
abstract `claimedEvals`, fed a flat stream's claims at the stream positions, IS the
verifier's combined record `cp.linEvals` at the same combination powers. Pure layout
reading through the region reads: neither the combination powers nor the `ft` slot are
looked at, so the statement is generic in `zM`/`zwM` and in any stream `S` that agrees
with `runStreamP` at the batch positions. -/
private theorem claimedEvals_stream_eq (zM zwM : C.ScalarField)
    (S : Vector (C.Point × C.ScalarField × C.ScalarField) (nc + 1 + tailRowCount * nc))
    (hS : ∀ (i : Fin batchRows) (c : Fin nc),
      S[(streamPos nc i c : ℕ)]'((streamPos nc i c).isLt)
        = (runStreamP C σ cvk cp pub pe)[(streamPos nc i c : ℕ)]'
            ((streamPos nc i c).isLt)) :
    claimedEvals zM zwM
        (fun (i : Fin batchRows) (ch : Fin nc) (j : Fin evalPts) =>
          ((S.map (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector C.ScalarField evalPts)))[
              (streamPos nc i ch : ℕ)]'((streamPos nc i ch).isLt))[(j : ℕ)]'j.isLt)
      = cp.linEvals zM zwM := by
  refine Evals.ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · funext col
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS (wRow col) ch, stream_read_w C col ch]
    rfl
  · funext col
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS (wRow col) ch, stream_read_w C col ch]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS zRow ch, stream_read_z C ch]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS zRow ch, stream_read_z C ch]
    rfl
  · funext i
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS (sRow i) ch, stream_read_s C i ch]
    rfl
  · funext col
    refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS (cRow col) ch, stream_read_c C col ch]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS (selRow 0) ch, stream_read_sel C 0 ch,
      tailRows_read_lit C (1 + ((0 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS (selRow 1) ch, stream_read_sel C 1 ch,
      tailRows_read_lit C (1 + ((1 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS (selRow 2) ch, stream_read_sel C 2 ch,
      tailRows_read_lit C (1 + ((2 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS (selRow 3) ch, stream_read_sel C 3 ch,
      tailRows_read_lit C (1 + ((3 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS (selRow 4) ch, stream_read_sel C 4 ch,
      tailRows_read_lit C (1 + ((4 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl
  · refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
    beta_reduce
    rw [stream_evals_read C S hS (selRow 5) ch, stream_read_sel C 5 ch,
      tailRows_read_lit C (1 + ((5 : Fin selCount) : ℕ)) (by decide)]
    show ((Vector.ofFn _)[(ch : ℕ)]'ch.isLt
      : C.Point × C.ScalarField × C.ScalarField).2.1 = _
    rw [Vector.getElem_ofFn]
    rfl

/-- **The combined public claim is the run's own**: `claimedPub` at a flat stream's
public-row claims is the verifier's chunk-combined public evaluation. Generic in the
combination power and in the stream, for the same reason as `claimedEvals_stream_eq`. -/
private theorem claimedPub_stream_eq (zM : C.ScalarField)
    (S : Vector (C.Point × C.ScalarField × C.ScalarField) (nc + 1 + tailRowCount * nc))
    (hS : ∀ (i : Fin batchRows) (c : Fin nc),
      S[(streamPos nc i c : ℕ)]'((streamPos nc i c).isLt)
        = (runStreamP C σ cvk cp pub pe)[(streamPos nc i c : ℕ)]'
            ((streamPos nc i c).isLt)) :
    claimedPub zM
        (fun (i : Fin batchRows) (ch : Fin nc) (j : Fin evalPts) =>
          ((S.map (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector C.ScalarField evalPts)))[
              (streamPos nc i ch : ℕ)]'((streamPos nc i ch).isLt))[(j : ℕ)]'j.isLt)
      = combineAt zM pe.zeta.toArray := by
  refine sum_readsTo C _ _ (by simp) _ fun ch => ?_
  beta_reduce
  rw [stream_evals_read C S hS pubRow ch, stream_read_pub C ch]
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
position. The layout bridge `hbound₀` consumes. Public because it is the flattening
identity the downstream layer needs in order to read the run's own commitment stream as
the abstract batch; `commitmentFn_streamPos` is its restatement at the run's input. -/
theorem batchC_eq_flat (i : Fin batchRows) (c : Fin nc) :
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

/-! ## The layout bridge: the run's commitment stream at a batch position

`batchC_eq_flat` reads the abstract 44-row batch off the flat stream; the two statements
below carry that read to the run's *opening-argument input* — the object the
knowledge-soundness game's family actually represents — and then, under the key–index
correspondence, all the way to the honest chunk commitments of the presented circuit's own
polynomials. Together they are the export that lets a downstream layer state "the family's
verifying-key representations are honest" without re-deriving the layout.

The generic form `batchC_eq_flat_gen` comes first, because the knowledge-soundness layer's
claim is NOT `runInput`: it is the challenge-generic `runInputWith` at the oracle table's
own challenges, whose flat stream differs from `runStreamP`'s in exactly one slot — the
`ft` row at flat position `nc`, which no batch stream position ever reads. -/

/-- The low read of the `(public block ++ ft ++ tail)` triple append. -/
private theorem append3_read_lo {α : Type*} {nc : ℕ} (A : Vector α nc) (B : Vector α 1)
    (D : Vector α (tailRowCount * nc)) (j : ℕ) (hj : j < nc) :
    ((A ++ B) ++ D)[j]'(by omega) = A[j]'hj := by
  rw [Vector.getElem_append, dif_pos (by omega : j < nc + 1), Vector.getElem_append,
    dif_pos hj]

/-- The high read of the `(public block ++ ft ++ tail)` triple append. -/
private theorem append3_read_hi {α : Type*} {nc : ℕ} (A : Vector α nc) (B : Vector α 1)
    (D : Vector α (tailRowCount * nc)) (j : ℕ) (hj : j < nc + 1 + tailRowCount * nc)
    (hge : nc + 1 ≤ j) :
    ((A ++ B) ++ D)[j]'hj = D[j - (nc + 1)]'(by omega) := by
  rw [Vector.getElem_append, dif_neg (by omega)]

/-- The `ft` read of the `(public block ++ ft ++ tail)` triple append: position `nc` is the
singleton middle block. -/
private theorem append3_read_ft {α : Type*} {nc : ℕ} (A : Vector α nc) (b : α)
    (D : Vector α (tailRowCount * nc)) (h : (nc : ℕ) < nc + 1 + tailRowCount * nc) :
    ((A ++ (⟨#[b], rfl⟩ : Vector α 1)) ++ D)[(nc : ℕ)]'h = b := by
  rw [Vector.getElem_append, dif_pos (by omega : (nc : ℕ) < nc + 1),
    Vector.getElem_append, dif_neg (by omega : ¬ (nc : ℕ) < nc)]
  simp only [Nat.sub_self]
  rfl

/-- Two `(public block ++ ft ++ tail)` triple appends that differ only in the `ft` slot read
alike off position `nc`. This is what makes the challenge-generic claim interchangeable with
the sponge-driven one at every batch stream position. -/
private theorem append3_read_ne_ft {α : Type*} {nc : ℕ} (A : Vector α nc) (B B' : Vector α 1)
    (D : Vector α (tailRowCount * nc)) (j : ℕ) (hj : j < nc + 1 + tailRowCount * nc)
    (hne : j ≠ nc) :
    ((A ++ B) ++ D)[j]'hj = ((A ++ B') ++ D)[j]'hj := by
  by_cases hlo : j < nc
  · rw [append3_read_lo _ _ _ _ hlo, append3_read_lo _ _ _ _ hlo]
  · rw [append3_read_hi _ _ _ _ hj (by omega), append3_read_hi _ _ _ _ hj (by omega)]

/-- No abstract batch stream position is the `ft` row's flat position `nc`: the public row's
chunks sit strictly below it and every later row strictly above. -/
private theorem streamPos_ne_ft {nc : ℕ} (i : Fin batchRows) (c : Fin nc) :
    (streamPos nc i c : ℕ) ≠ nc := by
  have hc := c.isLt
  show (if (i : ℕ) < 1 then (c : ℕ)
      else nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ)) ≠ nc
  split <;> omega

/-- **The layout bridge, challenge-generically**: the abstract 44-row chunked batch is the
commitment column of ANY flat stream in the deployed `to_batch` shape — a public block whose
commitments are the run's, then one `ft` slot, then the flattened 43-row tail. The `ft` slot
is left completely free because no batch stream position reads it (`streamPos_ne_ft`).

This is the form the knowledge-soundness layer needs: its claim is `runInputWith` at the
oracle table's challenges, which agrees with `runStreamP` everywhere except that slot. -/
theorem batchC_eq_flat_gen {C : Ipa.CommitmentCurve} {σ : SRS C.Point} {nc : ℕ}
    {cvk : KimchiVK C nc} {cp : KimchiProof C nc σ.k} {pub : Array C.ScalarField}
    (pubBlock : Fin nc → C.Point × C.ScalarField × C.ScalarField)
    (hpb : ∀ c : Fin nc, (pubBlock c).1 = (publicCommitment C σ cvk pub)[c])
    (ft : C.Point × C.ScalarField × C.ScalarField)
    (i : Fin batchRows) (c : Fin nc) :
    batchC (fun (col : Fin wCols) (c : Fin nc) => (cp.wComm[col])[c])
        (fun c => cp.zComm[c])
        (fun c => (publicCommitment C σ cvk pub)[c]) cvk.comms i c
      = ((((Vector.ofFn pubBlock)
            ++ (⟨#[ft], rfl⟩ : Vector (C.Point × C.ScalarField × C.ScalarField) 1))
            ++ (tailRowsOf C cvk cp).flatten)[(streamPos nc i c : ℕ)]'
          ((streamPos nc i c).isLt)).1 := by
  refine (batchC_eq_flat C (pe := runPubEvals C σ cvk cp pub) i c).trans ?_
  have hj : (streamPos nc i c : ℕ) < nc + 1 + tailRowCount * nc := (streamPos nc i c).isLt
  have hne := streamPos_ne_ft i c
  unfold runStreamP
  by_cases hlo : (streamPos nc i c : ℕ) < nc
  · rw [append3_read_lo _ _ _ _ hlo, append3_read_lo (Vector.ofFn pubBlock) _ _ _ hlo,
      Vector.getElem_ofFn, Vector.getElem_ofFn]
    exact (hpb ⟨_, hlo⟩).symm
  · rw [append3_read_hi _ _ _ _ hj (by omega),
      append3_read_hi (Vector.ofFn pubBlock) _ _ _ hj (by omega)]

/-- **The run's commitment stream at a batch position**: the opening-argument input's
commitment column reads, at the stream position of abstract batch row `i` and chunk `c`,
exactly the abstract batch's own entry there. This is `batchC_eq_flat` restated at
`runInput` rather than at `runStreamP`; it is the form a consumer that only knows the
run's `Ipa.Input` can use. -/
theorem commitmentFn_streamPos {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (i : Fin batchRows) (c : Fin nc) :
    (runInput C σ cvk cp pub).commitmentFn
        ⟨(streamPos nc i c : ℕ), (streamPos nc i c).isLt⟩
      = batchC (fun (col : Fin wCols) (c : Fin nc) => (cp.wComm[col])[c])
          (fun c => cp.zComm[c])
          (fun c => (publicCommitment C σ cvk pub)[c]) cvk.comms i c := by
  show ((runStreamP C σ cvk cp pub
      (runPubEvals C σ cvk cp pub)).map
        (·.1))[(streamPos nc i c : ℕ)]'((streamPos nc i c).isLt) = _
  rw [Vector.getElem_map]
  exact (batchC_eq_flat C i c).symm

/-- A chunk commitment is the hiding commitment of the chunk's coefficient window at
blinder `0`.

Alias of `Capstone/Algebraic.commitPolyChunk_eq_commit`, which iter 005 promoted out of
`private` for exactly this purpose; the duplicated proof is gone. The NAME survives only
because consumers outside this file (`Verifier/KnowledgeSoundness.lean`) still call it —
deleting it outright is a cross-file edit, not this file's to make. -/
theorem commitPolyChunk_as_commit {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] (σ : SRS G) (p : Polynomial F) (c : ℕ) :
    commitPolyChunk σ p c = commit σ (chunkCoeffs (2 ^ σ.k) p c) 0 :=
  commitPolyChunk_eq_commit σ p c

/-- The masked chunk commitment is the same window at blinder `1`. The companion of
`commitPolyChunk_as_commit`, and the same alias note applies. -/
theorem commitPolyMaskedChunk_as_commit {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] (σ : SRS G) (p : Polynomial F) (c : ℕ) :
    commitPolyMaskedChunk σ p c = commit σ (chunkCoeffs (2 ^ σ.k) p c) 1 := by
  rw [commitPolyMaskedChunk, commitPolyChunk_as_commit]
  simp [commit]

/-- Under binding the unblinded chunk relation of `dlRelation_of_chunk_rep_ne` is trivial,
so the representation IS the honest window. The discharge half; a local restatement of the
`private` `chunk_rep_of_commit` of `Verifier/Reduction/Soundness.lean`, built here on that
file's PUBLIC break branch. -/
private theorem rep_eq_of_chunkCommit {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F} {c : ℕ}
    (hcommit : commit σ a ρ = commitPolyChunk σ p c) :
    a = chunkCoeffs (2 ^ σ.k) p c := by
  obtain ⟨hrel, hnt⟩ := dlRelation_of_chunk_rep_ne σ hcommit
  by_contra hne
  exact hnt hne (hbind _ _ hrel).1

/-- The masked analogue of `rep_eq_of_chunkCommit` (selector and public rows). -/
private theorem rep_eq_of_maskedChunkCommit {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F} {c : ℕ}
    (hcommit : commit σ a ρ = commitPolyMaskedChunk σ p c) :
    a = chunkCoeffs (2 ^ σ.k) p c := by
  obtain ⟨hrel, hnt⟩ := dlRelation_of_chunk_rep_masked_ne σ hcommit
  by_contra hne
  exact hnt hne (hbind _ _ hrel).1

/-- **The σ rows of the run's commitment stream**: under the key–index correspondence the
run's opening-argument input carries, at the stream position of the `i`-th σ row and chunk
`c`, the unblinded chunk commitment of the circuit's own `sigmaPermCol i` permutation
polynomial. -/
theorem commitmentFn_streamPos_sRow_eq_commit {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {n : ℕ} [NeZero n] {idx : Index C.ScalarField n} (hvk : cvk.Corresponds σ idx)
    (i : Fin sigmaRows) (c : Fin nc) :
    (runInput C σ cvk cp pub).commitmentFn
        ⟨(streamPos nc (sRow i) c : ℕ), (streamPos nc (sRow i) c).isLt⟩
      = commit σ (chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly (sigmaPermCol i)) (c : ℕ)) 0 :=
  ((commitmentFn_streamPos σ cvk cp pub (sRow i) c).trans
    (batchC_sRow_of_corresponds σ hvk.1 _ _ _ i c)).trans
      (commitPolyChunk_as_commit σ _ (c : ℕ))

/-- **The coefficient rows of the run's commitment stream**: the unblinded chunk
commitment of the circuit's own `cc`-th coefficient interpolant. -/
theorem commitmentFn_streamPos_cRow_eq_commit {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {n : ℕ} [NeZero n] {idx : Index C.ScalarField n} (hvk : cvk.Corresponds σ idx)
    (cc : Fin coeffCols) (c : Fin nc) :
    (runInput C σ cvk cp pub).commitmentFn
        ⟨(streamPos nc (cRow cc) c : ℕ), (streamPos nc (cRow cc) c).isLt⟩
      = commit σ (chunkCoeffs (2 ^ σ.k) (idx.coeffPoly cc) (c : ℕ)) 0 :=
  ((commitmentFn_streamPos σ cvk cp pub (cRow cc) c).trans
    (batchC_cRow_of_corresponds σ hvk.1 _ _ _ cc c)).trans
      (commitPolyChunk_as_commit σ _ (c : ℕ))

/-- **The selector rows of the run's commitment stream**: the MASKED chunk commitment
(fixed unit blinder, `mask_custom`) of the circuit's own `selGate jj` selector
interpolant. -/
theorem commitmentFn_streamPos_selRow_eq_commit {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {n : ℕ} [NeZero n] {idx : Index C.ScalarField n} (hvk : cvk.Corresponds σ idx)
    (jj : Fin selCount) (c : Fin nc) :
    (runInput C σ cvk cp pub).commitmentFn
        ⟨(streamPos nc (selRow jj) c : ℕ), (streamPos nc (selRow jj) c).isLt⟩
      = commit σ (chunkCoeffs (2 ^ σ.k) (idx.selectorPoly (selGate jj)) (c : ℕ)) 1 :=
  ((commitmentFn_streamPos σ cvk cp pub (selRow jj) c).trans
    (batchC_selRow_of_corresponds σ hvk.1 _ _ _ jj c)).trans
      (commitPolyMaskedChunk_as_commit σ _ (c : ℕ))

/-- **The public row of the run's commitment stream**: the MASKED chunk commitment of the
NEGATED public interpolant. Unlike the other three families the public row is not a key
entry — it is recomputed by the verifier from the key's Lagrange basis — so this case
additionally needs the run's acceptance (for the Lagrange-basis size), the public-input
arity, and the `.val`-scalar collapse, exactly as `publicCommitment_corresponds` does. -/
theorem commitmentFn_streamPos_pubRow_eq_commit {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {n : ℕ} [NeZero n] {idx : Index C.ScalarField n}
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a • P = a.val • P)
    (hvk : cvk.Corresponds σ idx) (hpub : pub.size = idx.publicCount)
    (hacc : kimchiVerify C σ cvk cp pub = true) (c : Fin nc) :
    (runInput C σ cvk cp pub).commitmentFn
        ⟨(streamPos nc pubRow c : ℕ), (streamPos nc pubRow c).isLt⟩
      = commit σ
          (chunkCoeffs (2 ^ σ.k) (-(idx.pubPoly (pubView idx pub))) (c : ℕ)) 1 := by
  obtain ⟨hlagsz, _, _⟩ := kimchiVerify_reflects C σ cvk cp pub hacc
  refine ((commitmentFn_streamPos σ cvk cp pub pubRow c).trans ?_).trans
    (commitPolyMaskedChunk_as_commit σ _ (c : ℕ))
  exact (congrFun (batchC_pubRow (fun (col : Fin wCols) (c : Fin nc) => (cp.wComm[col])[c])
      (fun c => cp.zComm[c])
      (fun c => (publicCommitment C σ cvk pub)[c]) cvk.comms) c).trans
    (publicCommitment_corresponds C σ cvk pub idx
      (fun a P => (hsmul a P).symm) hvk.2.2.2.2.2.2 hlagsz hpub c)

/-! ## The run's claim at handed-in challenges

The knowledge-soundness game does not run the deployed verifier: its win event is the
CHALLENGE-GENERIC verifier, fed the six pre-IPA field challenges from an oracle table, and
its claim is that verifier's batched input. Every root above is stated at `runInput` — the
claim assembled from the run's OWN Poseidon sponge outputs — so none of them applies to a
run of the game.

The functions below are the challenge-generic twins of `Verifier/Reflect.lean`'s
sponge-driven abbreviations: the same bodies with `runOracles`' four fq-side squeezes and
the two fr-side scalars handed in as parameters. `runInputAt_eq_runInput` records that at
the sponge's own outputs they collapse, definitionally, to the deployed objects — nothing
new is assumed, only a parameter is exposed. -/

/-- The public evaluation chunk vectors at a handed-in `ζ`: `runPubEvals`'s body, with the
three derived powers (`ζω`, `ζⁿ`, `(ζω)ⁿ`) recomputed from the parameter exactly as the
verifier does. -/
def runPubEvalsAt (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) (zeta : C.ScalarField) :
    Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc) :=
  publicEvalChunks cp cvk.n cvk.omega zeta (zeta * cvk.omega)
    (powPow2 zeta cvk.domainLog2) (powPow2 (zeta * cvk.omega) cvk.domainLog2) pub

/-- The computed `ft(ζ)` claim at handed-in challenges — `runFtEval0`'s body with the four
fq-side squeezes as parameters. -/
def runFtEval0At (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta : C.ScalarField) : C.ScalarField :=
  ftEval0 cvk.n cvk.zkRows cvk.omega (fun i => cvk.shifts[i]) cvk.endo
    (mdsOfParams C.frParams) alpha beta gamma zeta
    (combineAt (powPow2 zeta σ.k) (runPubEvalsAt C σ cvk cp pub zeta).zeta.toArray)
    (cp.linEvals (powPow2 zeta σ.k) (powPow2 (zeta * cvk.omega) σ.k))

/-- The permutation scalar (the `f_comm` coefficient) at handed-in challenges —
`runPScalar`'s body with the four fq-side squeezes as parameters. It does not read the
public input: the sponge did, only to produce the challenges. -/
def runPScalarAt (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (beta gamma alpha zeta : C.ScalarField) : C.ScalarField :=
  permScalar beta gamma alpha (zkpmEval cvk.n cvk.zkRows cvk.omega zeta)
    (cp.linEvals (powPow2 zeta σ.k) (powPow2 (zeta * cvk.omega) σ.k))

/-- The constructed `ft` commitment at handed-in challenges — `runFtComm`'s DOUBLE collapse
at `ζ^{2^σ.k}` with the four fq-side squeezes as parameters. -/
def runFtCommAt (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (beta gamma alpha zeta : C.ScalarField) : C.Point :=
  Ipa.combineCommitments C (powPow2 zeta σ.k)
      (cvk.sigmaComm[6].map
        (fun P => (runPScalarAt C σ cvk cp beta gamma alpha zeta).val • P)).toArray
    - (powPow2 zeta cvk.domainLog2 - 1).val
        • Ipa.combineCommitments C (powPow2 zeta σ.k) cp.tComm

/-- The flat segment stream at handed-in challenges — `runStreamP`'s triple append with the
public block at the handed-in `ζ` and the `ft` slot rebuilt from the parameters. -/
def runStreamAt (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta : C.ScalarField) :
    Vector (C.Point × C.ScalarField × C.ScalarField) (nc + 1 + tailRowCount * nc) :=
  (Vector.ofFn fun c : Fin nc =>
      ((publicCommitment C σ cvk pub)[c], (runPubEvalsAt C σ cvk cp pub zeta).zeta[c],
        (runPubEvalsAt C σ cvk cp pub zeta).zetaOmega[c]))
    ++ (⟨#[(runFtCommAt C σ cvk cp beta gamma alpha zeta,
             runFtEval0At C σ cvk cp pub beta gamma alpha zeta, cp.ftEval1)], rfl⟩
        : Vector (C.Point × C.ScalarField × C.ScalarField) 1)
    ++ (tailRowsOf C cvk cp).flatten

/-- **The run's batched IPA claim at handed-in challenges**: the batched opening-argument
input the verifier assembles when the six pre-IPA challenges are supplied rather than
squeezed. This is the claim the knowledge-soundness game's win event checks; its body is
`runInputP`'s with every sponge read replaced by a parameter. -/
def runInputAt (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) :
    Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts where
  commitments := (runStreamAt C σ cvk cp pub beta gamma alpha zeta).map (·.1)
  xs := ⟨#[zeta, zeta * cvk.omega], rfl⟩
  evals := (runStreamAt C σ cvk cp pub beta gamma alpha zeta).map
    (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector C.ScalarField evalPts))
  polyscale := v
  evalscale := u
  proof := cp.opening

/-- At the run's own sponge outputs the challenge-generic claim IS the deployed one —
definitionally: the `At` functions are the deployed bodies with the squeezes exposed. -/
theorem runInputAt_eq_runInput (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    runInputAt C σ cvk cp pub (runOracles C σ cvk cp pub).beta
        (runOracles C σ cvk cp pub).gamma (runOracles C σ cvk cp pub).alpha
        (runOracles C σ cvk cp pub).zeta (runVU C σ cvk cp pub).1
        (runVU C σ cvk cp pub).2
      = runInput C σ cvk cp pub := rfl

/-- The challenge-generic stream and the sponge-driven stream at the handed-in `ζ`'s public
block agree at every batch stream position: they differ only in the `ft` slot, which
`streamPos_ne_ft` never reaches. -/
private theorem runStreamAt_read_eq {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta : C.ScalarField) (i : Fin batchRows) (c : Fin nc) :
    (runStreamAt C σ cvk cp pub beta gamma alpha zeta)[(streamPos nc i c : ℕ)]'
        ((streamPos nc i c).isLt)
      = (runStreamP C σ cvk cp pub (runPubEvalsAt C σ cvk cp pub zeta))[
          (streamPos nc i c : ℕ)]'((streamPos nc i c).isLt) :=
  append3_read_ne_ft _ _ _ _ _ _ (streamPos_ne_ft i c)

/-- **The layout bridge at handed-in challenges**: the challenge-generic claim's commitment
column reads, at the stream position of abstract batch row `i` and chunk `c`, exactly the
abstract batch's own entry there. `commitmentFn_streamPos` with the six challenges as
parameters. -/
theorem commitmentFn_streamPosAt {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) (i : Fin batchRows) (c : Fin nc) :
    (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn
        ⟨(streamPos nc i c : ℕ), (streamPos nc i c).isLt⟩
      = batchC (fun (col : Fin wCols) (c : Fin nc) => (cp.wComm[col])[c])
          (fun c => cp.zComm[c])
          (fun c => (publicCommitment C σ cvk pub)[c]) cvk.comms i c := by
  show ((runStreamAt C σ cvk cp pub beta gamma alpha zeta).map
      (·.1))[(streamPos nc i c : ℕ)]'((streamPos nc i c).isLt) = _
  rw [Vector.getElem_map, runStreamAt_read_eq]
  exact (batchC_eq_flat C i c).symm

/-- **The `ft` row's commitment at its own flat position**, challenge-generically: the
challenge-generic claim carries at flat position `nc` the constructed `ft` commitment
`runFtCommAt`. `commitmentFn_ftPos` with the challenges as parameters. -/
theorem commitmentFn_ftPosAt {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField)
    (hsz : (nc : ℕ) < nc + 1 + tailRowCount * nc) :
    (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn ⟨nc, hsz⟩
      = runFtCommAt C σ cvk cp beta gamma alpha zeta := by
  show ((runStreamAt C σ cvk cp pub beta gamma alpha zeta).map (·.1))[(nc : ℕ)]'hsz = _
  rw [Vector.getElem_map]
  exact congrArg Prod.fst (append3_read_ft _ _ _ hsz)

/-- **The `ft` row's claimed evaluation at its own flat position**, challenge-generically:
the claimed evaluation at flat position `nc` and the zeroth evaluation point is the computed
`ft` claim `runFtEval0At`. `evalFn_ftPos` with the challenges as parameters. -/
theorem evalFn_ftPosAt {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField)
    (hsz : (nc : ℕ) < nc + 1 + tailRowCount * nc) :
    (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalFn ⟨nc, hsz⟩ (0 : Fin evalPts)
      = runFtEval0At C σ cvk cp pub beta gamma alpha zeta := by
  show (((runStreamAt C σ cvk cp pub beta gamma alpha zeta).map
      (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector C.ScalarField evalPts)))[(nc : ℕ)]'hsz
      : Vector C.ScalarField evalPts)[(0 : ℕ)] = _
  have hft : (runStreamAt C σ cvk cp pub beta gamma alpha zeta)[(nc : ℕ)]'hsz
      = (runFtCommAt C σ cvk cp beta gamma alpha zeta,
          runFtEval0At C σ cvk cp pub beta gamma alpha zeta, cp.ftEval1) :=
    append3_read_ft _ _ _ hsz
  rw [Vector.getElem_map, hft]
  rfl

/-- The two evaluation points of the challenge-generic claim, in the shape the openings seam
consumes: the handed-in `ζ` and `ω·ζ` at the corresponded root of unity. -/
theorem pointFn_runInputAt {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) {n : ℕ}
    {idx : Index C.ScalarField n} (homega : cvk.omega = idx.omega) :
    (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn
      = ![zeta, idx.omega * zeta] := by
  funext j
  fin_cases j
  · rfl
  · show zeta * cvk.omega = _
    rw [homega]
    exact mul_comm _ _

/-! ### The verifying-key rows of the challenge-generic claim

The four challenge-generic twins of `commitmentFn_streamPos_{s,c,sel,pub}Row_eq_commit`.
They are what turns "the family's verifying-key representations are honest" from an
assumption into a theorem for a claim assembled at an oracle table's challenges: the group
side is fixed by the key–index correspondence, and no batch stream position reads the `ft`
slot, which is the only place the challenges enter the commitment column.

The public row takes the Lagrange-basis size bound `hlagsz` directly rather than an
acceptance of the deployed verifier: the challenge-generic verifier's own size guard is
exactly that bound, so a consumer whose win event is `kimchiVerifyWith` has it in hand. -/

/-- **The σ rows of the challenge-generic claim**: under the key–index correspondence the
claim carries, at the stream position of the `i`-th σ row and chunk `c`, the unblinded chunk
commitment of the circuit's own `sigmaPermCol i` permutation polynomial. -/
theorem commitmentFn_streamPosAt_sRow_eq_commit {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) {n : ℕ} [NeZero n]
    {idx : Index C.ScalarField n} (hvk : cvk.Corresponds σ idx)
    (i : Fin sigmaRows) (c : Fin nc) :
    (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn
        ⟨(streamPos nc (sRow i) c : ℕ), (streamPos nc (sRow i) c).isLt⟩
      = commit σ (chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly (sigmaPermCol i)) (c : ℕ)) 0 :=
  ((commitmentFn_streamPosAt σ cvk cp pub beta gamma alpha zeta v u (sRow i) c).trans
    (batchC_sRow_of_corresponds σ hvk.1 _ _ _ i c)).trans
      (commitPolyChunk_as_commit σ _ (c : ℕ))

/-- **The coefficient rows of the challenge-generic claim**: the unblinded chunk commitment
of the circuit's own `cc`-th coefficient interpolant. -/
theorem commitmentFn_streamPosAt_cRow_eq_commit {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) {n : ℕ} [NeZero n]
    {idx : Index C.ScalarField n} (hvk : cvk.Corresponds σ idx)
    (cc : Fin coeffCols) (c : Fin nc) :
    (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn
        ⟨(streamPos nc (cRow cc) c : ℕ), (streamPos nc (cRow cc) c).isLt⟩
      = commit σ (chunkCoeffs (2 ^ σ.k) (idx.coeffPoly cc) (c : ℕ)) 0 :=
  ((commitmentFn_streamPosAt σ cvk cp pub beta gamma alpha zeta v u (cRow cc) c).trans
    (batchC_cRow_of_corresponds σ hvk.1 _ _ _ cc c)).trans
      (commitPolyChunk_as_commit σ _ (c : ℕ))

/-- **The selector rows of the challenge-generic claim**: the MASKED chunk commitment (fixed
unit blinder, `mask_custom`) of the circuit's own `selGate jj` selector interpolant. -/
theorem commitmentFn_streamPosAt_selRow_eq_commit {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) {n : ℕ} [NeZero n]
    {idx : Index C.ScalarField n} (hvk : cvk.Corresponds σ idx)
    (jj : Fin selCount) (c : Fin nc) :
    (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn
        ⟨(streamPos nc (selRow jj) c : ℕ), (streamPos nc (selRow jj) c).isLt⟩
      = commit σ (chunkCoeffs (2 ^ σ.k) (idx.selectorPoly (selGate jj)) (c : ℕ)) 1 :=
  ((commitmentFn_streamPosAt σ cvk cp pub beta gamma alpha zeta v u (selRow jj) c).trans
    (batchC_selRow_of_corresponds σ hvk.1 _ _ _ jj c)).trans
      (commitPolyMaskedChunk_as_commit σ _ (c : ℕ))

/-- **The public row of the challenge-generic claim**: the MASKED chunk commitment of the
NEGATED public interpolant. Unlike the other three families the public row is not a key
entry — it is recomputed by the verifier from the key's Lagrange basis — so this case
additionally needs the Lagrange-basis size bound (the challenge-generic verifier's own size
guard), the public-input arity, and the `.val`-scalar collapse. -/
theorem commitmentFn_streamPosAt_pubRow_eq_commit {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) {n : ℕ} [NeZero n]
    {idx : Index C.ScalarField n}
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a • P = a.val • P)
    (hvk : cvk.Corresponds σ idx) (hpub : pub.size = idx.publicCount)
    (hlagsz : pub.size ≤ cvk.lagrangeBasis.size) (c : Fin nc) :
    (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn
        ⟨(streamPos nc pubRow c : ℕ), (streamPos nc pubRow c).isLt⟩
      = commit σ
          (chunkCoeffs (2 ^ σ.k) (-(idx.pubPoly (pubView idx pub))) (c : ℕ)) 1 := by
  refine ((commitmentFn_streamPosAt σ cvk cp pub beta gamma alpha zeta v u pubRow c).trans
    ?_).trans (commitPolyMaskedChunk_as_commit σ _ (c : ℕ))
  exact (congrFun (batchC_pubRow (fun (col : Fin wCols) (c : Fin nc) => (cp.wComm[col])[c])
      (fun c => cp.zComm[c])
      (fun c => (publicCommitment C σ cvk pub)[c]) cvk.comms) c).trans
    (publicCommitment_corresponds C σ cvk pub idx
      (fun a P => (hsmul a P).symm) hvk.2.2.2.2.2.2 hlagsz hpub c)

/-! ## The chunked run-level terminal roots

Residue-free AGM soundness of the deployed Pasta verifiers, stated over the run's own data.
Each root pairs the Schwartz–Zippel cardinality bounds (`RunBounds`) with a guarded
implication (`RunGuardImp`): at the run's own Fiat–Shamir challenges — provided they lie
outside the exclusion sets and off the two boundary points `1`, `ω^(n − zkRows)` — the
assembled witness table `runWTab` satisfies the circuit. The exclusion sets are the canonical
Schwartz–Zippel sets `Protocol.soundBad{B,G,A,Z}` at the run's assembled witness columns
`runW` and accumulator `runZ` — the same sets the openings seam
`kimchiProof_sound_of_openings` pins for the run's per-chunk representations, so the proofs
feed the seam directly. Both the exclusion sets and the satisfying table are explicit
functions of the run, so the conclusion constrains *these* challenges and *this* table.

That a genuine run's challenges avoid the exclusion sets is a hypothesis of `RunGuardImp`, as
is the good-combination-challenge condition `hξ`/`hr`. Bounding the probability that the
Fiat–Shamir challenges land in the (`card`-bounded) exclusion sets is the forking/density
argument, which this development does not carry. -/

/-- The assembled witness-column polynomials of a reflected run: the algebraic prover's own
per-chunk representations `aRef` at the witness-row stream positions, assembled into
degree-`< n` column polynomials. These are the `W` the openings seam pins for the run. -/
noncomputable def runW {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → C.ScalarField) :
    Fin wCols → Polynomial C.ScalarField :=
  fun col => assembledRow σ.k nc
    fun c => aRef ⟨(streamPos nc (wRow col) c : ℕ), (streamPos nc (wRow col) c).isLt⟩

/-- The assembled permutation-accumulator polynomial of a reflected run — the `z` the
openings seam pins, from `aRef` at the accumulator-row stream position. -/
noncomputable def runZ {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → C.ScalarField) :
    Polynomial C.ScalarField :=
  assembledRow σ.k nc
    fun c => aRef ⟨(streamPos nc zRow c : ℕ), (streamPos nc zRow c).isLt⟩

/-- The assembled witness table of a reflected run: `runW` read as a table over the domain.
This is the satisfying assignment the run-level roots deliver. -/
noncomputable def runWTab {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {n : ℕ} (idx : Index C.ScalarField n)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → C.ScalarField) :
    Fin n → Fin wCols → C.ScalarField :=
  extractTable idx.omega (runW σ cvk cp pub aRef)

/-- The Schwartz–Zippel cardinality bounds on a reflected run's exclusion sets: the `β`/`γ`
sets have card `≤ 7·(n − zkRows)`, the `α` set `≤ n·(gateAlphaCount + permAlphaCount − 1)`,
and each `ζ` set (for a degree-`< 7n` quotient) `≤ degreeBound n`. -/
def RunBounds {C : Ipa.CommitmentCurve}
    (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → C.ScalarField) : Prop :=
  (Protocol.soundBadB idx (runW σ cvk cp pub aRef)).card ≤ 7 * (n - idx.zkRows)
    ∧ (∀ β, (Protocol.soundBadG idx (runW σ cvk cp pub aRef) β).card
        ≤ 7 * (n - idx.zkRows))
    ∧ (∀ β γ, (Protocol.soundBadA idx (pubView idx pub) (runW σ cvk cp pub aRef)
          (runZ σ cvk cp pub aRef) β γ).card
        ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
    ∧ (∀ β γ α (t : Polynomial C.ScalarField), t.natDegree < 7 * n →
        (Protocol.soundBadZ idx (pubView idx pub) (runW σ cvk cp pub aRef)
          (runZ σ cvk cp pub aRef) β γ α t).card ≤ Index.degreeBound n)

/-- The guarded satisfaction of a reflected run: when the run's own Fiat–Shamir challenges
lie outside the canonical exclusion sets `Protocol.soundBad*` at `runW`/`runZ` and off the
boundary points (`ζ ≠ 1`, `ζ ≠ ω^(n−zkRows)`), the assembled table `runWTab` satisfies the
circuit. -/
def RunGuardImp {C : Ipa.CommitmentCurve}
    (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → C.ScalarField)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField) : Prop :=
  (runOracles C σ cvk cp pub).beta ∉ Protocol.soundBadB idx (runW σ cvk cp pub aRef) →
  (runOracles C σ cvk cp pub).gamma
      ∉ Protocol.soundBadG idx (runW σ cvk cp pub aRef)
          (runOracles C σ cvk cp pub).beta →
  (runOracles C σ cvk cp pub).alpha
      ∉ Protocol.soundBadA idx (pubView idx pub) (runW σ cvk cp pub aRef)
          (runZ σ cvk cp pub aRef) (runOracles C σ cvk cp pub).beta
          (runOracles C σ cvk cp pub).gamma →
  (runOracles C σ cvk cp pub).zeta
      ∉ Protocol.soundBadZ idx (pubView idx pub) (runW σ cvk cp pub aRef)
          (runZ σ cvk cp pub aRef) (runOracles C σ cvk cp pub).beta
          (runOracles C σ cvk cp pub).gamma (runOracles C σ cvk cp pub).alpha
          (ftChunkAssembly σ.k cp.tComm.size aT) →
  (runOracles C σ cvk cp pub).zeta ≠ 1 →
  (runOracles C σ cvk cp pub).zeta ≠ idx.omega ^ (n - idx.zkRows) →
  Satisfies idx (pubView idx pub) (runWTab σ cvk cp pub idx aRef)

/-- **Guarded satisfaction at handed-in challenges**: `RunGuardImp` with the four fq-side
squeezes as parameters. The assembled columns `runW`/`runZ`, the accumulator and the
extracted table `runWTab` do NOT mention the challenges — they are read off the
representations at the layout positions `streamPos` — so the exclusion sets and the
satisfying table are literally the same objects in both predicates; only the six guard
hypotheses move from the sponge's outputs to the parameters. -/
def RunGuardImpAt {C : Ipa.CommitmentCurve}
    (σ : SRS C.Point) {nc : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (beta gamma alpha zeta : C.ScalarField)
    (aRef : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ σ.k) → C.ScalarField)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField) : Prop :=
  beta ∉ Protocol.soundBadB idx (runW σ cvk cp pub aRef) →
  gamma ∉ Protocol.soundBadG idx (runW σ cvk cp pub aRef) beta →
  alpha ∉ Protocol.soundBadA idx (pubView idx pub) (runW σ cvk cp pub aRef)
      (runZ σ cvk cp pub aRef) beta gamma →
  zeta ∉ Protocol.soundBadZ idx (pubView idx pub) (runW σ cvk cp pub aRef)
      (runZ σ cvk cp pub aRef) beta gamma alpha
      (ftChunkAssembly σ.k cp.tComm.size aT) →
  zeta ≠ 1 →
  zeta ≠ idx.omega ^ (n - idx.zkRows) →
  Satisfies idx (pubView idx pub) (runWTab σ cvk cp pub idx aRef)

/-- **Run soundness at key-honest representations, at handed-in challenges**: the
binding-free, transcript-free run-level root with the six pre-IPA challenges supplied as
parameters rather than squeezed. This is the form the knowledge-soundness game consumes:
its win event is the challenge-generic verifier at the oracle table's own challenges, so its
claim is `runInputAt` and no root stated at `runInput` applies to it.

Mathematically this costs nothing. Every step the sponge-driven proof invokes — the
binding-free openings seam `kimchiProof_sound_of_openings_of_vkrep`, the `ft` chunk identity
`ft_identity_of_chunks_of_eq`, the layout bridge and the two scalar reconciliations — already
takes its challenges as arguments; the sponge appears only where the outermost wrapper
supplies them. `run_sound_algebraic_of_vkrep` is this theorem at `runOracles`' outputs, and
recovers its previous statement character for character. -/
theorem run_sound_algebraic_at_of_vkrep {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (beta gamma alpha zeta v u : C.ScalarField)
    (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n) (hn : cvk.n = n)
    (hvk : cvk.Corresponds σ idx)
    (htpos : 0 < cp.tComm.size)
    (aRef : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ σ.k) → C.ScalarField)
    (ρRef : Fin (nc + 1 + tailRowCount * nc) → C.ScalarField)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn i)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField)
    (hpins : ∀ (i : Fin (nc + 1 + tailRowCount * nc)) (j : Fin evalPts),
      (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalFn i j
        = innerProduct (aRef i)
            (evalVector (2 ^ σ.k)
              ((runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn j)))
    (hsigRep : ∀ (i : Fin sigmaRows) (c : Fin nc),
      aRef ⟨(streamPos nc (sRow i) c : ℕ), (streamPos nc (sRow i) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly (sigmaPermCol i)) (c : ℕ))
    (hcoeffRep : ∀ (cc : Fin coeffCols) (c : Fin nc),
      aRef ⟨(streamPos nc (cRow cc) c : ℕ), (streamPos nc (cRow cc) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.coeffPoly cc) (c : ℕ))
    (hselRep : ∀ (jj : Fin selCount) (c : Fin nc),
      aRef ⟨(streamPos nc (selRow jj) c : ℕ), (streamPos nc (selRow jj) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.selectorPoly (selGate jj)) (c : ℕ))
    (hpubRep : ∀ c : Fin nc,
      aRef ⟨(streamPos nc pubRow c : ℕ), (streamPos nc pubRow c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (-(idx.pubPoly (pubView idx pub))) (c : ℕ))
    (hftRep : ∀ i : Fin (nc + 1 + tailRowCount * nc), (i : ℕ) = nc →
      aRef i
        = runPScalarAt C σ cvk cp beta gamma alpha zeta
            • ∑ c : Fin nc, (zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly 6) (c : ℕ)
          - (zeta ^ n - 1)
            • ∑ j : Fin cp.tComm.size, (zeta ^ 2 ^ σ.k) ^ (j : ℕ) • aT j) :
    RunBounds σ cvk cp pub idx aRef
      ∧ RunGuardImpAt σ cvk cp pub idx beta gamma alpha zeta aRef aT := by
  obtain ⟨_hvkc, homega, hzk, hshift, hendo, hmds, _hlag⟩ := hvk
  have hlt : ∀ (i : Fin batchRows) (c : Fin nc),
      (streamPos nc i c : ℕ) < nc + 1 + tailRowCount * nc :=
    fun i c => (streamPos nc i c).isLt
  -- (2) the reference openings at the stream positions bind the abstract batch
  have hbound₀ : ∀ (i : Fin batchRows) (c : Fin nc),
      commit σ (aRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
          (ρRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
        = batchC (fun col c => (cp.wComm[col])[c]) (fun c => cp.zComm[c])
            (fun c => (publicCommitment C σ cvk pub)[c])
            cvk.comms i c := fun i c =>
    (hrep ⟨(streamPos nc i c : ℕ), hlt i c⟩).trans
      (commitmentFn_streamPosAt σ cvk cp pub beta gamma alpha zeta v u i c)
  -- (4) the binding-free openings seam — its exclusion sets are `runW`/`runZ`'s
  obtain ⟨hbounds, himp⟩ :=
    kimchiProof_sound_of_openings_of_vkrep σ idx hnc hk cvk.comms (pubView idx pub)
      (fun col c => (cp.wComm[col])[c]) (fun c => cp.zComm[c])
      (fun c => (publicCommitment C σ cvk pub)[c])
      (fun i c => aRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
  refine ⟨hbounds, ?_⟩
  intro hβ hγ hα hζ hζ1 hζb
  -- (5) the eval pins are the hypothesis `hpins` — the transcript seam
  -- (6) the ft row, named at its own flat position, and the Maller identity
  have hsz : (nc : ℕ) < nc + 1 + tailRowCount * nc := by omega
  have heval_ft : innerProduct (aRef ⟨nc, hsz⟩) (evalVector (2 ^ σ.k) zeta)
      = runFtEval0At C σ cvk cp pub beta gamma alpha zeta := by
    have hpin := hpins ⟨nc, hsz⟩ (0 : Fin evalPts)
    have hpt0 : (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn
        (0 : Fin evalPts) = zeta := rfl
    rw [hpt0] at hpin
    rw [← hpin]
    exact evalFn_ftPosAt σ cvk cp pub beta gamma alpha zeta v u hsz
  have hσ₆ : (idx.sigmaPoly 6).natDegree < nc * 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  obtain ⟨htdeg, hteq0⟩ := ft_identity_of_chunks_of_eq σ (idx.sigmaPoly 6) hσ₆
    htpos cp.tComm_le aT
    (runPScalarAt C σ cvk cp beta gamma alpha zeta) zeta
    (runFtEval0At C σ cvk cp pub beta gamma alpha zeta) n hk (aRef ⟨nc, hsz⟩) _ rfl
    heval_ft (hftRep ⟨nc, hsz⟩ rfl)
  -- (7) reconcile the derived identity into the consumer's shape
  have hSread := runStreamAt_read_eq σ cvk cp pub beta gamma alpha zeta
  have hce := claimedEvals_stream_eq C (powPow2 zeta σ.k)
    (powPow2 (zeta * cvk.omega) σ.k) _ hSread
  have hcpe := claimedPub_stream_eq C (powPow2 zeta σ.k) _ hSread
  have hζM : powPow2 zeta σ.k = zeta ^ 2 ^ σ.k := powPow2_eq zeta σ.k
  have hζwM : powPow2 (zeta * cvk.omega) σ.k = (idx.omega * zeta) ^ 2 ^ σ.k := by
    rw [powPow2_eq, homega, mul_comm]
  unfold runPScalarAt runFtEval0At at hteq0
  rw [← hce, ← hcpe, hζM, hζwM, hn, hzk, homega, hendo, hmds, hshift] at hteq0
  -- (8) the per-row pins, at the consumer's two eval points
  have hpt : (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn
      = ![zeta, idx.omega * zeta] := by
    funext j
    fin_cases j
    · rfl
    · show zeta * cvk.omega = _
      rw [homega]
      exact mul_comm _ _
  rw [hpt] at hpins
  -- (9) feed the consumer
  exact himp beta gamma alpha (ftChunkAssembly σ.k cp.tComm.size aT) zeta
    (fun (i : Fin batchRows) (ch : Fin nc) (j : Fin evalPts) =>
      ((runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evals[
          (streamPos nc i ch : ℕ)]'((streamPos nc i ch).isLt))[(j : ℕ)]'j.isLt)
    (fun i c => aRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
    (fun i c => ρRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
    hβ hγ hα hζ hζ1 hζb htdeg
    (fun i c => ⟨hbound₀ i c,
      fun j => hpins ⟨(streamPos nc i c : ℕ), hlt i c⟩ j⟩)
    (fun _ _ => rfl) (fun _ => rfl)
    hsigRep hcoeffRep hselRep hpubRep
    hteq0

/-- **Run soundness at key-honest representations** (transcript-free AND binding-free): the
pins-as-hypothesis root with DL-binding `hbind` deleted and replaced by the two things
binding was spent on downstream of the transcript — the four verifying-key row pinnings
(`hsigRep`/`hcoeffRep`/`hselRep`/`hpubRep`, transported to the flat stream along
`streamPos`) and the `ft` row's coefficient equality `hftRep`.

The seam is inherited from the two split cores. Step (4) calls the binding-free
`kimchiProof_sound_of_openings_of_vkrep`, whose two cross-point agreement hypotheses are
`rfl` here because this consumer supplies the SAME representation function on both sides,
and whose four verifying-key pinnings are exactly the new hypotheses. Step (6) calls
`ft_identity_of_chunks_of_eq`, whose coefficient equality is `hftRep` at the `ft` row's own
flat position `nc` (`evalFn_ftPos`). Steps (1)–(3), (5) and (7)–(9) mention neither binding
nor the group-side commitments and are unchanged.

Because the group-side pins are now hypotheses, four further hypotheses of the
pins-as-hypothesis root become unused and are dropped from the statement: `hbind`,
`hsmul` and `hacc` (which served only the public row's Lagrange chunk pin and the `ft`
commitment reconciliation), `hpub`, and the quotient chunk blinders `ρT`/`hTC` (the `ft`
identity no longer looks at the quotient commitments). `run_sound_algebraic_of_pins` is
recovered from this theorem by discharging all five new hypotheses from `hbind`.

This is the form the knowledge-soundness game consumes: over its sampled key basis binding
provably FAILS, and the verifying-key pinnings are supplied instead by the family's own
key-honesty predicate — with the dishonest complement priced as a discrete-log relation. -/
theorem run_sound_algebraic_of_vkrep {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n) (hn : cvk.n = n)
    (hvk : cvk.Corresponds σ idx)
    (htpos : 0 < cp.tComm.size)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → C.ScalarField)
    (ρRef : Fin (runInput C σ cvk cp pub).commitments.size → C.ScalarField)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput C σ cvk cp pub).commitmentFn i)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField)
    (hpins : ∀ (i : Fin (runInput C σ cvk cp pub).commitments.size) (j : Fin evalPts),
      (runInput C σ cvk cp pub).evalFn i j
        = innerProduct (aRef i)
            (evalVector (2 ^ σ.k) ((runInput C σ cvk cp pub).pointFn j)))
    (hsigRep : ∀ (i : Fin sigmaRows) (c : Fin nc),
      aRef ⟨(streamPos nc (sRow i) c : ℕ), (streamPos nc (sRow i) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly (sigmaPermCol i)) (c : ℕ))
    (hcoeffRep : ∀ (cc : Fin coeffCols) (c : Fin nc),
      aRef ⟨(streamPos nc (cRow cc) c : ℕ), (streamPos nc (cRow cc) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.coeffPoly cc) (c : ℕ))
    (hselRep : ∀ (jj : Fin selCount) (c : Fin nc),
      aRef ⟨(streamPos nc (selRow jj) c : ℕ), (streamPos nc (selRow jj) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.selectorPoly (selGate jj)) (c : ℕ))
    (hpubRep : ∀ c : Fin nc,
      aRef ⟨(streamPos nc pubRow c : ℕ), (streamPos nc pubRow c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (-(idx.pubPoly (pubView idx pub))) (c : ℕ))
    (hftRep : ∀ i : Fin (runInput C σ cvk cp pub).commitments.size, (i : ℕ) = nc →
      aRef i
        = runPScalar C σ cvk cp pub
            • ∑ c : Fin nc, ((runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly 6) (c : ℕ)
          - ((runOracles C σ cvk cp pub).zeta ^ n - 1)
            • ∑ j : Fin cp.tComm.size,
                ((runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (j : ℕ) • aT j) :
    RunBounds σ cvk cp pub idx aRef ∧ RunGuardImp σ cvk cp pub idx aRef aT :=
  run_sound_algebraic_at_of_vkrep σ cvk cp pub idx
    (runOracles C σ cvk cp pub).beta (runOracles C σ cvk cp pub).gamma
    (runOracles C σ cvk cp pub).alpha (runOracles C σ cvk cp pub).zeta
    (runVU C σ cvk cp pub).1 (runVU C σ cvk cp pub).2
    hnc hk hn hvk htpos aRef ρRef hrep aT hpins hsigRep hcoeffRep hselRep hpubRep hftRep

/-- **Run soundness from the eval pins** (transcript-free): the run-level root with the
Fiat–Shamir transcript tree and the two good-combination guards `hξ`/`hr` replaced by the
single hypothesis `hpins` — verbatim `eval_pins_of_opening`'s conclusion at the run's own
data. From a genuine acceptance `kimchiVerify σ cvk cp pub = true` at production chunking
`nc · 2^σ.k = n`, the AGM path still yields `RunBounds ∧ RunGuardImp`.

The seam. In `run_sound_algebraic_ft` the tree is consumed at exactly two sites — the flat
eval pins of step (5) and `ft_opening_of_reflected` at step (6) — and both run the same
two-step composite `ipa_soundnessA` then `eval_pins_of_opening` at the identical arguments.
Making the pins a hypothesis isolates that composite in the corollary
`run_sound_algebraic_ft`, which is where the `kimchi_fiat_shamir_*` axioms are henceforth
the only consumers. The knowledge-soundness game produces the same pins from its forking
extractor's own accepted opening, so it calls this theorem directly and stays axiom-clean.

DL-binding `hbind` is deliberately NOT removed: it is used at two further sites — the
openings seam of step (4) (`kimchiProof_sound_of_openings`) and the ft-chunk identity of
step (6) (`ft_identity_of_chunks`) — that have nothing to do with the transcript.

Recovered, statement unchanged, from the binding-free `run_sound_algebraic_of_vkrep`:
`hbind` is spent here and only here, discharging the four verifying-key row pinnings
(through `dlRelation_of_chunk_rep{,_masked}_ne` at the corresponding key's batch rows) and
the `ft` row's coefficient equality (through `ft_dlRelation_of_chunks_ne`). Each is a
difference relation between two representations of the same group element, which binding
kills. -/
theorem run_sound_algebraic_of_pins {C : Ipa.CommitmentCurve}
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
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size
      → Fin (2 ^ σ.k) → C.ScalarField)
    (ρRef : Fin (runInput C σ cvk cp pub).commitments.size → C.ScalarField)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInput C σ cvk cp pub).commitmentFn i)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField)
    (ρT : Fin cp.tComm.size → C.ScalarField)
    (hTC : ∀ j : Fin cp.tComm.size, commit σ (aT j) (ρT j) = cp.tComm[j])
    (hpins : ∀ (i : Fin (runInput C σ cvk cp pub).commitments.size) (j : Fin evalPts),
      (runInput C σ cvk cp pub).evalFn i j
        = innerProduct (aRef i)
            (evalVector (2 ^ σ.k) ((runInput C σ cvk cp pub).pointFn j))) :
    RunBounds σ cvk cp pub idx aRef ∧ RunGuardImp σ cvk cp pub idx aRef aT := by
  obtain ⟨hvkc, _, _, _, _, _, hlag⟩ := id hvk
  -- (1) the body reflection: the Lagrange-basis size feeds the public row's chunk pin
  obtain ⟨hlagsz, _, _⟩ := kimchiVerify_reflects C σ cvk cp pub hacc
  have hlt : ∀ (i : Fin batchRows) (c : Fin nc),
      (streamPos nc i c : ℕ) < (runInput C σ cvk cp pub).commitments.size :=
    fun i c => (streamPos nc i c).isLt
  -- (2) the reference openings at the stream positions bind the abstract batch
  have hbound₀ : ∀ (i : Fin batchRows) (c : Fin nc),
      commit σ (aRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
          (ρRef ⟨(streamPos nc i c : ℕ), hlt i c⟩)
        = batchC (fun col c => (cp.wComm[col])[c]) (fun c => cp.zComm[c])
            (fun c => (publicCommitment C σ cvk pub)[c])
            cvk.comms i c := fun i c =>
    (hrep ⟨(streamPos nc i c : ℕ), hlt i c⟩).trans
      (commitmentFn_streamPos σ cvk cp pub i c)
  -- (3) the public row pinned through the Lagrange chunk pin
  have hpubC : ∀ c : Fin nc,
      (publicCommitment C σ cvk pub)[c]
        = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ) :=
    fun c => publicCommitment_corresponds C σ cvk pub idx
      (fun a P => (hsmul a P).symm) hlag hlagsz hpub c
  -- (4) binding pins each verifying-key row's representation to the honest chunk window
  have hsigRep : ∀ (i : Fin sigmaRows) (c : Fin nc),
      aRef ⟨(streamPos nc (sRow i) c : ℕ), (streamPos nc (sRow i) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly (sigmaPermCol i)) (c : ℕ) := fun i c =>
    rep_eq_of_chunkCommit σ hbind
      ((hbound₀ (sRow i) c).trans (batchC_sRow_of_corresponds σ hvkc _ _ _ i c))
  have hcoeffRep : ∀ (cc : Fin coeffCols) (c : Fin nc),
      aRef ⟨(streamPos nc (cRow cc) c : ℕ), (streamPos nc (cRow cc) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.coeffPoly cc) (c : ℕ) := fun cc c =>
    rep_eq_of_chunkCommit σ hbind
      ((hbound₀ (cRow cc) c).trans (batchC_cRow_of_corresponds σ hvkc _ _ _ cc c))
  have hselRep : ∀ (jj : Fin selCount) (c : Fin nc),
      aRef ⟨(streamPos nc (selRow jj) c : ℕ), (streamPos nc (selRow jj) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.selectorPoly (selGate jj)) (c : ℕ) := fun jj c =>
    rep_eq_of_maskedChunkCommit σ hbind
      ((hbound₀ (selRow jj) c).trans (batchC_selRow_of_corresponds σ hvkc _ _ _ jj c))
  have hpubRep : ∀ c : Fin nc,
      aRef ⟨(streamPos nc pubRow c : ℕ), (streamPos nc pubRow c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (-(idx.pubPoly (pubView idx pub))) (c : ℕ) := fun c =>
    rep_eq_of_maskedChunkCommit σ hbind
      ((hbound₀ pubRow c).trans
        ((congrFun (batchC_pubRow (fun (col : Fin wCols) (c : Fin nc) => (cp.wComm[col])[c])
            (fun c => cp.zComm[c])
            (fun c => (publicCommitment C σ cvk pub)[c]) cvk.comms) c).trans (hpubC c)))
  -- (5) binding pins the ft row's representation to the intended combination
  have hsz : (nc : ℕ) < (runInput C σ cvk cp pub).commitments.size := by
    show (nc : ℕ) < nc + 1 + tailRowCount * nc
    omega
  have hCσ6 : ∀ c : Fin nc,
      (cvk.sigmaComm[6])[c] = commitPolyChunk σ (idx.sigmaPoly 6) (c : ℕ) :=
    fun c => congrFun (congrArg (fun cm => cm.sigma 6) hvkc) c
  have hcommit : commit σ (aRef ⟨nc, hsz⟩) (ρRef ⟨nc, hsz⟩)
      = runPScalar C σ cvk cp pub
          • ∑ c : Fin nc,
              ((runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • (cvk.sigmaComm[6])[c]
        - ((runOracles C σ cvk cp pub).zeta ^ n - 1)
            • ∑ j : Fin cp.tComm.size,
                ((runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (j : ℕ)
                  • cp.tComm[j] :=
    ((hrep ⟨nc, hsz⟩).trans (commitmentFn_ftPos σ cvk cp pub hsz)).trans
      (runFtComm_eq C hsmul hn)
  have hft : aRef ⟨nc, hsz⟩
      = runPScalar C σ cvk cp pub
          • ∑ c : Fin nc, ((runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (c : ℕ)
              • chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly 6) (c : ℕ)
        - ((runOracles C σ cvk cp pub).zeta ^ n - 1)
          • ∑ j : Fin cp.tComm.size,
              ((runOracles C σ cvk cp pub).zeta ^ 2 ^ σ.k) ^ (j : ℕ) • aT j := by
    obtain ⟨hrel, _⟩ := ft_dlRelation_of_chunks_ne σ (idx.sigmaPoly 6)
      (fun c => (cvk.sigmaComm[6])[c]) hCσ6
      (fun j => cp.tComm[j]) aT ρT hTC
      (runPScalar C σ cvk cp pub) (runOracles C σ cvk cp pub).zeta n
      (aRef ⟨nc, hsz⟩) (ρRef ⟨nc, hsz⟩) _ _ rfl rfl hcommit
    exact sub_eq_zero.mp (hbind _ _ hrel).1
  -- (6) feed the key-honest root
  exact run_sound_algebraic_of_vkrep σ cvk cp pub idx hnc hk hn hvk htpos
    aRef ρRef hrep aT hpins hsigRep hcoeffRep hselRep hpubRep
    (fun i hi => by
      have hie : i = ⟨nc, hsz⟩ := Fin.eq_of_val_eq hi
      rw [hie]
      exact hft)

/-- **The run-level residue-free root, curve-generically**: from a genuine acceptance
`kimchiVerify σ cvk cp pub = true` of the checked records at production chunking
`nc · 2^σ.k = n`, the AGM path yields `RunBounds ∧ RunGuardImp` — the Schwartz–Zippel
cardinality bounds together with the guarded satisfaction of the assembled table
`runWTab σ cvk cp pub idx aRef`, the algebraic prover's own per-chunk representations read as
a witness table. The exclusion sets and the table are the canonical named terms
`Protocol.soundBad*` at `runW`/`runZ` (`RunBounds`/`RunGuardImp`), so the conclusion
constrains the run's own Fiat–Shamir challenges; that those challenges avoid the exclusion
sets, and the good-combination conditions `hξ`/`hr`, are hypotheses — the forking/density
argument, not carried here. The two
curve-specific facts enter as
hypotheses: `hsmul`, the `.val`-scalar collapse of the point-count-backed `Module`
instance, and `hFS`, the Fiat–Shamir transcript tree at the run's own warm data —
taken ONCE and spent HERE, in the two-step composite `ipa_soundnessA` then
`eval_pins_of_opening`, whose output (the flat eval pins) is the whole hypothesis
surface `run_sound_algebraic_of_pins` needs: this theorem is now exactly that
manufacture, and the arithmetic all lives transcript-free in
`run_sound_algebraic_of_pins`. The public roots
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
    RunBounds σ cvk cp pub idx aRef ∧ RunGuardImp σ cvk cp pub idx aRef aT := by
  obtain ⟨_hlagsz, _hpubn, haccept⟩ := kimchiVerify_reflects C σ cvk cp pub hacc
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _ hFS haccept
  exact run_sound_algebraic_of_pins σ cvk cp pub idx hsmul hnc hk hn hvk hpub htpos
    hbind hacc aRef ρRef hrep aT ρT hTC
    (eval_pins_of_opening σ hbind (runInput C σ cvk cp pub).commitmentFn
      (runInput C σ cvk cp pub).pointFn aRef ρRef hrep (runInput C σ cvk cp pub).evalFn
      (runInput C σ cvk cp pub).polyscale (runInput C σ cvk cp pub).evalscale hξ hr
      a ρ hopen)

/-- **The run-level residue-free root (Vesta)**: from a genuine acceptance
`kimchiVerify σ cvk cp pub = true` of the checked records at production chunking
`nc · 2^σ.k = n`, the AGM path delivers the guarded
`RunBounds ∧ RunGuardImp` — the Schwartz–Zippel cardinality bounds together with the guarded
satisfaction of the assembled witness table `runWTab σ cvk cp pub idx aRef`, the algebraic
prover's own per-chunk representations. The exclusion sets and the table are the canonical
named terms `Protocol.soundBad*` at `runW`/`runZ` (`RunBounds`/`RunGuardImp`), so the
conclusion constrains the run's own Fiat–Shamir challenges; that those challenges avoid the
exclusion sets, and the conditions `hξ`/`hr`, are hypotheses (the forking/density argument).
A deployed run reaches this root through the
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
    RunBounds σ cvk cp pub idx aRef ∧ RunGuardImp σ cvk cp pub idx aRef aT :=
  run_sound_algebraic_ft σ cvk cp pub idx Pasta.vesta_smul_val hnc hk hn hvk hpub
    htpos hbind hacc (kimchi_fiat_shamir_vesta σ cvk cp pub) aRef ρRef hrep aT ρT
    hTC hξ hr

/-- **The run-level residue-free root (Pallas).** The Pallas-side twin of
`kimchiVesta_run_sound_algebraic_ft`, over `Fq`/`IpaPallas`. Same shape: the conclusion is
`RunBounds ∧ RunGuardImp` over the canonical exclusion sets `Protocol.soundBad*` at
`runW`/`runZ` and the assembled table `runWTab …`, with the run's avoidance of the exclusion
sets and the conditions `hξ`/`hr` left as hypotheses (the forking/density argument). The same
trust surface: the sole axiom consumed is its Fiat–Shamir assumption
`kimchi_fiat_shamir_pallas` (once, through `run_sound_algebraic_ft`), and the
computational hypotheses — the AGM representations `aRef`/`ρRef`/`aT`/`ρT`, the
good-challenge guards `hξ`/`hr`, and DL-binding `hbind` (see the `hbind` scope note in the
`Bulletproof/Soundness.lean` module docstring) — stay in the statement. -/
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
    RunBounds σ cvk cp pub idx aRef ∧ RunGuardImp σ cvk cp pub idx aRef aT :=
  run_sound_algebraic_ft σ cvk cp pub idx Pasta.pallas_smul_val hnc hk hn hvk hpub
    htpos hbind hacc (kimchi_fiat_shamir_pallas σ cvk cp pub) aRef ρRef hrep aT ρT
    hTC hξ hr

/-! ## What arm (4) of the knowledge-soundness game consumes from this layer

The game calls the challenge-generic root `run_sound_algebraic_at_of_vkrep` once per point of
its algebraic summand and must then convert the conclusion into a statement about the run's
own challenges. Three packagings keep that conversion out of the game file, in the same
spirit as `badChallenge_of_not_pins` (`Capstone/Algebraic.lean`):

* `runBounds_of_chunking` — the Schwartz–Zippel cardinality bounds hold unconditionally,
  from the production chunking equation alone;
* `runBounds_zeta_at_assembly` — the fourth bound, instantiated at the run's own assembled
  quotient polynomial, with the degree side condition discharged;
* `guard_fails_of_not_satisfies` — the contrapositive of `RunGuardImpAt`;
* `run_sound_algebraic_at_of_opening` — the root with the evaluation-pin hypothesis replaced
  by an accepted opening of the batched claim, the two fr-side exclusion memberships
  appearing as the alternative branches.

The composite `run_badChallenge_of_not_satisfies_at` chains all four: from an accepted
opening whose coefficient vector is the polyscale combination of the declared rows, and a
table that does NOT satisfy the circuit, one of the seven counted bad events fires. -/

/-- **The Schwartz–Zippel cardinality bounds of a reflected run are unconditional.** They are
the first component of the binding-free openings seam, whose inputs are the production
chunking equation `nc · 2^σ.k = n`, `0 < nc`, and the representation function alone — no
opening, no transcript, no pins. Stating this separately is what lets the knowledge-soundness
game price its exclusion sets on every branch, not only on the branch where the extracted
coefficients match.

Project-local: `run_sound_algebraic_at_of_vkrep` already delivers `RunBounds` in its
conjunction, but only under its full hypothesis stack; the game needs the bounds where that
stack is unavailable. -/
theorem runBounds_of_chunking {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n)
    (aRef : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ σ.k) → C.ScalarField) :
    RunBounds σ cvk cp pub idx aRef :=
  (kimchiProof_sound_of_openings_of_vkrep σ idx hnc hk cvk.comms (pubView idx pub)
    (fun col c => (cp.wComm[col])[c]) (fun c => cp.zComm[c])
    (fun c => (publicCommitment C σ cvk pub)[c])
    (fun i c => aRef ⟨(streamPos nc i c : ℕ), (streamPos nc i c).isLt⟩)).1

/-- **The `ζ` cardinality bound at the run's own assembled quotient.** `RunBounds`' fourth
clause is stated for an ARBITRARY polynomial of degree `< 7·n`; the game charges its `ζ` to
the exclusion set at the run's assembled quotient `ftChunkAssembly σ.k cp.tComm.size aT`, so
the degree side condition has to be discharged there. It is: `ftChunkAssembly_natDegree_lt`
bounds the assembly's degree by `cp.tComm.size · 2^σ.k`, the wire invariant `cp.tComm_le`
bounds the chunk count by `7·nc`, and the production chunking equation turns that into
`7·n`. The bound therefore holds unconditionally at the assembly.

Project-local: it keeps the degree bookkeeping out of the game file, where the bound is
needed once per point of the algebraic summand. -/
theorem runBounds_zeta_at_assembly {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (aRef : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ σ.k) → C.ScalarField)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField)
    (hk : nc * 2 ^ σ.k = n) (htpos : 0 < cp.tComm.size)
    (hbounds : RunBounds σ cvk cp pub idx aRef) (beta gamma alpha : C.ScalarField) :
    (Protocol.soundBadZ idx (pubView idx pub) (runW σ cvk cp pub aRef)
        (runZ σ cvk cp pub aRef) beta gamma alpha
        (ftChunkAssembly σ.k cp.tComm.size aT)).card ≤ Index.degreeBound n := by
  refine hbounds.2.2.2 beta gamma alpha _ ?_
  refine lt_of_lt_of_le (ftChunkAssembly_natDegree_lt σ.k htpos aT) ?_
  calc cp.tComm.size * 2 ^ σ.k
      ≤ 7 * nc * 2 ^ σ.k := Nat.mul_le_mul cp.tComm_le (le_refl _)
    _ = 7 * n := by rw [mul_assoc, hk]

/-- **The six exclusion sets this layer names cost what the run's Schwartz–Zippel budget
allots them.** The four fq-side sets come from `runBounds_of_chunking` (with the `ζ` one at
the run's own assembled quotient, via `runBounds_zeta_at_assembly`), the two fr-side sets
from `card_badXiOf_le` / `card_badROf_le` at the batch's `nc + 1 + tailRowCount·nc` rows.

The right-hand side is `Verifier/KnowledgeSoundness.szBudget nc n idx.zkRows` MINUS the `2`
that budget allots the `ζ` boundary set `zetaBoundaryBad` — the one exclusion set that lives
downstream of this file. So the game closes its accounting by adding
`card_zetaBoundaryBad_le` to this bound; the total is the budget term for term, with no
slack and no rounding.

Project-local: the budget is the endpoint's fourth summand, and this is where the sets it
prices are actually defined. -/
theorem runBadCard_sum_le {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (aRef : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ σ.k) → C.ScalarField)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField)
    (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n) (htpos : 0 < cp.tComm.size)
    (beta gamma alpha xi : C.ScalarField)
    (x : Fin evalPts → C.ScalarField)
    (E : Fin (nc + 1 + tailRowCount * nc) → Fin evalPts → C.ScalarField) :
    (Protocol.soundBadB idx (runW σ cvk cp pub aRef)).card
        + (Protocol.soundBadG idx (runW σ cvk cp pub aRef) beta).card
        + (Protocol.soundBadA idx (pubView idx pub) (runW σ cvk cp pub aRef)
            (runZ σ cvk cp pub aRef) beta gamma).card
        + (Protocol.soundBadZ idx (pubView idx pub) (runW σ cvk cp pub aRef)
            (runZ σ cvk cp pub aRef) beta gamma alpha
            (ftChunkAssembly σ.k cp.tComm.size aT)).card
        + (badXiOf σ aRef x E).card
        + (badROf σ aRef x E xi).card
      ≤ 2 * (7 * (n - idx.zkRows))
        + n * (Index.gateAlphaCount + Index.permAlphaCount - 1)
        + Index.degreeBound n
        + (2 * (nc + 1 + tailRowCount * nc - 1) + 1) := by
  have hb := runBounds_of_chunking σ cvk cp pub idx hnc hk aRef
  have h1 := hb.1
  have h2 := hb.2.1 beta
  have h3 := hb.2.2.1 beta gamma
  have h4 := runBounds_zeta_at_assembly σ cvk cp pub idx aRef aT hk htpos hb beta gamma alpha
  have h5 := card_badXiOf_le σ aRef x E
  have h6 := card_badROf_le σ aRef x E xi
  omega

/-- **A failure of satisfaction names a failing guard.** The contrapositive of
`RunGuardImpAt`: if the assembled table does not satisfy the circuit while guarded
satisfaction at handed-in challenges holds, one of the six guard conditions must fail — the
handed-in `β`, `γ`, `α` or `ζ` lies in its exclusion set, or `ζ` sits on one of the two
boundary points.

Project-local: classical and short, but it belongs beside `RunGuardImpAt`, and it keeps the
`by_contra` out of the game file — the same reasoning that put `badChallenge_of_not_pins`
beside `eval_pins_of_opening_of_eq`. -/
theorem guard_fails_of_not_satisfies {C : Ipa.CommitmentCurve} (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (beta gamma alpha zeta : C.ScalarField)
    (aRef : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ σ.k) → C.ScalarField)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField)
    (himp : RunGuardImpAt σ cvk cp pub idx beta gamma alpha zeta aRef aT)
    (hns : ¬ Satisfies idx (pubView idx pub) (runWTab σ cvk cp pub idx aRef)) :
    beta ∈ Protocol.soundBadB idx (runW σ cvk cp pub aRef)
      ∨ gamma ∈ Protocol.soundBadG idx (runW σ cvk cp pub aRef) beta
      ∨ alpha ∈ Protocol.soundBadA idx (pubView idx pub) (runW σ cvk cp pub aRef)
          (runZ σ cvk cp pub aRef) beta gamma
      ∨ zeta ∈ Protocol.soundBadZ idx (pubView idx pub) (runW σ cvk cp pub aRef)
          (runZ σ cvk cp pub aRef) beta gamma alpha
          (ftChunkAssembly σ.k cp.tComm.size aT)
      ∨ zeta = 1
      ∨ zeta = idx.omega ^ (n - idx.zkRows) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hβ, hγ, hα, hζ, hζ1, hζb⟩ := hcon
  exact hns (himp hβ hγ hα hζ hζ1 hζb)

/-- **Run soundness from an accepted opening, at handed-in challenges.**
`run_sound_algebraic_at_of_vkrep` with its evaluation-pin hypothesis `hpins` replaced by what
the knowledge-soundness extractor actually hands over: an accepted opening `(a, ρ)` of the
batched claim's combined commitment against the combined evaluation vector at the claim's own
checked value `Ipa.cipOf`, together with the coefficient equality `ha` certifying that `a` IS
the polyscale combination of the declared per-row representations.

The two fr-side exclusion memberships become the alternative branches of the conclusion:
either the run's polyscale challenge lies in `badXiOf`, or its evalscale challenge lies in
`badROf`, or the cardinality bounds and guarded satisfaction hold. Off both sets
`eval_pins_of_opening_of_eq` turns the opening into the per-row pins and the existing root
applies verbatim — no arithmetic is re-derived here.

Project-local: it is the single call the game's algebraic summand makes, replacing the
by-hand case split it would otherwise carry. -/
theorem run_sound_algebraic_at_of_opening {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (beta gamma alpha zeta v u : C.ScalarField)
    (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n) (hn : cvk.n = n)
    (hvk : cvk.Corresponds σ idx)
    (htpos : 0 < cp.tComm.size)
    (aRef : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ σ.k) → C.ScalarField)
    (ρRef : Fin (nc + 1 + tailRowCount * nc) → C.ScalarField)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn i)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField)
    (a : Fin (2 ^ σ.k) → C.ScalarField) (ρ : C.ScalarField)
    (hopen : openingRelationB σ
      (combinedCommitment (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).polyscale
        (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn)
      (combinedEvalVector (2 ^ σ.k)
        (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalscale
        (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn)
      (Ipa.cipOf (runInputAt C σ cvk cp pub beta gamma alpha zeta v u)) a ρ)
    (ha : a = ∑ i : Fin (nc + 1 + tailRowCount * nc),
      (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).polyscale ^ (i : ℕ) • aRef i)
    (hsigRep : ∀ (i : Fin sigmaRows) (c : Fin nc),
      aRef ⟨(streamPos nc (sRow i) c : ℕ), (streamPos nc (sRow i) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly (sigmaPermCol i)) (c : ℕ))
    (hcoeffRep : ∀ (cc : Fin coeffCols) (c : Fin nc),
      aRef ⟨(streamPos nc (cRow cc) c : ℕ), (streamPos nc (cRow cc) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.coeffPoly cc) (c : ℕ))
    (hselRep : ∀ (jj : Fin selCount) (c : Fin nc),
      aRef ⟨(streamPos nc (selRow jj) c : ℕ), (streamPos nc (selRow jj) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.selectorPoly (selGate jj)) (c : ℕ))
    (hpubRep : ∀ c : Fin nc,
      aRef ⟨(streamPos nc pubRow c : ℕ), (streamPos nc pubRow c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (-(idx.pubPoly (pubView idx pub))) (c : ℕ))
    (hftRep : ∀ i : Fin (nc + 1 + tailRowCount * nc), (i : ℕ) = nc →
      aRef i
        = runPScalarAt C σ cvk cp beta gamma alpha zeta
            • ∑ c : Fin nc, (zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly 6) (c : ℕ)
          - (zeta ^ n - 1)
            • ∑ j : Fin cp.tComm.size, (zeta ^ 2 ^ σ.k) ^ (j : ℕ) • aT j) :
    (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).polyscale
        ∈ badXiOf σ aRef (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn
            (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalFn
      ∨ (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalscale
          ∈ badROf σ aRef (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn
              (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalFn
              (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).polyscale
      ∨ (RunBounds σ cvk cp pub idx aRef
          ∧ RunGuardImpAt σ cvk cp pub idx beta gamma alpha zeta aRef aT) := by
  by_cases hξ : (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).polyscale
      ∈ badXiOf σ aRef (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn
          (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalFn
  · exact Or.inl hξ
  by_cases hr : (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalscale
      ∈ badROf σ aRef (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn
          (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalFn
          (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).polyscale
  · exact Or.inr (Or.inl hr)
  refine Or.inr (Or.inr ?_)
  exact run_sound_algebraic_at_of_vkrep σ cvk cp pub idx beta gamma alpha zeta v u hnc hk hn
    hvk htpos aRef ρRef hrep aT
    (eval_pins_of_opening_of_eq σ _ _ aRef _ _ _ hξ hr a ρ hopen ha)
    hsigRep hcoeffRep hselRep hpubRep hftRep

/-- **The seven counted bad events of the algebraic summand.** The composite the
knowledge-soundness game calls: from an accepted opening of the run's batched claim whose
coefficient vector is the declared polyscale combination, together with the statement that
the assembled table does NOT satisfy the circuit, one of seven counted memberships holds —
the four fq-side exclusion sets at the run's own assembled columns (the `ζ` one taken at the
run's assembled quotient), the two `ζ` boundary points, or one of the two fr-side exclusion
sets.

Nothing here is assumed: `runBounds_of_chunking` supplies the cardinality bounds
unconditionally, and each disjunct is a set whose cardinality this layer bounds
(`runBounds_zeta_at_assembly`, `card_badXiOf_le`, `card_badROf_le`). -/
theorem run_badChallenge_of_not_satisfies_at {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] (σ : SRS C.Point) {nc : ℕ}
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) {n : ℕ} [NeZero n] (idx : Index C.ScalarField n)
    (beta gamma alpha zeta v u : C.ScalarField)
    (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n) (hn : cvk.n = n)
    (hvk : cvk.Corresponds σ idx)
    (htpos : 0 < cp.tComm.size)
    (aRef : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ σ.k) → C.ScalarField)
    (ρRef : Fin (nc + 1 + tailRowCount * nc) → C.ScalarField)
    (hrep : ∀ i, commit σ (aRef i) (ρRef i)
      = (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn i)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField)
    (a : Fin (2 ^ σ.k) → C.ScalarField) (ρ : C.ScalarField)
    (hopen : openingRelationB σ
      (combinedCommitment (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).polyscale
        (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).commitmentFn)
      (combinedEvalVector (2 ^ σ.k)
        (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalscale
        (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn)
      (Ipa.cipOf (runInputAt C σ cvk cp pub beta gamma alpha zeta v u)) a ρ)
    (ha : a = ∑ i : Fin (nc + 1 + tailRowCount * nc),
      (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).polyscale ^ (i : ℕ) • aRef i)
    (hsigRep : ∀ (i : Fin sigmaRows) (c : Fin nc),
      aRef ⟨(streamPos nc (sRow i) c : ℕ), (streamPos nc (sRow i) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly (sigmaPermCol i)) (c : ℕ))
    (hcoeffRep : ∀ (cc : Fin coeffCols) (c : Fin nc),
      aRef ⟨(streamPos nc (cRow cc) c : ℕ), (streamPos nc (cRow cc) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.coeffPoly cc) (c : ℕ))
    (hselRep : ∀ (jj : Fin selCount) (c : Fin nc),
      aRef ⟨(streamPos nc (selRow jj) c : ℕ), (streamPos nc (selRow jj) c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (idx.selectorPoly (selGate jj)) (c : ℕ))
    (hpubRep : ∀ c : Fin nc,
      aRef ⟨(streamPos nc pubRow c : ℕ), (streamPos nc pubRow c).isLt⟩
        = chunkCoeffs (2 ^ σ.k) (-(idx.pubPoly (pubView idx pub))) (c : ℕ))
    (hftRep : ∀ i : Fin (nc + 1 + tailRowCount * nc), (i : ℕ) = nc →
      aRef i
        = runPScalarAt C σ cvk cp beta gamma alpha zeta
            • ∑ c : Fin nc, (zeta ^ 2 ^ σ.k) ^ (c : ℕ)
                • chunkCoeffs (2 ^ σ.k) (idx.sigmaPoly 6) (c : ℕ)
          - (zeta ^ n - 1)
            • ∑ j : Fin cp.tComm.size, (zeta ^ 2 ^ σ.k) ^ (j : ℕ) • aT j)
    (hns : ¬ Satisfies idx (pubView idx pub) (runWTab σ cvk cp pub idx aRef)) :
    beta ∈ Protocol.soundBadB idx (runW σ cvk cp pub aRef)
      ∨ gamma ∈ Protocol.soundBadG idx (runW σ cvk cp pub aRef) beta
      ∨ alpha ∈ Protocol.soundBadA idx (pubView idx pub) (runW σ cvk cp pub aRef)
          (runZ σ cvk cp pub aRef) beta gamma
      ∨ zeta ∈ Protocol.soundBadZ idx (pubView idx pub) (runW σ cvk cp pub aRef)
          (runZ σ cvk cp pub aRef) beta gamma alpha
          (ftChunkAssembly σ.k cp.tComm.size aT)
      ∨ zeta = 1
      ∨ zeta = idx.omega ^ (n - idx.zkRows)
      ∨ (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).polyscale
          ∈ badXiOf σ aRef (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn
              (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalFn
      ∨ (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalscale
          ∈ badROf σ aRef (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).pointFn
              (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).evalFn
              (runInputAt C σ cvk cp pub beta gamma alpha zeta v u).polyscale := by
  rcases run_sound_algebraic_at_of_opening σ cvk cp pub idx beta gamma alpha zeta v u hnc hk
      hn hvk htpos aRef ρRef hrep aT a ρ hopen ha hsigRep hcoeffRep hselRep hpubRep
      hftRep with hξ | hr | ⟨_, himp⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hξ))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr))))))
  · rcases guard_fails_of_not_satisfies σ cvk cp pub idx beta gamma alpha zeta aRef aT
        himp hns with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

end Kimchi.Verifier
