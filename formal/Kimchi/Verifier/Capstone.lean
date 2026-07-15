import Mathlib
import Kimchi.Verifier.KimchiSound
import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Reflection
import Kimchi.Verifier.Reflect

/-!
# The idealized composition (capstone 1.3a): `KimchiBundle` and `kimchiBundle_sound`

`Kimchi/Verifier/KimchiSound.lean` proves the audited counting core `kimchiProof_sound`:
from DL-binding, the verifier-key correspondence, and a single accepting REFERENCE
transcript (the batch data at a reference point `ζ₀`), it produces the four bad sets and
the guarded consumer implication ending in `∃ wTab, Satisfies idx pub wTab`. This module
repackages the transcript-side hypotheses of that theorem as ONE structure,
`KimchiBundle`, and restates the core as `kimchiBundle_sound` — the idealized soundness
statement in the special-soundness idiom of the IPA literature: the bundle is the
accepting-transcripts HYPOTHESIS, posited outright and never derived from a single run;
the concrete Fiat–Shamir-instantiated capstone discharges it later by exhibiting the
bundle from the deployed verifier's own transcript. The computational hypotheses stay
OUTSIDE the bundle as theorem hypotheses — `hk` (the SRS-width pin), `hbind` (the
discrete-log idealization), and `hvk` (the verifier-key correspondence) are assumptions
about the key and the group, not transcript data.

The field types are copied VERBATIM from `kimchiProof_sound`'s binder list
(`KimchiSound.lean`), and the conclusion of `kimchiBundle_sound` is the byte-identical
4-bad-set existential of the core (the sole textual delta: the bundled accumulator
commitment appears as `T.zC`). The proof is a single application of `kimchiProof_sound`
through the projections. See the module preamble of `KimchiSound.lean` for the full
trust story (what the challenge data surrogates, why binding is a hypothesis, and how
`VKCorresponds` is discharged for honest and production keys).

Below the idealized composition this module descends to the **concrete,
Fiat–Shamir-instantiated capstones** (capstone 1.3b): `kimchiVesta_sound` /
`kimchiPallas_sound`, stated over the wire verifier key (through `KimchiVK.comms`) and
the wire public-input array (through `pubView`). The trust story, in three strata:

* **HYPOTHESIS — the accumulated grid `KimchiBatchAcc`.** The
  tree-of-accepting-transcripts idiom of the IPA literature (Bulletproofs Theorem 1,
  Halo Theorems 1–2): a 43×2 grid of deployed acceptances `Ipa.verify … = true` of the
  same batched claim at injective combination scalars `(ξ₀, r₀)`. It is posited
  outright — never derived, and never derivable, from a single accepting run. No axiom
  may manufacture it from one run: a single run yields a single transcript, and the
  grid is precisely what rewinding/forking extraction would produce; that extraction is
  what stays hypothetical here, exactly as in `ipaVesta_sound`'s grid hypothesis
  (`Reflection.lean`).

* **AXIOM — `poseidon_fiat_shamir_{vesta,pallas}` only**, applied per grid node inside
  the bridges `kimchiBatchAcc_bundle_{vesta,pallas}`: each node's `FiatShamirTreeB`
  family is *derived* from the node's own deployed acceptance, never assumed. (The
  Pasta `Module` instances additionally carry the Hasse-bound axioms
  `{vesta,pallas}_hasse` through `vestaPointModule`/`pallasPointModule`, exactly as in
  `ipaVesta_sound` — pre-justified in TO_USER.md.)

* **PROVED — everything else.** The bridges instantiate `KimchiBundle` from the grid;
  the capstones are one application of `kimchiBundle_sound` through the wire views,
  their conclusions byte-identical to its (mod the stated instantiation).

Below the concrete capstones this module ends at the **run-level corollaries**
(capstone 1.3c, the finale): `kimchiVesta_run_sound` / `kimchiPallas_run_sound`, the
capstones' consumer implication INSTANTIATED at a real accepted run's own sponge
challenges — the literal `runOracles` fields of `Kimchi/Verifier/Reflect.lean` — over
the run's own commitments (the witness view `fun i => p.wComm.getD i 0`, the
accumulator `p.zComm`). What is DISCHARGED at the run: every node's Fiat–Shamir
transcript-tree family (`nodeFS` + the per-node `poseidon_fiat_shamir_*` axiom at the
consumer grid's own inputs), the grid acceptances (`T'.hacc`), the batch-challenge
injectivity (`T'.hξ₀`/`T'.hr₀`). What remains HYPOTHESIS: the two extraction grids
(`T`/`T'`, the rewinding/forking idiom — never derivable from one run), DL-binding
(`hbind`), the verifier-key correspondence (`hvk`), the run-`ζ` nondegeneracy
(`hζ1`/`hζb`), and the quotient residue (`t`/`hdeg`/`heq` — see the theorem
docstrings). The run acceptance `hacc` is the headline claim being witnessed: via
reflection (`kimchiVerify_reflects`) it pins the wire shapes of the run
(`p.wComm.size = 15`, …), so the `getD` views read genuine entries; the derivation
itself never needs the shape guards (the capstone quantifies over arbitrary `wC`), so
`hacc` — like `hzrun`, the pin tying the reference grid's accumulator to the run's
`z` commitment — enters as a deliberate statement pin.

The file closes with the **soundness-error reading** (capstone 1.4):
`kimchiBundle_sound_error` converts the four bad-set cardinalities of
`kimchiBundle_sound` into ONE bad-tuple count over the challenge space `F⁴` — at most
`soundnessErrorBound n zkRows · |F|³` of the `|F|⁴` challenge tuples `(β, γ, α, ζ)` are
bad, so under uniform challenges the interactive layer errs with probability at most
`soundnessErrorBound n zkRows / |F|` (the fraction clause of the statement; the proof
is pure counting — a union bound over the four challenge axes plus the two degenerate
`ζ` values, no probability library). The quotient strategy `tOf` is ADAPTIVE — a
function of `(β, γ, α)`, matching the Fiat–Shamir message order in which the prover
commits to `t` only after seeing those challenges — and the degenerate values `ζ = 1`
and `ζ = ω^(n−zkRows)` join the union bound, so a good tuple carries NO residual side
conditions: the consumer tail after `∉ badTuples` is verbatim `kimchiBundle_sound`'s.
The run-level corollaries (`*_run_sound`) deliberately do NOT get this wrapper: a fixed
run's sponge outputs are not random, so a probability reading over them IS the
Fiat–Shamir heuristic itself — that stays the declared assumption
(`poseidon_fiat_shamir_*`), never a theorem.
-/

namespace Kimchi.Verifier

open Polynomial Kimchi.Commitment.IPA Kimchi.Index Kimchi.Verifier.Linearization
  Kimchi.Verifier.Equation CompElliptic.Fields.Pasta

/-! ## The transcript bundle -/

/-- The transcript-side hypothesis bundle of `kimchiProof_sound`: the accumulator
commitment `zC` and the single accepting reference transcript at the reference point
`ζ₀` — its claimed evaluations `E₀`, its injective batch challenges `ξ₀`/`r₀`, its
acceptance predicates `A₀`, the per-point `FiatShamirTreeB` family `hFS₀`, and the
acceptances `hacc₀`. Field types are verbatim from the binder list of
`kimchiProof_sound`; the witness commitments `wC` are a structure PARAMETER (fixed
across the whole bundle, as across the whole challenge grid of the core). Project-local:
this is the packaging the concrete capstone instantiates. -/
structure KimchiBundle {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] (σ : SRS G) (idx : Index F n) (pub : Fin idx.publicCount → F)
    (comms : IndexComms G) (wC : Fin 15 → G) where
  /-- The accumulator (`z`) commitment of the reference transcript. -/
  zC : G
  /-- The reference evaluation point. -/
  ζ₀ : F
  /-- The claimed evaluations of the 43-row batch at `ζ₀` and `ω·ζ₀`. -/
  E₀ : Fin 43 → Fin 2 → F
  /-- The row-combination challenges of the reference batch. -/
  ξ₀ : Fin 43 → F
  /-- Distinctness of the row-combination challenges. -/
  hξ₀ : Function.Injective ξ₀
  /-- The point-combination challenges of the reference batch. -/
  r₀ : Fin 2 → F
  /-- Distinctness of the point-combination challenges. -/
  hr₀ : Function.Injective r₀
  /-- The acceptance predicates of the reference batch, per challenge pair. -/
  A₀ : Fin 43 → Fin 2 → Prop
  /-- The per-point Fiat–Shamir transcript-tree family of the reference batch. -/
  hFS₀ : ∀ (i : Fin 43) (j : Fin 2),
    FiatShamirTreeB σ (combinedCommitment (ξ₀ i) (batchC wC zC comms))
      (combinedEvalVector (2 ^ σ.k) (r₀ j) ![ζ₀, idx.omega * ζ₀])
      (combinedInnerProduct (ξ₀ i) (r₀ j) E₀) (A₀ i j)
  /-- The verifier accepts at every challenge pair. -/
  hacc₀ : ∀ i j, A₀ i j

/-! ## The idealized composition -/

/-- **The bundle closes the circuit** (idealized composition): a `KimchiBundle`,
DL-binding (`hbind`), the SRS-width pin (`hk`), and the verifier-key correspondence
(`hvk`) yield the four bad sets and the guarded consumer implication of
`kimchiProof_sound` — byte-identical, ending in `∃ wTab, Satisfies idx pub wTab`. The
proof is one application of the core through the bundle's projections. Project-local:
the idealized soundness statement the concrete Fiat–Shamir capstone consumes. -/
theorem kimchiBundle_sound {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F) (wC : Fin 15 → G)
    (T : KimchiBundle σ idx pub comms wC) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F),
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
            FiatShamirTreeB σ (combinedCommitment (ξ i) (batchC wC T.zC comms))
              (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
              (combinedInnerProduct (ξ i) (r j) E) (A i j)) →
          (∀ i j, A i j) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → F, Satisfies idx pub wTab :=
  kimchiProof_sound σ idx hk hbind comms hvk pub wC T.zC T.ζ₀ T.E₀ T.ξ₀ T.hξ₀ T.r₀
    T.hr₀ T.A₀ T.hFS₀ T.hacc₀

/-! ## The wire views -/

/-- The committed-column view of a wire verifier key: the `IndexComms` record the
abstract soundness layer speaks about, read off the key's arrays (`getD` at the checked
sizes — the shape guards of `kimchiVerify` pin `sigmaComm` to 7 and `coefficientsComm`
to 15 entries). This is the view through which `VKCorresponds` is stated for a wire
key. Project-local: the glue between the wire `KimchiVK` and the abstract capstone. -/
def KimchiVK.comms {C : Ipa.CommitmentCurve} (vk : KimchiVK C) : IndexComms C.Point where
  sigma i := vk.sigmaComm.getD (i : ℕ) 0
  coefficients c := vk.coefficientsComm.getD (c : ℕ) 0
  generic := vk.genericComm
  poseidon := vk.poseidonComm
  completeAdd := vk.completeAddComm
  varBaseMul := vk.mulComm
  endoMul := vk.emulComm
  endoScalar := vk.endomulScalarComm

/-- The public-input array as the `Fin idx.publicCount`-indexed function the circuit
model consumes (`getD`, total; the capstones pin `pub.size = idx.publicCount`, so the
view reads only genuine entries). Project-local: the wire-to-abstract public view. -/
def pubView {F : Type*} [Field F] {n : ℕ} (idx : Index F n) (pub : Array F) :
    Fin idx.publicCount → F :=
  fun i => pub.getD (i : ℕ) 0

/-! ## The accumulated grid — the special-soundness hypothesis -/

/-- **The accumulated grid** (the special-soundness HYPOTHESIS of the concrete
capstone): the tree-of-accepting-transcripts idiom of the IPA literature at the
deployed verifier — one reference point `ζ₀`, and per `(ξ₀ i, r₀ j)`-grid node a run of
the deployed `Ipa.verify` accepting the SAME batched claim: an opaque wire commitment
array pinned row-by-row to the abstract 43-row assembly `batchC wC zC comms`
(`cs`/`hcsSize`/`hcs` — a relation hypothesis, never an `Array.ofFn` build), a wire
evaluation matrix carrying the abstract claims (`es`/`hes`), the two eval points
`(ζ₀, ω·ζ₀)`, and per node an opening proof with the deployed acceptance
(`prf`/`hacc`). Posited outright, never derived from one run. The Pasta bridges below
derive each node's `FiatShamirTreeB` family from the per-node IPA axiom
(`poseidon_fiat_shamir_*`), so the grid carries no Fiat–Shamir-tree content of its own.
Generic over the curve bundle `C` (`Ipa.verify C` is curve-generic); only the bridges
are Pasta-specific. Project-local: the concrete instantiation data of `KimchiBundle`. -/
structure KimchiBatchAcc (C : Ipa.CommitmentCurve) [Module C.ScalarField C.Point]
    {n : ℕ} [NeZero n] (σ : SRS C.Point) (idx : Index C.ScalarField n)
    (comms : IndexComms C.Point) (wC : Fin 15 → C.Point) where
  /-- The accumulator (`z`) commitment of the reference transcript. -/
  zC : C.Point
  /-- The reference evaluation point. -/
  ζ₀ : C.ScalarField
  /-- The claimed evaluations of the 43-row batch at `ζ₀` and `ω·ζ₀`. -/
  E₀ : Fin 43 → Fin 2 → C.ScalarField
  /-- The row-combination challenges of the grid. -/
  ξ₀ : Fin 43 → C.ScalarField
  /-- Distinctness of the row-combination challenges. -/
  hξ₀ : Function.Injective ξ₀
  /-- The point-combination challenges of the grid. -/
  r₀ : Fin 2 → C.ScalarField
  /-- Distinctness of the point-combination challenges. -/
  hr₀ : Function.Injective r₀
  /-- The wire commitment array of the batch — opaque. -/
  cs : Array C.Point
  /-- The wire commitment array has the 43 batch rows. -/
  hcsSize : cs.size = 43
  /-- Row-by-row, the wire array is the abstract assembly `batchC wC zC comms`. -/
  hcs : ∀ i : Fin 43, cs.getD (i : ℕ) 0 = batchC wC zC comms i
  /-- The wire evaluation matrix of the batch — opaque. -/
  es : Array (Array C.ScalarField)
  /-- Entry-by-entry, the wire matrix carries the abstract claims `E₀`. -/
  hes : ∀ (i : Fin 43) (j : Fin 2), (es[(i : ℕ)]!)[(j : ℕ)]! = E₀ i j
  /-- Per `(ξ₀, r₀)`-grid node, the node's IPA opening proof. -/
  prf : Fin 43 → Fin 2 → Ipa.Proof C
  /-- The deployed verifier accepts every node's batched input — the acceptance the
  bridges hand to the per-node IPA axiom. -/
  hacc : ∀ (i : Fin 43) (j : Fin 2),
    Ipa.verify C σ (Ipa.mkInput C cs #[ζ₀, idx.omega * ζ₀] es (ξ₀ i) (r₀ j) (prf i j))
      = true

/-! ## The per-node Fiat–Shamir transport -/

/-- `combinedCommitment` congruence across an index-count equality: reindexing the
commitment family along `Fin.cast` preserves the polyscale combination. -/
private theorem combinedCommitment_reindex {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] (ξ : F) {n m : ℕ} (h : n = m) (Cn : Fin n → G) (Cm : Fin m → G)
    (hC : ∀ i : Fin n, Cn i = Cm (Fin.cast h i)) :
    combinedCommitment ξ Cn = combinedCommitment ξ Cm := by
  unfold combinedCommitment
  refine Fintype.sum_equiv (finCongr h) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast]
  rw [hC i]

/-- `combinedInnerProduct` congruence across a first-index-count equality. -/
private theorem combinedInnerProduct_reindex {F : Type*} [Field F] (ξ r : F)
    {n n' m : ℕ} (h : n = n') (e : Fin n → Fin m → F) (e' : Fin n' → Fin m → F)
    (he : ∀ (i : Fin n) (j : Fin m), e i j = e' (Fin.cast h i) j) :
    combinedInnerProduct ξ r e = combinedInnerProduct ξ r e' := by
  unfold combinedInnerProduct
  refine Fintype.sum_equiv (finCongr h) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast]
  refine congrArg (ξ ^ (i : ℕ) * ·) ?_
  exact Finset.sum_congr rfl fun j _ => by rw [he i j]

section BatchOfAcc

variable {C : Ipa.CommitmentCurve} [Module C.ScalarField C.Point] {n : ℕ} [NeZero n]
  {σ : SRS C.Point} {idx : Index C.ScalarField n} {comms : IndexComms C.Point}
  {wC : Fin 15 → C.Point}

/-- The wire input of one grid node: the grid's opaque commitment array and evaluation
matrix, batched at the node's `(ξ₀ i, r₀ j)` scalars over the two eval points
`(ζ₀, ω·ζ₀)`, with the node's opening proof. The accumulated `hacc` states the deployed
verifier accepts exactly this input; the bridges apply the per-node IPA axiom to it. -/
def KimchiBatchAcc.nodeInput (T : KimchiBatchAcc C σ idx comms wC)
    (i : Fin 43) (j : Fin 2) : Ipa.Input C :=
  Ipa.mkInput C T.cs #[T.ζ₀, idx.omega * T.ζ₀] T.es (T.ξ₀ i) (T.r₀ j) (T.prf i j)

/-- **Per-node Fiat–Shamir transport**: the IPA-axiom-shaped transcript-tree family at
a node's wire input (`hax`, defeq to `poseidon_fiat_shamir_*` at `nodeInput` — the
`hcip` move of `ipaVesta_sound`), re-expressed over the abstract batch data: the opaque
commitment array collapses to the 43-row assembly (`hcs`), the two wire eval points to
`![ζ₀, ω·ζ₀]`, and the wire combined inner product to the one over the abstract claims
(`hes`). Sub-terms stay opaque throughout — the acceptance proposition
`Ipa.verify … = true` is never reduced. -/
private theorem KimchiBatchAcc.nodeFS (T : KimchiBatchAcc C σ idx comms wC)
    (i : Fin 43) (j : Fin 2)
    (hax : FiatShamirTreeB σ
      (combinedCommitment (T.ξ₀ i) (fun t : Fin T.cs.size => T.cs[t]))
      (combinedEvalVector (2 ^ σ.k) (T.r₀ j) (T.nodeInput i j).pointFn)
      (Ipa.cipOf (T.nodeInput i j))
      (Ipa.verify C σ (T.nodeInput i j) = true)) :
    FiatShamirTreeB σ
      (combinedCommitment (T.ξ₀ i) (batchC wC T.zC comms))
      (combinedEvalVector (2 ^ σ.k) (T.r₀ j) ![T.ζ₀, idx.omega * T.ζ₀])
      (combinedInnerProduct (T.ξ₀ i) (T.r₀ j) T.E₀)
      (Ipa.verify C σ (T.nodeInput i j) = true) := by
  have hgetD : ∀ (m : ℕ) (hm : m < T.cs.size), T.cs.getD m 0 = T.cs[m] := by
    intro m hm
    simp [Array.getD, hm]
  -- the commitment column: the opaque wire array is the 43-row assembly
  have hP : combinedCommitment (T.ξ₀ i) (fun t : Fin T.cs.size => T.cs[t])
      = combinedCommitment (T.ξ₀ i) (batchC wC T.zC comms) := by
    refine combinedCommitment_reindex _ T.hcsSize _ _ fun t => ?_
    have h1 := T.hcs (Fin.cast T.hcsSize t)
    simp only [Fin.val_cast] at h1
    rw [hgetD (t : ℕ) t.isLt] at h1
    exact h1
  -- the eval points: the wire two-point array is `![ζ₀, ωζ₀]`
  have hx : ∀ t : Fin 2, (T.nodeInput i j).pointFn t
      = ![T.ζ₀, idx.omega * T.ζ₀] t := by
    intro t
    fin_cases t <;> rfl
  have hb : combinedEvalVector (2 ^ σ.k) (T.r₀ j) (T.nodeInput i j).pointFn
      = combinedEvalVector (2 ^ σ.k) (T.r₀ j) ![T.ζ₀, idx.omega * T.ζ₀] :=
    congrArg (fun x : Fin 2 → C.ScalarField =>
      combinedEvalVector (2 ^ σ.k) (T.r₀ j) x) (funext hx)
  -- the combined inner product: the wire matrix carries the abstract claims
  have hv : Ipa.cipOf (T.nodeInput i j)
      = combinedInnerProduct (T.ξ₀ i) (T.r₀ j) T.E₀ := by
    show combinedInnerProduct (T.ξ₀ i) (T.r₀ j)
        (fun (t : Fin T.cs.size) (u : Fin 2) => (T.es[(t : ℕ)]!)[(u : ℕ)]!)
      = combinedInnerProduct (T.ξ₀ i) (T.r₀ j) T.E₀
    exact combinedInnerProduct_reindex _ _ T.hcsSize _ _
      fun t u => T.hes (Fin.cast T.hcsSize t) u
  rw [hP, hb, hv] at hax
  exact hax

end BatchOfAcc

/-! ## The Pasta bridges -/

/-- **The Vesta bridge (the Fiat–Shamir derivation)**: an accumulated grid yields the
transcript bundle. Every node's `FiatShamirTreeB` family is *derived* — not assumed —
from the per-node IPA axiom `poseidon_fiat_shamir_vesta` at the node's own wire input
(`nodeInput`), transported to the abstract batch data by `nodeFS`; the acceptance
propositions `A₀` are the deployed per-node acceptances `Ipa.verify … = true`,
discharged by the accumulated `hacc`. This is where the concrete capstone invokes the
IPA-level assumption. `pub` enters only through the target type (`KimchiBundle` carries
the public input as a parameter; the grid does not mention it). -/
def kimchiBatchAcc_bundle_vesta {n : ℕ} [NeZero n] {σ : SRS IpaVesta.Point}
    {idx : Index Fp n} {comms : IndexComms IpaVesta.Point}
    {wC : Fin 15 → IpaVesta.Point} (pub : Fin idx.publicCount → Fp)
    (T : KimchiBatchAcc IpaVesta.curve σ idx comms wC) :
    KimchiBundle σ idx pub comms wC where
  zC := T.zC
  ζ₀ := T.ζ₀
  E₀ := T.E₀
  ξ₀ := T.ξ₀
  hξ₀ := T.hξ₀
  r₀ := T.r₀
  hr₀ := T.hr₀
  A₀ := fun i j => Ipa.verify IpaVesta.curve σ (T.nodeInput i j) = true
  hFS₀ := fun i j => T.nodeFS i j (poseidon_fiat_shamir_vesta σ (T.nodeInput i j))
  hacc₀ := fun i j => T.hacc i j

/-- **The Pallas bridge.** The Pallas-side twin of `kimchiBatchAcc_bundle_vesta`,
deriving every node's `FiatShamirTreeB` family from `poseidon_fiat_shamir_pallas`. -/
def kimchiBatchAcc_bundle_pallas {n : ℕ} [NeZero n] {σ : SRS IpaPallas.Point}
    {idx : Index Fq n} {comms : IndexComms IpaPallas.Point}
    {wC : Fin 15 → IpaPallas.Point} (pub : Fin idx.publicCount → Fq)
    (T : KimchiBatchAcc IpaPallas.curve σ idx comms wC) :
    KimchiBundle σ idx pub comms wC where
  zC := T.zC
  ζ₀ := T.ζ₀
  E₀ := T.E₀
  ξ₀ := T.ξ₀
  hξ₀ := T.hξ₀
  r₀ := T.r₀
  hr₀ := T.hr₀
  A₀ := fun i j => Ipa.verify IpaPallas.curve σ (T.nodeInput i j) = true
  hFS₀ := fun i j => T.nodeFS i j (poseidon_fiat_shamir_pallas σ (T.nodeInput i j))
  hacc₀ := fun i j => T.hacc i j

/-! ## The concrete capstones -/

/-- **Soundness of the deployed Vesta kimchi verifier** (the concrete capstone): a
special-soundness grid `KimchiBatchAcc` at the wire key's committed columns
(`vk.comms`), under DL-binding (`hbind`), the SRS-width pin (`hk`), and the
verifier-key correspondence (`hvk`), yields the four bad sets and the guarded consumer
implication of `kimchiBundle_sound` — byte-identical, at the wire views
(`pubView idx pub` for the public input), ending in
`∃ wTab, Satisfies idx (pubView idx pub) wTab`. The proof is `kimchiBundle_sound`
through the Vesta bridge; the only axiom consumed is `poseidon_fiat_shamir_vesta`, once
per grid node (plus the hasse-forced `Module` instance — see the module preamble).
`hpub` pins the wire public array to the circuit's count, making the `getD` view
honest. Project-local: the Vesta root of the concrete composition. -/
theorem kimchiVesta_sound (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → IpaVesta.Point)
    (T : KimchiBatchAcc IpaVesta.curve σ idx vk.comms wC) :
    ∃ (badB : Finset Fp) (badG : Fp → Finset Fp) (badA : Fp → Fp → Finset Fp)
        (badZ : Fp → Fp → Fp → Polynomial Fp → Finset Fp),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fp), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : Fp) (t : Polynomial Fp) (ζ : Fp)
          (E : Fin 43 → Fin 2 → Fp) (ξ : Fin 43 → Fp) (r : Fin 2 → Fp)
          (A : Fin 43 → Fin 2 → Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          Function.Injective ξ → Function.Injective r →
          (∀ (i : Fin 43) (j : Fin 2),
            FiatShamirTreeB σ (combinedCommitment (ξ i) (batchC wC T.zC vk.comms))
              (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
              (combinedInnerProduct (ξ i) (r j) E) (A i j)) →
          (∀ i j, A i j) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly (pubView idx pub)).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → Fp, Satisfies idx (pubView idx pub) wTab :=
  kimchiBundle_sound σ idx hk hbind vk.comms hvk (pubView idx pub) wC
    (kimchiBatchAcc_bundle_vesta (pubView idx pub) T)

/-- **Soundness of the deployed Pallas kimchi verifier.** The Pallas-side twin of
`kimchiVesta_sound`: `kimchiBundle_sound` through the Pallas bridge; the only axiom
consumed is `poseidon_fiat_shamir_pallas`, once per grid node (plus the hasse-forced
`Module` instance). Project-local: the Pallas root of the concrete composition. -/
theorem kimchiPallas_sound (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → IpaPallas.Point)
    (T : KimchiBatchAcc IpaPallas.curve σ idx vk.comms wC) :
    ∃ (badB : Finset Fq) (badG : Fq → Finset Fq) (badA : Fq → Fq → Finset Fq)
        (badZ : Fq → Fq → Fq → Polynomial Fq → Finset Fq),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fq), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : Fq) (t : Polynomial Fq) (ζ : Fq)
          (E : Fin 43 → Fin 2 → Fq) (ξ : Fin 43 → Fq) (r : Fin 2 → Fq)
          (A : Fin 43 → Fin 2 → Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          Function.Injective ξ → Function.Injective r →
          (∀ (i : Fin 43) (j : Fin 2),
            FiatShamirTreeB σ (combinedCommitment (ξ i) (batchC wC T.zC vk.comms))
              (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
              (combinedInnerProduct (ξ i) (r j) E) (A i j)) →
          (∀ i j, A i j) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly (pubView idx pub)).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → Fq, Satisfies idx (pubView idx pub) wTab :=
  kimchiBundle_sound σ idx hk hbind vk.comms hvk (pubView idx pub) wC
    (kimchiBatchAcc_bundle_pallas (pubView idx pub) T)

/-! ## The run-level corollaries (capstone 1.3c — the finale) -/

/-- **Run-level soundness of the deployed Vesta kimchi verifier** (the finale):
`kimchiVesta_sound`'s consumer implication instantiated at a real accepted run's own
sponge challenges — the literal `runOracles` fields — over the run's own commitments
(`wC := fun i => p.wComm.getD i 0`; the reference grid opens the run's accumulator,
`hzrun : T.zC = p.zComm`). The consumer grid `T'` shares the accumulator (`hzC`) and
sits at the run's own `ζ` (`hζ'`); its Fiat–Shamir trees, acceptances, and challenge
injectivity discharge the capstone's transcript antecedents, so the four bad sets
guard `∃ wTab, Satisfies idx (pubView idx pub) wTab` at the run's `(β, γ, α, ζ)`.

The quotient residue `(t, hdeg, heq)` is the ONE antecedent not discharged from
deployed acceptances: kimchi never opens the `t_comm` chunks directly — the verifier
checks only the scalar image of the quotient identity through the Maller `ft` row
(`runFtComm`/`runFtEval0`). Extracting an actual `t` with `t.natDegree < 7 * n` and
the identity at the run's `ζ` requires opening the t-chunk commitments — commitment
extractability beyond the batch grid — which the counting form deliberately does not
posit. It stays an explicit hypothesis; no axiom manufactures it.

`hacc` (the deployed acceptance — the headline claim) and `hzrun` are statement pins:
the derivation quantifies over arbitrary `wC`, so neither is load-bearing below, but
they are part of the claim's meaning (via `kimchiVerify_reflects`, `hacc` pins that
the `getD` views read genuine wire entries). Project-local: the Vesta run root. -/
theorem kimchiVesta_run_sound (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (p : KimchiVesta.Proof) (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : KimchiVesta.verify σ vk p pub = true)
    (T : KimchiBatchAcc IpaVesta.curve σ idx vk.comms
      (fun i => p.wComm.getD (i : ℕ) 0))
    (T' : KimchiBatchAcc IpaVesta.curve σ idx vk.comms
      (fun i => p.wComm.getD (i : ℕ) 0))
    (hzrun : T.zC = p.zComm)
    (hzC : T'.zC = T.zC)
    (hζ' : T'.ζ₀ = (runOracles IpaVesta.curve σ vk p pub).zeta)
    (hζ1 : (runOracles IpaVesta.curve σ vk p pub).zeta ≠ 1)
    (hζb : (runOracles IpaVesta.curve σ vk p pub).zeta
      ≠ idx.omega ^ (n - idx.zkRows))
    (t : Polynomial Fp) (hdeg : t.natDegree < 7 * n)
    (heq :
      permScalar (runOracles IpaVesta.curve σ vk p pub).beta
          (runOracles IpaVesta.curve σ vk p pub).gamma
          (runOracles IpaVesta.curve σ vk p pub).alpha
          (zkpmEval n idx.zkRows idx.omega (runOracles IpaVesta.curve σ vk p pub).zeta)
          (claimedEvals T'.E₀)
          * (idx.sigmaPoly 6).eval (runOracles IpaVesta.curve σ vk p pub).zeta
        - ((runOracles IpaVesta.curve σ vk p pub).zeta ^ n - 1)
            * t.eval (runOracles IpaVesta.curve σ vk p pub).zeta
        = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase
            (runOracles IpaVesta.curve σ vk p pub).alpha
            (runOracles IpaVesta.curve σ vk p pub).beta
            (runOracles IpaVesta.curve σ vk p pub).gamma
            (runOracles IpaVesta.curve σ vk p pub).zeta
            (-((idx.pubPoly (pubView idx pub)).eval
              (runOracles IpaVesta.curve σ vk p pub).zeta))
            (claimedEvals T'.E₀)) :
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
                (runOracles IpaVesta.curve σ vk p pub).alpha t →
          ∃ wTab : Fin n → Fin 15 → Fp, Satisfies idx (pubView idx pub) wTab) := by
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiVesta_sound σ vk pub idx hk hvk hpub hbind
      (fun i => p.wComm.getD (i : ℕ) 0) T
  refine ⟨badB, badG, badA, badZ, hbounds, fun hβ hγ hα hζ => ?_⟩
  refine himp (runOracles IpaVesta.curve σ vk p pub).beta
    (runOracles IpaVesta.curve σ vk p pub).gamma
    (runOracles IpaVesta.curve σ vk p pub).alpha t
    (runOracles IpaVesta.curve σ vk p pub).zeta
    T'.E₀ T'.ξ₀ T'.r₀
    (fun i j => Ipa.verify IpaVesta.curve σ (T'.nodeInput i j) = true)
    hβ hγ hα hζ hζ1 hζb hdeg T'.hξ₀ T'.hr₀ ?_ T'.hacc heq
  intro i j
  have h := T'.nodeFS i j (poseidon_fiat_shamir_vesta σ (T'.nodeInput i j))
  simp only [hzC, hζ'] at h
  exact h

/-- **Run-level soundness of the deployed Pallas kimchi verifier.** The Pallas-side
twin of `kimchiVesta_run_sound`, over `Fq`/`IpaPallas`, its Fiat–Shamir trees from
`poseidon_fiat_shamir_pallas`. See the Vesta docstring for the trust story — in
particular the quotient residue `(t, hdeg, heq)`, the one antecedent not discharged
from deployed acceptances, and the statement pins `hacc`/`hzrun`. Project-local: the
Pallas run root. -/
theorem kimchiPallas_run_sound (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (p : KimchiPallas.Proof) (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : KimchiPallas.verify σ vk p pub = true)
    (T : KimchiBatchAcc IpaPallas.curve σ idx vk.comms
      (fun i => p.wComm.getD (i : ℕ) 0))
    (T' : KimchiBatchAcc IpaPallas.curve σ idx vk.comms
      (fun i => p.wComm.getD (i : ℕ) 0))
    (hzrun : T.zC = p.zComm)
    (hzC : T'.zC = T.zC)
    (hζ' : T'.ζ₀ = (runOracles IpaPallas.curve σ vk p pub).zeta)
    (hζ1 : (runOracles IpaPallas.curve σ vk p pub).zeta ≠ 1)
    (hζb : (runOracles IpaPallas.curve σ vk p pub).zeta
      ≠ idx.omega ^ (n - idx.zkRows))
    (t : Polynomial Fq) (hdeg : t.natDegree < 7 * n)
    (heq :
      permScalar (runOracles IpaPallas.curve σ vk p pub).beta
          (runOracles IpaPallas.curve σ vk p pub).gamma
          (runOracles IpaPallas.curve σ vk p pub).alpha
          (zkpmEval n idx.zkRows idx.omega
            (runOracles IpaPallas.curve σ vk p pub).zeta)
          (claimedEvals T'.E₀)
          * (idx.sigmaPoly 6).eval (runOracles IpaPallas.curve σ vk p pub).zeta
        - ((runOracles IpaPallas.curve σ vk p pub).zeta ^ n - 1)
            * t.eval (runOracles IpaPallas.curve σ vk p pub).zeta
        = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase
            (runOracles IpaPallas.curve σ vk p pub).alpha
            (runOracles IpaPallas.curve σ vk p pub).beta
            (runOracles IpaPallas.curve σ vk p pub).gamma
            (runOracles IpaPallas.curve σ vk p pub).zeta
            (-((idx.pubPoly (pubView idx pub)).eval
              (runOracles IpaPallas.curve σ vk p pub).zeta))
            (claimedEvals T'.E₀)) :
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
                (runOracles IpaPallas.curve σ vk p pub).alpha t →
          ∃ wTab : Fin n → Fin 15 → Fq, Satisfies idx (pubView idx pub) wTab) := by
  obtain ⟨badB, badG, badA, badZ, hbounds, himp⟩ :=
    kimchiPallas_sound σ vk pub idx hk hvk hpub hbind
      (fun i => p.wComm.getD (i : ℕ) 0) T
  refine ⟨badB, badG, badA, badZ, hbounds, fun hβ hγ hα hζ => ?_⟩
  refine himp (runOracles IpaPallas.curve σ vk p pub).beta
    (runOracles IpaPallas.curve σ vk p pub).gamma
    (runOracles IpaPallas.curve σ vk p pub).alpha t
    (runOracles IpaPallas.curve σ vk p pub).zeta
    T'.E₀ T'.ξ₀ T'.r₀
    (fun i j => Ipa.verify IpaPallas.curve σ (T'.nodeInput i j) = true)
    hβ hγ hα hζ hζ1 hζb hdeg T'.hξ₀ T'.hr₀ ?_ T'.hacc heq
  intro i j
  have h := T'.nodeFS i j (poseidon_fiat_shamir_pallas σ (T'.nodeInput i j))
  simp only [hzC, hζ'] at h
  exact h

/-! ## The soundness error (capstone 1.4)

The counting kernel below is elementary and generic: a filtered-tuple cardinality over
`κ × κ × κ × κ` is bounded slice by slice — one lemma per coordinate position, each a
`Finset.card_filter`/`Fintype.sum_prod_type` computation — and the six slices of the
bad-tuple predicate (four bad-set memberships, two degenerate `ζ` values) are then
assembled by `Finset.filter_or` + `Finset.card_union_le`. -/

/-- One product step of the tuple counting: if every `a`-slice of a predicate on
`α × β` has at most `m` members, the filtered product has at most `|α| · m`.
Project-local: the recursion step of the position bounds below. -/
private theorem card_filter_pair {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → Prop) [∀ a b, Decidable (p a b)] {m : ℕ}
    (h : ∀ a, (Finset.univ.filter (p a)).card ≤ m) :
    (Finset.univ.filter fun x : α × β => p x.1 x.2).card ≤ Fintype.card α * m := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have step : ∀ a : α, (∑ b : β, if p a b then 1 else 0) ≤ m := by
    intro a
    rw [← Finset.card_filter]
    exact h a
  calc (∑ a : α, ∑ b : β, if p a b then 1 else 0)
      ≤ ∑ _a : α, m := Finset.sum_le_sum fun a _ => step a
    _ = Fintype.card α * m := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The head slice of the tuple counting: filtering `α × β` by a condition on the
first coordinate alone counts `|t| · |β|` exactly. -/
private theorem card_filter_head {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (t : Finset α) :
    (Finset.univ.filter fun x : α × β => x.1 ∈ t).card = t.card * Fintype.card β := by
  have h : (Finset.univ.filter fun x : α × β => x.1 ∈ t) = t ×ˢ Finset.univ := by
    ext x
    simp
  rw [h, Finset.card_product, Finset.card_univ]

/-- Position-1 slice bound: a condition on the first coordinate of a quadruple cuts
out at most `m · |κ|³` tuples. -/
private theorem card_filter_pos1 {κ : Type*} [Fintype κ] [DecidableEq κ]
    {s : Finset κ} {m : ℕ} (hs : s.card ≤ m) :
    (Finset.univ.filter fun x : κ × κ × κ × κ => x.1 ∈ s).card
      ≤ m * Fintype.card κ ^ 3 := by
  rw [card_filter_head]
  calc s.card * Fintype.card (κ × κ × κ) ≤ m * Fintype.card (κ × κ × κ) :=
        Nat.mul_le_mul_right _ hs
    _ = m * Fintype.card κ ^ 3 := by simp only [Fintype.card_prod]; ring

/-- Position-2 slice bound: a condition on the second coordinate of a quadruple,
depending on the first, cuts out at most `m · |κ|³` tuples. -/
private theorem card_filter_pos2 {κ : Type*} [Fintype κ] [DecidableEq κ]
    {s : κ → Finset κ} {m : ℕ} (hs : ∀ a, (s a).card ≤ m) :
    (Finset.univ.filter fun x : κ × κ × κ × κ => x.2.1 ∈ s x.1).card
      ≤ m * Fintype.card κ ^ 3 := by
  have h := card_filter_pair (fun (a : κ) (y : κ × κ × κ) => y.1 ∈ s a)
    (m := m * Fintype.card κ ^ 2) (fun a => by
      rw [card_filter_head]
      calc (s a).card * Fintype.card (κ × κ) ≤ m * Fintype.card (κ × κ) :=
            Nat.mul_le_mul_right _ (hs a)
        _ = m * Fintype.card κ ^ 2 := by simp only [Fintype.card_prod]; ring)
  calc (Finset.univ.filter fun x : κ × κ × κ × κ => x.2.1 ∈ s x.1).card
      ≤ Fintype.card κ * (m * Fintype.card κ ^ 2) := h
    _ = m * Fintype.card κ ^ 3 := by ring

/-- Position-3 slice bound: a condition on the third coordinate of a quadruple,
depending on the first two, cuts out at most `m · |κ|³` tuples. -/
private theorem card_filter_pos3 {κ : Type*} [Fintype κ] [DecidableEq κ]
    {s : κ → κ → Finset κ} {m : ℕ} (hs : ∀ a b, (s a b).card ≤ m) :
    (Finset.univ.filter fun x : κ × κ × κ × κ => x.2.2.1 ∈ s x.1 x.2.1).card
      ≤ m * Fintype.card κ ^ 3 := by
  have h := card_filter_pair (fun (a : κ) (y : κ × κ × κ) => y.2.1 ∈ s a y.1)
    (m := m * Fintype.card κ ^ 2) (fun a => by
      have h2 := card_filter_pair (fun (b : κ) (z : κ × κ) => z.1 ∈ s a b)
        (m := m * Fintype.card κ) (fun b => by
          rw [card_filter_head]
          exact Nat.mul_le_mul_right _ (hs a b))
      calc (Finset.univ.filter fun y : κ × κ × κ => y.2.1 ∈ s a y.1).card
          ≤ Fintype.card κ * (m * Fintype.card κ) := h2
        _ = m * Fintype.card κ ^ 2 := by ring)
  calc (Finset.univ.filter fun x : κ × κ × κ × κ => x.2.2.1 ∈ s x.1 x.2.1).card
      ≤ Fintype.card κ * (m * Fintype.card κ ^ 2) := h
    _ = m * Fintype.card κ ^ 3 := by ring

/-- Position-4 slice bound: a condition on the last coordinate of a quadruple,
depending on the first three, cuts out at most `m · |κ|³` tuples. -/
private theorem card_filter_pos4 {κ : Type*} [Fintype κ] [DecidableEq κ]
    {s : κ → κ → κ → Finset κ} {m : ℕ} (hs : ∀ a b c, (s a b c).card ≤ m) :
    (Finset.univ.filter fun x : κ × κ × κ × κ =>
      x.2.2.2 ∈ s x.1 x.2.1 x.2.2.1).card ≤ m * Fintype.card κ ^ 3 := by
  have h := card_filter_pair (fun (a : κ) (y : κ × κ × κ) => y.2.2 ∈ s a y.1 y.2.1)
    (m := m * Fintype.card κ ^ 2) (fun a => by
      have h2 := card_filter_pair (fun (b : κ) (z : κ × κ) => z.2 ∈ s a b z.1)
        (m := m * Fintype.card κ) (fun b => by
          have h3 := card_filter_pair (fun (c : κ) (d : κ) => d ∈ s a b c)
            (m := m) (fun c => by rw [Finset.filter_univ_mem]; exact hs a b c)
          calc (Finset.univ.filter fun z : κ × κ => z.2 ∈ s a b z.1).card
              ≤ Fintype.card κ * m := h3
            _ = m * Fintype.card κ := by ring)
      calc (Finset.univ.filter fun y : κ × κ × κ => y.2.2 ∈ s a y.1 y.2.1).card
          ≤ Fintype.card κ * (m * Fintype.card κ) := h2
        _ = m * Fintype.card κ ^ 2 := by ring)
  calc (Finset.univ.filter fun x : κ × κ × κ × κ =>
        x.2.2.2 ∈ s x.1 x.2.1 x.2.2.1).card
      ≤ Fintype.card κ * (m * Fintype.card κ ^ 2) := h
    _ = m * Fintype.card κ ^ 3 := by ring

/-- Degenerate-value slice bound: pinning the last coordinate of a quadruple to one
value cuts out at most `1 · |κ|³` tuples (stated with the `1 ·` so the six slices
assemble uniformly). -/
private theorem card_filter_last_eq {κ : Type*} [Fintype κ] [DecidableEq κ] {c : κ} :
    (Finset.univ.filter fun x : κ × κ × κ × κ => x.2.2.2 = c).card
      ≤ 1 * Fintype.card κ ^ 3 := by
  have he : (Finset.univ.filter fun x : κ × κ × κ × κ => x.2.2.2 = c)
      = Finset.univ.filter fun x : κ × κ × κ × κ => x.2.2.2 ∈ ({c} : Finset κ) := by
    ext x
    simp
  rw [he]
  exact card_filter_pos4 (s := fun _ _ _ => ({c} : Finset κ)) (m := 1)
    fun _ _ _ => le_of_eq (Finset.card_singleton c)

/-- The union-bound numerator of the soundness error: the four bad-set cardinality
bounds of `kimchiBundle_sound` — `7·(n − zkRows)` for `β`, the same for `γ`,
`n·(gateAlphaCount + permAlphaCount − 1)` for `α`, `degreeBound n` for `ζ` — plus the
two degenerate `ζ` values (`1` and `ω^(n − zkRows)`). Out of the `|F|⁴` challenge
tuples, at most `soundnessErrorBound n zkRows · |F|³` are bad
(`kimchiBundle_sound_error`), so the interactive soundness error is at most
`soundnessErrorBound n zkRows / |F|`. Project-local: kept symbolic — the four capstone
bounds plus `2` — so the error constant reads off the statement. -/
def soundnessErrorBound (n zkRows : ℕ) : ℕ :=
  7 * (n - zkRows) + 7 * (n - zkRows)
    + n * (Index.gateAlphaCount + Index.permAlphaCount - 1)
    + Index.degreeBound n + 2

/-- **The soundness error of the interactive layer** (capstone 1.4): the four bad-set
cardinalities of `kimchiBundle_sound` collapse into ONE bad-tuple count over the
challenge space `F⁴` — a set `badTuples` of at most
`soundnessErrorBound n zkRows · |F|³` challenge tuples (union bound over the four
challenge axes plus the two degenerate `ζ` values) — equivalently, at most a
`soundnessErrorBound / |F|` fraction of the `|F|⁴` tuples; the `ℚ`-division form is
interderivable with the counting bound and deliberately not duplicated — outside of
which the consumer
implication holds with NO residual side conditions: the tail after `∉ badTuples` is
verbatim `kimchiBundle_sound`'s, with the memberships, both `ζ ≠` guards, and the
degree bound absorbed into `badTuples`. The quotient strategy `tOf` is ADAPTIVE — a
function of `(β, γ, α)`, the Fiat–Shamir order in which the prover commits to `t` only
after those challenges — with its degree bound `htdeg` a strategy-level hypothesis.
Pure counting; no probability library enters. Project-local: the error-constant
reading of the idealized composition. -/
theorem kimchiBundle_sound_error {F G : Type*} [Field F] [Fintype F] [DecidableEq F]
    [AddCommGroup G] [Module F G] {n : ℕ} [NeZero n] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F) (wC : Fin 15 → G)
    (T : KimchiBundle σ idx pub comms wC)
    (tOf : F → F → F → Polynomial F)
    (htdeg : ∀ β γ α, (tOf β γ α).natDegree < 7 * n) :
    ∃ badTuples : Finset (F × F × F × F),
      badTuples.card ≤ soundnessErrorBound n idx.zkRows * Fintype.card F ^ 3
      ∧ ∀ β γ α ζ : F, (β, γ, α, ζ) ∉ badTuples →
          ∀ (E : Fin 43 → Fin 2 → F) (ξ : Fin 43 → F) (r : Fin 2 → F)
            (A : Fin 43 → Fin 2 → Prop),
            Function.Injective ξ → Function.Injective r →
            (∀ (i : Fin 43) (j : Fin 2),
              FiatShamirTreeB σ (combinedCommitment (ξ i) (batchC wC T.zC comms))
                (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
                (combinedInnerProduct (ξ i) (r j) E) (A i j)) →
            (∀ i j, A i j) →
            (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
                * (idx.sigmaPoly 6).eval ζ
              - (ζ ^ n - 1) * (tOf β γ α).eval ζ
              = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                  ζ (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) →
            ∃ wTab : Fin n → Fin 15 → F, Satisfies idx pub wTab := by
  obtain ⟨badB, badG, badA, badZ, ⟨hB, hG, hA, hZ⟩, himp⟩ :=
    kimchiBundle_sound σ idx hk hbind comms hvk pub wC T
  have hle : ∀ {s t : Finset (F × F × F × F)} {a b : ℕ}, s.card ≤ a → t.card ≤ b →
      (s ∪ t).card ≤ a + b := fun hs ht =>
    le_trans (Finset.card_union_le _ _) (Nat.add_le_add hs ht)
  have hcard : (Finset.univ.filter fun x : F × F × F × F =>
      x.1 ∈ badB ∨ x.2.1 ∈ badG x.1 ∨ x.2.2.1 ∈ badA x.1 x.2.1
        ∨ x.2.2.2 ∈ badZ x.1 x.2.1 x.2.2.1 (tOf x.1 x.2.1 x.2.2.1)
        ∨ x.2.2.2 = 1 ∨ x.2.2.2 = idx.omega ^ (n - idx.zkRows)).card
      ≤ soundnessErrorBound n idx.zkRows * Fintype.card F ^ 3 := by
    simp only [Finset.filter_or]
    refine le_trans (hle (card_filter_pos1 hB) (hle (card_filter_pos2 hG)
      (hle (card_filter_pos3 hA)
        (hle (card_filter_pos4 fun a b c => hZ a b c (tOf a b c) (htdeg a b c))
          (hle card_filter_last_eq card_filter_last_eq))))) (le_of_eq ?_)
    simp only [soundnessErrorBound]
    ring
  refine ⟨_, hcard, ?_⟩
  intro β γ α ζ hnot E ξ r A hξ hr hFS hacc heq
  have hmem : ¬(β ∈ badB ∨ γ ∈ badG β ∨ α ∈ badA β γ
      ∨ ζ ∈ badZ β γ α (tOf β γ α) ∨ ζ = 1 ∨ ζ = idx.omega ^ (n - idx.zkRows)) :=
    fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  simp only [not_or] at hmem
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hmem
  exact himp β γ α (tOf β γ α) ζ E ξ r A h1 h2 h3 h4 h5 h6 (htdeg β γ α) hξ hr
    hFS hacc heq

/-- **The soundness error of the deployed Vesta kimchi verifier**:
`kimchiVesta_sound`'s conclusion in the bad-tuple form — one set of at most
`soundnessErrorBound n zkRows · |F|³` challenge tuples (a `soundnessErrorBound / |F|`
fraction), outside of which the consumer implication holds at the adaptive quotient
strategy `tOf` with no residual side conditions. One application of
`kimchiBundle_sound_error` through the Vesta bridge; the trust story (the grid
hypothesis `T`, the per-node `poseidon_fiat_shamir_vesta`, DL-binding) is exactly
`kimchiVesta_sound`'s. Project-local: the Vesta error-constant root. -/
theorem kimchiVesta_sound_error (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → IpaVesta.Point)
    (T : KimchiBatchAcc IpaVesta.curve σ idx vk.comms wC)
    (tOf : Fp → Fp → Fp → Polynomial Fp)
    (htdeg : ∀ β γ α, (tOf β γ α).natDegree < 7 * n) :
    ∃ badTuples : Finset (Fp × Fp × Fp × Fp),
      badTuples.card ≤ soundnessErrorBound n idx.zkRows * Fintype.card Fp ^ 3
      ∧ ∀ β γ α ζ : Fp, (β, γ, α, ζ) ∉ badTuples →
          ∀ (E : Fin 43 → Fin 2 → Fp) (ξ : Fin 43 → Fp) (r : Fin 2 → Fp)
            (A : Fin 43 → Fin 2 → Prop),
            Function.Injective ξ → Function.Injective r →
            (∀ (i : Fin 43) (j : Fin 2),
              FiatShamirTreeB σ (combinedCommitment (ξ i) (batchC wC T.zC vk.comms))
                (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
                (combinedInnerProduct (ξ i) (r j) E) (A i j)) →
            (∀ i j, A i j) →
            (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
                * (idx.sigmaPoly 6).eval ζ
              - (ζ ^ n - 1) * (tOf β γ α).eval ζ
              = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                  ζ (-((idx.pubPoly (pubView idx pub)).eval ζ)) (claimedEvals E)) →
            ∃ wTab : Fin n → Fin 15 → Fp, Satisfies idx (pubView idx pub) wTab :=
  kimchiBundle_sound_error σ idx hk hbind vk.comms hvk (pubView idx pub) wC
    (kimchiBatchAcc_bundle_vesta (pubView idx pub) T) tOf htdeg

/-- **The soundness error of the deployed Pallas kimchi verifier.** The Pallas-side
twin of `kimchiVesta_sound_error`: `kimchiBundle_sound_error` through the Pallas
bridge, over `Fq`/`IpaPallas`. Project-local: the Pallas error-constant root. -/
theorem kimchiPallas_sound_error (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → IpaPallas.Point)
    (T : KimchiBatchAcc IpaPallas.curve σ idx vk.comms wC)
    (tOf : Fq → Fq → Fq → Polynomial Fq)
    (htdeg : ∀ β γ α, (tOf β γ α).natDegree < 7 * n) :
    ∃ badTuples : Finset (Fq × Fq × Fq × Fq),
      badTuples.card ≤ soundnessErrorBound n idx.zkRows * Fintype.card Fq ^ 3
      ∧ ∀ β γ α ζ : Fq, (β, γ, α, ζ) ∉ badTuples →
          ∀ (E : Fin 43 → Fin 2 → Fq) (ξ : Fin 43 → Fq) (r : Fin 2 → Fq)
            (A : Fin 43 → Fin 2 → Prop),
            Function.Injective ξ → Function.Injective r →
            (∀ (i : Fin 43) (j : Fin 2),
              FiatShamirTreeB σ (combinedCommitment (ξ i) (batchC wC T.zC vk.comms))
                (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
                (combinedInnerProduct (ξ i) (r j) E) (A i j)) →
            (∀ i j, A i j) →
            (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
                * (idx.sigmaPoly 6).eval ζ
              - (ζ ^ n - 1) * (tOf β γ α).eval ζ
              = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                  ζ (-((idx.pubPoly (pubView idx pub)).eval ζ)) (claimedEvals E)) →
            ∃ wTab : Fin n → Fin 15 → Fq, Satisfies idx (pubView idx pub) wTab :=
  kimchiBundle_sound_error σ idx hk hbind vk.comms hvk (pubView idx pub) wC
    (kimchiBatchAcc_bundle_pallas (pubView idx pub) T) tOf htdeg

end Kimchi.Verifier
