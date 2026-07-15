import Mathlib
import Kimchi.Verifier.KimchiSound
import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Reflection
import Kimchi.Verifier.Reflect
import Kimchi.Quotient.Rectangle

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

The file ends with the **grid-from-density layer** (forking stage (a)): the
combinatorial core of the forking lemma, PROVED — no new axiom. `batchAcceptSet` is the
accepting set of a batch-opening *strategy* `P : (ξ, r) ↦ opening proof` for one fixed
batched claim; the K×2 rectangle theorem (`exists_rectangle`, the heavy-rows /
Kővári–Sós–Turán counting idea) turns a density hypothesis on that set into the 43×2
extraction grid (`kimchiBatchAcc_of_density`), and the density capstones
`kimchi{Vesta,Pallas}_sound_density` restate the concrete capstones with the grid
HYPOTHESIS replaced by strategy + density. What remains hypothesis there: the density
itself, DL-binding, and the key correspondence (plus, at the run level only, the
quotient residue); Fiat–Shamir stays with the poseidon axioms, consumed per grid node
exactly as in the 1.3b capstones. The `[Fintype]` instances live only in this counting
layer, never on a core statement.

Finally, the **algebraic-prover reading** (the AGM corollary):
`kimchiProof_sound_algebraic` and its curve roots `kimchi{Vesta,Pallas}_sound_algebraic`
quantify over provers that SUPPLY SRS-basis representations `aw₀`/`ρw₀` of their
committed rows (the algebraic-group-model idiom), so a SINGLE accepted IPA opening
suffices — no grid, no density. The content delivered here: representations + ONE
accepted opening ⟹ the per-row eval pins (`eval_pins_of_opening`), replacing the
special-soundness grid; the pins land in `kimchiProof_sound_of_openings`' consumer
verbatim. Two new bad axes appear — the combination challenges `(ξ, r)` — with
proved-small bad sets (≤ 84 and ≤ 1, counting SZ via `SZ.badComb`), curried by the
consumer data `(E, ζ)`/`(E, ζ, ξ)` so they are quantified BEFORE `(ξ, r)`. Honest scope
note: this corollary KEEPS the ft/quotient identity `hteq` (and `t`, `t.natDegree`) as a
hypothesis — the same residue as the run-level capstones. The AGM also dissolves that
residue by extracting `t` from the `tComm` representation via the Maller relation; that
"algebraic quotient" step is a deliberate follow-on, not this layer. The standard-model
statement remains `*_sound_density`.

The **algebraic quotient** (the follow-on the AGM section promises) is delivered at the
end of the file: `kimchiProof_sound_algebraic_ft` and its curve roots
`kimchi{Vesta,Pallas}_sound_algebraic_ft`. The algebraic prover additionally supplies
the 7 `tComm`-chunk representations, and the quotient `t` — now the genuine
degree-`< 7n` assembly `ftChunkAssembly` of the committed chunks — and the Maller/ft
identity `hteq` are DERIVED from a checked ft opening via `ft_identity_of_chunks`; the
residue hypotheses disappear from the statement. What stays hypothetical there is
unchanged from the AGM corollary: the ft opening itself (which a fully deployed variant
would derive from `poseidon_fiat_shamir` on the ft row), DL-binding, the key
correspondence, and the per-transcript Fiat–Shamir families.
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

/-! ## The grid from density (forking stage (a))

The combinatorial core of the forking lemma (BCC+16 Theorem 6, Bulletproofs Theorem 6),
PROVED — no new axiom: a prover *strategy* `P : (ξ, r) ↦ opening proof` for one fixed
batched claim that the deployed verifier accepts on enough `(ξ, r)` pairs yields the
43×2 extraction grid `KimchiBatchAcc`, hence the full capstone conclusions. The engine
is `Kimchi.Quotient.exists_rectangle` (`Kimchi/Quotient/Rectangle.lean`), a K×2
combinatorial rectangle inside a dense subset of a product —
the heavy-rows / Zarankiewicz / Kővári–Sós–Turán counting idea: Cauchy–Schwarz over
the row degrees bounds the ordered-distinct-column-pair count from below, and
pigeonhole over the `|β|·(|β|−1)` ordered pairs hands one pair shared by `K` distinct
rows. Extracting a K×2 PRODUCT grid costs a quadratic (√) density threshold: the
`(K−1)·|α|·|β|·(|β|−1) < |S|·(|S|−|α|)` hypothesis asks for accepting density
`≳ √(42/|F|)` — about `2⁻¹²⁴` at the `≈ 2²⁵⁴` Pasta scalar fields — versus the
`~ K·|α|·|β|`-count threshold of a (K,2)-TREE of transcripts, which is why the bound is
what it is. What remains hypothesis in the density capstones: the density itself,
DL-binding (`hbind`), and the key correspondence (`hvk`); Fiat–Shamir stays with the
poseidon axioms, consumed per grid node exactly as in the 1.3b capstones. The
`[Fintype]` instances belong to this counting layer only — no core statement grows one.
-/

/-- The accepting set of a batch-opening strategy: the (ξ, r) pairs at which the
deployed verifier accepts the strategy's opening of the fixed batch (cs, es) at the two
points. The membership predicate is the deployed acceptance `Ipa.verify … = true`
itself — a `Bool` equality, decidable without ever reducing `Ipa.verify`. Project-local:
the strategy-side object the density capstones count. -/
def batchAcceptSet (C : Ipa.CommitmentCurve) [Module C.ScalarField C.Point]
    (σ : SRS C.Point) (cs : Array C.Point) (es : Array (Array C.ScalarField))
    (x₀ x₁ : C.ScalarField) (P : C.ScalarField → C.ScalarField → Ipa.Proof C)
    [Fintype C.ScalarField] [DecidableEq C.ScalarField] :
    Finset (C.ScalarField × C.ScalarField) :=
  Finset.univ.filter fun p =>
    Ipa.verify C σ (Ipa.mkInput C cs #[x₀, x₁] es p.1 p.2 (P p.1 p.2)) = true

/-- **The grid from density**: a strategy accepted on enough (ξ, r) pairs yields the
accumulated grid — the forking lemma's combinatorial stage, proved. 42 = 43 − 1; the
threshold is the `exists_rectangle` one at K = 43. The grid is built with the local
`zC` literally as its accumulator field, so the conclusion pins `T.zC = zC` by `rfl` —
exactly the link the density capstones need to state their conclusions at the local
batch assembly `batchC wC zC comms`. Project-local: the stage-(a) bridge from strategy
+ density to the special-soundness hypothesis of the concrete capstones. -/
theorem kimchiBatchAcc_of_density (C : Ipa.CommitmentCurve)
    [Module C.ScalarField C.Point] [Fintype C.ScalarField] [DecidableEq C.ScalarField]
    {n : ℕ} [NeZero n] (σ : SRS C.Point) (idx : Index C.ScalarField n)
    (comms : IndexComms C.Point) (wC : Fin 15 → C.Point) (zC : C.Point)
    (ζ₀ : C.ScalarField) (E₀ : Fin 43 → Fin 2 → C.ScalarField)
    (cs : Array C.Point) (hcsSize : cs.size = 43)
    (hcs : ∀ i : Fin 43, cs.getD (i : ℕ) 0 = batchC wC zC comms i)
    (es : Array (Array C.ScalarField))
    (hes : ∀ (i : Fin 43) (j : Fin 2), (es[(i : ℕ)]!)[(j : ℕ)]! = E₀ i j)
    (P : C.ScalarField → C.ScalarField → Ipa.Proof C)
    (hdens : 42 * Fintype.card C.ScalarField
        * (Fintype.card C.ScalarField * (Fintype.card C.ScalarField - 1))
        < (batchAcceptSet C σ cs es ζ₀ (idx.omega * ζ₀) P).card
          * ((batchAcceptSet C σ cs es ζ₀ (idx.omega * ζ₀) P).card
              - Fintype.card C.ScalarField)) :
    ∃ T : KimchiBatchAcc C σ idx comms wC, T.zC = zC := by
  obtain ⟨ξ₀, b₁, b₂, hξ, hbne, hmem⟩ :=
    Kimchi.Quotient.exists_rectangle
      (batchAcceptSet C σ cs es ζ₀ (idx.omega * ζ₀) P) 43 (by
      have h42 : (43 : ℕ) - 1 = 42 := rfl
      rw [h42]
      exact hdens)
  have hr : Function.Injective ![b₁, b₂] := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all
  have hacc : ∀ (i : Fin 43) (j : Fin 2),
      Ipa.verify C σ (Ipa.mkInput C cs #[ζ₀, idx.omega * ζ₀] es (ξ₀ i) (![b₁, b₂] j)
        (P (ξ₀ i) (![b₁, b₂] j))) = true := by
    intro i j
    fin_cases j
    · simpa [batchAcceptSet, Finset.mem_filter] using (hmem i).1
    · simpa [batchAcceptSet, Finset.mem_filter] using (hmem i).2
  exact ⟨⟨zC, ζ₀, E₀, ξ₀, hξ, ![b₁, b₂], hr, cs, hcsSize, hcs, es, hes,
    fun i j => P (ξ₀ i) (![b₁, b₂] j), hacc⟩, rfl⟩

/-- **Density soundness of the deployed Vesta kimchi verifier** (forking stage (a)):
`kimchiVesta_sound` with the grid HYPOTHESIS replaced by strategy + density — a
batch-opening strategy `P` whose accepting set at the reference points `(ζ₀, ω·ζ₀)` is
dense enough (`hdens`, the `exists_rectangle` threshold at K = 43: accepting density
`≳ √(42/|F|)`, about `2⁻¹²⁴` at the Pasta scalar field) yields the four bad sets and
the guarded consumer implication, VERBATIM the 1.3b conclusion at the LOCAL batch
assembly `batchC wC zC vk.comms`. No `KimchiBatchAcc` appears among the hypotheses:
the grid is constructed by `kimchiBatchAcc_of_density`. The trust story is otherwise
`kimchiVesta_sound`'s — `poseidon_fiat_shamir_vesta` per grid node, DL-binding, key
correspondence. Project-local: the Vesta density root. -/
theorem kimchiVesta_sound_density (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → IpaVesta.Point) (zC : IpaVesta.Point) (ζ₀ : Fp)
    (E₀ : Fin 43 → Fin 2 → Fp)
    (cs : Array IpaVesta.Point) (hcsSize : cs.size = 43)
    (hcs : ∀ i : Fin 43, cs.getD (i : ℕ) 0 = batchC wC zC vk.comms i)
    (es : Array (Array Fp))
    (hes : ∀ (i : Fin 43) (j : Fin 2), (es[(i : ℕ)]!)[(j : ℕ)]! = E₀ i j)
    (P : Fp → Fp → Ipa.Proof IpaVesta.curve)
    (hdens : 42 * Fintype.card IpaVesta.curve.ScalarField
        * (Fintype.card IpaVesta.curve.ScalarField
            * (Fintype.card IpaVesta.curve.ScalarField - 1))
        < (batchAcceptSet IpaVesta.curve σ cs es ζ₀ (idx.omega * ζ₀) P).card
          * ((batchAcceptSet IpaVesta.curve σ cs es ζ₀ (idx.omega * ζ₀) P).card
              - Fintype.card IpaVesta.curve.ScalarField)) :
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
            FiatShamirTreeB σ (combinedCommitment (ξ i) (batchC wC zC vk.comms))
              (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
              (combinedInnerProduct (ξ i) (r j) E) (A i j)) →
          (∀ i j, A i j) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly (pubView idx pub)).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → Fp, Satisfies idx (pubView idx pub) wTab := by
  obtain ⟨T, hzC⟩ := kimchiBatchAcc_of_density IpaVesta.curve σ idx vk.comms wC zC
    ζ₀ E₀ cs hcsSize hcs es hes P hdens
  rw [← hzC]
  exact kimchiVesta_sound σ vk pub idx hk hvk hpub hbind wC T

/-- **Density soundness of the deployed Pallas kimchi verifier.** The Pallas-side twin
of `kimchiVesta_sound_density`: strategy + density yield the VERBATIM 1.3b conclusion
of `kimchiPallas_sound` at the LOCAL batch assembly `batchC wC zC vk.comms`, over
`Fq`/`IpaPallas`, the per-node Fiat–Shamir from `poseidon_fiat_shamir_pallas`.
Project-local: the Pallas density root. -/
theorem kimchiPallas_sound_density (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → IpaPallas.Point) (zC : IpaPallas.Point) (ζ₀ : Fq)
    (E₀ : Fin 43 → Fin 2 → Fq)
    (cs : Array IpaPallas.Point) (hcsSize : cs.size = 43)
    (hcs : ∀ i : Fin 43, cs.getD (i : ℕ) 0 = batchC wC zC vk.comms i)
    (es : Array (Array Fq))
    (hes : ∀ (i : Fin 43) (j : Fin 2), (es[(i : ℕ)]!)[(j : ℕ)]! = E₀ i j)
    (P : Fq → Fq → Ipa.Proof IpaPallas.curve)
    (hdens : 42 * Fintype.card IpaPallas.curve.ScalarField
        * (Fintype.card IpaPallas.curve.ScalarField
            * (Fintype.card IpaPallas.curve.ScalarField - 1))
        < (batchAcceptSet IpaPallas.curve σ cs es ζ₀ (idx.omega * ζ₀) P).card
          * ((batchAcceptSet IpaPallas.curve σ cs es ζ₀ (idx.omega * ζ₀) P).card
              - Fintype.card IpaPallas.curve.ScalarField)) :
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
            FiatShamirTreeB σ (combinedCommitment (ξ i) (batchC wC zC vk.comms))
              (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
              (combinedInnerProduct (ξ i) (r j) E) (A i j)) →
          (∀ i j, A i j) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly (pubView idx pub)).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → Fq, Satisfies idx (pubView idx pub) wTab := by
  obtain ⟨T, hzC⟩ := kimchiBatchAcc_of_density IpaPallas.curve σ idx vk.comms wC zC
    ζ₀ E₀ cs hcsSize hcs es hes P hdens
  rw [← hzC]
  exact kimchiPallas_sound σ vk pub idx hk hvk hpub hbind wC T

/-! ## The algebraic-prover corollary (the AGM reading)

An ALGEBRAIC prover carries, with each commitment it sends, an SRS-basis representation
of the committed data — here the witness pairs `aw₀`/`ρw₀` with
`commit σ (aw₀ i) (ρw₀ i) = batchC wC zC comms i`. Those representations discharge the
REFERENCE side of `kimchiProof_sound_of_openings` outright, and the bridge below
(`eval_pins_of_opening`) discharges its CONSUMER side from ONE accepted batch opening:
by commitment linearity the combined commitment is the commitment of the ξ-combined
representation; by binding the opened witness IS that combination; substituting into the
opening's value equation leaves the single field identity
`∑ i, ξ^i · (∑ j, D i j · r^j) = 0` in the discrepancies
`D i j = E i j − ⟨aw₀ i, evalVector (x j)⟩`, and two counting-Schwartz–Zippel steps
(`SZ.badComb`, first at `r`, then at `ξ`) kill every `D i j` — the eval pins. The bad
`(ξ, r)` sets are COUNTED, never assumed: `badXiOf` (≤ 84 = 2·(43−1)) depends only on
`(σ, aw₀, x, E)`, `badROf` (≤ 1 = 2−1) additionally on `ξ` — neither mentions the
challenge it guards, which is what lets the capstones quantify them BEFORE `(ξ, r)`. -/

/-- The bad row-combination challenges of one claimed-vs-represented evaluation matrix:
the union over the two eval points of the counting-SZ bad sets of the discrepancy
columns `i ↦ E i j − ⟨aw₀ i, evalVector (x j)⟩`. Depends only on `(σ, aw₀, x, E)` —
never on `ξ` or `r` (anti-vacuity: the capstone quantifies it before both). -/
private noncomputable def badXiOf {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G) (aw₀ : Fin 43 → Fin (2 ^ σ.k) → F)
    (x : Fin 2 → F) (E : Fin 43 → Fin 2 → F) : Finset F :=
  Kimchi.Quotient.SZ.badComb
      (fun i : Fin 43 => E i 0 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 0)))
    ∪ Kimchi.Quotient.SZ.badComb
      (fun i : Fin 43 => E i 1 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 1)))

/-- The bad point-combination challenges at a fixed `ξ`: the counting-SZ bad set of the
two ξ-combined discrepancy columns. Depends on `(σ, aw₀, x, E, ξ)` — never on `r`. -/
private noncomputable def badROf {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G) (aw₀ : Fin 43 → Fin (2 ^ σ.k) → F)
    (x : Fin 2 → F) (E : Fin 43 → Fin 2 → F) (ξ : F) : Finset F :=
  Kimchi.Quotient.SZ.badComb (fun j : Fin 2 => ∑ i : Fin 43,
    ξ ^ (i : ℕ) * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))))

/-- `badXiOf` counts at most `84 = 2 · (43 − 1)` challenges: a union of two counting-SZ
bad sets over `Fin 43`. -/
private theorem card_badXiOf_le {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G) (aw₀ : Fin 43 → Fin (2 ^ σ.k) → F)
    (x : Fin 2 → F) (E : Fin 43 → Fin 2 → F) : (badXiOf σ aw₀ x E).card ≤ 84 := by
  unfold badXiOf
  refine le_trans (Finset.card_union_le _ _) ?_
  have h0 := Kimchi.Quotient.SZ.card_badComb_le
    (fun i : Fin 43 => E i 0 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 0)))
  have h1 := Kimchi.Quotient.SZ.card_badComb_le
    (fun i : Fin 43 => E i 1 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 1)))
  omega

/-- `badROf` counts at most `1 = 2 − 1` challenge: one counting-SZ bad set over
`Fin 2`. -/
private theorem card_badROf_le {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G) (aw₀ : Fin 43 → Fin (2 ^ σ.k) → F)
    (x : Fin 2 → F) (E : Fin 43 → Fin 2 → F) (ξ : F) :
    (badROf σ aw₀ x E ξ).card ≤ 1 := by
  unfold badROf
  exact Kimchi.Quotient.SZ.card_badComb_le _

/-- **The eval pins from one opening** (the AGM bridge): SRS-basis representations of
the 43 batch rows plus ONE accepted batch opening at good `(ξ, r)` pin every claimed
evaluation to the represented row's true evaluation. Linearity collapses the combined
commitment to one commitment of the ξ-combined representation (`commitₗ`, `map_sum`);
binding (`hbind`, through `commitmentBinding_iff_no_relation`) forces the opened witness
to BE that combination; the opening's value equation then reduces to
`∑ j, r^j · (∑ i, ξ^i · D i j) = 0` in the discrepancies `D`, and
`SZ.eq_zero_of_comb_eq_zero` — first at `r`, then per point at `ξ` — kills every
`D i j`. -/
private theorem eval_pins_of_opening {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (wh : F), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (C : Fin 43 → G) (x : Fin 2 → F)
    (aw₀ : Fin 43 → Fin (2 ^ σ.k) → F) (ρw₀ : Fin 43 → F)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = C i)
    (E : Fin 43 → Fin 2 → F) (ξ r : F)
    (hξ : ξ ∉ badXiOf σ aw₀ x E) (hr : r ∉ badROf σ aw₀ x E ξ)
    (a : Fin (2 ^ σ.k) → F) (ρ : F)
    (hopen : openingRelationB σ (combinedCommitment ξ C)
      (combinedEvalVector (2 ^ σ.k) r x) (combinedInnerProduct ξ r E) a ρ) :
    ∀ (i : Fin 43) (j : Fin 2),
      E i j = innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)) := by
  -- Step A (linearity): the combined commitment is ONE commitment of the ξ-combined
  -- representation — `map_sum` of `commitₗ` at `Fin 43`, mirroring `commit_combine`.
  have hpair : (∑ i : Fin 43, ξ ^ (i : ℕ)
        • ((aw₀ i, ρw₀ i) : (Fin (2 ^ σ.k) → F) × F))
      = (∑ i : Fin 43, ξ ^ (i : ℕ) • aw₀ i, ∑ i : Fin 43, ξ ^ (i : ℕ) • ρw₀ i) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    · rw [Prod.snd_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
  have hA : combinedCommitment ξ C
      = commit σ (∑ i : Fin 43, ξ ^ (i : ℕ) • aw₀ i)
          (∑ i : Fin 43, ξ ^ (i : ℕ) • ρw₀ i) := by
    calc combinedCommitment ξ C
        = ∑ i : Fin 43, ξ ^ (i : ℕ) • commit σ (aw₀ i) (ρw₀ i) := by
          unfold combinedCommitment
          exact Finset.sum_congr rfl fun i _ => by rw [hrep i]
      _ = commitₗ σ (∑ i : Fin 43, ξ ^ (i : ℕ)
            • ((aw₀ i, ρw₀ i) : (Fin (2 ^ σ.k) → F) × F)) := by
          rw [map_sum]
          simp only [map_smul]
          rfl
      _ = commit σ (∑ i : Fin 43, ξ ^ (i : ℕ) • aw₀ i)
            (∑ i : Fin 43, ξ ^ (i : ℕ) • ρw₀ i) := by rw [hpair]; rfl
  -- Step B (binding): the opened witness IS the ξ-combined representation — the
  -- interior of `bound_unique`, kept at witness level via `congrArg Prod.fst`.
  have hbd : CommitmentBinding (F := F) σ :=
    (commitmentBinding_iff_no_relation σ).mpr hbind
  have hcommit : commit σ a ρ
      = commit σ (∑ i : Fin 43, ξ ^ (i : ℕ) • aw₀ i)
          (∑ i : Fin 43, ξ ^ (i : ℕ) • ρw₀ i) := hopen.1.trans hA
  have ha : a = ∑ i : Fin 43, ξ ^ (i : ℕ) • aw₀ i :=
    congrArg Prod.fst (@hbd (a, ρ)
      (∑ i : Fin 43, ξ ^ (i : ℕ) • aw₀ i, ∑ i : Fin 43, ξ ^ (i : ℕ) • ρw₀ i) hcommit)
  -- Step C (substitute + expand): the value equation becomes the double-sum identity
  -- `∑ j, r^j · (∑ i, ξ^i · D i j) = 0` in the discrepancies `D`.
  have hip : ∀ b : Fin (2 ^ σ.k) → F,
      innerProduct (∑ i : Fin 43, ξ ^ (i : ℕ) • aw₀ i) b
        = ∑ i : Fin 43, ξ ^ (i : ℕ) * innerProduct (aw₀ i) b := by
    intro b
    unfold innerProduct
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have h1 : combinedInnerProduct ξ r E
      = ∑ j : Fin 2, r ^ (j : ℕ)
          * ∑ i : Fin 43, ξ ^ (i : ℕ)
              * innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)) := by
    rw [hopen.2, ha, innerProduct_combinedEvalVector]
    exact Finset.sum_congr rfl fun j _ => by rw [hip]
  have h2 : combinedInnerProduct ξ r E
      = ∑ j : Fin 2, r ^ (j : ℕ) * ∑ i : Fin 43, ξ ^ (i : ℕ) * E i j := by
    unfold combinedInnerProduct
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hsum : ∑ j : Fin 2, r ^ (j : ℕ) * (∑ i : Fin 43, ξ ^ (i : ℕ)
      * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)))) = 0 := by
    calc ∑ j : Fin 2, r ^ (j : ℕ) * (∑ i : Fin 43, ξ ^ (i : ℕ)
          * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))))
        = (∑ j : Fin 2, r ^ (j : ℕ) * ∑ i : Fin 43, ξ ^ (i : ℕ) * E i j)
          - ∑ j : Fin 2, r ^ (j : ℕ) * ∑ i : Fin 43, ξ ^ (i : ℕ)
              * innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_sub, ← Finset.sum_sub_distrib]
          refine congrArg (r ^ (j : ℕ) * ·)
            (Finset.sum_congr rfl fun i _ => ?_)
          ring
      _ = 0 := by rw [← h2, ← h1, sub_self]
  -- Step D (iterated counting SZ): first at `r` (the two point-columns), then per
  -- point at `ξ` (the 43 row-discrepancies).
  simp only [badROf] at hr
  have hcol : ∀ j : Fin 2, ∑ i : Fin 43, ξ ^ (i : ℕ)
      * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))) = 0 :=
    Kimchi.Quotient.SZ.eq_zero_of_comb_eq_zero _ r hr hsum
  simp only [badXiOf, Finset.notMem_union] at hξ
  intro i j
  have hj : ξ ∉ Kimchi.Quotient.SZ.badComb (fun i : Fin 43 =>
      E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))) := by
    fin_cases j
    · exact hξ.1
    · exact hξ.2
  exact sub_eq_zero.mp (Kimchi.Quotient.SZ.eq_zero_of_comb_eq_zero _ ξ hj (hcol j) i)

/-- **Algebraic-prover soundness from ONE transcript** (the AGM corollary): the
representations `aw₀`/`ρw₀` of the 43 batch rows discharge the openings interface of
`kimchiProof_sound_of_openings` on BOTH sides — the reference side outright (`hrep` IS
its `hbound₀`), the consumer side from a single accepted opening via
`ipa_soundnessA` + `eval_pins_of_opening`. The four bad-set bounds and the
ft-equation/`Satisfies` tail are verbatim `of_openings`'; the only new axis is the
combination-challenge pair `(ξ, r)`, guarded by the counted sets `badXi` (≤ 84) and
`badR` (≤ 1), curried by the consumer data `(E, ζ)`/`(E, ζ, ξ)` and quantified BEFORE
`(ξ, r)` — anti-vacuity exactly as for the four challenge axes. Honest scope note: the
quotient identity `hteq` (with `t` and its degree bound) REMAINS a hypothesis — the same
residue as the run-level capstones; dissolving it from the `tComm` representation via
the Maller relation is the follow-on "algebraic quotient" step. Model note: this theorem
quantifies over provers that SUPPLY representations; the standard-model statement is
`*_sound_density`. Project-local: the general AGM root. -/
theorem kimchiProof_sound_algebraic {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F)
    (wC : Fin 15 → G) (zC : G)
    (aw₀ : Fin 43 → Fin (2 ^ σ.k) → F) (ρw₀ : Fin 43 → F)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = batchC wC zC comms i) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F)
        (badXi : (Fin 43 → Fin 2 → F) → F → Finset F)
        (badR : (Fin 43 → Fin 2 → F) → F → F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n)
        ∧ (∀ (E : Fin 43 → Fin 2 → F) (ζ : F), (badXi E ζ).card ≤ 84)
        ∧ (∀ (E : Fin 43 → Fin 2 → F) (ζ ξ : F), (badR E ζ ξ).card ≤ 1))
      ∧ ∀ (β γ α : F) (t : Polynomial F) (ζ : F)
          (E : Fin 43 → Fin 2 → F) (ξ r : F) (A : Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          ξ ∉ badXi E ζ → r ∉ badR E ζ ξ →
          FiatShamirTreeB σ (combinedCommitment ξ (batchC wC zC comms))
            (combinedEvalVector (2 ^ σ.k) r ![ζ, idx.omega * ζ])
            (combinedInnerProduct ξ r E) A →
          A →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → F, Satisfies idx pub wTab := by
  obtain ⟨badB, badG, badA, badZ, ⟨hB, hG, hA, hZ⟩, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hk hbind comms hvk pub wC zC aw₀ ρw₀ hrep
  refine ⟨badB, badG, badA, badZ,
    fun E ζ => badXiOf σ aw₀ ![ζ, idx.omega * ζ] E,
    fun E ζ ξ => badROf σ aw₀ ![ζ, idx.omega * ζ] E ξ,
    ⟨hB, hG, hA, hZ, fun E ζ => card_badXiOf_le σ aw₀ ![ζ, idx.omega * ζ] E,
      fun E ζ ξ => card_badROf_le σ aw₀ ![ζ, idx.omega * ζ] E ξ⟩, ?_⟩
  intro β γ α t ζ E ξ r A hβ hγ hα hζ hζ1 hζb ht hξ hr hFS hAcc hteq
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _ hFS hAcc
  have hpins := eval_pins_of_opening σ hbind (batchC wC zC comms)
    ![ζ, idx.omega * ζ] aw₀ ρw₀ hrep E ξ r hξ hr a ρ hopen
  exact himp β γ α t ζ E aw₀ ρw₀ hβ hγ hα hζ hζ1 hζb ht
    (fun i => ⟨hrep i, fun j => hpins i j⟩) hteq

/-- **Algebraic-prover soundness of the deployed Vesta kimchi verifier** (the Vesta AGM
root): `kimchiProof_sound_algebraic` at the wire views — the wire key's committed
columns (`vk.comms`), the wire public array (`pubView idx pub`, made honest by `hpub`).
An algebraic prover's representations of the 43 batch rows replace the
special-soundness grid: ONE accepted IPA opening (the `FiatShamirTreeB` antecedent +
`A`, exactly as the general theorem exposes them — the caller supplies the accepted
transcript) delivers the consumer implication. Honest scope note: the quotient identity
`hteq` (with `t` and its degree bound) remains a hypothesis, as in the run-level
capstones; the standard-model statement is `kimchiVesta_sound_density`. Project-local:
the Vesta AGM root. -/
theorem kimchiVesta_sound_algebraic (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → IpaVesta.Point) (zC : IpaVesta.Point)
    (aw₀ : Fin 43 → Fin (2 ^ σ.k) → Fp) (ρw₀ : Fin 43 → Fp)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = batchC wC zC vk.comms i) :
    ∃ (badB : Finset Fp) (badG : Fp → Finset Fp) (badA : Fp → Fp → Finset Fp)
        (badZ : Fp → Fp → Fp → Polynomial Fp → Finset Fp)
        (badXi : (Fin 43 → Fin 2 → Fp) → Fp → Finset Fp)
        (badR : (Fin 43 → Fin 2 → Fp) → Fp → Fp → Finset Fp),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fp), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n)
        ∧ (∀ (E : Fin 43 → Fin 2 → Fp) (ζ : Fp), (badXi E ζ).card ≤ 84)
        ∧ (∀ (E : Fin 43 → Fin 2 → Fp) (ζ ξ : Fp), (badR E ζ ξ).card ≤ 1))
      ∧ ∀ (β γ α : Fp) (t : Polynomial Fp) (ζ : Fp)
          (E : Fin 43 → Fin 2 → Fp) (ξ r : Fp) (A : Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          ξ ∉ badXi E ζ → r ∉ badR E ζ ξ →
          FiatShamirTreeB σ (combinedCommitment ξ (batchC wC zC vk.comms))
            (combinedEvalVector (2 ^ σ.k) r ![ζ, idx.omega * ζ])
            (combinedInnerProduct ξ r E) A →
          A →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly (pubView idx pub)).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → Fp, Satisfies idx (pubView idx pub) wTab :=
  kimchiProof_sound_algebraic σ idx hk hbind vk.comms hvk (pubView idx pub) wC zC
    aw₀ ρw₀ hrep

/-- **Algebraic-prover soundness of the deployed Pallas kimchi verifier.** The
Pallas-side twin of `kimchiVesta_sound_algebraic`, over `Fq`/`IpaPallas`. See the Vesta
docstring for the trust story — in particular the quotient residue `hteq`, the one
antecedent the AGM reading keeps. Project-local: the Pallas AGM root. -/
theorem kimchiPallas_sound_algebraic (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → IpaPallas.Point) (zC : IpaPallas.Point)
    (aw₀ : Fin 43 → Fin (2 ^ σ.k) → Fq) (ρw₀ : Fin 43 → Fq)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = batchC wC zC vk.comms i) :
    ∃ (badB : Finset Fq) (badG : Fq → Finset Fq) (badA : Fq → Fq → Finset Fq)
        (badZ : Fq → Fq → Fq → Polynomial Fq → Finset Fq)
        (badXi : (Fin 43 → Fin 2 → Fq) → Fq → Finset Fq)
        (badR : (Fin 43 → Fin 2 → Fq) → Fq → Fq → Finset Fq),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fq), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n)
        ∧ (∀ (E : Fin 43 → Fin 2 → Fq) (ζ : Fq), (badXi E ζ).card ≤ 84)
        ∧ (∀ (E : Fin 43 → Fin 2 → Fq) (ζ ξ : Fq), (badR E ζ ξ).card ≤ 1))
      ∧ ∀ (β γ α : Fq) (t : Polynomial Fq) (ζ : Fq)
          (E : Fin 43 → Fin 2 → Fq) (ξ r : Fq) (A : Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          ξ ∉ badXi E ζ → r ∉ badR E ζ ξ →
          FiatShamirTreeB σ (combinedCommitment ξ (batchC wC zC vk.comms))
            (combinedEvalVector (2 ^ σ.k) r ![ζ, idx.omega * ζ])
            (combinedInnerProduct ξ r E) A →
          A →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly (pubView idx pub)).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → Fq, Satisfies idx (pubView idx pub) wTab :=
  kimchiProof_sound_algebraic σ idx hk hbind vk.comms hvk (pubView idx pub) wC zC
    aw₀ ρw₀ hrep

/-! ## The algebraic quotient — the ft residue dissolved from the chunk representations -/

/-- **The assembled quotient** — the genuine degree-`< 7·2^k` polynomial the 7 committed
`tComm` chunk rows represent: chunk `j` contributes its row polynomial shifted by
`X^(j·2^k)`, exactly kimchi's `t = ∑ⱼ X^(j·n) · tⱼ` chunking (`Chunk.lean`'s
`assemblePoly` at width `2^k`, phrased over `rowPoly` so the capstone statements read at
the committed vectors directly). Project-local: the named `t` of the residue-free
capstones — the `badZ` antecedent and the derived Maller identity are stated against THIS
polynomial, never an opaque existential witness. -/
noncomputable def ftChunkAssembly {F : Type*} [Field F] (k : ℕ)
    (aT : Fin 7 → Fin (2 ^ k) → F) : Polynomial F :=
  ∑ j : Fin 7, rowPoly (aT j) * Polynomial.X ^ ((j : ℕ) * 2 ^ k)

/-- The assembly meets the 7-chunk degree bound: each summand has degree
`≤ (2^k − 1) + j·2^k ≤ 7·2^k − 1`. -/
private theorem ftChunkAssembly_natDegree_lt {F : Type*} [Field F] (k : ℕ)
    (aT : Fin 7 → Fin (2 ^ k) → F) :
    (ftChunkAssembly k aT).natDegree < 7 * 2 ^ k := by
  have h2k : 0 < 2 ^ k := Nat.two_pow_pos k
  have hle : (ftChunkAssembly k aT).natDegree ≤ 7 * 2 ^ k - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine le_trans (natDegree_mul_le) ?_
    rw [natDegree_X_pow]
    have hrow := rowPoly_natDegree_lt_two_pow (aT j)
    have hj : (j : ℕ) ≤ 6 := by omega
    have hjm : (j : ℕ) * 2 ^ k ≤ 6 * 2 ^ k := Nat.mul_le_mul_right _ hj
    omega
  omega

/-- The assembly evaluates as the `(ζ^(2^k))`-power combination of the chunk-row
evaluations — kimchi's `combined_inner_product` recombination, at the assembly. -/
private theorem ftChunkAssembly_eval {F : Type*} [Field F] (k : ℕ)
    (aT : Fin 7 → Fin (2 ^ k) → F) (ζ : F) :
    (ftChunkAssembly k aT).eval ζ
      = ∑ j : Fin 7, (ζ ^ 2 ^ k) ^ (j : ℕ) * (rowPoly (aT j)).eval ζ := by
  unfold ftChunkAssembly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_pow, eval_X, mul_comm ((j : ℕ)) (2 ^ k), pow_mul]
  ring

/-- **The Maller/ft identity from the chunk representations** (the algebraic-quotient
engine): representations of the 7 `tComm` chunks plus ONE accepted ft opening — the
commitment equation `hcommit` (the verifier's ft row: `pScalar • Cσ6` minus the
`(ζ^n − 1)`-scaled `(ζ^n)`-power combination of the chunk commitments) and its value
equation `heval` — pin the opened row, via binding (`commitₗ`-linearity collapses the
combination to ONE commitment, exactly as in `eval_pins_of_opening`), to the
corresponding pointwise combination of the represented rows; reading that combination
through `rowPoly` yields BOTH residue facts at once: the assembled quotient's degree
bound `< 7n` and the ft equation `pScalar · σ₆(ζ) − (ζ^n − 1) · t(ζ) = v0` with
`t = ftChunkAssembly σ.k aT`. This is `ft_equation` (`Sound.lean`) generalized from its
`nc = 1` degenerate case (degree `< 2^k`, vacuous for the deployed 7-chunk
configuration) to the genuine chunked quotient. -/
private theorem ft_identity_of_chunks {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (σ₆ : Polynomial F) (hσ₆ : σ₆.natDegree < 2 ^ σ.k)
    (Cσ6 : G) (hC : Cσ6 = commitPoly σ σ₆)
    (TC : Fin 7 → G) (aT : Fin 7 → Fin (2 ^ σ.k) → F) (ρT : Fin 7 → F)
    (htc : ∀ j, commit σ (aT j) (ρT j) = TC j)
    (pScalar ζ v0 : F) (n : ℕ) (hk : 2 ^ σ.k = n)
    (a : Fin (2 ^ σ.k) → F) (ρ : F)
    (hcommit : commit σ a ρ
      = pScalar • Cσ6 - (ζ ^ n - 1) • ∑ j : Fin 7, (ζ ^ n) ^ (j : ℕ) • TC j)
    (heval : innerProduct a (evalVector (2 ^ σ.k) ζ) = v0) :
    (ftChunkAssembly σ.k aT).natDegree < 7 * n
      ∧ pScalar * σ₆.eval ζ - (ζ ^ n - 1) * (ftChunkAssembly σ.k aT).eval ζ = v0 := by
  subst hk
  -- Step A: σ₆'s commitment witness — the coefficient vector at blinder `0`.
  set w6 : Fin (2 ^ σ.k) → F := fun i => σ₆.coeff (i : ℕ) with hw6
  have hC6 : Cσ6 = commit σ w6 0 := hC.trans (commitPoly_eq_commit σ σ₆)
  have hip6 : innerProduct w6 (evalVector (2 ^ σ.k) ζ) = σ₆.eval ζ := by
    rw [← rowPoly_eval, rowPoly_coeff_self hσ₆]
  -- Step B: the ft commitment as ONE commitment of the pointwise-combined witness —
  -- `commitₗ`-linearity at the pair family, mirroring `eval_pins_of_opening` Step A.
  set b : Fin (2 ^ σ.k) → F :=
    pScalar • w6 - (ζ ^ 2 ^ σ.k - 1)
      • ∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j with hb
  set ρb : F :=
    -((ζ ^ 2 ^ σ.k - 1) • ∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • ρT j) with hρb
  have hpair : ((b, ρb) : (Fin (2 ^ σ.k) → F) × F)
      = pScalar • ((w6, 0) : (Fin (2 ^ σ.k) → F) × F)
        - (ζ ^ 2 ^ σ.k - 1) • ∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ)
            • ((aT j, ρT j) : (Fin (2 ^ σ.k) → F) × F) := by
    refine Prod.ext ?_ ?_
    · simp only [hb, Prod.fst_sub, Prod.smul_fst, Prod.fst_sum]
    · simp only [hρb, Prod.snd_sub, Prod.smul_snd, Prod.snd_sum, smul_zero, zero_sub]
  have hB : commit σ b ρb
      = pScalar • Cσ6
        - (ζ ^ 2 ^ σ.k - 1) • ∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • TC j := by
    have h0 : commit σ b ρb = commitₗ σ (b, ρb) := rfl
    have h1 : commitₗ σ ((w6, 0) : (Fin (2 ^ σ.k) → F) × F) = commit σ w6 0 := rfl
    rw [h0, hpair, map_sub, map_smul, map_smul, map_sum, h1, ← hC6]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    exact congrArg _ (htc j)
  -- Step C: binding, at witness level — the opened row IS the combination.
  have hbd : CommitmentBinding (F := F) σ :=
    (commitmentBinding_iff_no_relation σ).mpr hbind
  have hab : a = b :=
    congrArg Prod.fst (@hbd (a, ρ) (b, ρb) (hcommit.trans hB.symm))
  refine ⟨ftChunkAssembly_natDegree_lt σ.k aT, ?_⟩
  -- Step E: expand the inner product of `b` linearly and conclude.
  have hsub : innerProduct b (evalVector (2 ^ σ.k) ζ)
      = pScalar * innerProduct w6 (evalVector (2 ^ σ.k) ζ)
        - (ζ ^ 2 ^ σ.k - 1)
          * innerProduct (∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j)
              (evalVector (2 ^ σ.k) ζ) := by
    rw [hb]
    unfold innerProduct
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hipS : innerProduct (∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j)
      (evalVector (2 ^ σ.k) ζ)
      = ∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ)
          * innerProduct (aT j) (evalVector (2 ^ σ.k) ζ) := by
    unfold innerProduct
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [← heval, hab, hsub, hipS, hip6, ftChunkAssembly_eval]
  simp only [rowPoly_eval]

/-- **Algebraic-prover soundness, residue-free** (the algebraic quotient):
`kimchiProof_sound_algebraic` with the ft/quotient residue DISSOLVED — the algebraic
prover additionally supplies the 7 `tComm`-chunk representations (`aT`/`ρT`, tied to the
chunk commitments by `hTC`), and the quotient `t` and the Maller identity `hteq` are
DERIVED, no longer hypotheses. The trade is honest: `hteq` was an unchecked "∃ valid
`t`"; here it is replaced by a CHECKED fact — the ft opening (the two antecedents after
`A`), which the deployed verifier's ft-row acceptance provides — fed to
`ft_identity_of_chunks`. The ft opening is a hypothesis because this abstract capstone
does not reflect a deployed run; a fully deployed AGM variant would derive it from
`poseidon_fiat_shamir` on the ft row. The quotient is now the genuine degree-`< 7n`
polynomial `ftChunkAssembly σ.k aT` assembled from the committed chunks — NOT the
degree-`< 2^k` `ftQuotient` of `ft_equation` (`Sound.lean`), whose `nc = 1` shortcut is
vacuous for the deployed 7-chunk configuration. No-vacuity: an honest 7-chunk prover
satisfies every antecedent — `hCσ6` is discharged by `hvk` (`VKCorresponds` is
`indexerOf`, whose `sigma i` IS `commitPoly σ (idx.sigmaPoly i)`, `Correspond.lean`),
and the honest chunk vectors make `ftChunkAssembly` the real quotient. The six bad-set
bounds and the FS/acceptance/`Satisfies` consumer tail are verbatim
`kimchiProof_sound_algebraic`'s; `ζ ^ n ≠ 1` is the ft non-degeneracy pin.
Project-local: the residue-free AGM root. -/
theorem kimchiProof_sound_algebraic_ft {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F)
    (wC : Fin 15 → G) (zC : G)
    (aw₀ : Fin 43 → Fin (2 ^ σ.k) → F) (ρw₀ : Fin 43 → F)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = batchC wC zC comms i)
    (TC : Fin 7 → G) (aT : Fin 7 → Fin (2 ^ σ.k) → F) (ρT : Fin 7 → F)
    (hTC : ∀ j, commit σ (aT j) (ρT j) = TC j)
    (Cσ6 : G) (hCσ6 : Cσ6 = commitPoly σ (idx.sigmaPoly 6)) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F)
        (badXi : (Fin 43 → Fin 2 → F) → F → Finset F)
        (badR : (Fin 43 → Fin 2 → F) → F → F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n)
        ∧ (∀ (E : Fin 43 → Fin 2 → F) (ζ : F), (badXi E ζ).card ≤ 84)
        ∧ (∀ (E : Fin 43 → Fin 2 → F) (ζ ξ : F), (badR E ζ ξ).card ≤ 1))
      ∧ ∀ (β γ α ζ : F)
          (E : Fin 43 → Fin 2 → F) (ξ r : F) (A : Prop)
          (aft : Fin (2 ^ σ.k) → F) (ρft : F),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ →
          ζ ∉ badZ β γ α (ftChunkAssembly σ.k aT) →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) → ζ ^ n ≠ 1 →
          ξ ∉ badXi E ζ → r ∉ badR E ζ ξ →
          FiatShamirTreeB σ (combinedCommitment ξ (batchC wC zC comms))
            (combinedEvalVector (2 ^ σ.k) r ![ζ, idx.omega * ζ])
            (combinedInnerProduct ξ r E) A →
          A →
          (commit σ aft ρft
            = permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
                • Cσ6 - (ζ ^ n - 1) • ∑ j : Fin 7, (ζ ^ n) ^ (j : ℕ) • TC j) →
          (innerProduct aft (evalVector (2 ^ σ.k) ζ)
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → F, Satisfies idx pub wTab := by
  obtain ⟨badB, badG, badA, badZ, badXi, badR, hbounds, himp⟩ :=
    kimchiProof_sound_algebraic σ idx hk hbind comms hvk pub wC zC aw₀ ρw₀ hrep
  refine ⟨badB, badG, badA, badZ, badXi, badR, hbounds, ?_⟩
  intro β γ α ζ E ξ r A aft ρft hβ hγ hα hζ hζ1 hζb hζn hξ hr hFS hAcc hftc hftv
  have hσ₆ : (idx.sigmaPoly 6).natDegree < 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  obtain ⟨htdeg, hteq⟩ := ft_identity_of_chunks σ hbind (idx.sigmaPoly 6) hσ₆ Cσ6 hCσ6
    TC aT ρT hTC
    (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)) ζ
    (ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ ζ
      (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) n hk aft ρft hftc hftv
  exact himp β γ α (ftChunkAssembly σ.k aT) ζ E ξ r A hβ hγ hα hζ hζ1 hζb htdeg
    hξ hr hFS hAcc hteq

/-- **Residue-free algebraic-prover soundness of the deployed Vesta kimchi verifier**:
`kimchiVesta_sound_algebraic` with the quotient residue dissolved —
`kimchiProof_sound_algebraic_ft` at the wire views (the wire key's committed columns
`vk.comms`, the wire public array through `pubView idx pub`). The algebraic prover
additionally supplies the 7 `tComm`-chunk representations; the quotient `t` and the
Maller identity are DERIVED from the checked ft opening (the two antecedents after `A`).
See the general theorem's docstring for the trust accounting. Project-local: the
residue-free Vesta AGM root. -/
theorem kimchiVesta_sound_algebraic_ft (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → IpaVesta.Point) (zC : IpaVesta.Point)
    (aw₀ : Fin 43 → Fin (2 ^ σ.k) → Fp) (ρw₀ : Fin 43 → Fp)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = batchC wC zC vk.comms i)
    (TC : Fin 7 → IpaVesta.Point) (aT : Fin 7 → Fin (2 ^ σ.k) → Fp) (ρT : Fin 7 → Fp)
    (hTC : ∀ j, commit σ (aT j) (ρT j) = TC j)
    (Cσ6 : IpaVesta.Point) (hCσ6 : Cσ6 = commitPoly σ (idx.sigmaPoly 6)) :
    ∃ (badB : Finset Fp) (badG : Fp → Finset Fp) (badA : Fp → Fp → Finset Fp)
        (badZ : Fp → Fp → Fp → Polynomial Fp → Finset Fp)
        (badXi : (Fin 43 → Fin 2 → Fp) → Fp → Finset Fp)
        (badR : (Fin 43 → Fin 2 → Fp) → Fp → Fp → Finset Fp),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fp), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n)
        ∧ (∀ (E : Fin 43 → Fin 2 → Fp) (ζ : Fp), (badXi E ζ).card ≤ 84)
        ∧ (∀ (E : Fin 43 → Fin 2 → Fp) (ζ ξ : Fp), (badR E ζ ξ).card ≤ 1))
      ∧ ∀ (β γ α ζ : Fp)
          (E : Fin 43 → Fin 2 → Fp) (ξ r : Fp) (A : Prop)
          (aft : Fin (2 ^ σ.k) → Fp) (ρft : Fp),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ →
          ζ ∉ badZ β γ α (ftChunkAssembly σ.k aT) →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) → ζ ^ n ≠ 1 →
          ξ ∉ badXi E ζ → r ∉ badR E ζ ξ →
          FiatShamirTreeB σ (combinedCommitment ξ (batchC wC zC vk.comms))
            (combinedEvalVector (2 ^ σ.k) r ![ζ, idx.omega * ζ])
            (combinedInnerProduct ξ r E) A →
          A →
          (commit σ aft ρft
            = permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
                • Cσ6 - (ζ ^ n - 1) • ∑ j : Fin 7, (ζ ^ n) ^ (j : ℕ) • TC j) →
          (innerProduct aft (evalVector (2 ^ σ.k) ζ)
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly (pubView idx pub)).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → Fp, Satisfies idx (pubView idx pub) wTab :=
  kimchiProof_sound_algebraic_ft σ idx hk hbind vk.comms hvk (pubView idx pub) wC zC
    aw₀ ρw₀ hrep TC aT ρT hTC Cσ6 hCσ6

/-- **Residue-free algebraic-prover soundness of the deployed Pallas kimchi verifier.**
The Pallas-side twin of `kimchiVesta_sound_algebraic_ft`, over `Fq`/`IpaPallas` — see
the Vesta docstring, and the general theorem's for the trust accounting. Project-local:
the residue-free Pallas AGM root. -/
theorem kimchiPallas_sound_algebraic_ft (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hk : 2 ^ σ.k = n) (hvk : VKCorresponds σ vk.comms idx)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → IpaPallas.Point) (zC : IpaPallas.Point)
    (aw₀ : Fin 43 → Fin (2 ^ σ.k) → Fq) (ρw₀ : Fin 43 → Fq)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = batchC wC zC vk.comms i)
    (TC : Fin 7 → IpaPallas.Point) (aT : Fin 7 → Fin (2 ^ σ.k) → Fq) (ρT : Fin 7 → Fq)
    (hTC : ∀ j, commit σ (aT j) (ρT j) = TC j)
    (Cσ6 : IpaPallas.Point) (hCσ6 : Cσ6 = commitPoly σ (idx.sigmaPoly 6)) :
    ∃ (badB : Finset Fq) (badG : Fq → Finset Fq) (badA : Fq → Fq → Finset Fq)
        (badZ : Fq → Fq → Fq → Polynomial Fq → Finset Fq)
        (badXi : (Fin 43 → Fin 2 → Fq) → Fq → Finset Fq)
        (badR : (Fin 43 → Fin 2 → Fq) → Fq → Fq → Finset Fq),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fq), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n)
        ∧ (∀ (E : Fin 43 → Fin 2 → Fq) (ζ : Fq), (badXi E ζ).card ≤ 84)
        ∧ (∀ (E : Fin 43 → Fin 2 → Fq) (ζ ξ : Fq), (badR E ζ ξ).card ≤ 1))
      ∧ ∀ (β γ α ζ : Fq)
          (E : Fin 43 → Fin 2 → Fq) (ξ r : Fq) (A : Prop)
          (aft : Fin (2 ^ σ.k) → Fq) (ρft : Fq),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ →
          ζ ∉ badZ β γ α (ftChunkAssembly σ.k aT) →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) → ζ ^ n ≠ 1 →
          ξ ∉ badXi E ζ → r ∉ badR E ζ ξ →
          FiatShamirTreeB σ (combinedCommitment ξ (batchC wC zC vk.comms))
            (combinedEvalVector (2 ^ σ.k) r ![ζ, idx.omega * ζ])
            (combinedInnerProduct ξ r E) A →
          A →
          (commit σ aft ρft
            = permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
                • Cσ6 - (ζ ^ n - 1) • ∑ j : Fin 7, (ζ ^ n) ^ (j : ℕ) • TC j) →
          (innerProduct aft (evalVector (2 ^ σ.k) ζ)
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly (pubView idx pub)).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → Fq, Satisfies idx (pubView idx pub) wTab :=
  kimchiProof_sound_algebraic_ft σ idx hk hbind vk.comms hvk (pubView idx pub) wC zC
    aw₀ ρw₀ hrep TC aT ρT hTC Cσ6 hCσ6

end Kimchi.Verifier
