import Bulletproof.Forking.Game
import Bulletproof.Forking.Transcript
import Bulletproof.Forking.EndoChallenge

/-!
# The deployed single-claim extraction game

`Forking/Game.lean` proves an *abstract* Fiat–Shamir extraction game: for an oracle table
`O : T → Pre` over an arbitrary finite prefix type `T` with an arbitrary challenge map
`expand : Pre → F`, an algebraic bounded-query adversary that convinces the verifier either
hands the extractor an opening witness or a computed discrete-log break, except on a set of
tables of measure at most `(Q + k + 1) · 3 / |Pre|`.

This module *instantiates* that game at the deployed Pasta parameters. It fixes the four free
choices the abstract game leaves open — the prechallenge type `Pre`, the challenge map
`expand`, the oracle domain `T`, and the adversary's output type `Pf` — and states the
resulting deployed theorem together with the two anti-vacuity companions.

## The four choices

* **`Pre := Fin (2 ^ 128)`** (`Prechallenge`). The deployed verifier never squeezes a field
  element for a round challenge: `squeezeChallenge spec s = (endoExpand spec.lam n, s')` where
  `(n, s') = challengeNat spec s`. So the oracle's codomain is the 128-bit prechallenge domain
  and the error term divides by `2 ^ 128`, not by `|Fq| ≈ 2 ^ 254`.

* **`expand := expandPre C`**, the deployed endomorphism expansion at the curve's eigenvalue —
  the unique place a challenge enters the scalar field.

* **`T := IpaNode C k`**, a *structured node type*, and deliberately **not**
  `List (IpaTranscriptElt C)`. The abstract game's commit-then-challenge hypothesis
  (`DecodesFromPrefixes.final_eq`) asks for a plain function `final : T → G × G` returning
  `(π.delta, π.sg)`. The deployed Schnorr prefix
  `preC inp = preT ++ roundBlock k ++ [point δ, sqEndo]` absorbs `δ` but **not** `sg` — kimchi's
  schedule squeezes the Schnorr challenge immediately after `δ`. Two proofs with the same
  `(cip, L, R, δ)` and different `sg` therefore have *equal* `preC`, so no function of the list
  can return both values of `sg`. A second benefit: the node type is finite by construction,
  whereas `List (IpaTranscriptElt C)` is infinite and `PMF.uniformOfFintype` would not even
  typecheck at it.

  The node at which the Schnorr challenge is read must therefore carry `sg`, which the deployed
  sponge does not absorb. That is a deviation of the idealized model from the deployed schedule,
  and it is stated as such (`nodeTranscript` drops the `sg` slot). It is harmless, provably:
  `sg_determined_of_verifyWith` says the accepting `sg` equals `⟨bPolyCoefficients u, σ.g⟩`, a
  function of the round challenges read at *strictly earlier* nodes, so grinding on the `sg`
  component enumerates query points of which at most one is ever winning — and every one of them
  is priced by the query bound `Q`.

* **`Pf := Ipa.Proof C σ.k`**. The adversary outputs only the opening proof; the commitments,
  evaluation points, claimed evaluations, `ξ` and `r` are parameters. Hence `cip` is a
  parameter, hence `preT` and the transcript-derived base `U = toGroup (spongeOBase preT)`
  (`uBaseOf`) are fixed group data rather than adversary-controlled — the fixed-claim scope
  declared in `Game.lean`'s preamble.

Replacing the sponge's prechallenge by a uniform one is the single modelling step; it is stated
in prose and carried by no Lean axiom. `verifyOracle_spongeFS` (`Forking/Transcript.lean`) is
what pins `wireWins` fed the sponge's own reads to `Ipa.verify`.

## The trust boundary of the `sg` slot

The one place the idealization is not literally the deployed schedule is the `sg` component of the
Schnorr node: the deployed sponge absorbs `δ` and squeezes immediately (`preC`,
`Forking/Transcript.lean`), so "the sponge behaves as a uniform table over `IpaNode C k`" is a
statement about tables on the *enlarged* domain, while the honest idealization concerns tables on
the sg-free one. The section "The `sg` slot: locality and the pinning factorization" below is the
defence, and it is carried by two theorems:

* **`wireWins_pinTable`** — the measured win event is decided by `pinTable σ O`, which factors
  through `sgForget` (`pinTable_factors`), i.e. by a table on the honest sg-free node domain.
* **`chainAt_sg`** — the fork's own rewind points add no `sg`-bearing read: `chainAt t i` is
  either `sg`-free or `t` itself.

The scope is stated honestly: what factors is the *game's* reads. The **adversary's** own queries
do not factor and are not claimed to — it may query two nodes differing only in the `sg` slot and
branch on the answers. Those queries are priced one-for-one by the query bound `Q` of
`deployedExtract_failure_measure_le`, which is the whole role `Q` plays, so the enlarged domain
costs nothing beyond the term already present.
-/

namespace Bulletproof.Ipa.Forking

open Bulletproof Bulletproof.Forking Poseidon
open IpaTranscriptElt
open scoped ENNReal

/-! ## The challenge domain -/

/-- **The prechallenge type**: the 128-bit value `challengeNat` squeezes, before endo-expansion.
Finite, decidable and nonempty, with `|Prechallenge| = 2 ^ 128` — the number the deployed error
term divides by. -/
abbrev Prechallenge : Type := Fin (2 ^ 128)

instance instNonemptyPrechallenge : Nonempty Prechallenge := ⟨⟨0, by positivity⟩⟩

/-- The cardinality of the prechallenge domain — the deployed error's denominator. -/
theorem card_prechallenge : Fintype.card Prechallenge = 2 ^ 128 := Fintype.card_fin _

/-- **The challenge map**: the deployed endomorphism expansion of a prechallenge at the curve's
eigenvalue. It is the unique place a challenge enters the scalar field. -/
def expandPre (C : Ipa.CommitmentCurve) (q : Prechallenge) : C.ScalarField :=
  FqSponge.endoExpand C.sponge.lam (q : ℕ)

/-- **The Vesta challenge map is injective.** Immediate from `endoExpand_vesta_injOn`: an element
of `Fin (2 ^ 128)` has value `< 2 ^ 128` by definition, and the Vesta bundle's eigenvalue *is*
`FqVesta.spec.lam`. -/
theorem expandPre_vesta_injective : Function.Injective (expandPre IpaVesta.curve) := by
  intro a b h
  exact Fin.ext (endoExpand_vesta_injOn a.isLt b.isLt h)

/-- **The Pallas challenge map is injective.** -/
theorem expandPre_pallas_injective : Function.Injective (expandPre IpaPallas.curve) := by
  intro a b h
  exact Fin.ext (endoExpand_pallas_injOn a.isLt b.isLt h)

/-- **The Vesta challenge map never vanishes.** `endoExpand_vesta_ne_zero` needs no size
hypothesis at all — only bits `0..127` are read by the accumulator fold. -/
theorem expandPre_vesta_ne_zero (q : Prechallenge) : expandPre IpaVesta.curve q ≠ 0 :=
  endoExpand_vesta_ne_zero _

/-- **The Pallas challenge map never vanishes.** -/
theorem expandPre_pallas_ne_zero (q : Prechallenge) : expandPre IpaPallas.curve q ≠ 0 :=
  endoExpand_pallas_ne_zero _

/-! ## The oracle domain -/

/-- **A node of the deployed IPA transcript**: exactly the data the sponge has absorbed when a
challenge is squeezed, together with the index of that squeeze.

`idx` is the round whose challenge is being read (`idx = k` for the Schnorr challenge); `lr j` is
`some` exactly for the cross-terms already absorbed; `delta` and `sg` are `none` at a round node.
All five components are finite with decidable equality, so this is a `Fintype` with
`DecidableEq` — which `List (IpaTranscriptElt C)` is not.

A round node carries only the cross-terms of rounds `0, …, idx`: a node must *not* mention later
`L j, R j`, or the model would force the adversary to commit to its whole fold before the first
challenge, and the theorem would silently be about a weaker adversary. With the `Option`
truncation, two adversary outputs agreeing up to round `i` and diverging afterwards share the
round-`i` node — exactly the adaptivity the fork exploits. -/
@[ext]
structure IpaNode (C : Ipa.CommitmentCurve) (k : ℕ) where
  /-- The index of the squeeze this node is read at; `Fin.last k` is the Schnorr squeeze. -/
  idx : Fin (k + 1)
  /-- The combined inner product absorbed first — claim data, hence a parameter of the game. -/
  cip : C.ScalarField
  /-- The cross-terms absorbed so far: `some` at rounds `≤ idx`, `none` afterwards. -/
  lr : Fin k → Option (C.Point × C.Point)
  /-- The Schnorr commitment `δ`, absorbed only at the Schnorr node. -/
  delta : Option C.Point
  /-- The folded generator `sg`. **Not** absorbed by the deployed sponge — see the module
  preamble and `sg_determined_of_verifyWith`. -/
  sg : Option C.Point
  deriving DecidableEq

variable {C : Ipa.CommitmentCurve} {k m p : ℕ}

/-- A node is the five-fold product of its components — the shape the `Fintype` instance is
transported along. (Spelled by hand: the `deriving Fintype` handler does not fire through the
curve bundle's `Fintype (ZMod C.base)`, which is what makes `C.Point` finite.) -/
private def ipaNodeEquivProd (C : Ipa.CommitmentCurve) (k : ℕ) :
    (Fin (k + 1) × C.ScalarField × (Fin k → Option (C.Point × C.Point)) ×
        Option C.Point × Option C.Point) ≃ IpaNode C k where
  toFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  invFun t := (t.idx, t.cip, t.lr, t.delta, t.sg)
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeIpaNode : Fintype (IpaNode C k) :=
  Fintype.ofEquiv _ (ipaNodeEquivProd C k)

/-- The node at which round `i`'s challenge is squeezed: the cross-terms of rounds `0, …, i`,
nothing later, and neither `δ` nor `sg`. -/
def nodeU (cip : C.ScalarField) (π : Ipa.Proof C k) (i : Fin k) : IpaNode C k where
  idx := i.castSucc
  cip := cip
  lr := fun j => if (j : ℕ) ≤ (i : ℕ) then some π.lr[j] else none
  delta := none
  sg := none

/-- The node at which the Schnorr challenge is squeezed: every cross-term, `δ`, and `sg`. -/
def nodeC (cip : C.ScalarField) (π : Ipa.Proof C k) : IpaNode C k where
  idx := Fin.last k
  cip := cip
  lr := fun j => some π.lr[j]
  delta := some π.delta
  sg := some π.sg

/-- **The deployed prefixes**: the `k` round nodes, then the Schnorr node. This is the
`prefixes : Pf → Fin (σ.k + 1) → T` the abstract game asks for. -/
def nodes (cip : C.ScalarField) (π : Ipa.Proof C k) : Fin (k + 1) → IpaNode C k :=
  Fin.snoc (nodeU cip π) (nodeC cip π)

/-- `nodes` by cases on the index — the round nodes below `k`, the Schnorr node at `k`. The
`Fin.snoc` computation rules, packaged for the arbitrary-index reasoning below. -/
theorem nodes_eq (cip : C.ScalarField) (π : Ipa.Proof C k) (j : Fin (k + 1)) :
    nodes cip π j = if h : (j : ℕ) < k then nodeU cip π ⟨(j : ℕ), h⟩ else nodeC cip π := by
  refine Fin.lastCases ?_ ?_ j
  · simp [nodes]
  · intro i; simp [nodes]

/-- The round decoder: a node's own cross-term pair, `(0, 0)` at the Schnorr node. -/
private def nodeRound (t : IpaNode C k) : C.Point × C.Point :=
  if h : (t.idx : ℕ) < k then (t.lr ⟨(t.idx : ℕ), h⟩).getD (0, 0) else (0, 0)

/-- The leaf decoder: a node's `(δ, sg)` pair. -/
private def nodeFinal (t : IpaNode C k) : C.Point × C.Point :=
  (t.delta.getD 0, t.sg.getD 0)

/-- The wire proof viewed as the soundness layer's `OpeningProof`: the `Vector`-indexed `lr`
becomes the `Fin k`-indexed field, everything else transfers unchanged. (`Reflection.lean` has
the same map but declares it `private`, so it is redefined here rather than reused.) -/
def toOpening (π : Ipa.Proof C k) : OpeningProof C.ScalarField C.Point k where
  lr := fun j => π.lr[j]
  delta := π.delta
  z1 := π.z1
  z2 := π.z2
  sg := π.sg

section Module

variable [Module C.ScalarField C.Point]

/-- **Commit-then-challenge holds at the deployed prefixes.** For every claim (hence `cip`) and
every SRS at round count `σ.k`, `(nodeRound, nodeFinal)` witness `DecodesFromPrefixes`. Both
obligations are unfoldings of `Fin.snoc`'s computation rules; nothing is assumed about the
adversary. -/
private def decodesFromPrefixes_nodes (σ : SRS C.Point) (cip : C.ScalarField) :
    DecodesFromPrefixes (F := C.ScalarField) σ toOpening (nodes cip) where
  round := nodeRound
  final := nodeFinal
  round_eq := by
    intro π j
    simp only [nodes, Fin.snoc_castSucc, nodeRound, nodeU, toOpening, Fin.val_castSucc,
      Fin.is_lt, dif_pos]
    simp
  final_eq := by
    intro π
    simp [nodes, nodeFinal, nodeC, toOpening]

end Module

/-- **The deployed prefixes decode.** The round of a node is its own index, and the chain of a
node truncates it to an earlier round. This is where the structured node pays off: distinctness
is an inequality of indices, needing nothing about injectivity of a transcript encoding. -/
private def prefixDecode_nodes (cip : C.ScalarField) :
    Zcash.Snark.PrefixDecode (IpaNode C k) (k + 1) (nodes cip) where
  roundOf t := (t.idx : ℕ)
  chainAt t i :=
    if (i : ℕ) < k then
      { idx := i, cip := t.cip,
        lr := fun j => if (j : ℕ) ≤ (i : ℕ) then t.lr j else none,
        delta := none, sg := none }
    else t
  roundOf_prefixes := by
    intro π j
    rw [nodes_eq]
    by_cases h : (j : ℕ) < k
    · rw [dif_pos h]; simp [nodeU]
    · rw [dif_neg h]
      have : (j : ℕ) = k := by have := j.isLt; omega
      simp [nodeC, this]
  chainAt_prefixes := by
    intro π j i hij
    by_cases hi : (i : ℕ) < k
    · rw [if_pos hi, nodes_eq cip π i, dif_pos hi, nodes_eq cip π j]
      by_cases hj : (j : ℕ) < k
      · rw [dif_pos hj]
        refine IpaNode.ext rfl rfl ?_ rfl rfl
        funext l
        by_cases hl : (l : ℕ) ≤ (i : ℕ)
        · simp only [nodeU, if_pos hl, if_pos (le_trans hl hij)]
        · simp only [nodeU, if_neg hl]
      · rw [dif_neg hj]
        refine IpaNode.ext rfl rfl ?_ rfl rfl
        funext l
        by_cases hl : (l : ℕ) ≤ (i : ℕ)
        · simp only [nodeU, nodeC, if_pos hl]
        · simp only [nodeU, nodeC, if_neg hl]
    · have hik : (i : ℕ) = k := by have := i.isLt; omega
      have hje : j = i := Fin.ext (by have := j.isLt; omega)
      rw [if_neg hi, hje]
  chainAt_ne := by
    intro t i hlt
    have hik : (i : ℕ) < k := lt_of_lt_of_le hlt (Nat.lt_succ_iff.mp t.idx.isLt)
    rw [if_pos hik]
    intro h
    exact absurd (congrArg (fun s => (s.idx : ℕ)) h) (by simpa using Nat.ne_of_lt hlt)

/-! ## Faithfulness to the deployed schedule

The node type is an abstraction; the two identities below are what make it an abstraction *of
the deployed transcript* rather than a convenient invention. -/

/-- **The node's transcript**: the `IpaTranscriptElt` list the deployed sponge would have
absorbed at `t` — the `cip` absorb and the base-squeeze marker, then one
`[point L j, point R j, sqEndo]` block per `some` entry of `t.lr` up to `t.idx`, then, when
`t.delta` is `some`, `[point δ, sqEndo]`. The `sg` component is dropped: it is exactly the
modelling deviation recorded in the preamble. -/
private def nodeTranscript (t : IpaNode C k) : List (IpaTranscriptElt C) :=
  [frScalar (Ipa.shiftScalar C t.cip), sqBase] ++
    (List.finRange k).flatMap (fun j : Fin k =>
      if (j : ℕ) ≤ (t.idx : ℕ) then
        match t.lr j with
        | some LR => [point LR.1, point LR.2, sqEndo]
        | none => []
      else []) ++
    (match t.delta with
     | some d => [point d, sqEndo]
     | none => [])

/-- A guarded `flatMap` over `Fin n` is the `flatMap` over the truncated index list — the
index-side twin of `roundBlock`'s `List.take`. -/
private theorem flatMap_finRange_take {γ : Type*} :
    ∀ (n : ℕ) (h : Fin n → List γ) (i : ℕ),
      (List.finRange n).flatMap (fun j : Fin n => if (j : ℕ) ≤ i then h j else [])
        = ((List.finRange n).take (i + 1)).flatMap h := by
  intro n
  induction n with
  | zero => intro h i; simp
  | succ n ih =>
    intro h i
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map, List.take_succ_cons,
      List.flatMap_cons, ← List.map_take, List.flatMap_map]
    simp only [Fin.val_zero, Nat.zero_le, if_pos]
    congr 1
    cases i with
    | zero => simp
    | succ i' =>
      have hih := ih (fun j => h j.succ) i'
      simpa [Fin.val_succ, Nat.succ_le_succ_iff] using hih

/-- A vector's list is its index list mapped by its own reads — the bridge between the node's
`Fin k`-indexed assembly and `roundBlock`'s `Vector.toList`. -/
private theorem toList_eq_map_finRange {α : Type*} {n : ℕ} (v : Vector α n) :
    v.toList = (List.finRange n).map (fun j => v[j]) := by
  refine List.ext_getElem (by simp) (fun j h1 h2 => ?_)
  simp

/-- **The nodes are the deployed prefixes.** The round nodes assemble `preU` and the Schnorr node
assembles `preC`, so the idealized oracle domain really does abstract the deployed schedule. -/
theorem nodeTranscript_nodes (inp : Ipa.Input C k m p) :
    (∀ i : Fin k,
        nodeTranscript (nodeU (Ipa.cipOf inp) inp.proof i) = preU inp i) ∧
      nodeTranscript (nodeC (Ipa.cipOf inp) inp.proof) = preC inp := by
  set π := inp.proof with hπ
  set blk : C.Point × C.Point → List (IpaTranscriptElt C) :=
    fun LR => [point LR.1, point LR.2, sqEndo] with hblk
  -- the round block, re-indexed over `Fin k` instead of over the vector's list
  have hblock : ∀ n : ℕ, roundBlock inp n
      = ((List.finRange k).take n).flatMap (fun j => blk π.lr[j]) := by
    intro n
    rw [roundBlock, toList_eq_map_finRange π.lr, ← List.map_take, List.flatMap_map]
  constructor
  · intro i
    have hfn : (fun j : Fin k =>
          if (j : ℕ) ≤ ((nodeU (Ipa.cipOf inp) π i).idx : ℕ) then
            (match (nodeU (Ipa.cipOf inp) π i).lr j with
             | some LR => blk LR
             | none => ([] : List (IpaTranscriptElt C)))
          else [])
        = fun j : Fin k => if (j : ℕ) ≤ (i : ℕ) then blk π.lr[j] else [] := by
      funext j
      by_cases hj : (j : ℕ) ≤ (i : ℕ)
      · simp only [nodeU, Fin.val_castSucc, if_pos hj]
      · simp only [nodeU, Fin.val_castSucc, if_neg hj]
    rw [nodeTranscript, hfn, flatMap_finRange_take, preU, preT, preTAbsorbs, hblock]
    simp [nodeU]
  · have hfn : (fun j : Fin k =>
          if (j : ℕ) ≤ ((nodeC (Ipa.cipOf inp) π).idx : ℕ) then
            (match (nodeC (Ipa.cipOf inp) π).lr j with
             | some LR => blk LR
             | none => ([] : List (IpaTranscriptElt C)))
          else [])
        = fun j : Fin k => blk π.lr[j] := by
      funext j
      simp only [nodeC, Fin.val_last, if_pos (Nat.le_of_lt j.isLt)]
    rw [nodeTranscript, hfn, preC, preT, preTAbsorbs, hblock k]
    have hk : ((List.finRange k).take k) = List.finRange k := by simp
    rw [hk]
    simp [nodeC, hπ]

/-- **The accepting `sg` is already determined.** `verifyWith` is the conjunction of the Schnorr
equation and `decide (sg = msm C σ.g (bPolyCoefficients chal))`, so acceptance pins `sg` as a
function of the round challenges alone — read at nodes strictly earlier than the Schnorr node.

This is the theorem that discharges the modelling deviation: the extra `sg` component of the
Schnorr node ranges over values of which at most one is compatible with acceptance. -/
theorem sg_determined_of_verifyWith (σ : SRS C.Point) (uBase : C.Point)
    (chals : Vector C.ScalarField σ.k) (c : C.ScalarField) (inp : Ipa.Input C σ.k m p)
    (h : Ipa.verifyWith C σ uBase chals c inp = true) :
    inp.proof.sg = Ipa.msm C σ.g (bPolyCoefficients fun i => chals[i]) := by
  simp only [Ipa.verifyWith, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-! ## The win condition is the wire -/

/-- **The transcript-derived base.** Since the claim — hence `cip` — is a parameter, this is a
fixed group element; it coincides with the deployed `U` of `transcriptFrom` by
`toGroup_spongeOBase_preT`. It is not randomised: the `U` base is derived from claim data only,
so no oracle read of the game is spent on it. -/
def uBaseOf (C : Ipa.CommitmentCurve) (cip : C.ScalarField) : C.Point :=
  C.toGroup (spongeOBase [frScalar (Ipa.shiftScalar C cip), sqBase])

/-- `uBaseOf` at a checked input's own `cip` is `transcriptFrom`'s `U`. -/
theorem uBaseOf_eq_transcript (inp : Ipa.Input C k m p) :
    uBaseOf C (Ipa.cipOf inp) = (Ipa.transcriptFrom C FqSponge.init inp).1 :=
  toGroup_spongeOBase_preT inp

/-- **The deployed win**: the executable wire verifier's own `Bool`, at the challenges the table
supplies through `expandPre`. At the deployed source this *is* the deployed verifier —
`verifyWith` fed `transcriptFrom`'s output is `verifyFrom`, hence `Ipa.verify`, which is what
`verifyOracle_spongeFS` packages. -/
def wireWins (σ : SRS C.Point) (claim : Ipa.Input C σ.k m p)
    (O : IpaNode C σ.k → Prechallenge) (π : Ipa.Proof C σ.k) : Prop :=
  Ipa.verifyWith C σ (uBaseOf C (Ipa.cipOf claim))
      (Vector.ofFn fun i => expandPre C (O (nodeU (Ipa.cipOf claim) π i)))
      (expandPre C (O (nodeC (Ipa.cipOf claim) π)))
      { claim with proof := π } = true

section Wire

variable [Module C.ScalarField C.Point]
  (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)

include hsmul in
/-- The executable MSM is `commitGen`. (`Reflection.lean` has the same lemma, but declares it
`private`; it is re-derived here because the wire bridge needs it at a *free* challenge vector.) -/
private theorem msm_eq_commitGen {n : ℕ} (g : Fin n → C.Point) (a : Fin n → C.ScalarField) :
    Ipa.msm C g a = commitGen g a := by
  simp only [Ipa.msm, commitGen]
  exact Finset.sum_congr rfl fun i _ => (hsmul (a i) (g i)).symm

omit [Module C.ScalarField C.Point] in
/-- Generalized-accumulator running-power fold over a list: from any starting accumulator `acc`
and running power `q`, the first component is `acc` plus the `(q · ξ^i)`-scaled sum of the list
entries. The engine behind `combineCommitments_arr_eq` (`private` in `Reflection.lean`). -/
private theorem combineFoldl_aux (ξ : C.ScalarField) (l : List C.Point) (acc : C.Point)
    (q : C.ScalarField) :
    (l.foldl (fun (a : C.Point × C.ScalarField) P => (a.1 + a.2.val • P, a.2 * ξ)) (acc, q)).1
      = acc + ∑ i : Fin l.length, (q * ξ ^ (i : ℕ)).val • l[i] := by
  induction l generalizing acc q with
  | nil => simp
  | cons P t ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
      Fin.val_succ]
    rw [← _root_.add_assoc]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    rw [pow_succ]; ring

include hsmul in
/-- The executable running-power combination is `combinedCommitment`. (`Reflection.lean` proves
this as the public `combineCommitments_eq`, but that module is not in this file's import closure —
`Deployed.lean` sits under `Forking/`, which imports only `Wire`/`Protocol`/`Soundness` through
`Game` — so it is re-derived here from `combineFoldl_aux`.) -/
private theorem combineCommitments_arr_eq (ξ : C.ScalarField) (cs : Array C.Point) :
    Ipa.combineCommitments C ξ cs = combinedCommitment ξ (fun i : Fin cs.size => cs[i]) := by
  rw [Ipa.combineCommitments, ← Array.foldl_toList, combineFoldl_aux]
  simp only [one_mul, _root_.zero_add]
  rw [combinedCommitment]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsmul]; congr 1

include hsmul in
/-- The executable running-power combination of a checked commitment *vector* is
`combinedCommitment` of its indexed function: `combineCommitments_arr_eq` transported along the
`Vector`/`Array` size coercion. -/
private theorem combineCommitments_toArray_eq (ξ : C.ScalarField) {n : ℕ}
    (cs : Vector C.Point n) :
    Ipa.combineCommitments C ξ cs.toArray
      = combinedCommitment ξ (fun i : Fin n => cs[i]) := by
  rw [combineCommitments_arr_eq hsmul, combinedCommitment, combinedCommitment]
  exact Fintype.sum_equiv (finCongr (by simp)) _ _ fun i => rfl

omit [Module C.ScalarField C.Point] in
/-- A left fold that adds `g x` for each list element equals the start plus the sum of `g` over
the list — the engine behind the recombination bridge (`private` in `Reflection.lean`). -/
private theorem foldl_add_eq_sum {D : Type*} (g : D → C.Point) (l : List D) (init : C.Point) :
    l.foldl (fun acc x => acc + g x) init = init + ∑ i : Fin l.length, g l[i] := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, _root_.add_assoc]
    simp [Fin.sum_univ_succ]

omit [Module C.ScalarField C.Point] in
/-- The executable zip-fold recombination equals the abstract indexed sum: folding `(L, R, u)`
triples matches `∑ j, (uⱼ⁻¹ • Lⱼ + uⱼ • Rⱼ)` scaled through `val` (`private` in
`Reflection.lean`). -/
private theorem zipFold_eq_recombine (init : C.Point) (lr : Array (C.Point × C.Point))
    (ch : Array C.ScalarField) (n : ℕ) (hlr : lr.size = n) (hch : ch.size = n) :
    (lr.zip ch).foldl
        (fun (acc : C.Point) (LRu : (C.Point × C.Point) × C.ScalarField) =>
          acc + (LRu.2⁻¹.val • LRu.1.1 + LRu.2.val • LRu.1.2)) init
      = init + ∑ j : Fin n,
          ((ch[(j : ℕ)]'(by omega))⁻¹.val • (lr[(j : ℕ)]'(by omega)).1
            + (ch[(j : ℕ)]'(by omega)).val • (lr[(j : ℕ)]'(by omega)).2) := by
  rw [← Array.foldl_toList, foldl_add_eq_sum]
  congr 1
  have hlen : (lr.zip ch).toList.length = n := by
    rw [Array.length_toList, Array.size_zip, hlr, hch, min_self]
  refine Fintype.sum_equiv (finCongr hlen) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast, Fin.getElem_fin, Array.getElem_toList,
    Array.getElem_zip]

include hsmul in
/-- **The executable wire acceptance is `VerifierAcceptsAt`, at arbitrary challenges.** The
challenge-generic core of `verify_reflects`: `verifyWith` is literally `decide` of the two
conjuncts `VerifierAcceptsAt` names, so the `Bool` equation `= true` and the `Prop` are
*equivalent*, not merely one-directionally related. Three equalities carry it — the executable
combiners are the library combiners (`combineCommitments_toArray_eq`, `msm_eq_commitGen`), the
zip-fold is `recombine` (`zipFold_eq_recombine`), and the wire's `b₀` slot is the inner product
against the combined eval vector (`combinedB_eq_innerProduct`). -/
theorem verifyWith_iff_verifierAcceptsAt (σ : SRS C.Point) (uBase : C.Point)
    (chals : Vector C.ScalarField σ.k) (c : C.ScalarField) (claim : Ipa.Input C σ.k m p) :
    Ipa.verifyWith C σ uBase chals c claim = true
      ↔ VerifierAcceptsAt { σ with U := uBase } (toOpening claim.proof)
          (combinedCommitment claim.polyscale claim.commitmentFn)
          (innerProduct (bPolyCoefficients fun i => chals[i])
            (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn))
          (Ipa.cipOf claim) c (fun i => chals[i]) := by
  rw [Ipa.verifyWith]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [zipFold_eq_recombine _ claim.proof.lr.toArray chals.toArray σ.k (by simp) (by simp),
    combineCommitments_toArray_eq hsmul, msm_eq_commitGen hsmul, combinedB_eq_innerProduct]
  unfold VerifierAcceptsAt recombine toOpening
  simp only [hsmul, Fin.getElem_fin, Vector.getElem_toArray]
  exact Iff.rfl

include hsmul in
/-- **The wire bridge.** The executable run at the table's challenges accepts *exactly when* the
abstract game's `Wins` holds, against the SRS whose randomisation base is the transcript-derived
`uBaseOf`.

`Wins` unfolds to `VerifierAcceptsAt` at exactly the challenge vector `wireWins` feeds
`verifyWith` (by the computation rules for `Fin.snoc` and `Vector.ofFn`), so the statement is the
reflection of the executable verifier into the `Prop`-level acceptance at *arbitrary* challenges
rather than the sponge-derived ones — the challenge-generic version of `verify_reflects`, whose
three helper lemmas are `private` there and are therefore re-derived above.

It is an **equivalence**, and that is load-bearing. The forward direction is what
`deployedExtract_failure_measure_le` needs (it makes the deployed failure set a subset of the
abstract one); the backward direction is what the anti-vacuity companion needs, since the honest
machine's algebra delivers `Wins` while the measure bound is stated over `wireWins`. A
one-directional bridge would leave `{O | wireWins σ claim O π} = ∅` open — exactly the vacuity
the companion exists to exclude. It costs nothing: every step of the derivation is an equality of
terms. -/
private theorem wireWins_iff_wins (σ : SRS C.Point) (claim : Ipa.Input C σ.k m p)
    (O : IpaNode C σ.k → Prechallenge) (π : Ipa.Proof C σ.k) :
    wireWins σ claim O π ↔
      Wins { σ with U := uBaseOf C (Ipa.cipOf claim) }
        (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn)
        (Ipa.cipOf claim)
        (combinedCommitment claim.polyscale claim.commitmentFn)
        (expandPre C) toOpening (nodes (Ipa.cipOf claim)) O π := by
  rw [wireWins, verifyWith_iff_verifierAcceptsAt hsmul]
  unfold Wins oracleChallenges
  simp only [nodes, Fin.snoc_castSucc, Fin.snoc_last, Fin.getElem_fin, Vector.getElem_ofFn]
  exact Iff.rfl

end Wire

/-! ## The `sg` slot: locality and the pinning factorization

The preamble recorded a modelling deviation: the Schnorr node carries an `sg` slot that the
deployed sponge never absorbs (`preC` absorbs `δ` and then squeezes). The idealization "the sponge
behaves as a uniform table" is therefore literally a statement about tables on the *sg-free* node
domain, while the game above is run over tables on the enlarged domain `IpaNode C σ.k`. This
section turns `sg_determined_of_verifyWith` into the statement that carries the trust boundary:
on the events the headline theorem measures, the table is only ever evaluated at nodes whose `sg`
slot is the *pinned* one, so the enlarged model and the honest sg-free model agree on everything
measured. The two lemmas that say it are `wireWins_pinTable` (the win event is decided by a table
that factors through `sgForget`, i.e. by a table on the honest sg-free domain) and `chainAt_sg`
(the fork's own rewind points read no `sg`-bearing node beyond the queried ones).

The scope is stated honestly and is not blurred: what factors is the *game's* own reads — the win
event and the fork's rewind points. The **adversary's** own queries do *not* factor and are not
claimed to: an oracle machine may query any node it likes, including two nodes differing only in
the `sg` slot, and behave differently on the answers. Those queries are priced, one for one, by
the query bound `Q` in `deployedExtract_failure_measure_le`; that is the whole role `Q` plays, and
it is why the enlarged domain costs nothing beyond the term already present. -/

/-- **The round truncation of a node**: the node at which round `i`'s challenge is read,
reconstructed from `t`. It is the `i < k` branch of `prefixDecode_nodes`' `chainAt` field, named
separately so it can be reasoned about outside that structure. -/
private def roundNodeOf (t : IpaNode C k) (i : Fin k) : IpaNode C k where
  idx := i.castSucc
  cip := t.cip
  lr := fun j => if (j : ℕ) ≤ (i : ℕ) then t.lr j else none
  delta := none
  sg := none

/-- **The truncations of the Schnorr node are the round nodes.** Componentwise: the indices agree
(`i.castSucc` on both sides), `cip` is copied, `δ` and `sg` are `none` on both sides, and the `lr`
components agree because `(nodeC cip π).lr j = some π.lr[j]` for every `j`, so guarding it by
`j ≤ i` produces exactly `(nodeU cip π i).lr`. -/
private theorem roundNodeOf_nodeC (cip : C.ScalarField) (π : Ipa.Proof C k) (i : Fin k) :
    roundNodeOf (nodeC cip π) i = nodeU cip π i := by
  refine IpaNode.ext rfl rfl ?_ rfl rfl
  funext j
  by_cases hj : (j : ℕ) ≤ (i : ℕ)
  · simp only [roundNodeOf, nodeC, nodeU, if_pos hj]
  · simp only [roundNodeOf, nodeC, nodeU, if_neg hj]

/-- **The sg-forgetting map.** Its image is the *honest node domain*: the data the deployed sponge
has genuinely absorbed at a squeeze. A table on the honest domain is the same thing as a table on
`IpaNode C k` that is constant on the fibres of `sgForget`; "`O` factors through `sgForget`" below
means exactly that. -/
private def sgForget (t : IpaNode C k) : IpaNode C k := { t with sg := none }

/-- **The pinned node.** A round node has its `sg` slot cleared (at a round node the deployed
sponge has absorbed no `sg`, and a queried round node already carries `none`); a Schnorr node has
its `sg` slot overwritten by the *canonical* value that `sg_determined_of_verifyWith` says an
accepting proof must carry, computed from the round challenges `O` itself supplies at strictly
earlier nodes.

Both branches discard the incoming `sg` slot outright, and everything they read (`idx`, `cip`,
`lr`, `delta`, and `O` at round truncations, which are built from those same components) survives
`sgForget`. That is the whole reason `pinNode_factors` holds — note in particular that the round
branch returns `sgForget t`, **not** `t`. -/
private def pinNode (σ : SRS C.Point) (O : IpaNode C σ.k → Prechallenge) (t : IpaNode C σ.k) :
    IpaNode C σ.k :=
  if (t.idx : ℕ) < σ.k then sgForget t
  else
    { t with
      sg := some (Ipa.msm C σ.g
        (bPolyCoefficients fun i => expandPre C (O (roundNodeOf t i)))) }

/-- **The pinned table**: `O` precomposed with `pinNode σ O`. -/
private def pinTable (σ : SRS C.Point) (O : IpaNode C σ.k → Prechallenge) :
    IpaNode C σ.k → Prechallenge :=
  fun t => O (pinNode σ O t)

/-- **The pinned node factors through `sgForget`.** The hypothesis says `t` and `t'` agree in
`idx`, `cip`, `lr` and `delta`, and may differ only in `sg`. The guard is therefore the same for
both, so the same branch is taken; in the round branch the value is the hypothesis itself, and in
the Schnorr branch the record's four surviving components agree while its `sg` slot is `some` of a
value computed from `O` at the nodes `roundNodeOf t i`, each of which is built from
`(idx, cip, lr)` alone. -/
private theorem pinNode_factors (σ : SRS C.Point) (O : IpaNode C σ.k → Prechallenge)
    {t t' : IpaNode C σ.k} (h : sgForget t = sgForget t') :
    pinNode σ O t = pinNode σ O t' := by
  obtain ⟨i₁, c₁, l₁, d₁, s₁⟩ := t
  obtain ⟨i₂, c₂, l₂, d₂, s₂⟩ := t'
  simp only [sgForget, IpaNode.mk.injEq] at h
  obtain ⟨hi, hc, hl, hd, -⟩ := h
  subst hi; subst hc; subst hl; subst hd
  simp only [pinNode, sgForget, roundNodeOf]

/-- **The pinned table factors through `sgForget`** — `pinNode_factors` followed by `congr`.
Equivalently: `pinTable σ O` is the pullback along `sgForget` of a table on the honest, sg-free
node domain. -/
theorem pinTable_factors (σ : SRS C.Point) (O : IpaNode C σ.k → Prechallenge)
    {t t' : IpaNode C σ.k} (h : sgForget t = sgForget t') :
    pinTable σ O t = pinTable σ O t' :=
  congrArg O (pinNode_factors σ O h)

/-- **The Schnorr node is fixed by pinning exactly when its `sg` slot is already the canonical
one.** The condition is what `sg_determined_of_verifyWith` supplies on the win event; isolating it
is what makes both directions of `wireWins_pinTable` available. -/
private theorem pinNode_nodeC_of_sg (σ : SRS C.Point) (cip : C.ScalarField)
    (O : IpaNode C σ.k → Prechallenge) (π : Ipa.Proof C σ.k)
    (hsg : π.sg
      = Ipa.msm C σ.g (bPolyCoefficients fun i => expandPre C (O (nodeU cip π i)))) :
    pinNode σ O (nodeC cip π) = nodeC cip π := by
  have hnlt : ¬ (((nodeC cip π).idx : ℕ) < σ.k) := by simp [nodeC]
  rw [pinNode, if_neg hnlt]
  refine IpaNode.ext rfl rfl rfl rfl ?_
  have hrn : (fun i : Fin σ.k => expandPre C (O (roundNodeOf (nodeC cip π) i)))
      = fun i : Fin σ.k => expandPre C (O (nodeU cip π i)) :=
    funext fun i => by rw [roundNodeOf_nodeC]
  rw [hrn]
  exact congrArg some hsg.symm

/-- **A round node is fixed by pinning, unconditionally.** Its `idx` is `i.castSucc`, of value
`i < σ.k`, so the first branch applies and returns the node with its `sg` slot set to `none` —
which it already is. -/
private theorem pinNode_nodeU (σ : SRS C.Point) (cip : C.ScalarField)
    (O : IpaNode C σ.k → Prechallenge) (π : Ipa.Proof C σ.k) (i : Fin σ.k) :
    pinNode σ O (nodeU cip π i) = nodeU cip π i := by
  have hlt : ((nodeU cip π i).idx : ℕ) < σ.k := by simp [nodeU]
  rw [pinNode, if_pos hlt]
  rfl

/-- **The queried nodes are fixed by pinning.** Together: on the win event, every one of the
`σ.k + 1` nodes the game reads is already pinned. Part (1) is unconditional; part (2) is
`pinNode_nodeC_of_sg` fed by `sg_determined_of_verifyWith` applied to `wireWins`' own
`verifyWith` call. -/
private theorem pinNode_nodes (σ : SRS C.Point) (claim : Ipa.Input C σ.k m p)
    (O : IpaNode C σ.k → Prechallenge) (π : Ipa.Proof C σ.k) :
    (∀ i : Fin σ.k,
        pinNode σ O (nodeU (Ipa.cipOf claim) π i) = nodeU (Ipa.cipOf claim) π i) ∧
      (wireWins σ claim O π →
        pinNode σ O (nodeC (Ipa.cipOf claim) π) = nodeC (Ipa.cipOf claim) π) := by
  refine ⟨fun i => pinNode_nodeU σ _ O π i, fun hw => ?_⟩
  refine pinNode_nodeC_of_sg σ _ O π ?_
  have hsg := sg_determined_of_verifyWith σ (uBaseOf C (Ipa.cipOf claim))
    (Vector.ofFn fun i => expandPre C (O (nodeU (Ipa.cipOf claim) π i)))
    (expandPre C (O (nodeC (Ipa.cipOf claim) π))) { claim with proof := π } hw
  simpa using hsg

/-- **`wireWins` reads its table only at the `σ.k + 1` nodes of `π`.** The locality statement
behind `wireWins_pinTable`: the query points are determined by `cip` and `π` and do not depend on
the table, so two tables agreeing there decide the win identically. -/
private theorem wireWins_congr (σ : SRS C.Point) (claim : Ipa.Input C σ.k m p)
    {O₁ O₂ : IpaNode C σ.k → Prechallenge} (π : Ipa.Proof C σ.k)
    (hu : ∀ i : Fin σ.k,
      O₁ (nodeU (Ipa.cipOf claim) π i) = O₂ (nodeU (Ipa.cipOf claim) π i))
    (hc : O₁ (nodeC (Ipa.cipOf claim) π) = O₂ (nodeC (Ipa.cipOf claim) π)) :
    wireWins σ claim O₁ π ↔ wireWins σ claim O₂ π := by
  have hv : (fun i : Fin σ.k => expandPre C (O₁ (nodeU (Ipa.cipOf claim) π i)))
      = fun i : Fin σ.k => expandPre C (O₂ (nodeU (Ipa.cipOf claim) π i)) :=
    funext fun i => by rw [hu i]
  unfold wireWins
  rw [hv, hc]

/-- **The win event factors through the sg-forgetting map.** Since `pinTable σ O` factors through
`sgForget` (`pinTable_factors`), the win event is decided by a table on the honest, sg-free node
domain — the one the deployed idealization is a statement about.

At the round nodes the two tables agree unconditionally (`pinNode_nodeU`), so both runs read the
*same* round challenge vector; that is what makes both directions available. Forward,
`pinNode_nodes`(2) gives agreement at the Schnorr node too. Backward,
`sg_determined_of_verifyWith` applied to the *pinned* run pins `π.sg` to `msm` at the pinned round
challenges, which by the previous sentence are the unpinned ones — precisely the condition
`pinNode_nodeC_of_sg` asks for. -/
theorem wireWins_pinTable (σ : SRS C.Point) (claim : Ipa.Input C σ.k m p)
    (O : IpaNode C σ.k → Prechallenge) (π : Ipa.Proof C σ.k) :
    wireWins σ claim O π ↔ wireWins σ claim (pinTable σ O) π := by
  have hu : ∀ i : Fin σ.k,
      O (nodeU (Ipa.cipOf claim) π i) = pinTable σ O (nodeU (Ipa.cipOf claim) π i) := by
    intro i
    rw [pinTable, pinNode_nodeU σ _ O π i]
  constructor
  · intro hw
    refine (wireWins_congr σ claim π hu ?_).mp hw
    rw [pinTable, (pinNode_nodes σ claim O π).2 hw]
  · intro hw
    refine (wireWins_congr σ claim π hu ?_).mpr hw
    have hsg := sg_determined_of_verifyWith σ (uBaseOf C (Ipa.cipOf claim))
      (Vector.ofFn fun i => expandPre C (pinTable σ O (nodeU (Ipa.cipOf claim) π i)))
      (expandPre C (pinTable σ O (nodeC (Ipa.cipOf claim) π)))
      { claim with proof := π } hw
    have hsg' : π.sg = Ipa.msm C σ.g
        (bPolyCoefficients fun i => expandPre C (O (nodeU (Ipa.cipOf claim) π i))) := by
      simpa [← hu] using hsg
    rw [pinTable, pinNode_nodeC_of_sg σ _ O π hsg']

/-- **The fork's rewind points are sg-free or already queried.** For every node `t` and index `i`,
the chained node `chainAt t i` of `prefixDecode_nodes` either has `sg = none` (when `i < k`) or is
`t` itself (when `i = k`). Consequently the only extra oracle point the fork machinery visits
beyond the queried nodes carries no `sg` data at all, and `wireWins_pinTable` covers the remaining
one. -/
theorem chainAt_sg (cip : C.ScalarField) (t : IpaNode C k) (i : Fin (k + 1)) :
    ((i : ℕ) < k → ((prefixDecode_nodes cip).chainAt t i).sg = none) ∧
      (¬ ((i : ℕ) < k) → (prefixDecode_nodes cip).chainAt t i = t) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [prefixDecode_nodes, if_pos h]
  · simp only [prefixDecode_nodes, if_neg h]

/-! ## The deployed extractor and the deployed bound -/

section Extractor

variable [Module C.ScalarField C.Point]

/-- **The deployed extractor**: `kimchiExtract` at `T := IpaNode C σ.k`,
`Pre := Fin (2 ^ 128)`, `Pf := Ipa.Proof C σ.k`, `expand := expandPre C`,
`proofOf := toOpening`, `prefixes := nodes cip`, with the `DecodesFromPrefixes` argument supplied
by `decodesFromPrefixes_nodes`.

It is a plain `def` — *never* `noncomputable`: the return type is data, and its computability is
the gate that distinguishes a reduction that computes the break from one that merely asserts a
relation exists. -/
def deployedExtract (σ : SRS C.Point) (cip : C.ScalarField)
    (b : Fin (2 ^ σ.k) → C.ScalarField) (v : C.ScalarField) (P : C.Point)
    (pg : Fin (2 ^ σ.k) → C.ScalarField) (pw : C.ScalarField)
    (hP : P = commitGen σ.g pg + pw • σ.h)
    (A : Zcash.Snark.OracleComp (IpaNode C σ.k) Prechallenge (Ipa.Proof C σ.k))
    (O : IpaNode C σ.k → Prechallenge)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (σ.k + 1)) :
    Option (OpeningOrBreak { σ with U := uBaseOf C cip } P b v) :=
  kimchiExtract { σ with U := uBaseOf C cip } b v P pg pw hP (expandPre C) A toOpening
    (nodes cip) (decodesFromPrefixes_nodes _ cip) O coins

/-- **The deployed single-claim bound.** The measure of the set of oracle tables on which the
adversary convinces the deployed *wire* verifier while the extractor fails is at most
`(Q + σ.k + 1) · 3 / 2 ^ 128` — the operational query-loss slice, one `3 / 2 ^ 128` per adversary
query and per forked round, over the prechallenge domain.

Proved by `kimchiExtract_failure_measure_le` at the instantiation of `deployedExtract`: the
forward half of `wireWins_iff_wins` makes the deployed failure set a subset of the abstract one, and
`card_prechallenge` rewrites `3 / |Pre|` into `3 / 2 ^ 128`. The two hypotheses on `expandPre`
are *theorems* at both deployed curves (`expandPre_{vesta,pallas}_{injective,ne_zero}`). -/
theorem deployedExtract_failure_measure_le
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hinj : Function.Injective (expandPre C)) (hne : ∀ q, expandPre C q ≠ 0)
    (σ : SRS C.Point) (claim : Ipa.Input C σ.k m p)
    (pg : Fin (2 ^ σ.k) → C.ScalarField) (pw : C.ScalarField)
    (hP : combinedCommitment claim.polyscale claim.commitmentFn
      = commitGen σ.g pg + pw • σ.h)
    (A : Zcash.Snark.OracleComp (IpaNode C σ.k) Prechallenge (Ipa.Proof C σ.k))
    {Q : ℕ} (hQ : A.QueryBound Q)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (σ.k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype (IpaNode C σ.k → Prechallenge)).toOuterMeasure
        {O | wireWins σ claim O (A.run O) ∧
          deployedExtract σ (Ipa.cipOf claim)
              (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn)
              (Ipa.cipOf claim) (combinedCommitment claim.polyscale claim.commitmentFn)
              pg pw hP A O coins = none}
      ≤ (Q + σ.k + 1) * (3 / (2 ^ 128 : ℕ)) := by
  -- (a) the deployed failure set is the abstract one: `wireWins_iff_wins` at exactly these
  -- arguments, and `deployedExtract` is `kimchiExtract` at the deployed instantiation by
  -- definition (so the second conjunct transfers by `exact`, never by `rw`).
  have hsub :
      {O : IpaNode C σ.k → Prechallenge | wireWins σ claim O (A.run O) ∧
          deployedExtract σ (Ipa.cipOf claim)
              (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn)
              (Ipa.cipOf claim) (combinedCommitment claim.polyscale claim.commitmentFn)
              pg pw hP A O coins = none}
        ⊆ {O : IpaNode C σ.k → Prechallenge |
          Wins { σ with U := uBaseOf C (Ipa.cipOf claim) }
              (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn)
              (Ipa.cipOf claim) (combinedCommitment claim.polyscale claim.commitmentFn)
              (expandPre C) toOpening (nodes (Ipa.cipOf claim)) O (A.run O) ∧
            kimchiExtract { σ with U := uBaseOf C (Ipa.cipOf claim) }
                (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn)
                (Ipa.cipOf claim) (combinedCommitment claim.polyscale claim.commitmentFn)
                pg pw hP (expandPre C) A toOpening (nodes (Ipa.cipOf claim))
                (decodesFromPrefixes_nodes _ (Ipa.cipOf claim)) O coins = none} := by
    rintro O ⟨hw, hf⟩
    exact ⟨(wireWins_iff_wins hsmul σ claim O (A.run O)).mp hw, hf⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  -- (b) the abstract bound, instantiated; then `3 / |Pre|` is `3 / 2 ^ 128`.
  refine le_trans (kimchiExtract_failure_measure_le
    { σ with U := uBaseOf C (Ipa.cipOf claim) }
    (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn)
    (Ipa.cipOf claim) (combinedCommitment claim.polyscale claim.commitmentFn)
    pg pw hP (expandPre C) hinj hne A hQ toOpening (nodes (Ipa.cipOf claim))
    (decodesFromPrefixes_nodes _ (Ipa.cipOf claim)) (prefixDecode_nodes (Ipa.cipOf claim))
    coins hcoins) (le_of_eq ?_)
  rw [card_prechallenge]

/-- **The deployed extractor's call count** — `kimchiExtractRuns` at the same instantiation
`deployedExtract` uses, so it counts that extractor's own recursion and cannot drift from it.
Consumed by `DeployedFamily.ReductionEfficient` (`Forking/KnowledgeSoundness.lean`). -/
def deployedExtractRuns (σ : SRS C.Point) (cip : C.ScalarField)
    (b : Fin (2 ^ σ.k) → C.ScalarField) (v : C.ScalarField) (P : C.Point)
    (A : Zcash.Snark.OracleComp (IpaNode C σ.k) Prechallenge (Ipa.Proof C σ.k))
    (O : IpaNode C σ.k → Prechallenge)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (σ.k + 1)) : ℕ :=
  kimchiExtractRuns { σ with U := uBaseOf C cip } b v P (expandPre C) A toOpening
    (nodes cip) (decodesFromPrefixes_nodes _ cip) O coins

end Extractor

/-! ## The two anti-vacuity companions

The bound above is satisfiable by an extractor that always answers `none` *if* the win set is
empty, and it would be false-but-unprovable if the win condition were satisfiable without
knowledge. Both are ruled out — the second one here (`verifyWith_of_deferred_delta` below), the
first one in `Forking/Honest.lean`, which builds the honest machine at this node domain and states
its conclusion with the `wireWins` event the measure bound is actually about (available there via
`wireWins_iff_wins`). -/

/-- **The deferred-`δ` cheat, and what blocks it.** With `lr` all-zero, `z1 = z2 = 0`,
`sg := msm C σ.g (bPolyCoefficients chal)` and `δ := -(c • Q)`, the wire verifier accepts at
*any* claim: the `sg` check is definitional and the Schnorr equation reads `0 = 0`.

This is the deployed form of the deferred-δ counterexample, and it is the reason the
Schnorr node of `nodes` must carry `δ`: an adversary allowed to choose `δ` after reading `c`
convinces the wire verifier while knowing nothing, so no extractor could succeed and
`deployedExtract_failure_measure_le` would be false. Commit-then-challenge
(`decodesFromPrefixes_nodes`) is what excludes it — a *theorem* about the deployed node
structure, not an informal reading of the protocol. -/
theorem verifyWith_of_deferred_delta (σ : SRS C.Point) (uBase : C.Point)
    (chals : Vector C.ScalarField σ.k) (c : C.ScalarField) (claim : Ipa.Input C σ.k m p) :
    Ipa.verifyWith C σ uBase chals c
      { claim with
        proof :=
          { lr := Vector.replicate σ.k (0, 0)
            delta := -(c.val •
              (Ipa.combineCommitments C claim.polyscale claim.commitments.toArray
                + (Ipa.cipOf claim).val • uBase))
            z1 := 0
            z2 := 0
            sg := Ipa.msm C σ.g (bPolyCoefficients fun i => chals[i]) } } = true := by
  have hfold : ∀ (n : ℕ) (cs : List C.ScalarField) (init : C.Point),
      ((List.replicate n ((0 : C.Point), (0 : C.Point))).zip cs).foldl
          (fun (acc : C.Point) (LRu : (C.Point × C.Point) × C.ScalarField) =>
            acc + (LRu.2⁻¹.val • LRu.1.1 + LRu.2.val • LRu.1.2)) init = init := by
    intro n
    induction n with
    | zero => intro cs init; simp
    | succ n ih =>
      intro cs init
      cases cs with
      | nil => simp
      | cons u t => rw [List.replicate_succ, List.zip_cons_cons, List.foldl_cons, ih]; simp
  have hcip : ∀ π : Ipa.Proof C σ.k, Ipa.cipOf ({ claim with proof := π }) = Ipa.cipOf claim :=
    fun _ => rfl
  simp only [Ipa.verifyWith, Bool.and_eq_true, decide_eq_true_eq, ← Array.foldl_toList,
    Vector.toArray_replicate, Array.toList_zip, Array.toList_replicate, hfold, hcip,
    and_true, smul_add, ZMod.val_zero, zero_smul, zero_mul, add_zero]
  abel

end Bulletproof.Ipa.Forking
