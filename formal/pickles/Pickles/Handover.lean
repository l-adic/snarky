import Kimchi.Columns
import Pickles.StepWrap
import Pickles.WrapStep

/-!
# The accumulator handover along a chain of proofs

Pickles never checks a proof's deferred `sg` equation (`SgOk`) on the proof itself: the proof's
`(sg, round challenges)` becomes an old accumulator of the next proof on the same curve, whose
batch opening checks it (`accOk`). Each capstone gives its proof `kimchiVerify` from `SgOk`.
This module composes those along a chain in which each proof carries its predecessor's
obligation (`carry`), and shows that the circuits carry it: the accumulator one link emits is
an old accumulator of the step proof the next link verifies.

## Main definitions

* `WrapStepRun`: one link's run, a wrap circuit and the next step circuit with the slot of it
  that verifies the wrap proof; `WrapStepRun.Emits` and `WrapStepRun.Consumes` are what the
  capstone says of it, `WrapStepRun.Hands` the tie between two links.

## Main results

* `chain_kimchiVerify_iff`: in a carried chain, every proof verifies exactly when every
  carried accumulator passes `accOk`, the last proof's own `SgOk` being given.
* `opened_by_next`: the accumulator a link emits is an old accumulator of the step proof the
  next link verifies, unless Poseidon collides on the messages passed between them.

## Implementation notes

The chain is deterministic: nothing here says that a proof's acceptance certifies the
accumulators it carries. The first opening equation can be solved for any old `sg`, so that
implication is cryptographic and stays out of the tree; the theorem reduces verification to
exactly the `accOk` checks.

Two links share no cells: each circuit run has its own valuation, and an accumulator reaches the
next link only through the digests of its messages, carried in public inputs. The wrap digest
crosses the step circuit's statement reduced into the step field, so the wrap collision
`opened_by_next` names is one of the reduced digests (`WrapStepRun.WrapCollision`).
-/

namespace Pickles

open Kimchi.Verifier Bulletproof Bulletproof.Ipa

variable {C : KimchiCurve}

/-- **A carried chain verifies exactly when its carried accumulators pass the deferred
check.** Each proof's capstone gives it `kimchiVerify` from its `SgOk`, `carry` makes a proof's
`SgOk` the next proof's `accOk`, and the last proof's `SgOk` is given. -/
theorem chain_kimchiVerify_iff {m : ℕ} (σ : SRS C.Point) {nc : Fin (m + 1) → ℕ}
    (cvk : (k : Fin (m + 1)) → KimchiVK C (nc k))
    (P : (k : Fin (m + 1)) → KimchiProof C (nc k) σ.k)
    (pub : Fin (m + 1) → Array C.ScalarField)
    -- each proof's capstone
    (hcap : ∀ k, Guards C (cvk k) (P k) (pub k) →
      SgOk σ (cvk k) (P k) (pub k) → kimchiVerify C σ (cvk k) (P k) (pub k) = true)
    (hg : ∀ k, Guards C (cvk k) (P k) (pub k))
    -- each proof carries its predecessor's obligation as its old accumulator `j k`
    (j : (k : Fin m) → Fin (P k.succ).olds.size)
    (hcarry : ∀ k : Fin m,
      carry σ (cvk k.castSucc) (P k.castSucc) (pub k.castSucc) (P k.succ) (j k) = true)
    -- the last proof's deferred equation, checked out of circuit
    (hlast : SgOk σ (cvk (Fin.last m)) (P (Fin.last m)) (pub (Fin.last m))) :
    (∀ k, kimchiVerify C σ (cvk k) (P k) (pub k) = true) ↔
      ∀ k : Fin m, accOk σ (P k.succ).olds[j k] = true := by
  constructor
  · intro hv k
    exact (sgOk_iff_accOk_of_carry σ _ _ _ _ _ (hcarry k)).mp
      (sgOk_of_kimchiVerify σ _ _ _ (hv k.castSucc))
  · intro hacc k
    refine hcap k (hg k) ?_
    induction k using Fin.lastCases with
    | last => exact hlast
    | cast k => exact (sgOk_iff_accOk_of_carry σ _ _ _ _ _ (hcarry k)).mpr (hacc k)

section Links

open Snarky Snarky.Kimchi
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-! ## One link's run -/

/-- One link's run, as `wrapStep_kimchiVerify` names it: a wrap circuit's statement and cells,
the next step circuit's cells, and the slot of it that verifies the wrap proof. -/
structure WrapStepRun (branches w ncStep kw ks n wNext : ℕ) (ws : Fin n → ℕ)
    (slotWidths : Vector (Fin (MaxProofsVerified + 1)) w) where
  /-- The wrap circuit's valuation. -/
  Vw : Valuation Fq
  /-- The step circuit's valuation. -/
  Vs : Valuation Fp
  /-- The wrap circuit's statement. -/
  wrapStmt : StatementPacked ks (Type1 (FVar Fq)) (FVar Fq)
  /-- The wrap circuit's finalize cells. -/
  wrapFinalizeOut : WrapMainFinalizeOut branches w ncStep kw slotWidths
  /-- The wrap circuit's verify cells. -/
  wrapVerifyOut : WrapMainVerifyOut w ncStep kw ks
  /-- The step circuit's cells. -/
  stepOut : StepMainOut n wNext ws 1 ncStep kw ks
  /-- Each slot verifies at most `MaxProofsVerified` accumulators. -/
  hws : ∀ i, ws i ≤ MaxProofsVerified
  /-- The `sg` padding the missing accumulators. -/
  dummySg : AffinePoint (FVar Fp)
  /-- The slot that verifies the wrap proof. -/
  i : Fin n
  /-- The slot is at the wrap circuit's width. -/
  hwi : ws i = w
  /-- The slot's mask. -/
  ms : Vector Bool (ws i)
  /-- The slot's key cells. -/
  key : VkComms 1 (AffinePoint (FVar Fp))

namespace WrapStepRun

variable {branches w ncStep kw ks n wNext : ℕ} {ws : Fin n → ℕ}
  {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
  (r : WrapStepRun branches w ncStep kw ks n wNext ws slotWidths)

/-- The slot's input cells. -/
def inp : VerifyOneInput ks kw 1 ncStep (ws r.i) :=
  slotInput (r.hws r.i) r.dummySg r.stepOut.prevs[r.i] (r.stepOut.slots r.i) r.stepOut.unfs[r.i]
    r.stepOut.msgs[r.i]

/-- The link's tie and hashing: the slot's wrap proof was made at the wrap circuit's public input
(a premise of `wrapStep_kimchiVerify`), and both circuits hash their messages (its conclusions).
-/
def Hashes (cvk : KimchiVK IpaPallas.curve 1) (dummy : Vector Fq kw) : Prop :=
  CircuitType.Reads r.Vw r.wrapStmt (r.inp.packedAt cvk r.Vs r.ms) ∧
  r.wrapVerifyOut.HashesMessages r.Vw dummy r.wrapStmt r.wrapFinalizeOut ∧
  r.stepOut.HashesMessages r.Vs

/-- The link emits `A`, as `wrapStep_kimchiVerify` concludes. -/
def Emits (cvk : KimchiVK IpaPallas.curve 1) (dummy : Vector Fq kw)
    (A : Accumulator IpaVesta.curve ks) : Prop :=
  r.Hashes cvk dummy ∧
  WrapStep.emittedAccumulator r.Vw r.Vs r.i r.wrapVerifyOut r.wrapFinalizeOut r.stepOut = A

/-- The link consumes `olds`, as `wrapStep_kimchiVerify` concludes. -/
def Consumes (cvk : KimchiVK IpaPallas.curve 1) (dummy : Vector Fq kw)
    (olds : List (Accumulator IpaVesta.curve ks)) : Prop :=
  r.Hashes cvk dummy ∧
  WrapStep.consumedAccumulators r.Vw r.Vs r.wrapFinalizeOut (r.inp.messagesForNextStepProof r.key)
    r.hwi r.ms = olds

end WrapStepRun

/-! ## Two links -/

variable {branches w ncStep kw ks n wNext : ℕ} {ws : Fin n → ℕ}
  {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
  {branches' ncStep' ks' n' wNext' : ℕ} {ws' : Fin n' → ℕ}
  {slotWidths' : Vector (Fin (MaxProofsVerified + 1)) wNext}

/-- The link `rk` hands its step proof to the next link `rk1`: the step proof `rk`'s step circuit
makes is the one `rk1`'s wrap circuit verifies, and `rk1`'s slot keeps exactly `rk`'s slots. -/
def WrapStepRun.Hands (rk : WrapStepRun branches w ncStep kw ks n wNext ws slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw ks' n' wNext' ws' slotWidths') : Prop :=
  CircuitType.Reads rk.Vs rk.stepOut.out
    (StepStatement.ofWrap rk1.Vw rk1.wrapVerifyOut.statement) ∧
  ∀ (j : ℕ) (hj : j < ws' rk1.i), rk1.ms[j] = decide (ws' rk1.i - n ≤ j)

/-- The next link's wrap slot of the slot `rk.i`: the step statement front-pads. -/
def WrapStepRun.slotIndex (rk : WrapStepRun branches w ncStep kw ks n wNext ws slotWidths)
    (hn : n ≤ wNext) : Fin wNext :=
  ⟨wNext - n + rk.i, by omega⟩

/-- The wrap message `rk` sends and the one the next link `rk1` rebuilds for it read differently,
but their digests agree once the step circuit reads them. -/
def WrapStepRun.WrapCollision (rk : WrapStepRun branches w ncStep kw ks n wNext ws slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw ks' n' wNext' ws' slotWidths')
    (hn : n ≤ wNext) (dummy : Vector Fq kw) : Prop :=
  ∃ (sg sg' : AffinePoint Fq) (chals : Vector (Vector Fq kw) w)
    (chals' : Vector (Vector Fq kw) slotWidths'[rk.slotIndex hn]),
    CircuitType.Reads rk.Vw
      (rk.wrapVerifyOut.messagesForNextWrapProof rk.wrapFinalizeOut).challengePolynomialCommitment
      sg ∧
    CircuitType.Reads rk.Vw
      (rk.wrapVerifyOut.messagesForNextWrapProof rk.wrapFinalizeOut).oldBulletproofChallenges
      chals ∧
    CircuitType.Reads rk1.Vw
      (rk1.wrapFinalizeOut.messagesForNextWrapProof (rk.slotIndex hn)).challengePolynomialCommitment
      sg' ∧
    CircuitType.Reads rk1.Vw
      (rk1.wrapFinalizeOut.messagesForNextWrapProof (rk.slotIndex hn)).oldBulletproofChallenges
      chals' ∧
    Collision IpaVesta.curve.sponge.params (fun x : Fq => ((ToNat.toNat x : ℕ) : Fp))
      (wrapMsgInput dummy ⟨sg, chals⟩) (wrapMsgInput dummy ⟨sg', chals'⟩)

/-- The step message `rk` sends and the one the next link `rk1`'s slot rebuilds read differently,
but hash alike. -/
def WrapStepRun.StepCollision (rk : WrapStepRun branches w ncStep kw ks n wNext ws slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw ks' n' wNext' ws' slotWidths')
    (cvk : KimchiVK IpaPallas.curve 1) : Prop :=
  ∃ (vk : VkComms 1 (AffinePoint Fp)) (sgs : Vector (AffinePoint Fp) n)
    (chals : Vector (Vector Fp ks) n),
    CircuitType.Reads rk.Vs rk.stepOut.messagesForNextStepProof.dlogPlonkIndex vk ∧
    CircuitType.Reads rk.Vs rk.stepOut.messagesForNextStepProof.challengePolynomialCommitments
      sgs ∧
    CircuitType.Reads rk.Vs rk.stepOut.messagesForNextStepProof.oldBulletproofChallenges chals ∧
    Collision IpaPallas.curve.sponge.params id
      (stepMsgInput
        ⟨rk.stepOut.messagesForNextStepProof.appState.map (·.val rk.Vs), vk, sgs, chals⟩)
      (cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y])
        ++ rk1.inp.appState.map (·.val rk1.Vs)
        ++ keptValues rk1.Vs rk1.ms (rk1.inp.prevSgs.zip rk1.inp.prevChallenges))

/-! ## Proof helpers -/

section Helpers

variable {F : Type} [Field F]

private theorem reads_pt (V : Valuation F) (P : AffinePoint (FVar F)) :
    CircuitType.Reads V P (⟨P.x.val V, P.y.val V⟩ : AffinePoint F) :=
  reads_affinePoint.mpr ⟨rfl, rfl⟩

private theorem reads_pts {m : ℕ} (V : Valuation F) (v : Vector (AffinePoint (FVar F)) m) :
    CircuitType.Reads V v (v.map fun P => (⟨P.x.val V, P.y.val V⟩ : AffinePoint F)) :=
  CircuitType.reads_vector.mpr fun i _ => by rw [Vector.getElem_map]; exact reads_pt V _

private theorem reads_vecs {m k : ℕ} (V : Valuation F) (v : Vector (Vector (FVar F) k) m) :
    CircuitType.Reads V v (v.map (·.map (·.val V))) :=
  CircuitType.reads_vector.mpr fun i _ => CircuitType.reads_vector.mpr fun j _ => by simp

private theorem reads_key {nc : ℕ} (V : Valuation F) (key : VkComms nc (AffinePoint (FVar F))) :
    CircuitType.Reads V key (key.map fun P => (⟨P.x.val V, P.y.val V⟩ : AffinePoint F)) := by
  rw [CircuitType.reads_ofEquiv]
  simp only [VkComms.equivProd, VkComms.map, Equiv.coe_fn_mk, CircuitType.reads_prod]
  have hcols : ∀ {m : ℕ} (c : Vector (Vector (AffinePoint (FVar F)) nc) m),
      CircuitType.Reads V c (c.map (·.map fun P => (⟨P.x.val V, P.y.val V⟩ : AffinePoint F))) :=
    fun c => CircuitType.reads_vector.mpr fun i _ => by
      rw [Vector.getElem_map]; exact reads_pts V _
  exact ⟨hcols _, hcols _, reads_pts V _, reads_pts V _, reads_pts V _, reads_pts V _,
    reads_pts V _, reads_pts V _⟩

/-- Lists of chunks of one length with equal flattenings are equal. -/
private theorem flatten_inj {α : Type} {m : ℕ} :
    ∀ {L1 L2 : List (List α)}, (∀ c ∈ L1, c.length = m) → (∀ c ∈ L2, c.length = m) →
      L1.length = L2.length → L1.flatten = L2.flatten → L1 = L2
  | [], [], _, _, _, _ => rfl
  | c1 :: L1, c2 :: L2, h1, h2, hl, hf => by
    simp only [List.flatten_cons] at hf
    obtain ⟨hc, ht⟩ := List.append_inj hf (by rw [h1 c1 (by simp), h2 c2 (by simp)])
    rw [hc, flatten_inj (fun c hc => h1 c (by simp [hc])) (fun c hc => h2 c (by simp [hc]))
      (by simpa using hl) ht]
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

/-- With the first `m − n` entries masked out, the kept values are the last `n` entries'. -/
private theorem keptValues_front {m n k : ℕ} (V : Valuation F) (ms : Vector Bool m)
    (proofs : Vector (AffinePoint (FVar F) × Vector (FVar F) k) m)
    (hms : ∀ (j : ℕ) (hj : j < m), ms[j] = decide (m - n ≤ j)) :
    keptValues V ms proofs
      = List.flatten ((proofs.toList.drop (m - n)).map fun q =>
          (q.1.x :: q.1.y :: q.2.toList).map (·.val V)) := by
  have hL : (Vector.zipWith (fun b (q : AffinePoint (FVar F) × Vector (FVar F) k) =>
      if b then (q.1.x :: q.1.y :: q.2.toList).map (·.val V) else []) ms proofs).toList
      = List.replicate (m - n) [] ++ (proofs.toList.drop (m - n)).map fun q =>
          (q.1.x :: q.1.y :: q.2.toList).map (·.val V) := by
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [Vector.getElem_toList, Vector.getElem_zipWith, hms j (by simpa using h1)]
    by_cases hj : j < m - n
    · rw [List.getElem_append_left (by simpa using hj)]
      simp [show ¬(m - n ≤ j) by omega]
    · rw [List.getElem_append_right (by simpa using hj)]
      simp [show m - n ≤ j by omega, show m - n + (j - (m - n)) = j by omega]
  unfold keptValues
  rw [hL, List.flatten_append]
  simp

private theorem mem_applyMask {α : Type} {m : ℕ} (v : Vector α m) (ms : Vector Bool m) (j : ℕ)
    (hj : j < m) (h : ms[j] = true) : v[j] ∈ v.applyMask ms := by
  unfold Vector.applyMask
  refine List.mem_map.mpr ⟨(v[j], ms[j]), List.mem_filter.mpr ⟨?_, by simpa using h⟩, rfl⟩
  exact List.mem_iff_getElem.mpr ⟨j, by simpa using hj, by simp⟩

end Helpers

private theorem toFp_redFq (x : Fp) : ((ZMod.val (redFq x) : ℕ) : Fp) = x := by
  rw [val_redFq, ZMod.natCast_zmod_val]

private theorem readPt_congr {V V' : Valuation Fq} {p q : AffinePoint (FVar Fq)}
    (hx : p.x.val V = q.x.val V') (hy : p.y.val V = q.y.val V') :
    readPt (C := IpaVesta.curve) V p = readPt (C := IpaVesta.curve) V' q := by
  simp only [readPt, hx, hy]

/-- A tie's two message digests. -/
private theorem digests_of_tie {ks k ncw ncs w : ℕ} {Vw : Valuation Fq} {Vs : Valuation Fp}
    {stmt : StatementPacked ks (Type1 (FVar Fq)) (FVar Fq)} {inp : VerifyOneInput ks k ncw ncs w}
    {cvk : KimchiVK IpaPallas.curve ncw} {ms : Vector Bool w}
    (h : CircuitType.Reads Vw stmt (inp.packedAt cvk Vs ms)) :
    stmt.digests[1].val Vw = redFq (inp.messagesForNextWrapProof.val Vs) ∧
    stmt.digests[2].val Vw = redFq (inp.stepMsgDigest cvk Vs ms) := by
  simp only [CircuitType.reads_ofEquiv, StatementPacked.equivProd, Equiv.coe_fn_mk,
    CircuitType.reads_prod] at h
  have hd := h.2.2.2.1
  exact ⟨CircuitType.reads_fvar.mp (CircuitType.reads_vector.mp hd 1 (by decide)),
    CircuitType.reads_fvar.mp (CircuitType.reads_vector.mp hd 2 (by decide))⟩

/-- A step statement reading as a wrap circuit's: its digests are the wrap cells' reductions. -/
private theorem digests_of_ofWrap {k w : ℕ} {Vs : Valuation Fp} {Vw : Valuation Fq}
    {out : StepStatement (UnfVar k) (FVar Fp) w}
    {st : StepStatement (UnfinalizedProof k (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) (FVar Fq) w}
    (h : CircuitType.Reads Vs out (StepStatement.ofWrap Vw st)) :
    out.proofState.messagesForNextStepProof.val Vs
      = ((ZMod.val (st.proofState.messagesForNextStepProof.val Vw) : ℕ) : Fp) ∧
    ∀ (j : ℕ) (hj : j < w), out.messagesForNextWrapProof[j].val Vs
      = ((ZMod.val (st.messagesForNextWrapProof[j].val Vw) : ℕ) : Fp) := by
  simp only [CircuitType.reads_ofEquiv, StepStatement.equivProd, StepProofState.equivProd,
    Equiv.coe_fn_mk, CircuitType.reads_prod] at h
  refine ⟨CircuitType.reads_fvar.mp h.1.2, fun j hj => ?_⟩
  rw [CircuitType.reads_fvar.mp (CircuitType.reads_vector.mp h.2 j hj)]
  simp only [StepStatement.ofWrap, Vector.getElem_map]
  rfl

/-- **The next step proof opens each emitted accumulator.** The link `rk` emits `A`, and the next
link `rk1` consumes the olds of the step proof `cp` that `rk`'s step circuit made. Then `A` is one
of `cp`'s olds, which `cp`'s batch opens first (`runStreamP_olds`), unless Poseidon collides on
the messages passed between the links. -/
theorem opened_by_next (rk : WrapStepRun branches w ncStep kw ks n wNext ws slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw ks n' wNext' ws' slotWidths')
    (hn : n ≤ wNext) (cvk cvk1 : KimchiVK IpaPallas.curve 1) (dummy : Vector Fq kw)
    (A : Accumulator IpaVesta.curve ks) (cp : KimchiProof IpaVesta.curve ncStep' ks)
    (he : rk.Emits cvk dummy A) (hc : rk1.Consumes cvk1 dummy cp.olds.toList)
    (hh : rk.Hands rk1) :
    A ∈ cp.olds.toList ∨ rk.WrapCollision rk1 hn dummy ∨ rk.StepCollision rk1 cvk1 := by
  obtain ⟨⟨htk, hWk, hSk⟩, hA⟩ := he
  obtain ⟨⟨htk1, hWk1, -⟩, hcons⟩ := hc
  obtain ⟨hpub, hmask⟩ := hh
  obtain ⟨hpubD, hpubM⟩ := digests_of_ofWrap hpub
  have hw1 := rk1.hwi
  -- link k's outgoing messages, read
  let mW := rk.wrapVerifyOut.messagesForNextWrapProof rk.wrapFinalizeOut
  let mS := rk.stepOut.messagesForNextStepProof
  let sg : AffinePoint Fq :=
    ⟨mW.challengePolynomialCommitment.x.val rk.Vw, mW.challengePolynomialCommitment.y.val rk.Vw⟩
  let chalsW := mW.oldBulletproofChallenges.map (·.map (·.val rk.Vw))
  let vk := mS.dlogPlonkIndex.map fun P => (⟨P.x.val rk.Vs, P.y.val rk.Vs⟩ : AffinePoint Fp)
  let sgs := mS.challengePolynomialCommitments.map fun P =>
    (⟨P.x.val rk.Vs, P.y.val rk.Vs⟩ : AffinePoint Fp)
  let chals := mS.oldBulletproofChallenges.map (·.map (·.val rk.Vs))
  -- link k1's rebuilt wrap message for the slot, read
  let j := rk.slotIndex hn
  let mW' := rk1.wrapFinalizeOut.messagesForNextWrapProof j
  let sg' : AffinePoint Fq :=
    ⟨mW'.challengePolynomialCommitment.x.val rk1.Vw, mW'.challengePolynomialCommitment.y.val rk1.Vw⟩
  let chalsW' := mW'.oldBulletproofChallenges.map (·.map (·.val rk1.Vw))
  -- the wrap digest, from link k's wrap circuit through its step circuit to link k1's wrap circuit
  have hwrapD : ((ZMod.val (wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg, chalsW⟩) : ℕ)
      : Fp) = ((ZMod.val (wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg', chalsW'⟩) : ℕ)
      : Fp) := by
    have h1 := hWk.1 sg chalsW (reads_pt _ _) (reads_vecs _ _)
    have h2 := (digests_of_tie htk).1
    have h3 := hSk.2 hn rk.i
    have h4 := hpubM (wNext - n + rk.i) (by omega)
    have h5 : (rk1.wrapVerifyOut.statement.messagesForNextWrapProof[wNext - n + rk.i]).val rk1.Vw
        = wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg', chalsW'⟩ :=
      hWk1.2.1 j sg' chalsW' (reads_pt _ _) (reads_vecs _ _)
    rw [← h1, h2, toFp_redFq]
    show rk.stepOut.msgs[rk.i].val rk.Vs = _
    rw [← h3, h4, h5]
  -- the step digest, from link k's step circuit through link k1's wrap circuit to its slot
  have hstepD : Poseidon.RandomOracle.hash IpaPallas.curve.sponge.params
        (stepMsgInput ⟨mS.appState.map (·.val rk.Vs), vk, sgs, chals⟩)
      = Poseidon.RandomOracle.hash IpaPallas.curve.sponge.params
        (cvk1.comms.indexPoints.flatMap (fun P => [P.x, P.y])
          ++ rk1.inp.appState.map (·.val rk1.Vs)
          ++ keptValues rk1.Vs rk1.ms (rk1.inp.prevSgs.zip rk1.inp.prevChallenges)) := by
    have h1 := hSk.1 vk sgs chals (reads_key _ _) (reads_pts _ _) (reads_vecs _ _)
    have h3 := hWk1.2.2
    have h4 := (digests_of_tie htk1).2
    rw [h3] at h4
    rw [h4, toFp_redFq] at hpubD
    rw [Poseidon.RandomOracle.hash_eq_squeeze, Poseidon.RandomOracle.hash_eq_squeeze]
    have e := h1.symm.trans hpubD
    simp only [stepMsgDigest, VerifyOneInput.stepMsgDigest, KimchiVK.indexState] at e
    simp only [Poseidon.absorb, List.foldl_append] at e ⊢
    exact e
  -- distinct step inputs collide
  by_cases hX : stepMsgInput ⟨mS.appState.map (·.val rk.Vs), vk, sgs, chals⟩
      = cvk1.comms.indexPoints.flatMap (fun P => [P.x, P.y])
          ++ rk1.inp.appState.map (·.val rk1.Vs)
          ++ keptValues rk1.Vs rk1.ms (rk1.inp.prevSgs.zip rk1.inp.prevChallenges)
  swap
  · exact Or.inr (Or.inr ⟨vk, sgs, chals, reads_key _ _, reads_pts _ _, reads_vecs _ _, hX,
      hstepD⟩)
  -- distinct wrap inputs collide
  by_cases hW : wrapMsgInput dummy ⟨sg, chalsW⟩ = wrapMsgInput dummy ⟨sg', chalsW'⟩
  swap
  · refine Or.inr (Or.inl ⟨sg, sg', chalsW, chalsW', reads_pt _ _, reads_vecs _ _, reads_pt _ _,
      reads_vecs _ _, hW, ?_⟩)
    rw [Poseidon.RandomOracle.hash_eq_squeeze, Poseidon.RandomOracle.hash_eq_squeeze]
    exact hwrapD
  left
  -- the commitment: both wrap inputs end with it
  obtain ⟨-, hsg⟩ := List.append_inj' hW rfl
  simp only [List.cons.injEq, and_true] at hsg
  -- the challenges: both step inputs end with the kept slots'
  set m := ws' rk1.i with hm
  have hmn : n ≤ m := hw1 ▸ hn
  simp only [stepMsgInput, MessagesForNextStepProof.proofs] at hX
  have hkept := keptValues_front rk1.Vs rk1.ms (rk1.inp.prevSgs.zip rk1.inp.prevChallenges) hmask
  rw [hkept] at hX
  have hC := (List.append_inj' hX (by
    simp [List.length_flatMap, List.length_flatten, Function.comp_def]
    omega)).2
  rw [List.flatMap_def] at hC
  have hchunks := flatten_inj (m := ks + 2)
    (by simp only [List.mem_map]; rintro _ ⟨q, -, rfl⟩; simp)
    (by simp only [List.mem_map]; rintro _ ⟨q, -, rfl⟩; simp) (by simp; omega) hC
  have hu := congrArg (fun L => L[rk.i.val]?) hchunks
  simp at hu
  obtain ⟨a, b, hab, -, -, hb⟩ := hu
  rw [List.getElem?_eq_getElem (by simp; omega), Option.some.injEq, List.getElem_zip] at hab
  simp only [Prod.mk.injEq] at hab
  obtain ⟨-, rfl⟩ := hab
  -- `A` is the kept entry at link k1's slot `j`
  have hb' : m - n + rk.i < m := by omega
  rw [← hcons, ← hA]
  convert mem_applyMask _ rk1.ms (m - n + rk.i) hb' (by rw [hmask]; simp; omega) using 1
  have hj : (⟨m - n + rk.i, by omega⟩ : Fin wNext) = j :=
    Fin.ext (by simp [j, WrapStepRun.slotIndex]; omega)
  simp only [WrapStep.emittedAccumulator, Accumulator.ofCells, Vector.getElem_zipWith,
    Vector.getElem_cast, Vector.getElem_finRange, VerifyOneInput.messagesForNextStepProof, hj]
  congr 1
  · exact readPt_congr hsg.1 hsg.2
  · apply Vector.toList_inj.mp
    simp only [Vector.toList_map]
    have hb2 : (rk1.inp.prevChallenges[m - n + rk.i]).toList.map (·.val rk1.Vs)
        = chals[(rk.i : ℕ)].toList := by
      rw [← hb]
      simp [hm]
    rw [hb2]
    simp [chals, mS, Vector.toList_map]

end Links

end Pickles
