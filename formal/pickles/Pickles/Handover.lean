import Kimchi.Columns
import Pickles.StepWrap
import Pickles.WrapStep

/-!
# The accumulator handover along a chain of proofs

Pickles never checks a proof's deferred `sg` equation (`SgOk`) on the proof itself: the proof's
`(sg, round challenges)` becomes an old accumulator of the next proof on the same curve, whose
batch opening checks it. Each capstone gives its proof `kimchiVerify` from `SgOk`. This module
shows that the circuits hand the accumulator over: the accumulator one link emits is an old
accumulator of the proof the next link verifies, which that proof's batch opens.

## Main definitions

* `WrapStepRun`: one link's run, a wrap circuit and the next step circuit with the slot of it
  that verifies the wrap proof; `WrapStepRun.Emits` and `WrapStepRun.Consumes` are what the
  capstone says of it, `WrapStepRun.Hands` the tie between two links.
* `StepWrapRun`: the same for a step circuit's slot verifying a wrap proof and the next wrap
  circuit.
* `WrapMsgCollision`, `StepMsgCollision`: two links' messages that read differently but whose
  digests agree.

## Main results

* `opened_by_next`, `opened_by_next_wrap`: the accumulator a link emits is an old accumulator of
  the step, respectively wrap, proof the next link verifies, unless Poseidon collides on the
  messages passed between them.

## Implementation notes

The handover is deterministic: nothing here says that a proof's acceptance certifies the
accumulators it carries. The first opening equation can be solved for any old `sg`, so that
implication is cryptographic and stays out of the tree.

Two links share no cells: each circuit run has its own valuation, and an accumulator reaches the
next link only through the digests of its messages, carried in public inputs. The wrap digest
crosses the step circuit's statement reduced into the step field, so the wrap collision both
theorems name is one of the reduced digests (`WrapMsgCollision`).
-/

namespace Pickles

open Kimchi.Verifier Bulletproof Bulletproof.Ipa

section Links

open Snarky Snarky.Kimchi
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-! ## Collisions between two links -/

/-- The wrap message a wrap circuit sends (its verify cells `out` over `fin`, under `V`) and the
one a later wrap circuit rebuilds for its slot `j` (`fin'`, under `V'`) read differently, but
their digests agree once a step circuit reads them. -/
def WrapMsgCollision {branches w ncStep kw ks branches' w' ncStep' : ℕ}
    {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
    {slotWidths' : Vector (Fin (MaxProofsVerified + 1)) w'}
    (V : Valuation Fq) (out : WrapMainVerifyOut w ncStep kw ks)
    (fin : WrapMainFinalizeOut branches w ncStep kw slotWidths) (V' : Valuation Fq)
    (fin' : WrapMainFinalizeOut branches' w' ncStep' kw slotWidths') (j : Fin w')
    (dummy : Vector Fq kw) : Prop :=
  ∃ (sg sg' : AffinePoint Fq) (chals : Vector (Vector Fq kw) w)
    (chals' : Vector (Vector Fq kw) slotWidths'[j]),
    CircuitType.Reads V (out.messagesForNextWrapProof fin).challengePolynomialCommitment sg ∧
    CircuitType.Reads V (out.messagesForNextWrapProof fin).oldBulletproofChallenges chals ∧
    CircuitType.Reads V' (fin'.messagesForNextWrapProof j).challengePolynomialCommitment sg' ∧
    CircuitType.Reads V' (fin'.messagesForNextWrapProof j).oldBulletproofChallenges chals' ∧
    Collision IpaVesta.curve.sponge.params (fun x : Fq => ((ToNat.toNat x : ℕ) : Fp))
      (wrapMsgInput dummy ⟨sg, chals⟩) (wrapMsgInput dummy ⟨sg', chals'⟩)

/-- The step message a step circuit sends (`out`, under `V`) and the one a later slot rebuilds
(`inp` with mask `ms`, under `V'`, over the key `cvk`) read differently, but hash alike. -/
def StepMsgCollision {n w : ℕ} {ws : Fin n → ℕ} {ncs kw ks k' ncs' w' : ℕ}
    (V : Valuation Fp) (out : StepMainOut n w ws 1 ncs kw ks) (V' : Valuation Fp)
    (inp : VerifyOneInput ks k' 1 ncs' w') (ms : Vector Bool w')
    (cvk : KimchiVK IpaPallas.curve 1) : Prop :=
  ∃ (vk : VkComms 1 (AffinePoint Fp)) (sgs : Vector (AffinePoint Fp) n)
    (chals : Vector (Vector Fp ks) n),
    CircuitType.Reads V out.messagesForNextStepProof.dlogPlonkIndex vk ∧
    CircuitType.Reads V out.messagesForNextStepProof.challengePolynomialCommitments sgs ∧
    CircuitType.Reads V out.messagesForNextStepProof.oldBulletproofChallenges chals ∧
    Collision IpaPallas.curve.sponge.params id
      (stepMsgInput ⟨out.messagesForNextStepProof.appState.map (·.val V), vk, sgs, chals⟩)
      (cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y]) ++ inp.appState.map (·.val V')
        ++ keptValues V' ms (inp.prevSgs.zip inp.prevChallenges))

/-! ## A wrap-step link -/

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

/-- The wrap message `rk` sends and the one the next link `rk1` rebuilds for it collide
(`WrapMsgCollision`). -/
def WrapStepRun.WrapCollision (rk : WrapStepRun branches w ncStep kw ks n wNext ws slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw ks n' wNext' ws' slotWidths')
    (hn : n ≤ wNext) (dummy : Vector Fq kw) : Prop :=
  WrapMsgCollision rk.Vw rk.wrapVerifyOut rk.wrapFinalizeOut rk1.Vw rk1.wrapFinalizeOut
    (rk.slotIndex hn) dummy

/-- The step message `rk` sends and the one the next link `rk1`'s slot rebuilds collide
(`StepMsgCollision`). -/
def WrapStepRun.StepCollision (rk : WrapStepRun branches w ncStep kw ks n wNext ws slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw ks n' wNext' ws' slotWidths')
    (cvk : KimchiVK IpaPallas.curve 1) : Prop :=
  StepMsgCollision rk.Vs rk.stepOut rk1.Vs rk1.inp rk1.ms cvk

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

private theorem readPt_congr {C : KimchiCurve} {V V' : Valuation C.BaseField}
    {p q : AffinePoint (FVar C.BaseField)}
    (hx : p.x.val V = q.x.val V') (hy : p.y.val V = q.y.val V') : readPt V p = readPt V' q := by
  simp only [readPt, hx, hy]

/-- Equal step inputs, the rebuilt one keeping exactly the last `n` of its `m` slots: its slot
`m − n + i` reads as the sent message's entry `i`. -/
private theorem kept_of_stepInput_eq {n m ks : ℕ} {V : Valuation Fp}
    (cvk : KimchiVK IpaPallas.curve 1) {app : List Fp} {vk : VkComms 1 (AffinePoint Fp)}
    {sgs : Vector (AffinePoint Fp) n} {chals : Vector (Vector Fp ks) n} {app' : List (FVar Fp)}
    {ms : Vector Bool m} {psgs : Vector (AffinePoint (FVar Fp)) m}
    {pchals : Vector (Vector (FVar Fp) ks) m}
    (hmask : ∀ (j : ℕ) (hj : j < m), ms[j] = decide (m - n ≤ j)) (hnm : n ≤ m)
    (h : stepMsgInput ⟨app, vk, sgs, chals⟩
      = cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y]) ++ app'.map (·.val V)
        ++ keptValues V ms (psgs.zip pchals))
    (i : Fin n) :
    psgs[m - n + i].x.val V = sgs[i].x ∧ psgs[m - n + i].y.val V = sgs[i].y ∧
      pchals[m - n + i].map (·.val V) = chals[i] := by
  simp only [stepMsgInput, MessagesForNextStepProof.proofs] at h
  rw [keptValues_front V ms (psgs.zip pchals) hmask] at h
  have hC := (List.append_inj' h (by
    simp [List.length_flatMap, List.length_flatten, Function.comp_def]
    omega)).2
  rw [List.flatMap_def] at hC
  have hchunks := flatten_inj (m := ks + 2)
    (by simp only [List.mem_map]; rintro _ ⟨q, -, rfl⟩; simp)
    (by simp only [List.mem_map]; rintro _ ⟨q, -, rfl⟩; simp) (by simp; omega) hC
  have hu := congrArg (fun L => L[i.val]?) hchunks
  simp at hu
  obtain ⟨a, b, hab, hx, hy, hb⟩ := hu
  rw [List.getElem?_eq_getElem (by simp; omega), Option.some.injEq, List.getElem_zip] at hab
  simp only [Prod.mk.injEq] at hab
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨by simpa using hx, by simpa using hy, Vector.toList_inj.mp ?_⟩
  simpa [Vector.toList_map] using hb

/-- An entry of padded challenge stacks, read: the dummy stack in the padding, the real stack
past it. -/
private theorem padChallenges_read {k w : ℕ} (V : Valuation Fq) (dummy : Vector Fq k)
    (real : Vector (Vector (FVar Fq) k) w) (hw : w ≤ MaxProofsVerified) (t : ℕ)
    (ht : t < MaxProofsVerified) :
    ((padChallenges dummy real hw)[t].map (·.val V)).toList
      = (List.replicate (MaxProofsVerified - w) dummy.toList
          ++ (real.map (·.map (·.val V))).toList.map Vector.toList)[t]'(by simp; omega) := by
  unfold padChallenges
  by_cases h : t < MaxProofsVerified - w
  · rw [List.getElem_append_left (by simpa using h)]
    simp [h, Function.comp_def, CVar.val]
  · rw [List.getElem_append_right (by simpa using h)]
    simp [Vector.getElem_append, h]

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
  obtain ⟨-, -, hu⟩ := kept_of_stepInput_eq cvk1 hmask hmn hX rk.i
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
  · rw [hu]
    simp [chals, mS]

/-! ## A step-wrap link -/

/-- One link's run, as `stepWrap_kimchiVerify` names it: a step circuit's cells and its slot that
verifies a wrap proof, and the next wrap circuit's statement and cells. -/
structure StepWrapRun (n w : ℕ) (ws : Fin n → ℕ) (ncs kw ks branches ncStep : ℕ)
    (slotWidths : Vector (Fin (MaxProofsVerified + 1)) w) where
  /-- The step circuit's valuation. -/
  Vg : Valuation Fp
  /-- The wrap circuit's valuation. -/
  Vs : Valuation Fq
  /-- The step circuit's cells. -/
  stepOut : StepMainOut n w ws 1 ncs kw ks
  /-- Each slot verifies at most `MaxProofsVerified` accumulators. -/
  hws : ∀ i, ws i ≤ MaxProofsVerified
  /-- The `sg` padding the missing accumulators. -/
  dummySg : IpaPallas.curve.Point
  /-- The slot that verifies a wrap proof. -/
  i : Fin n
  /-- The rule verifies at most the tag's `w` slots. -/
  hn : n ≤ w
  /-- The tag verifies at most `MaxProofsVerified`. -/
  hw : w ≤ MaxProofsVerified
  /-- The slot's mask. -/
  ms : Vector Bool (ws i)
  /-- The wrap circuit's statement. -/
  wrapStmt : StatementPacked ks (Type1 (FVar Fq)) (FVar Fq)
  /-- The wrap circuit's finalize cells. -/
  wrapFinalizeOut : WrapMainFinalizeOut branches w ncStep kw slotWidths
  /-- The wrap circuit's verify cells. -/
  wrapVerifyOut : WrapMainVerifyOut w ncStep kw ks

namespace StepWrapRun

variable {n w : ℕ} {ws : Fin n → ℕ} {ncs kw ks branches ncStep : ℕ}
  {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
  (r : StepWrapRun n w ws ncs kw ks branches ncStep slotWidths)

/-- The slot's input cells. -/
def inp : VerifyOneInput ks kw 1 ncs (ws r.i) :=
  slotInput (r.hws r.i) (constPt r.dummySg) r.stepOut.prevs[r.i] (r.stepOut.slots r.i)
    r.stepOut.unfs[r.i] r.stepOut.msgs[r.i]

/-- The wrap circuit's slot for the step slot: the step statement front-pads. -/
def jf : Fin w :=
  Fin.cast (Nat.sub_add_cancel r.hn) (Fin.natAdd (w - n) r.i)

/-- The link's tie and hashing: the step proof's public input is the step circuit's statement (a
premise of `stepWrap_kimchiVerify`), and both circuits hash their messages (its conclusions). -/
def Hashes (dummy : Vector Fq kw) : Prop :=
  CircuitType.Reads r.Vg r.stepOut.out (StepStatement.ofWrap r.Vs r.wrapVerifyOut.statement) ∧
  r.stepOut.HashesMessages r.Vg ∧
  r.wrapVerifyOut.HashesMessages r.Vs dummy r.wrapStmt r.wrapFinalizeOut

/-- The link emits `A`, as `stepWrap_kimchiVerify` concludes. -/
def Emits (dummy : Vector Fq kw) (A : Accumulator IpaPallas.curve kw) : Prop :=
  r.Hashes dummy ∧
  StepWrap.emittedAccumulator r.Vg r.Vs r.i r.jf r.stepOut r.wrapVerifyOut r.wrapFinalizeOut = A

/-- The link consumes `olds`, as `stepWrap_kimchiVerify` concludes. -/
def Consumes (dummy : Vector Fq kw) (olds : List (Accumulator IpaPallas.curve kw)) : Prop :=
  r.Hashes dummy ∧
  StepWrap.consumedAccumulators r.Vg r.Vs r.inp dummy r.wrapFinalizeOut r.jf = olds

end StepWrapRun

section StepWrapLinks

variable {n w : ℕ} {ws : Fin n → ℕ} {ncs kw ks branches ncStep : ℕ}
  {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
  {n' w' : ℕ} {ws' : Fin n' → ℕ} {ncs' branches' ncStep' : ℕ}
  {slotWidths' : Vector (Fin (MaxProofsVerified + 1)) w'}

/-- The link `rk` hands its wrap proof to the next link `rk1`: `rk1`'s slot verifies it at `rk`'s
wrap circuit's public input, over the key `cvk`, at `rk`'s width, and keeps exactly `rk`'s slots.
-/
def StepWrapRun.Hands (rk : StepWrapRun n w ws ncs kw ks branches ncStep slotWidths)
    (rk1 : StepWrapRun n' w' ws' ncs' kw ks branches' ncStep' slotWidths')
    (cvk : KimchiVK IpaPallas.curve 1) : Prop :=
  CircuitType.Reads rk.Vs rk.wrapStmt (rk1.inp.packedAt cvk rk1.Vg rk1.ms) ∧
  ws' rk1.i = w ∧
  ∀ (j : ℕ) (hj : j < ws' rk1.i), rk1.ms[j] = decide (ws' rk1.i - n ≤ j)

/-- The wrap message `rk` sends and the one the next link `rk1` rebuilds for its slot collide
(`WrapMsgCollision`). -/
def StepWrapRun.WrapCollision (rk : StepWrapRun n w ws ncs kw ks branches ncStep slotWidths)
    (rk1 : StepWrapRun n' w' ws' ncs' kw ks branches' ncStep' slotWidths')
    (dummy : Vector Fq kw) : Prop :=
  WrapMsgCollision rk.Vs rk.wrapVerifyOut rk.wrapFinalizeOut rk1.Vs rk1.wrapFinalizeOut rk1.jf
    dummy

/-- The step message `rk` sends and the one the next link `rk1`'s slot rebuilds collide
(`StepMsgCollision`). -/
def StepWrapRun.StepCollision (rk : StepWrapRun n w ws ncs kw ks branches ncStep slotWidths)
    (rk1 : StepWrapRun n' w' ws' ncs' kw ks branches' ncStep' slotWidths')
    (cvk : KimchiVK IpaPallas.curve 1) : Prop :=
  StepMsgCollision rk.Vg rk.stepOut rk1.Vg rk1.inp rk1.ms cvk

/-- **The next wrap proof opens each emitted accumulator.** The link `rk` emits `A`, and the next
link `rk1` consumes the olds of the wrap proof `cp` that `rk`'s wrap circuit made. Then `A` is one
of `cp`'s olds, which `cp`'s batch opens first (`runStreamP_olds`), unless Poseidon collides on
the messages passed between the links. -/
theorem opened_by_next_wrap (rk : StepWrapRun n w ws ncs kw ks branches ncStep slotWidths)
    (rk1 : StepWrapRun n' w' ws' ncs' kw ks branches' ncStep' slotWidths')
    (cvk : KimchiVK IpaPallas.curve 1) (dummy : Vector Fq kw)
    (A : Accumulator IpaPallas.curve kw) (cp : KimchiProof IpaPallas.curve 1 kw)
    (he : rk.Emits dummy A) (hc : rk1.Consumes dummy cp.olds.toList) (hh : rk.Hands rk1 cvk) :
    A ∈ cp.olds.toList ∨ rk.WrapCollision rk1 dummy ∨ rk.StepCollision rk1 cvk := by
  obtain ⟨⟨hpub, hSk, hWk⟩, hA⟩ := he
  obtain ⟨⟨hpub1, hS1, hW1⟩, hcons⟩ := hc
  obtain ⟨htie, hw1, hmask⟩ := hh
  obtain ⟨hpubD, -⟩ := digests_of_ofWrap hpub
  obtain ⟨-, hpubM1⟩ := digests_of_ofWrap hpub1
  -- link k's outgoing messages, read
  let mW := rk.wrapVerifyOut.messagesForNextWrapProof rk.wrapFinalizeOut
  let mS := rk.stepOut.messagesForNextStepProof
  let sg : AffinePoint Fq :=
    ⟨mW.challengePolynomialCommitment.x.val rk.Vs, mW.challengePolynomialCommitment.y.val rk.Vs⟩
  let chalsW := mW.oldBulletproofChallenges.map (·.map (·.val rk.Vs))
  let vk := mS.dlogPlonkIndex.map fun P => (⟨P.x.val rk.Vg, P.y.val rk.Vg⟩ : AffinePoint Fp)
  let sgs := mS.challengePolynomialCommitments.map fun P =>
    (⟨P.x.val rk.Vg, P.y.val rk.Vg⟩ : AffinePoint Fp)
  let chals := mS.oldBulletproofChallenges.map (·.map (·.val rk.Vg))
  -- link k1's rebuilt wrap message for its slot, read
  let mW' := rk1.wrapFinalizeOut.messagesForNextWrapProof rk1.jf
  let sg' : AffinePoint Fq :=
    ⟨mW'.challengePolynomialCommitment.x.val rk1.Vs, mW'.challengePolynomialCommitment.y.val rk1.Vs⟩
  let chalsW' := mW'.oldBulletproofChallenges.map (·.map (·.val rk1.Vs))
  -- the wrap digest, from link k's wrap circuit through link k1's step circuit to its wrap circuit
  have hwrapD : ((ZMod.val (wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg, chalsW⟩) : ℕ)
      : Fp) = ((ZMod.val (wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg', chalsW'⟩) : ℕ)
      : Fp) := by
    have hn1 := rk1.hn
    have h1 := hWk.1 sg chalsW (reads_pt _ _) (reads_vecs _ _)
    have h2 := (digests_of_tie htie).1
    have h3 := hS1.2 rk1.hn rk1.i
    have h4 := hpubM1 (w' - n' + rk1.i) (by omega)
    have h5 : (rk1.wrapVerifyOut.statement.messagesForNextWrapProof[w' - n' + rk1.i]).val rk1.Vs
        = wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg', chalsW'⟩ :=
      hW1.2.1 rk1.jf sg' chalsW' (reads_pt _ _) (reads_vecs _ _)
    rw [← h1, h2, toFp_redFq]
    show rk1.stepOut.msgs[rk1.i].val rk1.Vg = _
    rw [← h3, h4, h5]
  -- the step digest, from link k's step circuit through its wrap circuit to link k1's slot
  have hstepD : Poseidon.RandomOracle.hash IpaPallas.curve.sponge.params
        (stepMsgInput ⟨mS.appState.map (·.val rk.Vg), vk, sgs, chals⟩)
      = Poseidon.RandomOracle.hash IpaPallas.curve.sponge.params
        (cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y])
          ++ rk1.inp.appState.map (·.val rk1.Vg)
          ++ keptValues rk1.Vg rk1.ms (rk1.inp.prevSgs.zip rk1.inp.prevChallenges)) := by
    have h1 := hSk.1 vk sgs chals (reads_key _ _) (reads_pts _ _) (reads_vecs _ _)
    have h3 := hWk.2.2
    have h4 := (digests_of_tie htie).2
    rw [h3] at h4
    rw [h4, toFp_redFq] at hpubD
    rw [Poseidon.RandomOracle.hash_eq_squeeze, Poseidon.RandomOracle.hash_eq_squeeze]
    have e := h1.symm.trans hpubD
    simp only [stepMsgDigest, VerifyOneInput.stepMsgDigest, KimchiVK.indexState] at e
    simp only [Poseidon.absorb, List.foldl_append] at e ⊢
    exact e
  -- distinct step inputs collide
  by_cases hX : stepMsgInput ⟨mS.appState.map (·.val rk.Vg), vk, sgs, chals⟩
      = cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y])
          ++ rk1.inp.appState.map (·.val rk1.Vg)
          ++ keptValues rk1.Vg rk1.ms (rk1.inp.prevSgs.zip rk1.inp.prevChallenges)
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
  set m := ws' rk1.i with hm
  have hmn : n ≤ m := hw1 ▸ rk.hn
  -- the commitment: link k1's kept slot is link k's slot `i`
  obtain ⟨hsx, hsy, -⟩ := kept_of_stepInput_eq cvk hmask hmn hX rk.i
  -- the challenges: both wrap inputs pad to the same stacks
  obtain ⟨hpre, -⟩ := List.append_inj' hW rfl
  simp only [toList_flatten'] at hpre
  rw [← List.flatten_append, ← List.flatten_append] at hpre
  have hw := rk.hw
  have hsw := (slotWidths'[rk1.jf]).isLt
  have hL := flatten_inj (m := kw)
    (by simp only [List.mem_append, List.mem_replicate, List.mem_map]
        rintro c (⟨-, rfl⟩ | ⟨v, -, rfl⟩) <;> simp)
    (by simp only [List.mem_append, List.mem_replicate, List.mem_map]
        rintro c (⟨-, rfl⟩ | ⟨v, -, rfl⟩) <;> simp)
    (by simp; omega) hpre
  -- `A` is the consumed entry past the padding at link k1's slot
  have hm1 := rk1.hws rk1.i
  have hi := rk.i.isLt
  rw [← hcons, ← hA]
  simp only [StepWrap.consumedAccumulators, StepWrap.emittedAccumulator]
  refine List.mem_iff_getElem.mpr ⟨MaxProofsVerified - n + rk.i, by simp; omega, ?_⟩
  simp only [Vector.getElem_toList, Vector.getElem_zipWith, Accumulator.ofCells]
  rw [Accumulator.mk.injEq]
  refine ⟨?_, ?_⟩
  · -- past the padding, the slot's old commitments are its previous proofs'
    have hsg : rk1.inp.sgOld[MaxProofsVerified - n + rk.i] = rk1.inp.prevSgs[m - n + rk.i] := by
      simp only [StepWrapRun.inp, slotInput, Vector.getElem_cast]
      have hidx : MaxProofsVerified - n + ↑rk.i - (MaxProofsVerified - ws' rk1.i)
          = m - n + rk.i := by omega
      rw [Vector.getElem_append_right (by omega)]
      · simp only [Vector.getElem_map, hidx]
      · omega
    rw [hsg]
    exact readPt_congr (hsx.trans (by simp [sgs, mS])) (hsy.trans (by simp [sgs, mS]))
  · -- past the padding, the slot's challenges are link k's emitted ones
    apply Vector.toList_inj.mp
    rw [padChallenges_read rk1.Vs dummy _ _ _ (by omega)]
    have ht := List.getElem_of_eq hL (i := MaxProofsVerified - n + rk.i) (by simp; omega)
    rw [List.getElem_append_right (by simp; omega)] at ht
    refine ht.symm.trans ?_
    have hidx : MaxProofsVerified - n + ↑rk.i - (MaxProofsVerified - w) = w - n + rk.i := by
      omega
    simp [chalsW, mW, StepWrapRun.jf, hidx]

end StepWrapLinks

end Links

end Pickles
