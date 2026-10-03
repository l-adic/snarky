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

* `WrapStepRun.handover_or_collision`, `StepWrapRun.handover_or_collision`: both complete
  messages agree and the earlier proof accepts, or the accepted later proof exhibits
  `AccumulatorFailure`, unless Poseidon collides on the messages passed between them.

## Implementation notes

The handover is deterministic. `AccumulatorFailure` names acceptance with an invalid old
accumulator; excluding that event requires a cryptographic argument outside this development.
Message equality holds in both the acceptance and accumulator-failure alternatives.

Two links share no cells: each circuit run has its own valuation, and an accumulator reaches the
next link only through the digests of its messages, carried in public inputs. The wrap digest
crosses the step circuit's statement reduced into the step field; the wrap circuit's public-input
ladder bounds it below `2^254 < p`, so the reduction loses nothing and both collisions are exact
Poseidon collisions.

The branch a wrap circuit takes is witnessed, so the handover names no branch: it reads only that
the next slot keeps the last `k` of its slots. A `k` other than the number of proofs the previous
rule sent makes the slot rebuild a step input of another length, two or more cells off, which
collides with the sent one.
-/

namespace Pickles

open Kimchi.Verifier Bulletproof Bulletproof.Ipa

section Links

open Snarky Snarky.Kimchi
open CompElliptic.Fields.Pasta

/-- Read the affine coordinates of a message commitment. -/
def readPoint {F : Type} [Field F]
    (V : Valuation F) (p : AffinePoint (FVar F)) : AffinePoint F :=
  ⟨p.x.val V, p.y.val V⟩

/-- The message entries selected by a slot mask, in their original order. -/
def keep {α : Type} {n : Nat} (mask : Vector Bool n) (xs : Vector α n) : List α :=
  ((List.finRange n).filter fun i => mask[i]).map fun i => xs[i]

/-- A step message with its application state and predecessor entries read as lists. -/
abbrev StepMessageValue (ks : Nat) :=
  MessagesForNextStepProof
    (VkComms 1 (AffinePoint Fp)) (List Fp)
    (List (AffinePoint Fp)) (List (Vector Fp ks))

/-- A wrap message with its challenge stack padded to the protocol width. -/
abbrev WrapMessageValue (kw : Nat) :=
  MessagesForNextWrapProof (AffinePoint Fq) (List (Vector Fq kw))

/-- Read every component of a sent step message. -/
def readStepMessage {sa n ks : Nat} (V : Valuation Fp)
    (m : MessagesForNextStepProof
      (VkComms 1 (AffinePoint (FVar Fp))) (Vector (FVar Fp) sa)
      (Vector (AffinePoint (FVar Fp)) n) (Vector (Vector (FVar Fp) ks) n)) :
    StepMessageValue ks where
  appState := m.appState.toList.map (·.val V)
  dlogPlonkIndex := m.dlogPlonkIndex.map (readPoint V)
  challengePolynomialCommitments :=
    m.challengePolynomialCommitments.toList.map (readPoint V)
  oldBulletproofChallenges := m.oldBulletproofChallenges.toList.map (·.map (·.val V))

/-- Rebuild the complete step message received by a verifier slot. -/
def rebuildStepMessage {s ks kw ncs w : Nat} (V : Valuation Fp)
    (vk : KimchiVK IpaPallas.curve 1)
    (inp : VerifyOneInput s ks kw 1 ncs w) (mask : Vector Bool w) :
    StepMessageValue ks where
  appState := inp.appState.toList.map (·.val V)
  dlogPlonkIndex := vk.comms.map fun p => ⟨p.x, p.y⟩
  challengePolynomialCommitments := (keep mask inp.prevSgs).map (readPoint V)
  oldBulletproofChallenges := (keep mask inp.prevChallenges).map (·.map (·.val V))

/-- Read a wrap message, including its dummy challenge padding. -/
def readWrapMessage {w kw : Nat} (V : Valuation Fq) (dummy : Vector Fq kw)
    (m : MessagesForNextWrapProof
      (AffinePoint (FVar Fq)) (Vector (Vector (FVar Fq) kw) w)) :
    WrapMessageValue kw where
  challengePolynomialCommitment := readPoint V m.challengePolynomialCommitment
  oldBulletproofChallenges := List.replicate (MaxProofsVerified - w) dummy ++
    m.oldBulletproofChallenges.toList.map (·.map (·.val V))

/-- An accepted proof carries an old accumulator whose deferred equation is false. -/
def AccumulatorFailure {C : KimchiCurve} {nc : Nat}
    (σ : SRS C.Point) (vk : KimchiVK C nc)
    (q : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : Prop :=
  kimchiVerify C σ vk q pub = true ∧
    ∃ a ∈ q.olds.toList, accOk σ a = false


/-- Once handover gives membership, acceptance closes the earlier proof or witnesses failure. -/
theorem accepts_or_accumulatorFailure {C : KimchiCurve} {nc nc' : Nat}
    (σ : SRS C.Point) (vk : KimchiVK C nc) (p : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField)
    (nextVk : KimchiVK C nc') (q : KimchiProof C nc' σ.k) (nextPub : Array C.ScalarField)
    (hmem : (⟨p.opening.sg, wireChallenges σ vk p pub⟩ : Accumulator C σ.k) ∈ q.olds.toList)
    (hAccept : kimchiVerify C σ nextVk q nextPub = true)
    (hCapstone : SgOk σ vk p pub → kimchiVerify C σ vk p pub = true) :
    kimchiVerify C σ vk p pub = true ∨ AccumulatorFailure σ nextVk q nextPub := by
  by_cases hAcc : accOk σ ⟨p.opening.sg, wireChallenges σ vk p pub⟩ = true
  · have hSg : SgOk σ vk p pub := by
      simp only [accOk, decide_eq_true_eq] at hAcc
      exact hAcc
    exact Or.inl (hCapstone hSg)
  · exact Or.inr ⟨hAccept, _, hmem, Bool.eq_false_iff.mpr hAcc⟩


/-! ## Collisions between two links -/

/-- The wrap message a wrap circuit sends (its verify cells `out` over `fin`, under `V`) and the
one a later wrap circuit rebuilds for its slot `j` (`fin'`, under `V'`) read differently, but hash
alike. -/
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
    Collision IpaVesta.curve.sponge.params
      (wrapMsgInput dummy ⟨sg, chals⟩) (wrapMsgInput dummy ⟨sg', chals'⟩)

/-- The step message a step circuit sends (`out`, under `V`) and the one a later slot rebuilds
(`inp` with mask `ms`, under `V'`, over the key `cvk`) read differently, but hash alike. -/
def StepMsgCollision {n w : ℕ} {ws ss ncs : Fin n → ℕ} {sa kw ks s' k' ncs' w' : ℕ}
    (V : Valuation Fp) (out : StepMainOut n w ws ss sa 1 ncs kw ks) (V' : Valuation Fp)
    (inp : VerifyOneInput s' ks k' 1 ncs' w') (ms : Vector Bool w')
    (cvk : KimchiVK IpaPallas.curve 1) : Prop :=
  ∃ (vk : VkComms 1 (AffinePoint Fp)) (sgs : Vector (AffinePoint Fp) n)
    (chals : Vector (Vector Fp ks) n),
    CircuitType.Reads V out.messagesForNextStepProof.dlogPlonkIndex vk ∧
    CircuitType.Reads V out.messagesForNextStepProof.challengePolynomialCommitments sgs ∧
    CircuitType.Reads V out.messagesForNextStepProof.oldBulletproofChallenges chals ∧
    Collision IpaPallas.curve.sponge.params
      (stepMsgInput ⟨out.messagesForNextStepProof.appState.map (·.val V), vk, sgs, chals⟩)
      (cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y]) ++ inp.appState.toList.map (·.val V')
        ++ keptValues V' ms (inp.prevSgs.zip inp.prevChallenges))

/-! ## A wrap-step link -/

/-- One link's run, as `wrapStep_kimchiVerify` names it: a wrap circuit's statement and cells,
the next step circuit's cells, and the slot of it that verifies the wrap proof. -/
structure WrapStepRun (branches w ncStep kw ks n wNext : ℕ) (ws ss ncs : Fin n → ℕ) (sa : ℕ)
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
  stepOut : StepMainOut n wNext ws ss sa 1 ncs kw ks
  /-- The rule verifies at most the tag's `wNext` slots. -/
  hn : n ≤ wNext
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

namespace WrapStepRun

variable {branches w ncStep kw ks n wNext sa : ℕ} {ws ss ncs : Fin n → ℕ}
  {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
  (r : WrapStepRun branches w ncStep kw ks n wNext ws ss ncs sa slotWidths)

/-- The slot's input cells. -/
def inp : VerifyOneInput (ss r.i) ks kw 1 (ncs r.i) (ws r.i) :=
  slotInput (r.hws r.i) r.dummySg (r.stepOut.prevs r.i) (r.stepOut.slots r.i) r.stepOut.unfs[r.i]
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

/-- The link consumes `olds`, its slot keeping the last of the wrap circuit's slots, as
`wrapStep_kimchiVerify` concludes. -/
def Consumes (cvk : KimchiVK IpaPallas.curve 1) (dummy : Vector Fq kw)
    (olds : List (Accumulator IpaVesta.curve ks)) : Prop :=
  r.Hashes cvk dummy ∧
  WrapStep.consumedAccumulators r.Vw r.Vs r.wrapFinalizeOut r.inp.prevChallenges r.hwi r.ms
    = olds ∧
  ∃ k ≤ w, ∀ (j : ℕ) (hj : j < ws r.i), r.ms[j] = decide (w - k ≤ j)

end WrapStepRun

/-! ## Two links -/

variable {branches w ncStep kw ks n wNext sa : ℕ} {ws ss ncs : Fin n → ℕ}
  {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
  {branches' ncStep' ks' n' wNext' sa' : ℕ} {ws' ss' ncs' : Fin n' → ℕ}
  {slotWidths' : Vector (Fin (MaxProofsVerified + 1)) wNext}

/-- The link `rk` hands its step proof to the next link `rk1`: the step proof `rk`'s step circuit
makes is the one `rk1`'s wrap circuit verifies, and `rk1`'s slot reads a previous statement of the
size of `rk`'s application state. -/
def WrapStepRun.Hands (rk : WrapStepRun branches w ncStep kw ks n wNext ws ss ncs sa slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw ks' n' wNext' ws' ss' ncs' sa' slotWidths') :
    Prop :=
  CircuitType.Reads rk.Vs rk.stepOut.out
    (StepStatement.ofWrap rk1.Vw rk1.wrapVerifyOut.statement) ∧
  ss' rk1.i = sa

/-- The next link's wrap slot of the slot `rk.i`: the step statement front-pads. -/
def WrapStepRun.slotIndex
    (rk : WrapStepRun branches w ncStep kw ks n wNext ws ss ncs sa slotWidths) : Fin wNext :=
  ⟨wNext - n + rk.i, by have := rk.hn; omega⟩

/-- The wrap message `rk` sends and the one the next link `rk1` rebuilds for it collide
(`WrapMsgCollision`). -/
def WrapStepRun.WrapCollision
    (rk : WrapStepRun branches w ncStep kw ks n wNext ws ss ncs sa slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw ks n' wNext' ws' ss' ncs' sa' slotWidths')
    (dummy : Vector Fq kw) : Prop :=
  WrapMsgCollision rk.Vw rk.wrapVerifyOut rk.wrapFinalizeOut rk1.Vw rk1.wrapFinalizeOut
    rk.slotIndex dummy

/-- The step message `rk` sends and the one the next link `rk1`'s slot rebuilds collide
(`StepMsgCollision`). -/
def WrapStepRun.StepCollision
    (rk : WrapStepRun branches w ncStep kw ks n wNext ws ss ncs sa slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw ks n' wNext' ws' ss' ncs' sa' slotWidths')
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

/-- A suffix mask selects the corresponding suffix of a vector. -/
private theorem keep_front {α : Type} {m n : ℕ} (ms : Vector Bool m) (xs : Vector α m)
    (hms : ∀ (j : ℕ) (hj : j < m), ms[j] = decide (m - n ≤ j)) :
    keep ms xs = xs.toList.drop (m - n) := by
  have hL : (Vector.zipWith (fun b x => if b then [x] else []) ms xs).toList =
      List.replicate (m - n) [] ++ (xs.toList.drop (m - n)).map (fun x => [x]) := by
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [Vector.getElem_toList, Vector.getElem_zipWith, hms j (by simpa using h1)]
    by_cases hj : j < m - n
    · rw [List.getElem_append_left (by simpa using hj)]
      simp [show ¬(m - n ≤ j) by omega]
    · rw [List.getElem_append_right (by simpa using hj)]
      simp [show m - n ≤ j by omega, show m - n + (j - (m - n)) = j by omega]
  have hf := congrArg List.flatten hL
  have hv {β : Type} (v : Vector β m) : v.toList = List.ofFn (fun i : Fin m => v[i]) := by
    apply List.ext_getElem <;> simp
  rw [Vector.toList_zipWith, hv ms, hv xs, flatten_zipWith_keep] at hf
  rw [show xs.toList = List.ofFn (fun i : Fin m => xs[i]) from hv xs]
  simpa only [keep, ← List.map_drop, List.flatten_append, List.flatten_replicate_nil,
    List.nil_append, ← List.flatMap_def, List.flatMap_singleton'] using hf

private theorem indexPoints_injective {α : Type} {nc : ℕ} :
    Function.Injective (VkComms.indexPoints (nc := nc) (f := α)) := by
  intro a b h
  have hchunks := flatten_inj (m := nc)
    (by simp only [List.mem_map]; rintro _ ⟨v, -, rfl⟩; simp)
    (by simp only [List.mem_map]; rintro _ ⟨v, -, rfl⟩; simp)
    (by simp) (show _ = _ from h)
  have hv : a.sigmaComm.toList ++ a.coefficientsComm.toList ++ a.selectors.toList =
      b.sigmaComm.toList ++ b.coefficientsComm.toList ++ b.selectors.toList :=
    (List.map_inj_right (fun _ _ h => Vector.toList_inj.mp h)).mp hchunks
  obtain ⟨hp, hs⟩ := List.append_inj hv (by simp)
  obtain ⟨hσ, hc⟩ := List.append_inj hp (by simp)
  have hσ := Vector.toList_inj.mp hσ
  have hc := Vector.toList_inj.mp hc
  simp only [VkComms.selectors, Vector.toList_mk, List.cons.injEq, and_true] at hs
  cases a; cases b
  simp_all

private theorem keyCoords_injective {α : Type} {nc : ℕ}
    (a b : VkComms nc (AffinePoint α))
    (h : a.indexPoints.flatMap (fun p => [p.x, p.y]) =
      b.indexPoints.flatMap (fun p => [p.x, p.y])) : a = b := by
  apply indexPoints_injective
  have hc := flatten_inj (m := 2)
    (by simp only [List.mem_map]; rintro _ ⟨p, -, rfl⟩; rfl)
    (by simp only [List.mem_map]; rintro _ ⟨p, -, rfl⟩; rfl)
    (by simp [VkComms.indexPoints, List.length_flatMap, VkComms.selectors]) h
  exact (List.map_inj_right (by intro p q h; cases p; cases q; simpa using h)).mp hc

private theorem indexPoints_map {α β : Type} {nc : ℕ} (f : α → β) (k : VkComms nc α) :
    (k.map f).indexPoints = k.indexPoints.map f := by
  simp [VkComms.indexPoints, VkComms.map, VkComms.selectors, Vector.toList_map, List.flatMap_map,
    List.map_flatMap]

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

end Helpers

private theorem natCast_val_redFq (x : Fp) : ((ZMod.val (redFq x) : ℕ) : Fp) = x := by
  rw [val_redFq, ZMod.natCast_zmod_val]

/-- A wrap-field value below `2^254 < p` survives reduction into the step field and back. -/
private theorem redFq_natCast_val_of_lt (x : Fq) (h : ZMod.val x < 2 ^ 254) :
    redFq ((ZMod.val x : ℕ) : Fp) = x := by
  have hp : (2 : ℕ) ^ 254 < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
  rw [redFq, ZMod.val_natCast_of_lt (h.trans hp), ZMod.natCast_zmod_val]

private theorem readPt_congr {C : KimchiCurve} {V V' : Valuation C.BaseField}
    {p q : AffinePoint (FVar C.BaseField)}
    (hx : p.x.val V = q.x.val V') (hy : p.y.val V = q.y.val V') : readPt V p = readPt V' q := by
  simp only [readPt, hx, hy]

/-- Equal step inputs, the rebuilt one keeping exactly the last `n` of its `m` slots: its slot
`m − n + i` reads as the sent message's entry `i`. -/
private theorem kept_of_stepInput_eq {n m ks sa s' : ℕ} {V : Valuation Fp}
    (cvk : KimchiVK IpaPallas.curve 1) {app : Vector Fp sa} {vk : VkComms 1 (AffinePoint Fp)}
    {sgs : Vector (AffinePoint Fp) n} {chals : Vector (Vector Fp ks) n}
    {app' : Vector (FVar Fp) s'}
    {ms : Vector Bool m} {psgs : Vector (AffinePoint (FVar Fp)) m}
    {pchals : Vector (Vector (FVar Fp) ks) m}
    (hmask : ∀ (j : ℕ) (hj : j < m), ms[j] = decide (m - n ≤ j)) (hnm : n ≤ m)
    (h : stepMsgInput ⟨app, vk, sgs, chals⟩
      = cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y]) ++ app'.toList.map (·.val V)
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

/-- Equality of the absorbed step inputs determines every field of the complete messages. -/
private theorem stepMessage_eq_of_input_eq {n sa s ks kw ncs m : ℕ}
    (V V' : Valuation Fp)
    (msg : MessagesForNextStepProof (VkComms 1 (AffinePoint (FVar Fp)))
      (Vector (FVar Fp) sa) (Vector (AffinePoint (FVar Fp)) n)
      (Vector (Vector (FVar Fp) ks) n))
    (cvk : KimchiVK IpaPallas.curve 1) (inp : VerifyOneInput s ks kw 1 ncs m)
    (ms : Vector Bool m) (hs : s = sa) (hn : n ≤ m)
    (hmask : ∀ (j : ℕ) (hj : j < m), ms[j] = decide (m - n ≤ j))
    (h : stepMsgInput ⟨msg.appState.map (·.val V), msg.dlogPlonkIndex.map (readPoint V),
        msg.challengePolynomialCommitments.map (readPoint V),
        msg.oldBulletproofChallenges.map (·.map (·.val V))⟩ =
      cvk.comms.indexPoints.flatMap (fun p => [p.x, p.y]) ++
        inp.appState.toList.map (·.val V') ++
        keptValues V' ms (inp.prevSgs.zip inp.prevChallenges)) :
    readStepMessage V msg = rebuildStepMessage V' cvk inp ms := by
  have hpre := (List.append_inj h (by
    simp [VkComms.indexPoints, VkComms.selectors, List.length_flatMap, hs])).1
  obtain ⟨hkey, happ⟩ := List.append_inj hpre (by
    simp [VkComms.indexPoints, VkComms.selectors, List.length_flatMap])
  have hkey' : msg.dlogPlonkIndex.map (readPoint V) =
      cvk.comms.map (fun p => (⟨p.x, p.y⟩ : AffinePoint Fp)) := by
    apply keyCoords_injective
    simpa [indexPoints_map, List.flatMap_map] using hkey
  have hi := kept_of_stepInput_eq cvk hmask hn h
  simp only [readStepMessage, rebuildStepMessage, MessagesForNextStepProof.mk.injEq,
    keep_front ms _ hmask]
  refine ⟨by simpa [Vector.toList_map] using happ, hkey', ?_, ?_⟩
  · apply List.ext_getElem (by simp; omega)
    intro j hj hj'
    have he := hi ⟨j, by simpa using hj⟩
    simp only [List.getElem_map, List.getElem_drop, Vector.getElem_toList]
    simp only [Fin.getElem_fin, Vector.getElem_map, readPoint] at he
    simp only [readPoint, AffinePoint.mk.injEq]
    exact ⟨he.1.symm, he.2.1.symm⟩
  · apply List.ext_getElem (by simp; omega)
    intro j hj hj'
    have he := (hi ⟨j, by simpa using hj⟩).2.2
    simpa using he.symm

/-- Equality of the absorbed wrap inputs determines the commitment and padded challenge stack. -/
private theorem wrapMessage_eq_of_input_eq {w w' kw : ℕ}
    (V V' : Valuation Fq) (dummy : Vector Fq kw)
    (msg : MessagesForNextWrapProof (AffinePoint (FVar Fq))
      (Vector (Vector (FVar Fq) kw) w))
    (msg' : MessagesForNextWrapProof (AffinePoint (FVar Fq))
      (Vector (Vector (FVar Fq) kw) w'))
    (hw : w ≤ MaxProofsVerified) (hw' : w' ≤ MaxProofsVerified)
    (h : wrapMsgInput dummy ⟨readPoint V msg.challengePolynomialCommitment,
        msg.oldBulletproofChallenges.map (·.map (·.val V))⟩ =
      wrapMsgInput dummy ⟨readPoint V' msg'.challengePolynomialCommitment,
        msg'.oldBulletproofChallenges.map (·.map (·.val V'))⟩) :
    readWrapMessage V dummy msg = readWrapMessage V' dummy msg' := by
  obtain ⟨hpre, hsg⟩ := List.append_inj' h rfl
  have hc : (readWrapMessage V dummy msg).oldBulletproofChallenges.map Vector.toList =
      (readWrapMessage V' dummy msg').oldBulletproofChallenges.map Vector.toList := by
    apply flatten_inj (m := kw)
    · simp only [List.mem_map]; rintro _ ⟨v, -, rfl⟩; simp
    · simp only [List.mem_map]; rintro _ ⟨v, -, rfl⟩; simp
    · simp only [readWrapMessage, List.length_map, List.length_append, List.length_replicate,
        Vector.length_toList]
      omega
    · simpa [readWrapMessage, List.map_append, List.flatten_append, toList_flatten',
        Vector.toList_map, List.map_map, Function.comp_def] using hpre
  have hc' := (List.map_inj_right (fun _ _ h => Vector.toList_inj.mp h)).mp hc
  simp only [readWrapMessage, MessagesForNextWrapProof.mk.injEq]
  exact ⟨by simpa [readPoint, AffinePoint.mk.injEq] using hsg, hc'⟩

/-- A step message carrying `n` proofs and a slot's rebuild of it keeping a suffix of `k`, over a
statement of the message's size: their lengths differ by the `ks + 2` cells of each proof one
holds and the other does not. -/
private theorem length_stepInput {n m k ks sa s' : ℕ} {V : Valuation Fp}
    (cvk : KimchiVK IpaPallas.curve 1) {app : Vector Fp sa} {vk : VkComms 1 (AffinePoint Fp)}
    {sgs : Vector (AffinePoint Fp) n} {chals : Vector (Vector Fp ks) n}
    {app' : Vector (FVar Fp) s'} {ms : Vector Bool m} {psgs : Vector (AffinePoint (FVar Fp)) m}
    {pchals : Vector (Vector (FVar Fp) ks) m} (hs : s' = sa)
    (hmask : ∀ (j : ℕ) (hj : j < m), ms[j] = decide (m - k ≤ j)) (hkm : k ≤ m) :
    (stepMsgInput ⟨app, vk, sgs, chals⟩).length + k * (ks + 2)
      = (cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y]) ++ app'.toList.map (·.val V)
        ++ keptValues V ms (psgs.zip pchals)).length + n * (ks + 2) := by
  subst hs
  rw [keptValues_front V ms (psgs.zip pchals) hmask]
  simp [stepMsgInput, MessagesForNextStepProof.proofs, List.length_flatMap, List.length_flatten,
    Function.comp_def, VkComms.indexPoints, VkComms.selectors, Nat.sub_sub_self hkm]
  ring

/-- Lengths that differ by `ks + 2` cells per proof, over different proof counts, are two or more
apart. -/
private theorem length_apart {L L' n k ks : ℕ} (h : L + k * (ks + 2) = L' + n * (ks + 2))
    (hkn : k ≠ n) : L + 2 ≤ L' ∨ L' + 2 ≤ L := by
  rcases Nat.lt_or_gt_of_ne hkn with hlt | hlt
  · have := Nat.mul_le_mul_right (ks + 2) hlt
    rw [Nat.succ_mul] at this
    omega
  · have := Nat.mul_le_mul_right (ks + 2) hlt
    rw [Nat.succ_mul] at this
    omega

/-- A key's coordinates are nonempty: every commitment has a chunk. -/
private theorem indexCoords_ne_nil {f F : Type} (key : VkComms 1 f) (x y : f → F) :
    key.indexPoints.flatMap (fun P => [x P, y P]) ≠ [] := by
  have hP : key.sigmaComm[0][0] ∈ key.indexPoints := by
    simp only [VkComms.indexPoints, List.mem_flatMap]
    exact ⟨key.sigmaComm[0], by simp, by simp⟩
  exact List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨_, hP, List.mem_cons_self⟩)

/-- Two wrap messages' inputs have one length: each pads its challenge stacks to
`MaxProofsVerified`. -/
private theorem length_wrapMsgInput {k w w' : ℕ} (dummy : Vector Fq k)
    (hw : w ≤ MaxProofsVerified) (hw' : w' ≤ MaxProofsVerified) (sg sg' : AffinePoint Fq)
    (chals : Vector (Vector Fq k) w) (chals' : Vector (Vector Fq k) w') :
    (wrapMsgInput dummy ⟨sg, chals⟩).length = (wrapMsgInput dummy ⟨sg', chals'⟩).length := by
  simp only [wrapMsgInput, List.length_append, List.length_flatten, List.map_replicate,
    List.sum_replicate, Vector.length_toList, List.length_cons, List.length_nil, smul_eq_mul]
  rw [← Nat.add_mul, ← Nat.add_mul, Nat.sub_add_cancel hw, Nat.sub_add_cancel hw']

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
private theorem digests_of_tie {s ks k ncw ncs w : ℕ} {Vw : Valuation Fq} {Vs : Valuation Fp}
    {stmt : StatementPacked ks (Type1 (FVar Fq)) (FVar Fq)} {inp : VerifyOneInput s ks k ncw ncs w}
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

/-- A wrap message and the next wrap circuit's rebuild of it hash alike. The step circuit between
them verifies the first wrap circuit's proof in slot `i`, so the digest crosses the slot's
statement and the step statement, past its padding, into the next wrap circuit's slot `j`. That
circuit's ladder bounds the cell below `2^254 < p`, so the reduction into the step field loses
nothing. -/
private theorem wrapMsgDigest_eq
    {branches mpv ncStep kw ks : ℕ} {slotWidths : Vector (Fin (MaxProofsVerified + 1)) mpv}
    {branches' w ncStep' ks' : ℕ} {slotWidths' : Vector (Fin (MaxProofsVerified + 1)) w}
    {n : ℕ} {ws ss ncs : Fin n → ℕ} {sa ksS s k' ncs' w'' : ℕ}
    {Vw Vw' : Valuation Fq} {Vg : Valuation Fp} {dummy : Vector Fq kw}
    {stmt : StatementPacked ks (Type1 (FVar Fq)) (FVar Fq)}
    {fin : WrapMainFinalizeOut branches mpv ncStep kw slotWidths}
    {out : WrapMainVerifyOut mpv ncStep kw ks}
    {stmt' : StatementPacked ks' (Type1 (FVar Fq)) (FVar Fq)}
    {fin' : WrapMainFinalizeOut branches' w ncStep' kw slotWidths'}
    {out' : WrapMainVerifyOut w ncStep' kw ks'}
    {stepOut : StepMainOut n w ws ss sa 1 ncs kw ksS}
    {inp : VerifyOneInput s ks k' 1 ncs' w''} {cvk : KimchiVK IpaPallas.curve 1}
    {ms : Vector Bool w''} (hn : n ≤ w) (i : Fin n) (j : Fin w) (hj : (j : ℕ) = w - n + i)
    (hW : out.HashesMessages Vw dummy stmt fin)
    (htie : CircuitType.Reads Vw stmt (inp.packedAt cvk Vg ms))
    (hmsg : inp.messagesForNextWrapProof = stepOut.msgs[i])
    (hS : stepOut.HashesMessages Vg)
    (hpub : CircuitType.Reads Vg stepOut.out (StepStatement.ofWrap Vw' out'.statement))
    (hW' : out'.HashesMessages Vw' dummy stmt' fin')
    {sg sg' : AffinePoint Fq} {chals : Vector (Vector Fq kw) mpv}
    {chals' : Vector (Vector Fq kw) slotWidths'[j]}
    (hsg : CircuitType.Reads Vw (out.messagesForNextWrapProof fin).challengePolynomialCommitment sg)
    (hch : CircuitType.Reads Vw (out.messagesForNextWrapProof fin).oldBulletproofChallenges chals)
    (hsg' : CircuitType.Reads Vw' (fin'.messagesForNextWrapProof j).challengePolynomialCommitment
      sg')
    (hch' : CircuitType.Reads Vw' (fin'.messagesForNextWrapProof j).oldBulletproofChallenges
      chals') :
    wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg, chals⟩
      = wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg', chals'⟩ := by
  obtain ⟨j, hjw⟩ := j
  simp only at hj
  subst hj
  have h5 : (out'.statement.messagesForNextWrapProof[w - n + i]).val Vw'
      = wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg', chals'⟩ :=
    hW'.2.1 ⟨w - n + i, hjw⟩ sg' chals' hsg' hch'
  -- the step circuit reads the bounded digest exactly
  have h6 : ZMod.val ((out'.statement.messagesForNextWrapProof[w - n + i]).val Vw') < 2 ^ 254 :=
    hW'.2.2.2 ⟨w - n + i, hjw⟩
  rw [← hW.1 sg chals hsg hch, (digests_of_tie htie).1, hmsg, ← hS.2 hn i,
    (digests_of_ofWrap hpub).2 (w - n + i) (by omega), redFq_natCast_val_of_lt _ h6, h5]

/-- A step message and a slot's rebuild of it hash alike, when a wrap circuit carries the
message's digest from the step circuit's statement to the public input the slot verifies. -/
private theorem hash_stepInput_eq {n w : ℕ} {ws ss ncs : Fin n → ℕ} {sa kw ksS : ℕ}
    {branches ncStep ks : ℕ} {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
    {s k' ncs' w' : ℕ} {Vg V' : Valuation Fp} {Vw : Valuation Fq} {dummy : Vector Fq kw}
    {stepOut : StepMainOut n w ws ss sa 1 ncs kw ksS}
    {stmt : StatementPacked ks (Type1 (FVar Fq)) (FVar Fq)}
    {fin : WrapMainFinalizeOut branches w ncStep kw slotWidths}
    {out : WrapMainVerifyOut w ncStep kw ks} {inp : VerifyOneInput s ks k' 1 ncs' w'}
    {cvk : KimchiVK IpaPallas.curve 1} {ms : Vector Bool w'}
    (hS : stepOut.HashesMessages Vg)
    (hpub : CircuitType.Reads Vg stepOut.out (StepStatement.ofWrap Vw out.statement))
    (hW : out.HashesMessages Vw dummy stmt fin)
    (htie : CircuitType.Reads Vw stmt (inp.packedAt cvk V' ms))
    {vk : VkComms 1 (AffinePoint Fp)} {sgs : Vector (AffinePoint Fp) n}
    {chals : Vector (Vector Fp ksS) n}
    (hvk : CircuitType.Reads Vg stepOut.messagesForNextStepProof.dlogPlonkIndex vk)
    (hsgs : CircuitType.Reads Vg stepOut.messagesForNextStepProof.challengePolynomialCommitments
      sgs)
    (hch : CircuitType.Reads Vg stepOut.messagesForNextStepProof.oldBulletproofChallenges chals) :
    Poseidon.RandomOracle.hash IpaPallas.curve.sponge.params
        (stepMsgInput ⟨stepOut.messagesForNextStepProof.appState.map (·.val Vg), vk, sgs, chals⟩)
      = Poseidon.RandomOracle.hash IpaPallas.curve.sponge.params
        (cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y]) ++ inp.appState.toList.map (·.val V')
          ++ keptValues V' ms (inp.prevSgs.zip inp.prevChallenges)) := by
  have h4 := (digests_of_tie htie).2
  rw [hW.2.2.1] at h4
  have hpubD := (digests_of_ofWrap hpub).1
  rw [h4, natCast_val_redFq] at hpubD
  rw [Poseidon.RandomOracle.hash_eq_squeeze, Poseidon.RandomOracle.hash_eq_squeeze]
  have e := (hS.1 vk sgs chals hvk hsgs hch).symm.trans hpubD
  simp only [stepMsgDigest, VerifyOneInput.stepMsgDigest, KimchiVK.indexState] at e
  simp only [Poseidon.absorb, List.foldl_append] at e ⊢
  exact e

/-- A step message carrying `n` proofs and a slot's rebuild of it keeping a suffix of `k`, over a
statement of the message's size, that hash alike: *either* `k = n` and the inputs are equal, *or*
they collide. -/
private theorem stepInput_eq_or_collision {n m k ks sa s' : ℕ} {V : Valuation Fp}
    (cvk : KimchiVK IpaPallas.curve 1) {app : Vector Fp sa} {vk : VkComms 1 (AffinePoint Fp)}
    {sgs : Vector (AffinePoint Fp) n} {chals : Vector (Vector Fp ks) n}
    {app' : Vector (FVar Fp) s'} {ms : Vector Bool m} {psgs : Vector (AffinePoint (FVar Fp)) m}
    {pchals : Vector (Vector (FVar Fp) ks) m} (hs : s' = sa)
    (hmask : ∀ (j : ℕ) (hj : j < m), ms[j] = decide (m - k ≤ j)) (hkm : k ≤ m)
    (hh : Poseidon.RandomOracle.hash IpaPallas.curve.sponge.params
        (stepMsgInput ⟨app, vk, sgs, chals⟩)
      = Poseidon.RandomOracle.hash IpaPallas.curve.sponge.params
        (cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y]) ++ app'.toList.map (·.val V)
          ++ keptValues V ms (psgs.zip pchals))) :
    (k = n ∧ stepMsgInput ⟨app, vk, sgs, chals⟩
        = cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y]) ++ app'.toList.map (·.val V)
          ++ keptValues V ms (psgs.zip pchals)) ∨
      Collision IpaPallas.curve.sponge.params (stepMsgInput ⟨app, vk, sgs, chals⟩)
        (cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y]) ++ app'.toList.map (·.val V)
          ++ keptValues V ms (psgs.zip pchals)) := by
  have hl := length_stepInput cvk hs hmask hkm (app := app) (vk := vk) (sgs := sgs)
    (chals := chals) (V := V) (app' := app') (psgs := psgs) (pchals := pchals)
  by_cases hkn : k = n
  · subst hkn
    by_cases hX : stepMsgInput ⟨app, vk, sgs, chals⟩
        = cvk.comms.indexPoints.flatMap (fun P => [P.x, P.y]) ++ app'.toList.map (·.val V)
          ++ keptValues V ms (psgs.zip pchals)
    · exact Or.inl ⟨rfl, hX⟩
    · exact Or.inr (Collision.of_length_eq (Nat.add_right_cancel hl) hX hh)
  · -- keeping other than `n` proofs, the rebuild is two or more cells off
    exact Or.inr (Collision.of_length_apart
      (List.append_ne_nil_of_left_ne_nil
        (List.append_ne_nil_of_left_ne_nil (indexCoords_ne_nil _ _ _) _) _)
      (List.append_ne_nil_of_left_ne_nil
        (List.append_ne_nil_of_left_ne_nil (indexCoords_ne_nil _ _ _) _) _)
      (length_apart hl hkn) hh)

/-- Two wrap messages' inputs, each with at most `MaxProofsVerified` stacks, that hash alike:
*either* they are equal, *or* they collide. -/
private theorem wrapInput_eq_or_collision {k w w' : ℕ} (dummy : Vector Fq k)
    (hw : w ≤ MaxProofsVerified) (hw' : w' ≤ MaxProofsVerified) {sg sg' : AffinePoint Fq}
    {chals : Vector (Vector Fq k) w} {chals' : Vector (Vector Fq k) w'}
    (hh : wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg, chals⟩
      = wrapMsgDigest IpaVesta.curve.sponge.params dummy ⟨sg', chals'⟩) :
    wrapMsgInput dummy ⟨sg, chals⟩ = wrapMsgInput dummy ⟨sg', chals'⟩ ∨
      Collision IpaVesta.curve.sponge.params (wrapMsgInput dummy ⟨sg, chals⟩)
        (wrapMsgInput dummy ⟨sg', chals'⟩) := by
  by_cases hW : wrapMsgInput dummy ⟨sg, chals⟩ = wrapMsgInput dummy ⟨sg', chals'⟩
  · exact Or.inl hW
  · refine Or.inr (Collision.of_length_eq
      (length_wrapMsgInput dummy hw hw' _ _ _ _) hW ?_)
    rw [Poseidon.RandomOracle.hash_eq_squeeze, Poseidon.RandomOracle.hash_eq_squeeze]
    exact hh

/-- Equal complete messages carry the emitted accumulator into the next step proof's olds,
unless a message hash collides. -/
private theorem WrapStepRun.messages_mem_or_collision
    (rk : WrapStepRun branches w ncStep kw ks n wNext ws ss ncs sa slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw ks n' wNext' ws' ss' ncs' sa' slotWidths')
    (cvk : KimchiVK IpaPallas.curve 1)
    (cvk1 : KimchiVK IpaPallas.curve 1)
    (dummy : Vector Fq kw)
    (A : Accumulator IpaVesta.curve ks)
    (cp : KimchiProof IpaVesta.curve ncStep' ks) :
    rk.Emits cvk dummy A →
    rk1.Consumes cvk1 dummy cp.olds.toList →
    rk.Hands rk1 →
    (readStepMessage rk.Vs rk.stepOut.messagesForNextStepProof =
        rebuildStepMessage rk1.Vs cvk1 rk1.inp rk1.ms ∧
      readWrapMessage rk.Vw dummy
          (rk.wrapVerifyOut.messagesForNextWrapProof rk.wrapFinalizeOut) =
        readWrapMessage rk1.Vw dummy
          (rk1.wrapFinalizeOut.messagesForNextWrapProof rk.slotIndex) ∧
      A ∈ cp.olds.toList) ∨ rk.WrapCollision rk1 dummy ∨ rk.StepCollision rk1 cvk1 := by
  intro he hc hh
  have hn := rk.hn
  obtain ⟨⟨htk, hWk, hSk⟩, hA⟩ := he
  obtain ⟨⟨htk1, hWk1, -⟩, hcons, k, hkw, hkept⟩ := hc
  obtain ⟨hpub, hss⟩ := hh
  have hw1 := rk1.hwi
  -- link k1's slot keeps the last `k` of its slots
  have hkm : k ≤ ws' rk1.i := by omega
  have hmaskk : ∀ (j : ℕ) (hj : j < ws' rk1.i), rk1.ms[j] = decide (ws' rk1.i - k ≤ j) := by
    intro j hj
    rw [hkept j hj, hw1]
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
  let j := rk.slotIndex
  let mW' := rk1.wrapFinalizeOut.messagesForNextWrapProof j
  let sg' : AffinePoint Fq :=
    ⟨mW'.challengePolynomialCommitment.x.val rk1.Vw, mW'.challengePolynomialCommitment.y.val rk1.Vw⟩
  let chalsW' := mW'.oldBulletproofChallenges.map (·.map (·.val rk1.Vw))
  -- the wrap digest, from link k's wrap circuit through its step circuit to link k1's wrap circuit
  have hwrapD := wrapMsgDigest_eq hn rk.i j rfl hWk htk rfl hSk hpub hWk1 (sg := sg) (sg' := sg')
    (chals := chalsW) (chals' := chalsW') (reads_pt _ _) (reads_vecs _ _) (reads_pt _ _)
    (reads_vecs _ _)
  -- the step digest, from link k's step circuit through link k1's wrap circuit to its slot
  have hstepD := hash_stepInput_eq hSk hpub hWk1 htk1 (vk := vk) (sgs := sgs) (chals := chals)
    (reads_key _ _) (reads_pts _ _) (reads_vecs _ _)
  rcases stepInput_eq_or_collision cvk1 hss hmaskk hkm hstepD with ⟨hkn, hX⟩ | hcol
  swap
  · exact Or.inr (Or.inr ⟨vk, sgs, chals, reads_key _ _, reads_pts _ _, reads_vecs _ _, hcol⟩)
  -- link k1's slot keeps exactly `rk`'s slots
  have hmask : ∀ (j : ℕ) (hj : j < ws' rk1.i), rk1.ms[j] = decide (ws' rk1.i - n ≤ j) := by
    intro j hj
    rw [hmaskk j hj, hkn]
  rcases wrapInput_eq_or_collision dummy (rk.hwi ▸ rk.hws rk.i)
    (Nat.lt_succ_iff.mp (slotWidths'[j]).isLt) hwrapD with hW | hcol
  swap
  · exact Or.inr (Or.inl ⟨sg, sg', chalsW, chalsW', reads_pt _ _, reads_vecs _ _, reads_pt _ _,
      reads_vecs _ _, hcol⟩)
  refine Or.inl ⟨stepMessage_eq_of_input_eq rk.Vs rk1.Vs mS cvk1 rk1.inp rk1.ms hss
    (by omega) hmask hX, wrapMessage_eq_of_input_eq rk.Vw rk1.Vw dummy mW mW'
    (rk.hwi ▸ rk.hws rk.i) (Nat.lt_succ_iff.mp (slotWidths'[j]).isLt) hW, ?_⟩
  -- the commitment: both wrap inputs end with it
  obtain ⟨-, hsg⟩ := List.append_inj' hW rfl
  simp only [List.cons.injEq, and_true] at hsg
  -- the challenges: both step inputs end with the kept slots'
  set m := ws' rk1.i with hm
  have hmn : n ≤ m := hw1 ▸ hn
  obtain ⟨-, -, hu⟩ := kept_of_stepInput_eq cvk1 hmask hmn hX rk.i
  -- `A` is the kept entry at link k1's slot `j`
  have hb' : m - n + rk.i < m := by omega
  rw [← hcons, ← hA, WrapStep.consumedAccumulators]
  refine List.mem_map.mpr ⟨⟨m - n + rk.i, hb'⟩, List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩, ?_⟩
  · simp only [Fin.getElem_fin, hmask, decide_eq_true_eq]
    omega
  symm
  have hj : Fin.cast rk1.hwi ⟨m - n + rk.i, hb'⟩ = j :=
    Fin.ext (by simp [j, WrapStepRun.slotIndex]; omega)
  simp only [WrapStep.emittedAccumulator, Accumulator.ofCells, Fin.getElem_fin, hj]
  congr 1
  · exact readPt_congr hsg.1 hsg.2
  · rw [hu]
    simp [chals, mS]

/-- Complete messages agree and the earlier proof accepts, or the accepted later proof carries
an invalid accumulator, unless one of the two message hashes collides. -/
theorem WrapStepRun.handover_or_collision
    (σ : SRS IpaVesta.curve.Point)
    (rk : WrapStepRun branches w ncStep kw σ.k n wNext ws ss ncs sa slotWidths)
    (rk1 : WrapStepRun branches' wNext ncStep' kw σ.k n' wNext' ws' ss' ncs' sa' slotWidths')
    (cvk cvk1 : KimchiVK IpaPallas.curve 1)
    (dummy : Vector Fq kw)
    (vk : KimchiVK IpaVesta.curve ncStep)
    (p : KimchiProof IpaVesta.curve ncStep σ.k)
    (pub : Array Fp)
    (nextVk : KimchiVK IpaVesta.curve ncStep')
    (q : KimchiProof IpaVesta.curve ncStep' σ.k)
    (nextPub : Array Fp) :
  let sentStep := readStepMessage rk.Vs rk.stepOut.messagesForNextStepProof
  let receivedStep := rebuildStepMessage rk1.Vs cvk1 rk1.inp rk1.ms
  let sentWrap := readWrapMessage rk.Vw dummy
    (rk.wrapVerifyOut.messagesForNextWrapProof rk.wrapFinalizeOut)
  let receivedWrap := readWrapMessage rk1.Vw dummy
    (rk1.wrapFinalizeOut.messagesForNextWrapProof rk.slotIndex)
  rk.Emits cvk dummy ⟨p.opening.sg, wireChallenges σ vk p pub⟩ →
  rk1.Consumes cvk1 dummy q.olds.toList →
  rk.Hands rk1 →
  kimchiVerify IpaVesta.curve σ nextVk q nextPub = true →
  (SgOk σ vk p pub → kimchiVerify IpaVesta.curve σ vk p pub = true) →
  (sentStep = receivedStep ∧
   sentWrap = receivedWrap ∧
   (kimchiVerify IpaVesta.curve σ vk p pub = true ∨
    AccumulatorFailure σ nextVk q nextPub)) ∨
  rk.WrapCollision rk1 dummy ∨
  rk.StepCollision rk1 cvk1 := by
  dsimp only
  intro he hc hh hAccept hCapstone
  rcases rk.messages_mem_or_collision rk1 cvk cvk1 dummy _ q he hc hh with h | h
  · exact Or.inl ⟨h.1, h.2.1,
      accepts_or_accumulatorFailure σ vk p pub nextVk q nextPub h.2.2 hAccept hCapstone⟩
  · exact Or.inr h

/-! ## A step-wrap link -/

/-- One link's run, as `stepWrap_kimchiVerify` names it: a step circuit's cells and its slot that
verifies a wrap proof, and the next wrap circuit's statement and cells. -/
structure StepWrapRun (n w : ℕ) (ws ss : Fin n → ℕ) (sa : ℕ) (ncs : Fin n → ℕ)
    (kw ks branches ncStep : ℕ)
    (slotWidths : Vector (Fin (MaxProofsVerified + 1)) w) where
  /-- The step circuit's valuation. -/
  Vg : Valuation Fp
  /-- The wrap circuit's valuation. -/
  Vs : Valuation Fq
  /-- The step circuit's cells. -/
  stepOut : StepMainOut n w ws ss sa 1 ncs kw ks
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

variable {n w : ℕ} {ws ss ncs : Fin n → ℕ} {sa kw ks branches ncStep : ℕ}
  {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
  (r : StepWrapRun n w ws ss sa ncs kw ks branches ncStep slotWidths)

/-- The slot's input cells. -/
def inp : VerifyOneInput (ss r.i) ks kw 1 (ncs r.i) (ws r.i) :=
  slotInput (r.hws r.i) (constPt r.dummySg) (r.stepOut.prevs r.i) (r.stepOut.slots r.i)
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

/-- The link consumes `olds`, its slot's mask being what the slot's mask cells read as, as
`stepWrap_kimchiVerify` concludes. -/
def Consumes (dummy : Vector Fq kw) (olds : List (Accumulator IpaPallas.curve kw)) : Prop :=
  r.Hashes dummy ∧
  StepWrap.consumedAccumulators r.Vg r.Vs r.inp dummy r.wrapFinalizeOut r.jf = olds ∧
  CircuitType.Reads r.Vg r.inp.proofMask r.ms

end StepWrapRun

section StepWrapLinks

variable {n w : ℕ} {ws ss ncs : Fin n → ℕ} {sa kw ks branches ncStep : ℕ}
  {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
  {n' w' : ℕ} {ws' ss' ncs' : Fin n' → ℕ} {sa' branches' ncStep' : ℕ}
  {slotWidths' : Vector (Fin (MaxProofsVerified + 1)) w'}

/-- The link `rk` hands its wrap proof to the next link `rk1` through the wrap-step link between
them, `rk`'s wrap circuit and `rk1`'s step slot: the tie and the slot's width are
`wrapStep_kimchiVerify`'s premises for that link and the kept suffix its conclusion; the slot
reads a previous statement of the size of `rk`'s application state. -/
def StepWrapRun.Hands (rk : StepWrapRun n w ws ss sa ncs kw ks branches ncStep slotWidths)
    (rk1 : StepWrapRun n' w' ws' ss' sa' ncs' kw ks branches' ncStep' slotWidths')
    (cvk : KimchiVK IpaPallas.curve 1) : Prop :=
  CircuitType.Reads rk.Vs rk.wrapStmt (rk1.inp.packedAt cvk rk1.Vg rk1.ms) ∧
  ws' rk1.i = w ∧
  (∃ k ≤ w, ∀ (j : ℕ) (hj : j < ws' rk1.i), rk1.ms[j] = decide (w - k ≤ j)) ∧
  ss' rk1.i = sa

/-- The wrap message `rk` sends and the one the next link `rk1` rebuilds for its slot collide
(`WrapMsgCollision`). -/
def StepWrapRun.WrapCollision (rk : StepWrapRun n w ws ss sa ncs kw ks branches ncStep slotWidths)
    (rk1 : StepWrapRun n' w' ws' ss' sa' ncs' kw ks branches' ncStep' slotWidths')
    (dummy : Vector Fq kw) : Prop :=
  WrapMsgCollision rk.Vs rk.wrapVerifyOut rk.wrapFinalizeOut rk1.Vs rk1.wrapFinalizeOut rk1.jf
    dummy

/-- The step message `rk` sends and the one the next link `rk1`'s slot rebuilds collide
(`StepMsgCollision`). -/
def StepWrapRun.StepCollision (rk : StepWrapRun n w ws ss sa ncs kw ks branches ncStep slotWidths)
    (rk1 : StepWrapRun n' w' ws' ss' sa' ncs' kw ks branches' ncStep' slotWidths')
    (cvk : KimchiVK IpaPallas.curve 1) : Prop :=
  StepMsgCollision rk.Vg rk.stepOut rk1.Vg rk1.inp rk1.ms cvk

/-- Equal complete messages carry the emitted accumulator into the next wrap proof's olds,
unless a message hash collides. -/
private theorem StepWrapRun.messages_mem_or_collision
    (rk : StepWrapRun n w ws ss sa ncs kw ks branches ncStep slotWidths)
    (rk1 : StepWrapRun n' w' ws' ss' sa' ncs' kw ks branches' ncStep' slotWidths')
    (cvk : KimchiVK IpaPallas.curve 1)
    (dummy : Vector Fq kw)
    (A : Accumulator IpaPallas.curve kw)
    (cp : KimchiProof IpaPallas.curve 1 kw) :
    rk.Emits dummy A →
    rk1.Consumes dummy cp.olds.toList →
    rk.Hands rk1 cvk →
    (readStepMessage rk.Vg rk.stepOut.messagesForNextStepProof =
        rebuildStepMessage rk1.Vg cvk rk1.inp rk1.ms ∧
      readWrapMessage rk.Vs dummy
          (rk.wrapVerifyOut.messagesForNextWrapProof rk.wrapFinalizeOut) =
        readWrapMessage rk1.Vs dummy
          (rk1.wrapFinalizeOut.messagesForNextWrapProof rk1.jf) ∧
      A ∈ cp.olds.toList) ∨ rk.WrapCollision rk1 dummy ∨ rk.StepCollision rk1 cvk := by
  intro he hc hh
  obtain ⟨⟨hpub, hSk, hWk⟩, hA⟩ := he
  obtain ⟨⟨hpub1, hS1, hW1⟩, hcons, -⟩ := hc
  obtain ⟨htie, hw1, ⟨k, hkw, hkept⟩, hss⟩ := hh
  -- the slot keeps the last `k` of its slots
  have hkm : k ≤ ws' rk1.i := by omega
  have hmaskk : ∀ (j : ℕ) (hj : j < ws' rk1.i), rk1.ms[j] = decide (ws' rk1.i - k ≤ j) := by
    intro j hj
    rw [hkept j hj, hw1]
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
  have hwrapD := wrapMsgDigest_eq rk1.hn rk1.i rk1.jf rfl hWk htie rfl hS1 hpub1 hW1 (sg := sg)
    (sg' := sg') (chals := chalsW) (chals' := chalsW') (reads_pt _ _) (reads_vecs _ _)
    (reads_pt _ _) (reads_vecs _ _)
  -- the step digest, from link k's step circuit through its wrap circuit to link k1's slot
  have hstepD := hash_stepInput_eq hSk hpub hWk htie (vk := vk) (sgs := sgs) (chals := chals)
    (reads_key _ _) (reads_pts _ _) (reads_vecs _ _)
  rcases stepInput_eq_or_collision cvk hss hmaskk hkm hstepD with ⟨hkn, hX⟩ | hcol
  swap
  · exact Or.inr (Or.inr ⟨vk, sgs, chals, reads_key _ _, reads_pts _ _, reads_vecs _ _, hcol⟩)
  -- the slot keeps exactly `rk`'s slots
  have hmask : ∀ (j : ℕ) (hj : j < ws' rk1.i), rk1.ms[j] = decide (ws' rk1.i - n ≤ j) := by
    intro j hj
    rw [hmaskk j hj, hkn]
  rcases wrapInput_eq_or_collision dummy rk.hw (Nat.lt_succ_iff.mp (slotWidths'[rk1.jf]).isLt)
    hwrapD with hW | hcol
  swap
  · exact Or.inr (Or.inl ⟨sg, sg', chalsW, chalsW', reads_pt _ _, reads_vecs _ _, reads_pt _ _,
      reads_vecs _ _, hcol⟩)
  refine Or.inl ⟨stepMessage_eq_of_input_eq rk.Vg rk1.Vg mS cvk rk1.inp rk1.ms hss
    (by have := rk.hn; omega) hmask hX, wrapMessage_eq_of_input_eq rk.Vs rk1.Vs dummy mW mW'
    rk.hw (Nat.lt_succ_iff.mp (slotWidths'[rk1.jf]).isLt) hW, ?_⟩
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

/-- Complete messages agree and the earlier proof accepts, or the accepted later proof carries
an invalid accumulator, unless one of the two message hashes collides. -/
theorem StepWrapRun.handover_or_collision
    (σ : SRS IpaPallas.curve.Point)
    {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
    {slotWidths' : Vector (Fin (MaxProofsVerified + 1)) w'}
    (rk : StepWrapRun n w ws ss sa ncs σ.k ks branches ncStep slotWidths)
    (rk1 : StepWrapRun n' w' ws' ss' sa' ncs' σ.k ks branches' ncStep' slotWidths')
    (dummy : Vector Fq σ.k)
    (vk : KimchiVK IpaPallas.curve 1)
    (p : KimchiProof IpaPallas.curve 1 σ.k)
    (pub : Array Fq)
    (nextVk : KimchiVK IpaPallas.curve 1)
    (q : KimchiProof IpaPallas.curve 1 σ.k)
    (nextPub : Array Fq) :
  let sentStep := readStepMessage rk.Vg rk.stepOut.messagesForNextStepProof
  let receivedStep := rebuildStepMessage rk1.Vg nextVk rk1.inp rk1.ms
  let sentWrap := readWrapMessage rk.Vs dummy
    (rk.wrapVerifyOut.messagesForNextWrapProof rk.wrapFinalizeOut)
  let receivedWrap := readWrapMessage rk1.Vs dummy
    (rk1.wrapFinalizeOut.messagesForNextWrapProof rk1.jf)
  rk.Emits dummy ⟨p.opening.sg, wireChallenges σ vk p pub⟩ →
  rk1.Consumes dummy q.olds.toList →
  rk.Hands rk1 nextVk →
  kimchiVerify IpaPallas.curve σ nextVk q nextPub = true →
  (SgOk σ vk p pub → kimchiVerify IpaPallas.curve σ vk p pub = true) →
  (sentStep = receivedStep ∧
   sentWrap = receivedWrap ∧
   (kimchiVerify IpaPallas.curve σ vk p pub = true ∨
    AccumulatorFailure σ nextVk q nextPub)) ∨
  rk.WrapCollision rk1 dummy ∨
  rk.StepCollision rk1 nextVk := by
  dsimp only
  intro he hc hh hAccept hCapstone
  rcases rk.messages_mem_or_collision rk1 nextVk dummy _ q he hc hh with h | h
  · exact Or.inl ⟨h.1, h.2.1,
      accepts_or_accumulatorFailure σ vk p pub nextVk q nextPub h.2.2 hAccept hCapstone⟩
  · exact Or.inr h

end StepWrapLinks

end Links

end Pickles
