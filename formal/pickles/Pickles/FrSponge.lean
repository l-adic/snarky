import Snarky.Kimchi.Circuit.Sponge
import Snarky.Kimchi.Circuit.RangeCheck
import Kimchi.Verifier.Kimchi
import Pickles.ListLemmas
import Pickles.OptSponge
import Pickles.Prechallenge

set_option mvcgen.warning false

/-!
# The fr-sponge in circuit

Port of the fr-sponge gadgets of `packages/pickles/src/Pickles/PlonkChecks.purs`: the digest
of the previous proofs' bulletproof challenges, and the verifier's fr-sponge schedule —
absorb the digest before evaluations, the challenge digest and every evaluation, then
squeeze the two prechallenges `ξ` and `r` as 128-bit values.

## Main definitions

* `challengeDigest`: a fresh sponge absorbing every previous challenge, squeezed once.
* `maskedChallengeDigest`: the step side's digest, the conditional sponge over the
  challenges guarded by their proof's mask bit.
* `squeezeXiR`: the schedule of `Kimchi.Verifier.frTranscript` at any chunk count, the
  challenge digest computed between its first two absorbs, then two squeezes each split by
  `lowest128Bits'`.

## Main results

* `challengeDigest_spec`: the output reads as the squeeze of the value sponge over the
  challenges.
* `maskedChallengeDigest_spec`: the output reads as the squeeze of the value sponge over
  the challenge vectors whose mask bit is set.
* `squeezeXiR_spec`: the sponge reads as `Poseidon.absorb` of `frTranscript`, and each
  output is the low half of the corresponding squeeze: `x = lo + 2¹²⁸·hi` with `hi < 2¹²⁸`,
  and `lo < 2¹²⁸` where the low bits are constrained.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]

/-- Absorb a list, left to right. -/
def absorbList [ConstraintHolds F c] (p : Poseidon.Params F) (sv : SpongeVar F) :
    List (FVar F) → CircuitM F c (SpongeVar F)
  | [] => pure sv
  | x :: xs => do
    let sv' ← SpongeVar.absorb p sv x
    absorbList p sv' xs

/-- The digest of the previous proofs' bulletproof challenges `c_{j,i}`: a fresh sponge
absorbing them in order, squeezed once. -/
def challengeDigest [ConstraintHolds F c] {n k : ℕ} (p : Poseidon.Params F)
    (prev : Vector (Vector (FVar F) k) n) : CircuitM F c (FVar F) := do
  let sv ← absorbList p SpongeVar.init prev.flatten.toList
  let (d, _) ← SpongeVar.squeeze p sv
  pure d

/-- Each challenge paired with its vector's guard, in order. -/
private def maskedEntries {β α : Type} {n k : ℕ} (mask : Vector β n)
    (prev : Vector (Vector α k) n) : Vector (β × α) (n * k) :=
  (Vector.zipWith (fun b cs => cs.map (b, ·)) mask prev).flatten

/-- The step side's digest of the previous proofs' challenges: the conditional sponge over the
challenges, each guarded by its proof's mask bit, squeezed once. -/
def maskedChallengeDigest [ConstraintHolds F c] {n k : ℕ} (p : Poseidon.Params F)
    (mask : Vector (BoolVar F) n) (prev : Vector (Vector (FVar F) k) n) : CircuitM F c (FVar F) :=
  OptSponge.squeeze p (maskedEntries mask prev).toList

/-- The fr-sponge schedule at `nc` chunks per column: absorb `digestBefore`, run `digest` and
absorb its result, then the rest of `Kimchi.Verifier.frTranscript` at the same width — `ft(ζω)`,
the public chunks and every column's chunks, a column's `ζ` chunks before its `ζω` chunks — then
squeeze `ξ` and `r`, each split to its low 128 bits — `ξ` with the low bits constrained iff
`xiConstrainLowBits`, `r` always. -/
def squeezeXiR [ConstraintHolds F c] [ToNat F] {nc : ℕ} (p : Poseidon.Params F)
    (digestBefore : FVar F) (digest : CircuitM F c (FVar F)) (ftEval1 : FVar F)
    (pub : PointEvaluations (Vector (FVar F) nc)) (evals : ProofEvaluations (Vector (FVar F) nc))
    (endo : FVar F) (xiConstrainLowBits : Bool) :
    CircuitM F c (SizedF 128 (FVar F) × SizedF 128 (FVar F)) := do
  let sv ← SpongeVar.absorb p SpongeVar.init digestBefore
  let d ← digest
  let sv ← absorbList p sv (frTranscript digestBefore d ftEval1 pub evals).tail
  let (x₁, sv) ← SpongeVar.squeeze p sv
  let xi ← lowest128Bits' xiConstrainLowBits endo x₁
  let (x₂, _) ← SpongeVar.squeeze p sv
  let r ← lowest128Bits' true endo x₂
  pure (xi, r)

/-! ## Soundness -/

variable {V : Valuation F}

/-- Absorbing a list reads as the value absorb of the readings. -/
theorem absorbList_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) :
    ∀ (sv : SpongeVar F) (xs : List (FVar F)),
      ⦃⌜True⌝⦄ absorbList (c := Builder V (KimchiConstraint F)) p sv xs
      ⦃⇓ r _ => ⌜∀ s, SpongeVar.ReadsAt V sv s →
        SpongeVar.ReadsAt V r (Poseidon.absorb p s (xs.map (·.val V)))⌝⦄
  | sv, [] => by
    simp only [absorbList]
    mvcgen
    simp [Poseidon.absorb]
  | sv, x :: xs => by
    simp only [absorbList]
    have hx := SpongeVar.absorb_spec (V := V) p hsize sv x
    have ih := fun sv' => absorbList_spec p hsize sv' xs
    mvcgen [hx, ih]
    rename_i _ _ _ hstep _ _
    intro hrest s hs
    exact hrest _ (hstep s hs)

/-- Under any valuation satisfying the emitted constraints, with the challenges reading as
`c_{j,i}`, the output reads as the first squeeze of the value sponge that absorbed them in
order: `(squeeze p (absorb p init [c_{0,0}, …, c_{n−1,k−1}])).1`, which is the fr-sponge
digest `frDigest` of the absorbed challenges. -/
theorem challengeDigest_spec {n k : ℕ} (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (prev : Vector (Vector (FVar F) k) n) :
    ⦃⌜True⌝⦄ challengeDigest (c := Builder V (KimchiConstraint F)) p prev
    ⦃⇓ d _ => ⌜d.val V = (Poseidon.squeeze p
      (Poseidon.absorb p Poseidon.init (prev.flatten.toList.map (·.val V)))).1⌝⦄ := by
  simp only [challengeDigest]
  have ha := absorbList_spec (V := V) p hsize SpongeVar.init prev.flatten.toList
  have hsq := fun sv => SpongeVar.squeeze_spec (V := V) p hsize sv
  mvcgen [ha, hsq]
  rename_i _ _ _ habs _ _ hsqz
  exact (hsqz _ (habs _ SpongeVar.ReadsAt.init)).1

/-- The guarded entries read entrywise once the mask does. -/
private theorem maskedEntries_forall₂ {n k : ℕ} {mask : Vector (BoolVar F) n} {ms : Vector Bool n}
    (hm : CircuitType.Reads V mask ms) (prev : Vector (Vector (FVar F) k) n) :
    List.Forall₂ (CircuitType.Reads V) (maskedEntries mask prev).toList
      (maskedEntries ms (prev.map (·.map (·.val V)))).toList := by
  simp only [maskedEntries, toList_flatten']
  refine List.rel_flatten ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine forall₂_toList_iff.mpr fun i => forall₂_toList_iff.mpr fun j => ?_
  simp only [Fin.getElem_fin, Vector.getElem_zipWith, Vector.getElem_map]
  exact CircuitType.reads_prod.mpr
    ⟨CircuitType.reads_vector.mp hm i i.isLt, CircuitType.reads_fvar.mpr rfl⟩

omit [Field F] [DecidableEq F] in
/-- The kept entries are the vectors whose guard is set, in order. -/
private theorem kept_maskedEntries {α : Type} {n k : ℕ} (f : α → F) (ms : Vector Bool n)
    (vs : Vector (Vector α k) n) :
    ((maskedEntries ms (vs.map (·.map f))).toList.filter (·.1)).map (·.2)
      = (Vector.zipWith (fun m cs => if m then cs.toList.map f else []) ms vs).toList.flatten := by
  simp only [maskedEntries, toList_flatten', List.filter_flatten, List.map_flatten, List.map_map]
  congr 1
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  have hi' : i < n := by simpa using hi
  simp only [List.getElem_map, Vector.getElem_toList, Vector.getElem_zipWith, Vector.getElem_map,
    Function.comp_apply]
  cases ms[i] <;> simp [Vector.toList_map, List.filter_map, Function.comp_def]

/-- Under any valuation satisfying the emitted constraints, with the mask reading as
`m_0, …, m_{n−1}` and the challenge vectors as `c_j = (c_{j,0}, …, c_{j,k−1})`, the output
reads as the first squeeze of the value sponge that absorbed exactly the kept vectors in
order: `(squeeze p (absorb p init (c_{j₁} ++ … ++ c_{jₗ}))).1` for `j₁ < … < jₗ` the indices
with `m_j = 1`. -/
theorem maskedChallengeDigest_spec {n k : ℕ} (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k)
    (mask : Vector (BoolVar F) n) (prev : Vector (Vector (FVar F) k) n) (ms : Vector Bool n)
    (hm : CircuitType.Reads V mask ms)
    (hchar : ∀ j : ℕ, j ≤ n * k → (j : F) = 0 → j = 0) :
    ⦃⌜True⌝⦄ maskedChallengeDigest (c := Builder V (KimchiConstraint F)) p mask prev
    ⦃⇓ d _ => ⌜d.val V = (Poseidon.squeeze p (Poseidon.absorb p Poseidon.init
      (Vector.zipWith (fun m cs => if m then cs.toList.map (·.val V) else []) ms
        prev).toList.flatten)).1⌝⦄ := by
  simp only [maskedChallengeDigest]
  have h := OptSponge.squeeze_spec (V := V) p hsize hall _ _ (maskedEntries_forall₂ hm prev)
    (fun j hj => hchar j (by simpa using hj))
  rwa [kept_maskedEntries] at h

omit [DecidableEq F] in
/-- The circuit transcript reads as `frTranscript` of the readings: the transcript is natural
in its entries. -/
private theorem map_val_frTranscript {nc : ℕ} (digestBefore recDigest ftEval1 : FVar F)
    (pub : PointEvaluations (Vector (FVar F) nc)) (evals : ProofEvaluations (Vector (FVar F) nc)) :
    (frTranscript digestBefore recDigest ftEval1 pub evals).map (·.val V)
      = frTranscript (digestBefore.val V) (recDigest.val V) (ftEval1.val V)
          (pub.map fun v => v.map (·.val V)) (evals.map fun v => v.map (·.val V)) := by
  simp [frTranscript, PointEvaluations.map, ProofEvaluations.map, List.map_flatten,
    Function.comp_def, Vector.toList_map, List.map_map]

/-- Under any valuation satisfying the emitted constraints, with `digest` reading as `dv`
and the inputs as themselves, the two squeezes are the wire verifier's
`frSqueezes p (frTranscript digestBefore dv ft(ζω) pub evals)` — the raw elements behind
`frOracles`' `(v, u)` (`Kimchi.Verifier.frOracles_eq_frPrechallenges`) — and the outputs `ξ`, `r`
are their low halves (`Low128`), `r` a prechallenge and, where the low bits are
constrained, `ξ` too. -/
theorem squeezeXiR_spec [ToNat F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsw : SplitWidth F)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (digestBefore : FVar F) (digest : CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
    (dv : F) (hd : ⦃⌜True⌝⦄ digest ⦃⇓ d _ => ⌜d.val V = dv⌝⦄)
    {nc : ℕ} (ftEval1 : FVar F) (pub : PointEvaluations (Vector (FVar F) nc))
    (evals : ProofEvaluations (Vector (FVar F) nc)) (endo : FVar F) (xiConstrainLowBits : Bool) :
    ⦃⌜True⌝⦄
    squeezeXiR (c := Builder V (KimchiConstraint F)) p digestBefore digest ftEval1 pub evals
      endo xiConstrainLowBits
    ⦃⇓ out _ => ⌜
      let sq := frSqueezes p
        (frTranscript (digestBefore.val V) dv (ftEval1.val V)
          (pub.map fun v => v.map (·.val V)) (evals.map fun v => v.map (·.val V)))
      let x₁ := sq.1
      let x₂ := sq.2
      Low128 V x₁ out.1 ∧ Low128 V x₂ out.2 ∧
        (xiConstrainLowBits = true → ∃ m : Prechallenge, Reads128 V out.1 m) ∧
        (∃ m : Prechallenge, Reads128 V out.2 m)⌝⦄ := by
  simp only [squeezeXiR]
  have h0 := SpongeVar.absorb_spec (V := V) p hsize SpongeVar.init digestBefore
  have ha := fun sv d => absorbList_spec (V := V) p hsize sv
    (frTranscript digestBefore d ftEval1 pub evals).tail
  have hsq := fun sv => SpongeVar.squeeze_spec (V := V) p hsize sv
  have hlo := fun b x => builder_spec_and _ _ _ (lowest128Bits'_spec (V := V) h2 h3 b endo x)
    (lowest128Bits'_below (V := V) h2 h3 hsw.inj hsw.modulus_lt b endo x)
  mvcgen [h0, hd, ha, hsq, hlo]
  rename_i _ _ _ hA d _ hdv svB _ hB _ _ hsq1 _ _ hlo1 _ _ hsq2 _ _ hlo2
  have hS : SpongeVar.ReadsAt V svB (Poseidon.absorb p Poseidon.init
      (frTranscript (digestBefore.val V) dv (ftEval1.val V)
        (pub.map fun v => v.map (·.val V)) (evals.map fun v => v.map (·.val V)))) := by
    have h := hB _ (hA _ SpongeVar.ReadsAt.init)
    have hcons : frTranscript digestBefore d ftEval1 pub evals
        = digestBefore :: (frTranscript digestBefore d ftEval1 pub evals).tail := rfl
    rw [← hdv, ← map_val_frTranscript, hcons, List.map_cons, Poseidon.absorb, List.foldl_cons]
    rw [Poseidon.absorb] at h
    exact h
  obtain ⟨hx1, hs1⟩ := hsq1 _ hS
  obtain ⟨hx2, -⟩ := hsq2 _ hs1
  obtain ⟨⟨-, -, -, hb₁⟩, hc₁⟩ := hlo1
  obtain ⟨⟨-, -, -, hr₂⟩, hc₂⟩ := hlo2
  simp only [frSqueezes]
  exact ⟨fun lo hl hr => hx1 ▸ hc₁ lo hl hr, fun lo hl hr => hx2 ▸ hc₂ lo hl hr,
    fun h => reads128_of_nat (hb₁ h), reads128_of_nat hr₂⟩

/-! The gadgets are sealed after their specs: a consumer composes `challengeDigest_spec`,
`maskedChallengeDigest_spec` and `squeezeXiR_spec`, never the bodies. -/
attribute [irreducible] absorbList challengeDigest maskedChallengeDigest squeezeXiR

end Pickles
