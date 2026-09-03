import Snarky.Kimchi.Circuit.Sponge
import Snarky.Kimchi.Circuit.RangeCheck
import Kimchi.Verifier.Kimchi

set_option mvcgen.warning false

/-!
# The fr-sponge in circuit

Port of the PureScript `Pickles.PlonkChecks.challengeDigest` and `squeezeXiR`: the digest
of the previous proofs' bulletproof challenges, and the verifier's fr-sponge schedule —
absorb the digest before evaluations, the challenge digest and every evaluation, then
squeeze the two prechallenges `ξ` and `r` as 128-bit values.

## Main definitions

* `challengeDigest`: a fresh sponge absorbing every previous challenge, squeezed once.
* `squeezeXiR`: the schedule of `Kimchi.Verifier.frTranscript`, the challenge digest
  computed between its first two absorbs, then two squeezes each split by
  `lowest128Bits'`.

## Main results

* `challengeDigest_spec`: the output reads as the squeeze of the value sponge over the
  challenges.
* `squeezeXiR_spec`: the sponge reads as `Poseidon.absorb` of `frTranscript`, and each
  output is the low half of the corresponding squeeze: `x = lo + 2¹²⁸·hi` with `hi < 2¹²⁸`,
  and `lo < 2¹²⁸` where the low bits are constrained.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]

/-- Absorb a list, left to right. -/
private def absorbList (p : Poseidon.Params F) (sv : SpongeVar F) :
    List (FVar F) → CircuitM F c (SpongeVar F)
  | [] => pure sv
  | x :: xs => do
    let sv' ← SpongeVar.absorb p sv x
    absorbList p sv' xs

/-- The digest of the previous proofs' bulletproof challenges `c_{j,i}`: a fresh sponge
absorbing them in order, squeezed once. -/
def challengeDigest (p : Poseidon.Params F) (prev : List (List (FVar F))) :
    CircuitM F c (FVar F) := do
  let sv ← absorbList p SpongeVar.init prev.flatten
  let (d, _) ← SpongeVar.squeeze p sv
  pure d

/-- The transcript after the digest before evaluations: `frTranscript` from its second
entry, at one chunk per column. -/
private def frTail (recDigest ftEval1 : FVar F) (pub : PointEvaluations (FVar F))
    (evals : ProofEvaluations (FVar F)) : List (FVar F) :=
  let pt := fun (e : PointEvaluations (FVar F)) => [e.zeta, e.zetaOmega]
  [recDigest, ftEval1, pub.zeta, pub.zetaOmega]
    ++ pt evals.z ++ pt evals.genericSelector ++ pt evals.poseidonSelector
    ++ pt evals.completeAddSelector ++ pt evals.mulSelector ++ pt evals.emulSelector
    ++ pt evals.endomulScalarSelector
    ++ (evals.w.toList.map pt).flatten ++ (evals.coefficients.toList.map pt).flatten
    ++ (evals.s.toList.map pt).flatten

/-- The fr-sponge schedule: absorb `digestBefore`, run `digest` and absorb its result,
absorb `ft(ζω)`, the public pair and every column pair, then squeeze `ξ` and `r`, each
split to its low 128 bits — `ξ` with the low bits constrained iff `xiConstrainLowBits`,
`r` always. -/
def squeezeXiR [ToNat F] (p : Poseidon.Params F) (digestBefore : FVar F)
    (digest : CircuitM F c (FVar F)) (ftEval1 : FVar F) (pub : PointEvaluations (FVar F))
    (evals : ProofEvaluations (FVar F)) (endo : FVar F) (xiConstrainLowBits : Bool) :
    CircuitM F c (SizedF 128 (FVar F) × SizedF 128 (FVar F)) := do
  let sv ← SpongeVar.absorb p SpongeVar.init digestBefore
  let d ← digest
  let sv ← absorbList p sv (frTail d ftEval1 pub evals)
  let (x₁, sv) ← SpongeVar.squeeze p sv
  let xi ← lowest128Bits' xiConstrainLowBits endo x₁
  let (x₂, _) ← SpongeVar.squeeze p sv
  let r ← lowest128Bits' true endo x₂
  pure (xi, r)

/-! ## Soundness -/

variable {V : Valuation F}

omit [DecidableEq F] in
/-- The fresh circuit sponge reads as the fresh value sponge. -/
private theorem readsAt_init : SpongeVar.ReadsAt V (SpongeVar.init (F := F)) Poseidon.init :=
  ⟨rfl, rfl⟩

/-- Absorbing a list reads as the value absorb of the readings. -/
private theorem absorbList_spec (p : Poseidon.Params F)
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
theorem challengeDigest_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (prev : List (List (FVar F))) :
    ⦃⌜True⌝⦄ challengeDigest (c := Builder V (KimchiConstraint F)) p prev
    ⦃⇓ d _ => ⌜d.val V = (Poseidon.squeeze p
      (Poseidon.absorb p Poseidon.init (prev.flatten.map (·.val V)))).1⌝⦄ := by
  simp only [challengeDigest]
  have ha := absorbList_spec (V := V) p hsize SpongeVar.init prev.flatten
  have hsq := fun sv => SpongeVar.squeeze_spec (V := V) p hsize sv
  mvcgen [ha, hsq]
  rename_i _ _ _ habs _ _ hsqz
  exact (hsqz _ (habs _ readsAt_init)).1

omit [DecidableEq F] in
/-- The circuit transcript reads as `frTranscript` at one chunk per column. -/
private theorem map_val_frTail (digestBefore recDigest ftEval1 : FVar F)
    (pub : PointEvaluations (FVar F)) (evals : ProofEvaluations (FVar F)) :
    (digestBefore :: frTail recDigest ftEval1 pub evals).map (·.val V)
      = frTranscript (digestBefore.val V) (recDigest.val V) (ftEval1.val V)
          (pub.map fun x => #v[x.val V]) (evals.map fun x => #v[x.val V]) := by
  simp [frTail, frTranscript, PointEvaluations.map, ProofEvaluations.map, List.map_flatten,
    Function.comp_def, Vector.toList_map, List.map_map]

/-- Under any valuation satisfying the emitted constraints, with `digest` reading as `dv`
and the inputs as themselves, the sponge after the absorbs reads as
`absorb p init (frTranscript digestBefore dv ft(ζω) pub evals)`; with `x₁` its first squeeze
and `x₂` the second, the outputs `ξ`, `r` satisfy `x₁ = ξ + 2¹²⁸·h₁` and `x₂ = r + 2¹²⁸·h₂`
for some `h₁, h₂ < 2¹²⁸`, with `r < 2¹²⁸` and, where the low bits are constrained,
`ξ < 2¹²⁸`. -/
theorem squeezeXiR_spec [ToNat F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (digestBefore : FVar F) (digest : CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
    (dv : F) (hd : ⦃⌜True⌝⦄ digest ⦃⇓ d _ => ⌜d.val V = dv⌝⦄)
    (ftEval1 : FVar F) (pub : PointEvaluations (FVar F)) (evals : ProofEvaluations (FVar F))
    (endo : FVar F) (xiConstrainLowBits : Bool) :
    ⦃⌜True⌝⦄
    squeezeXiR (c := Builder V (KimchiConstraint F)) p digestBefore digest ftEval1 pub evals
      endo xiConstrainLowBits
    ⦃⇓ out _ => ⌜
      let s := Poseidon.absorb p Poseidon.init
        (frTranscript (digestBefore.val V) dv (ftEval1.val V)
          (pub.map fun x => #v[x.val V]) (evals.map fun x => #v[x.val V]))
      let (x₁, s₁) := Poseidon.squeeze p s
      let x₂ := (Poseidon.squeeze p s₁).1
      ∃ h₁ h₂ : ℕ, h₁ < 2 ^ 128 ∧ h₂ < 2 ^ 128 ∧
        x₁ = out.1.val.val V + 2 ^ 128 * h₁ ∧ x₂ = out.2.val.val V + 2 ^ 128 * h₂ ∧
        (xiConstrainLowBits = true → ∃ n : ℕ, n < 2 ^ 128 ∧ out.1.val.val V = n) ∧
        (∃ n : ℕ, n < 2 ^ 128 ∧ out.2.val.val V = n)⌝⦄ := by
  simp only [squeezeXiR]
  have h0 := SpongeVar.absorb_spec (V := V) p hsize SpongeVar.init digestBefore
  have ha := fun sv d => absorbList_spec (V := V) p hsize sv (frTail d ftEval1 pub evals)
  have hsq := fun sv => SpongeVar.squeeze_spec (V := V) p hsize sv
  have hlo := fun b x => lowest128Bits'_spec (V := V) h2 h3 b endo x
  mvcgen [h0, hd, ha, hsq, hlo]
  rename_i _ _ _ hA _ _ hdv svB _ hB _ _ hsq1 _ _ hlo1 _ _ hsq2 _ _ hlo2
  have hS : SpongeVar.ReadsAt V svB (Poseidon.absorb p Poseidon.init
      (frTranscript (digestBefore.val V) dv (ftEval1.val V)
        (pub.map fun x => #v[x.val V]) (evals.map fun x => #v[x.val V]))) := by
    have h := hB _ (hA _ readsAt_init)
    rw [← hdv, ← map_val_frTail, List.map_cons, Poseidon.absorb, List.foldl_cons]
    rw [Poseidon.absorb] at h
    exact h
  obtain ⟨hx1, hs1⟩ := hsq1 _ hS
  obtain ⟨hx2, -⟩ := hsq2 _ hs1
  obtain ⟨hiv₁, he₁, ⟨n₁, hn₁, rfl⟩, hb₁⟩ := hlo1
  obtain ⟨hiv₂, he₂, ⟨n₂, hn₂, rfl⟩, hr₂⟩ := hlo2
  refine ⟨n₁, n₂, hn₁, hn₂, ?_, ?_, hb₁, hr₂⟩
  · rw [← hx1, he₁]
  · rw [← hx2, he₂]

end Pickles
