import Bulletproof.Forking.Deployed
import Bulletproof.Forking.Prover

/-!
# The honest machine at the node domain — the first anti-vacuity companion

`Forking/Deployed.lean`'s `deployedExtract_failure_measure_le` bounds the measure of

```
{ O | wireWins σ claim O (A.run O) ∧ deployedExtract … O coins = none }
```

An extractor that always answers `none` satisfies that bound whenever the win event is *empty*.
The bound is therefore worth nothing until the win event is shown to be reachable, and reachable
**by an honest party**: an adversary holding a genuine opening witness must convince the deployed
wire verifier, on *every* table, within the `σ.k + 1` query budget the error term charges for.
That is this module's endpoint (`honestNode_wins_everywhere`, and its wire form
`honestNode_wireWins_everywhere`), and by the project's phase-P1 gate it lands before any work on
the measure bound itself.

## Why the abstract companion does not transport

`Forking/Game.lean` proves the abstract analogue `honest_wins_everywhere`, but over its *own*
prefix type `HonestPrefix Pre (k+1) = Σ j : Fin (k+1), Fin j → Pre` and with output type
`Fin (k+1) → Pre` — the answer vector. Neither choice survives here, where the prefixes are
`nodes cip` (structured `IpaNode`s) and the output must be a wire `Ipa.Proof C σ.k`, because
`wireWins` runs the executable verifier on it. So the machine is rebuilt.

Worse, every ingredient of that proof is `private` in the frozen `Game.lean`: the `commitGen`
bilinearity block and the fold identity, the honest strategy and its acceptance invariant, the
query machine with its run and budget lemmas, and the two prefix-determination congruences. What
*is* public and reusable is `Forking/Prover.lean`: `KimchiProver` with `lrAt`, `leafAt`,
`proofAt`, the folded acceptance `kimchiProverAccept` together with
`kimchiProverAccept_iff_verifierAcceptsAt`. This module therefore rebuilds the private half on
top of the public half. Nothing is re-*invented*: every statement below is the node-domain
counterpart of a statement that already exists somewhere in the frozen tree.

## The one genuinely new argument

`honestNodeAdv_prefixes`: at the node domain the query points are the nodes of the machine's
*own output*, so the construction is a fixed point. It resolves because `lrAt_congr` says round
`l`'s cross-terms read only challenges strictly below `l`, and the round-`j` accumulator holds
exactly the answers below `j ≥ l`; and `leafAt_congr` says `(δ, sg)` read only the round
challenges, never the Schnorr one.

One structural simplification the node design buys, and which should not be missed: the abstract
companion had to produce a `DecodesFromPrefixes` witness as part of its existential, because
there the prefix map is chosen along with the adversary. Here `nodes cip` is fixed in advance and
`decodesFromPrefixes_nodes` already holds for *every* proof, unconditionally. The honest machine
therefore owes no ordering obligation at all — it only has to make its query points be the nodes
of its own output.

## What this module deliberately does not do

* It does not claim the honest machine is the *only* winner, nor that the win event has measure
  `1` for a claim without an opening — both would be false. It establishes reachability of the
  win event, which is all anti-vacuity needs.
* It does not re-derive `kimchiProverAccept`, `proofAt`, or the folded/flat equivalence. Those
  are public in `Forking/Prover.lean` and are used, not copied. Only the declarations that are
  `private` in the frozen `Game.lean` are restated.
-/

namespace Bulletproof.Ipa.Forking

open Bulletproof Bulletproof.Forking

/-! ## The fold algebra, restated

The five lemmas of this section are verbatim restatements of `private` declarations of
`Forking/Game.lean` (themselves restatements of `private` declarations of the frozen
`Forking/Triviality.lean`). Each is a two- or three-line computation; they are listed
individually so the dependency graph is honest about what the honest strategy rests on. -/

section FoldAlgebra

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Additivity of `commitGen` in the generators. -/
theorem commitGen_add_gen {n : ℕ} (g g' : Fin n → G) (a : Fin n → F) :
    commitGen (g + g') a = commitGen g a + commitGen g' a := by
  simp only [commitGen, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- `commitGen` pulls a scalar out of the generators. -/
theorem commitGen_smul_gen {n : ℕ} (s : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen (s • g) a = s • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (a i) s (g i)

/-- Additivity of `commitGen` in the coefficients. -/
theorem commitGen_add_coeff {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a + a') = commitGen g a + commitGen g a' := by
  simp only [commitGen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- `commitGen` pulls a scalar out of the coefficients. -/
theorem commitGen_smul_coeff {n : ℕ} (s : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen g (s • a) = s • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- A length-`2^{d+1}` commitment splits over the two halves. -/
theorem commitGen_split {d : ℕ} (g : Fin (2 ^ (d + 1)) → G) (a : Fin (2 ^ (d + 1)) → F) :
    commitGen g a = commitGen (loHalf g) (loHalf a) + commitGen (hiHalf g) (hiHalf a) := by
  have e : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by rw [pow_succ]; ring
  let φ : Fin (2 ^ d) ⊕ Fin (2 ^ d) ≃ Fin (2 ^ (d + 1)) := finSumFinEquiv.trans (finCongr e)
  simp only [commitGen]
  rw [← φ.sum_comp (fun j => a j • g j), Fintype.sum_sum_type]
  congr 1

/-- **One-round fold identity.** Committing the honest sub-witness `loHalf a + u⁻¹ • hiHalf a`
against the folded generators `foldHalves g u` recovers the parent commitment plus the two
blinded cross-terms. Stated over the section's module `G`; it is used at `G` (the generator
commitment) *and* at `F` (the inner product). -/
theorem commitGen_fold_identity {d : ℕ}
    (g : Fin (2 ^ (d + 1)) → G) (a : Fin (2 ^ (d + 1)) → F) (u : F) (hu : u ≠ 0) :
    commitGen (foldHalves g u) (loHalf a + u⁻¹ • hiHalf a) =
      commitGen g a + u⁻¹ • commitGen (loHalf g) (hiHalf a)
        + u • commitGen (hiHalf g) (loHalf a) := by
  rw [commitGen_split g a]
  simp only [foldHalves, commitGen_add_gen, commitGen_smul_gen, commitGen_add_coeff,
    commitGen_smul_coeff, smul_add, smul_smul, inv_mul_cancel₀ hu, one_smul]
  abel

/-- `commitGen` over a singleton index family. -/
theorem commitGen_one (g : Fin (2 ^ 0) → G) (a : Fin (2 ^ 0) → F) :
    commitGen g a = a 0 • g 0 :=
  Fin.sum_univ_one fun i => a i • g i

end FoldAlgebra

/-! ## The honest strategy and its acceptance -/

section HonestStrategy

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- **The honest prover strategy from an opening witness.** At each round it commits to the
cross-terms `L = ⟨a_hi, g_lo⟩ + ⟨a_hi, b_lo⟩ • U` and `R = ⟨a_lo, g_hi⟩ + ⟨a_lo, b_hi⟩ • U` — the
`U` components are mandatory, they absorb the inner-product cross terms while the claimed value
`v` stays fixed — and continues on the folded data. The Schnorr layer is taken with zero
blinding: `δ = 0`, `z1 = c · a₀`, `z2 = c · ρ`. -/
def honestProver (U : G) (ρ : F) :
    {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → (Fin (2 ^ d) → F) → KimchiProver F G d
  | 0, g, _, a => .leaf (g 0) 0 (fun c => (c * a 0, c * ρ))
  | _ + 1, g, bb, a =>
      .node (commitGen (loHalf g) (hiHalf a) + commitGen (loHalf bb) (hiHalf a) • U)
        (commitGen (hiHalf g) (loHalf a) + commitGen (hiHalf bb) (loHalf a) • U)
        (fun u => honestProver U ρ (foldHalves g u) (foldHalves bb u)
          (loHalf a + u⁻¹ • hiHalf a))

/-- **The honest fold invariant.** If the running commitment `P` satisfies
`P + v • U = ⟨a, g⟩ + ⟨a, b⟩ • U + ρ • H`, then the honest strategy is accepted along *every*
challenge vector whose round challenges are nonzero. Note `v` is fixed while `⟨a, b⟩` folds —
that is exactly what the `U` components of `L` and `R` pay for. -/
theorem honestProver_accept (U H : G) (ρ v : F) :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (bb : Fin (2 ^ d) → F) → (a : Fin (2 ^ d) → F) →
      (P : G) → (χ : Fin (d + 1) → F) → (∀ i : Fin d, χ i.castSucc ≠ 0) →
      P + v • U = commitGen g a + commitGen bb a • U + ρ • H →
      kimchiProverAccept (honestProver U ρ g bb a) g bb U H v P χ
  | 0, g, bb, a, P, χ, _, hinv => by
      refine ⟨rfl, ?_⟩
      rw [commitGen_one g a, commitGen_one bb a, smul_eq_mul] at hinv
      show χ 0 • (P + v • U) + (0 : G) = _
      rw [hinv]
      module
  | d + 1, g, bb, a, P, χ, hne, hinv => by
      have hu : χ 0 ≠ 0 := by
        have := hne 0
        rwa [show ((0 : Fin (d + 1)).castSucc) = (0 : Fin (d + 2)) from rfl] at this
      show kimchiProverAccept (honestProver U ρ (foldHalves g (χ 0)) (foldHalves bb (χ 0))
        (loHalf a + (χ 0)⁻¹ • hiHalf a)) _ _ U H v _ (Fin.tail χ)
      refine honestProver_accept U H ρ v _ _ _ _ (Fin.tail χ) (fun i => ?_) ?_
      · have := hne i.succ
        rwa [show (Fin.tail χ) i.castSucc = χ i.succ.castSucc from by
          simp only [Fin.tail, Fin.succ_castSucc]]
      · rw [commitGen_fold_identity g a (χ 0) hu, commitGen_fold_identity bb a (χ 0) hu]
        rw [show P + (χ 0)⁻¹ • (commitGen (loHalf g) (hiHalf a)
                + commitGen (loHalf bb) (hiHalf a) • U)
              + (χ 0) • (commitGen (hiHalf g) (loHalf a)
                + commitGen (hiHalf bb) (loHalf a) • U) + v • U
            = (P + v • U) + (χ 0)⁻¹ • (commitGen (loHalf g) (hiHalf a)
                + commitGen (loHalf bb) (hiHalf a) • U)
              + (χ 0) • (commitGen (hiHalf g) (loHalf a)
                + commitGen (hiHalf bb) (loHalf a) • U) from by abel]
        rw [hinv]
        module

/-! ### The honest proof is prefix-determined

The two congruences that make the node-domain fixed point available: `lrAt` at round `j` reads
only the challenges strictly before round `j`, and the leaf's `(sg, δ)` read only the round
challenges — never the Schnorr challenge. -/

omit [Field F] [AddCommGroup G] [Module F G] in
/-- Round `j`'s cross-terms depend only on the challenges strictly before round `j`. -/
theorem lrAt_congr :
    {d : ℕ} → (pr : KimchiProver F G d) → (χ χ' : Fin (d + 1) → F) → (j : Fin d) →
      (∀ i : Fin d, (i : ℕ) < (j : ℕ) → χ i.castSucc = χ' i.castSucc) →
      pr.lrAt χ j = pr.lrAt χ' j
  | 0, _, _, _, j, _ => j.elim0
  | _ + 1, .node L R cont, χ, χ', j, h => by
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
      · simp only [KimchiProver.lrAt, Fin.cons_zero]
      · have h0 : χ 0 = χ' 0 := by
          have := h 0 (by simp)
          simpa using this
        simp only [KimchiProver.lrAt, Fin.cons_succ, h0]
        refine lrAt_congr (cont (χ' 0)) (Fin.tail χ) (Fin.tail χ') i (fun i' hi' => ?_)
        have := h i'.succ (by simpa using hi')
        simpa only [Fin.tail, Fin.succ_castSucc] using this

omit [Field F] [AddCommGroup G] [Module F G] in
/-- The leaf's `(sg, δ)` depend only on the round challenges — never on the Schnorr challenge,
which is what commit-then-challenge asks of the honest prover. -/
theorem leafAt_congr :
    {d : ℕ} → (pr : KimchiProver F G d) → (χ χ' : Fin (d + 1) → F) →
      (∀ i : Fin d, χ i.castSucc = χ' i.castSucc) →
      ((pr.leafAt χ).1, (pr.leafAt χ).2.1) = ((pr.leafAt χ').1, (pr.leafAt χ').2.1)
  | 0, .leaf _ _ _, _, _, _ => rfl
  | _ + 1, .node _ _ cont, χ, χ', h => by
      have h0 : χ 0 = χ' 0 := by simpa using h 0
      simp only [KimchiProver.leafAt, h0]
      refine leafAt_congr (cont (χ' 0)) (Fin.tail χ) (Fin.tail χ') (fun i => ?_)
      have := h i.succ
      simpa only [Fin.tail, Fin.succ_castSucc] using this

end HonestStrategy

/-! ## Padding a partial challenge vector -/

/-- Pad a partial challenge vector out to full length by zeros. Only the entries below `m` are
ever consulted (by `lrAt_congr` / `leafAt_congr`), so the filler is immaterial; using `0` avoids
needing an inhabitant of the prechallenge type. -/
def padChal {F : Type*} [Zero F] {m N : ℕ} (w : Fin m → F) : Fin N → F :=
  fun i => if h : (i : ℕ) < m then w ⟨i, h⟩ else 0

/-- Padding a full-length vector is the identity. -/
@[simp] theorem padChal_self {F : Type*} [Zero F] {N : ℕ} (w : Fin N → F) :
    padChal (N := N) w = w := by
  funext i
  simp only [padChal, dif_pos i.isLt, Fin.eta]

/-- Reading a padded vector below the pad length. -/
theorem padChal_apply_of_lt {F : Type*} [Zero F] {m N : ℕ} (w : Fin m → F) (i : Fin N)
    (h : (i : ℕ) < m) : padChal (N := N) w i = w ⟨i, h⟩ := dif_pos h

/-! ## Mapping the result of an oracle computation

`OracleComp` is a free structure with no `Functor` instance in the frozen tree; the honest
machine collects prechallenges but must return a wire proof, so the two-line post-composition is
supplied here together with its `run` and `QueryBound` laws. The *query points* are untouched,
which is what makes the fixed-point lemma below apply to the mapped machine. -/

section MapComp

variable {T Pre α β : Type*}

/-- Post-compose a function onto the result of an oracle computation. -/
def mapComp (f : α → β) : Zcash.Snark.OracleComp T Pre α → Zcash.Snark.OracleComp T Pre β
  | .pure a => .pure (f a)
  | .query t g => .query t fun q => mapComp f (g q)

/-- Running a mapped computation is the map of the run: the query tree, hence the answers, are
untouched. -/
@[simp] theorem mapComp_run (f : α → β) (A : Zcash.Snark.OracleComp T Pre α) (O : T → Pre) :
    (mapComp f A).run O = f (A.run O) := by
  induction A with
  | pure a => rfl
  | query t g ih => simpa [mapComp, Zcash.Snark.OracleComp.run] using ih (O t)

/-- Mapping the result preserves the query budget: the query tree is unchanged. -/
theorem mapComp_queryBound (f : α → β) {A : Zcash.Snark.OracleComp T Pre α} {Q : ℕ}
    (h : A.QueryBound Q) : (mapComp f A).QueryBound Q := by
  induction h with
  | pure a Q => exact .pure _ _
  | query _ ih => exact .query fun q => ih q

end MapComp

/-! ## The wire view of an abstract proof -/

variable {C : Ipa.CommitmentCurve} {k m p : ℕ}

/-- The abstract `OpeningProof` packed back onto the wire: the `Fin k`-indexed `lr` becomes a
`Vector`, everything else transfers unchanged. It is a section of `toOpening`. -/
def wireProofOf (ω : OpeningProof C.ScalarField C.Point k) : Ipa.Proof C k where
  lr := Vector.ofFn ω.lr
  delta := ω.delta
  z1 := ω.z1
  z2 := ω.z2
  sg := ω.sg

/-- `wireProofOf` is a section of `toOpening`. -/
@[simp] theorem toOpening_wireProofOf (ω : OpeningProof C.ScalarField C.Point k) :
    toOpening (wireProofOf ω) = ω := by
  cases ω
  simp only [toOpening, wireProofOf, OpeningProof.mk.injEq, and_true]
  funext j
  simp

/-- The `lr` entries of a wire-packed proof. -/
@[simp] theorem wireProofOf_lr_getElem (ω : OpeningProof C.ScalarField C.Point k) (j : Fin k) :
    (wireProofOf ω).lr[j] = ω.lr j := by
  simp [wireProofOf]

/-! ## The honest machine over the node domain -/

section Machine

/-- **The honest query point.** With `j` answers already read (`acc`), the machine's next query
is the round-`j` node of the proof it is in the middle of building: at `j < k` a `nodeU`-shaped
record carrying the cross-terms of rounds `0, …, j`, and at `j = k` the `nodeC`-shaped record
carrying every cross-term together with `δ` and `sg`.

This is well-defined — i.e. `acc` really does contain everything needed — for exactly the reason
of `lrAt_congr`: entry `l ≤ j` of `lr` consults only challenges strictly below `l ≤ j`, all of
which are in `acc`; and the leaf data consult only the `k` round challenges, all of which are in
`acc` at the last step. -/
def honestNode (cip : C.ScalarField) (pr : KimchiProver C.ScalarField C.Point k)
    {j : ℕ} (hj : j < k + 1) (acc : Fin j → Prechallenge) : IpaNode C k :=
  if j < k then
    { idx := ⟨j, hj⟩
      cip := cip
      lr := fun l => if (l : ℕ) ≤ j then
          some (pr.lrAt (padChal fun i => expandPre C (acc i)) l) else none
      delta := none
      sg := none }
  else
    { idx := ⟨j, hj⟩
      cip := cip
      lr := fun l => some (pr.lrAt (padChal fun i => expandPre C (acc i)) l)
      delta := some (pr.leafAt (padChal fun i => expandPre C (acc i))).2.1
      sg := some (pr.leafAt (padChal fun i => expandPre C (acc i))).1 }

/-- The round-`i` query point of a *completed* answer vector: the honest node built from the
answers strictly before `i`. This is the node-domain counterpart of `Game.lean`'s
`honestPrefixes`. -/
def honestPrefixNode (cip : C.ScalarField) (pr : KimchiProver C.ScalarField C.Point k)
    (q : Fin (k + 1) → Prechallenge) (i : Fin (k + 1)) : IpaNode C k :=
  honestNode cip pr i.isLt (fun l => q (l.castLE i.isLt.le))

/-- The honest machine's query stage, with `j` answers already collected and `m` rounds still to
read: query at the honest node for the answers so far, then continue; when nothing is left,
return the answer vector. -/
def honestNodeAdvAux (cip : C.ScalarField) (pr : KimchiProver C.ScalarField C.Point k) :
    (mm j : ℕ) → j + mm = k + 1 → (Fin j → Prechallenge) →
      Zcash.Snark.OracleComp (IpaNode C k) Prechallenge (Fin (k + 1) → Prechallenge)
  | 0, _, h, acc => .pure fun i => acc (Fin.cast (by omega) i)
  | mm + 1, j, h, acc =>
      .query (honestNode cip pr (show j < k + 1 by omega) acc)
        fun q => honestNodeAdvAux cip pr mm (j + 1) (by omega) (Fin.snoc acc q)

/-- **The honest machine**: `k + 1` nested queries at its own nodes over a final `pure`,
returning the wire proof the honest strategy assembles along the challenges it read. -/
def honestNodeAdv (cip : C.ScalarField) (pr : KimchiProver C.ScalarField C.Point k) :
    Zcash.Snark.OracleComp (IpaNode C k) Prechallenge (Ipa.Proof C k) :=
  mapComp (fun q => wireProofOf (pr.proofAt fun i => expandPre C (q i)))
    (honestNodeAdvAux cip pr (k + 1) 0 (by omega) Fin.elim0)

/-- The query stage makes exactly `mm` queries on every path. -/
theorem honestNodeAdvAux_queryBound (cip : C.ScalarField)
    (pr : KimchiProver C.ScalarField C.Point k) :
    ∀ (mm j : ℕ) (h : j + mm = k + 1) (acc : Fin j → Prechallenge),
      (honestNodeAdvAux cip pr mm j h acc).QueryBound mm := by
  intro mm
  induction mm with
  | zero => intro j h acc; exact .pure _ _
  | succ mm ih =>
      intro j h acc
      exact .query fun q => ih (j + 1) (by omega) (Fin.snoc acc q)

/-- **The honest machine stays within budget** `k + 1`. -/
theorem honestNodeAdv_queryBound (cip : C.ScalarField)
    (pr : KimchiProver C.ScalarField C.Point k) :
    (honestNodeAdv cip pr).QueryBound (k + 1) :=
  mapComp_queryBound _ (honestNodeAdvAux_queryBound cip pr (k + 1) 0 (by omega) Fin.elim0)

/-- **The run of the honest machine.** The accumulated answers survive the remaining run, and
every not-yet-read entry of the output vector is the table's value at exactly the honest node
built from the run's own earlier entries. -/
theorem honestNodeAdvAux_run (cip : C.ScalarField) (pr : KimchiProver C.ScalarField C.Point k)
    (O : IpaNode C k → Prechallenge) :
    ∀ (mm j : ℕ) (h : j + mm = k + 1) (acc : Fin j → Prechallenge),
      (∀ (i : Fin (k + 1)) (hi : (i : ℕ) < j),
          (honestNodeAdvAux cip pr mm j h acc).run O i = acc ⟨i, hi⟩) ∧
        (∀ i : Fin (k + 1), j ≤ (i : ℕ) →
          (honestNodeAdvAux cip pr mm j h acc).run O i
            = O (honestPrefixNode cip pr ((honestNodeAdvAux cip pr mm j h acc).run O) i)) := by
  intro mm
  induction mm with
  | zero =>
      intro j h acc
      refine ⟨fun i hi => rfl, fun i hi => ?_⟩
      exact absurd i.isLt (by omega)
  | succ mm ih =>
      intro j h acc
      have hj : j + 1 + mm = k + 1 := by omega
      have hjN : j < k + 1 := by omega
      set t : IpaNode C k := honestNode cip pr hjN acc with ht
      have hrun : (honestNodeAdvAux cip pr (mm + 1) j h acc).run O
          = (honestNodeAdvAux cip pr mm (j + 1) hj (Fin.snoc acc (O t))).run O := rfl
      obtain ⟨A, B⟩ := ih (j + 1) hj (Fin.snoc acc (O t))
      have hlo : ∀ (i : Fin (k + 1)) (hi : (i : ℕ) < j),
          (honestNodeAdvAux cip pr (mm + 1) j h acc).run O i = acc ⟨i, hi⟩ := by
        intro i hi
        rw [hrun, A i (by omega)]
        rw [show (⟨(i : ℕ), Nat.lt_succ_of_lt hi⟩ : Fin (j + 1))
            = Fin.castSucc ⟨(i : ℕ), hi⟩ from rfl, Fin.snoc_castSucc]
      refine ⟨hlo, fun i hi => ?_⟩
      rcases eq_or_lt_of_le hi with heq | hlt
      · -- the current round: the answer is read exactly at `t`, and `t` is the prefix node
        have hij : i = ⟨j, hjN⟩ := Fin.ext heq.symm
        subst hij
        have hL : (honestNodeAdvAux cip pr (mm + 1) j h acc).run O ⟨j, hjN⟩ = O t := by
          rw [hrun, A ⟨j, hjN⟩ (Nat.lt_succ_self j)]
          rw [show (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) = Fin.last j from rfl, Fin.snoc_last]
        have hR : honestPrefixNode cip pr
            ((honestNodeAdvAux cip pr (mm + 1) j h acc).run O) (⟨j, hjN⟩ : Fin (k + 1)) = t := by
          rw [ht, honestPrefixNode]
          exact congrArg (honestNode cip pr hjN) (funext fun l => hlo _ (by simp))
        rw [hL, hR]
      · rw [hrun]
        exact B i (by omega)

/-- **The run reads each answer at its own node.** The `i`-th answer the honest machine collects
is the table's value at the honest node built from the answers strictly before `i`. -/
theorem honestNodeAdv_run (cip : C.ScalarField)
    (pr : KimchiProver C.ScalarField C.Point k) (O : IpaNode C k → Prechallenge)
    (i : Fin (k + 1)) :
    (honestNodeAdvAux cip pr (k + 1) 0 (by omega) Fin.elim0).run O i
      = O (honestPrefixNode cip pr
          ((honestNodeAdvAux cip pr (k + 1) 0 (by omega) Fin.elim0).run O) i) :=
  (honestNodeAdvAux_run cip pr O (k + 1) 0 (by omega) Fin.elim0).2 i (Nat.zero_le _)

/-! ### The fixed point: the query points are the nodes of the output

This is the one genuinely new argument of the module, and it is where `lrAt_congr` /
`leafAt_congr` are spent. -/

/-- **The query points are the nodes of the output.** The honest node built from the first `i`
answers of `q` is exactly the `i`-th deployed prefix of the proof the honest strategy assembles
along the *full* challenge vector of `q`. -/
theorem honestPrefixNode_eq_nodes (cip : C.ScalarField)
    (pr : KimchiProver C.ScalarField C.Point k) (q : Fin (k + 1) → Prechallenge)
    (i : Fin (k + 1)) :
    honestPrefixNode cip pr q i
      = nodes cip (wireProofOf (pr.proofAt fun l => expandPre C (q l))) i := by
  set χ : Fin (k + 1) → C.ScalarField := fun l => expandPre C (q l) with hχ
  set ψ : Fin (k + 1) → C.ScalarField :=
    padChal (fun l : Fin (i : ℕ) => expandPre C (q (l.castLE i.isLt.le))) with hψ
  -- the padded partial vector agrees with the full one at every round index below `i`
  have hagree : ∀ i' : Fin k, (i' : ℕ) < (i : ℕ) → ψ i'.castSucc = χ i'.castSucc := by
    intro i' hi'
    have hlt : ((i'.castSucc : Fin (k + 1)) : ℕ) < (i : ℕ) := by simpa using hi'
    rw [hψ, padChal_apply_of_lt _ _ hlt, hχ]
    exact congrArg (expandPre C) (congrArg q (Fin.ext (by simp)))
  -- the wire-packed honest proof reads its components off `lrAt` / `leafAt` at `χ`
  have hlrπ : ∀ l : Fin k,
      (wireProofOf (pr.proofAt χ) : Ipa.Proof C k).lr[l] = pr.lrAt χ l := by
    intro l
    rw [wireProofOf_lr_getElem]
    rfl
  have hdeltaπ : (wireProofOf (pr.proofAt χ) : Ipa.Proof C k).delta = (pr.leafAt χ).2.1 := rfl
  have hsgπ : (wireProofOf (pr.proofAt χ) : Ipa.Proof C k).sg = (pr.leafAt χ).1 := rfl
  rw [honestPrefixNode, honestNode, nodes_eq]
  by_cases h : (i : ℕ) < k
  · rw [dif_pos h, if_pos h]
    refine IpaNode.ext ?_ rfl ?_ rfl rfl
    · rfl
    · funext l
      simp only [nodeU]
      by_cases hl : (l : ℕ) ≤ (i : ℕ)
      · rw [if_pos hl, if_pos (show (l : ℕ) ≤ ((⟨(i : ℕ), h⟩ : Fin k) : ℕ) from hl), hlrπ]
        exact congrArg some (lrAt_congr pr _ _ l fun i' hi' => hagree i' (by omega))
      · rw [if_neg hl, if_neg (show ¬ (l : ℕ) ≤ ((⟨(i : ℕ), h⟩ : Fin k) : ℕ) from hl)]
  · rw [dif_neg h, if_neg h]
    have hik : (i : ℕ) = k := le_antisymm (Nat.lt_succ_iff.mp i.isLt) (Nat.not_lt.mp h)
    have hlast : ∀ i' : Fin k, ψ i'.castSucc = χ i'.castSucc :=
      fun i' => hagree i' (by omega)
    have hleaf := leafAt_congr pr ψ χ hlast
    refine IpaNode.ext ?_ rfl ?_ ?_ ?_
    · exact Fin.ext (by simpa [nodeC] using hik)
    · funext l
      simp only [nodeC]
      rw [hlrπ]
      exact congrArg some (lrAt_congr pr _ _ l fun i' _ => hlast i')
    · simp only [nodeC]
      rw [hdeltaπ]
      exact congrArg some (Prod.ext_iff.mp hleaf).2
    · simp only [nodeC]
      rw [hsgπ]
      exact congrArg some (Prod.ext_iff.mp hleaf).1

/-- **The honest run reads its challenges at its own output's nodes.** Combining the run analysis
with the fixed point: the answer at the `i`-th deployed prefix of the machine's output is exactly
the `i`-th entry of the vector the machine collected. -/
theorem honestNodeAdv_prefixes (cip : C.ScalarField)
    (pr : KimchiProver C.ScalarField C.Point k) (O : IpaNode C k → Prechallenge)
    (i : Fin (k + 1)) :
    O (nodes cip ((honestNodeAdv cip pr).run O) i)
      = (honestNodeAdvAux cip pr (k + 1) 0 (by omega) Fin.elim0).run O i := by
  have h := honestNodeAdv_run cip pr O i
  rw [honestNodeAdv, mapComp_run]
  rw [← honestPrefixNode_eq_nodes cip pr _ i]
  exact h.symm

end Machine

/-! ## The companion -/

section Companion

variable [Module C.ScalarField C.Point]

/-- **The honest prover wins on every table.** From a genuine opening witness there is an oracle
machine over the deployed node domain, within budget `σ.k + 1`, whose output satisfies `Wins` for
*every* table. So the win set can have measure `1`, and an extractor that always returns `none`
cannot satisfy the deployed bound.

This is `Game.lean`'s `honest_wins_everywhere` transported from its own prefix type
`HonestPrefix Pre (k+1)` to `IpaNode C k`: the honest machine is the same `k + 1` nested queries
over a final `pure`, but its query points are now nodes of its own proof rather than abstract
answer-history prefixes, and its output is a wire proof rather than the answer vector. The
reindexing is legitimate because round `j`'s output depends only on challenges strictly before
`j` — `lrAt_congr` / `leafAt_congr`, restated above because they are `private` in the frozen
`Game.lean`. Nonzeroness of the round challenges is `expandPre_{vesta,pallas}_ne_zero`, which
holds for every prechallenge without any hypothesis. -/
theorem honestNode_wins_everywhere (hne : ∀ q, expandPre C q ≠ 0)
    (σ : SRS C.Point) (cip : C.ScalarField)
    (b : Fin (2 ^ σ.k) → C.ScalarField) (v : C.ScalarField) (P : C.Point)
    (a : Fin (2 ^ σ.k) → C.ScalarField) (ρ : C.ScalarField)
    (hopen : openingRelationB { σ with U := uBaseOf C cip } P b v a ρ) :
    ∃ A : Zcash.Snark.OracleComp (IpaNode C σ.k) Prechallenge (Ipa.Proof C σ.k),
      A.QueryBound (σ.k + 1) ∧
        ∀ O : IpaNode C σ.k → Prechallenge,
          Wins { σ with U := uBaseOf C cip } b v P (expandPre C) toOpening (nodes cip) O
            (A.run O) := by
  obtain ⟨hP1, hv1⟩ := hopen
  set U : C.Point := uBaseOf C cip with hU
  set pr : KimchiProver C.ScalarField C.Point σ.k := honestProver U ρ σ.g b a with hpr
  have hcb : commitGen b a = v := by
    rw [hv1]
    simp only [commitGen, innerProduct, smul_eq_mul]
  have hinv : P + v • U = commitGen σ.g a + commitGen b a • U + ρ • σ.h := by
    rw [hcb, ← hP1]
    show commitGen σ.g a + ρ • σ.h + v • U = _
    abel
  refine ⟨honestNodeAdv cip pr, honestNodeAdv_queryBound cip pr, ?_⟩
  intro O
  set π : Ipa.Proof C σ.k := (honestNodeAdv cip pr).run O with hπ
  set q : Fin (σ.k + 1) → Prechallenge :=
    (honestNodeAdvAux cip pr (σ.k + 1) 0 (by omega) Fin.elim0).run O with hq
  set χ : Fin (σ.k + 1) → C.ScalarField := fun i => expandPre C (q i) with hχdef
  -- the challenge vector the game reads is the one the machine collected
  have hchi : oracleChallenges { σ with U := U } (expandPre C) (nodes cip) O π = χ := by
    funext i
    rw [oracleChallenges, hχdef]
    exact congrArg (expandPre C) (honestNodeAdv_prefixes cip pr O i)
  have hproof : toOpening π = pr.proofAt χ := by
    rw [hπ, honestNodeAdv, mapComp_run, toOpening_wireProofOf]
  have hsnoc : Fin.snoc (fun i : Fin σ.k => χ i.castSucc) (χ (Fin.last σ.k)) = χ :=
    Fin.snoc_init_self χ
  have hacc : kimchiProverAccept pr σ.g b U σ.h v P χ :=
    honestProver_accept U σ.h ρ v σ.g b a P χ (fun i => by rw [hχdef]; exact hne _) hinv
  have key := (kimchiProverAccept_iff_verifierAcceptsAt { σ with U := U } pr b v P
    (fun i : Fin σ.k => χ i.castSucc) (χ (Fin.last σ.k))).mp (by rw [hsnoc]; exact hacc)
  rw [hsnoc] at key
  show VerifierAcceptsAt { σ with U := U } (toOpening π) P
    (innerProduct (bPolyCoefficients fun i : Fin σ.k =>
      oracleChallenges { σ with U := U } (expandPre C) (nodes cip) O π i.castSucc) b) v
    (oracleChallenges { σ with U := U } (expandPre C) (nodes cip) O π (Fin.last σ.k))
    (fun i : Fin σ.k =>
      oracleChallenges { σ with U := U } (expandPre C) (nodes cip) O π i.castSucc)
  rw [hchi, hproof]
  exact key

/-- **The honest prover wins on the wire, on every table.** The same machine, measured by the
`Bool` the deployed wire verifier actually returns — which is the form
`deployedExtract_failure_measure_le`'s win event is stated in.

This is `honestNode_wins_everywhere` followed by the *backward* direction of
`wireWins_iff_wins` at each table; it is the entire reason that bridge is stated as an
equivalence. Consequently the event measured by the deployed bound is not vacuous: for a claim
with a genuine opening its win component has measure `1`, so an extractor that always answers
`none` violates the bound as soon as `(Q + σ.k + 1) · 3 / 2 ^ 128 < 1`. -/
theorem honestNode_wireWins_everywhere
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    (σ : SRS C.Point) (claim : Ipa.Input C σ.k m p)
    (a : Fin (2 ^ σ.k) → C.ScalarField) (ρ : C.ScalarField)
    (hopen : openingRelationB { σ with U := uBaseOf C (Ipa.cipOf claim) }
      (combinedCommitment claim.polyscale claim.commitmentFn)
      (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn)
      (Ipa.cipOf claim) a ρ) :
    ∃ A : Zcash.Snark.OracleComp (IpaNode C σ.k) Prechallenge (Ipa.Proof C σ.k),
      A.QueryBound (σ.k + 1) ∧
        ∀ O : IpaNode C σ.k → Prechallenge, wireWins σ claim O (A.run O) := by
  obtain ⟨A, hQ, hW⟩ := honestNode_wins_everywhere hne σ (Ipa.cipOf claim)
    (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn) (Ipa.cipOf claim)
    (combinedCommitment claim.polyscale claim.commitmentFn) a ρ hopen
  exact ⟨A, hQ, fun O => (wireWins_iff_wins hsmul σ claim O (A.run O)).mpr (hW O)⟩

end Companion

end Bulletproof.Ipa.Forking
