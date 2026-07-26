import Bulletproof.Forking.Capstone
import Bulletproof.Forking.Prover
import Zcash.Snark.Soundness.Forking.Adversary.Recursive

/-!
# The Fiat–Shamir extraction game — the statement Stage 5b must prove

This module states the endpoint of the refoundation and nothing else: the theorem whose proof
would let `Bulletproof.poseidon_fiat_shamir_{vesta,pallas}` be deleted. Everything here is a
statement; the extractor's body and the bound are the remaining work.

## The model, and every assumption in it

* **The oracle.** Challenges come from a table `O : T → Pre` over transcript prefixes, drawn
  uniformly. Idealizing the Poseidon sponge as such a table is the *sole* trust boundary
  (decision "Option A") — it is a modelling choice stated in prose, **not** a Lean axiom, so a
  successful Stage 5b removes two kernel axioms and adds none.

* **The challenge domain is the prechallenge domain, not the field.** The deployed verifier
  squeezes a 128-bit prechallenge and endo-expands it, so the oracle's codomain is `Pre` and the
  field challenge is `expand p`. The two facts that make this transport work are hypotheses here
  and *theorems* at the deployed instantiation (`Forking/EndoChallenge.lean`): `expand` is
  injective (fork distinctness survives) and never zero (the fork's nonzero side conditions come
  free). This is why the error term below divides by `Fintype.card Pre ≈ 2¹²⁸` and not by `|F|`:
  the honest number, and the one that makes the counting satisfiable at all.

* **The claim is fixed, structurally.** `P`, `b`, `v` and the commitment's representation
  `(pg, pw)` are parameters, and the adversary outputs only an opening proof — so a rewound run
  cannot switch which claim it opens. That *is* the fixed-claim assumption (decision "D4"),
  made structural rather than carried as a `ClaimStable` hypothesis. It is a real scope limit:
  the standalone **cold** verifier does not absorb the commitments, so an adaptive adversary
  there could switch claims. Kimchi's deployed usage is the **warm** start, where the
  commitments are already in the sponge state before the IPA transcript begins; closing the gap
  for the cold verifier is out of scope, and must not be papered over by strengthening the game.

* **The prover is algebraic.** `(pg, pw)` is the AGM representation of `P`. Only the root needs
  one: ironwood's `produceDeployed` recovers the deployed tree's decorations by Vandermonde
  interpolation of the sibling recursions, so no per-node representations appear (decision
  "D7").

## Why this conclusion carries content where a `Prop` one would not

The extractor returns `Option (OpeningOrBreak …)` — a `Σ'`/`⊕'` of **data**. At the deployed
Pasta parameters a `Prop`-level `∃ opening ∨ ∃ relation` is free (proved, twice:
`Forking/Triviality.lean` and `kimchi_knowledge_soundness_conclusion_free_at_1dim`), because the
point group is a 1-dimensional `F`-vector space. Coefficients that a reduction *computes* are
not free. Correctness needs no separate theorem: it is the extractor's return type.

## The two ways this statement could be cheated, and what blocks each

Worth spelling out, because the previous two attempts at this endpoint were both satisfiable
without doing any work.

* **Always answer `none`.** Then the failure set is the whole win set, and the bound claims every
  adversary wins with probability `≤ (Q+k+1)·3/2¹²⁸`. False: an honest prover wins on *every*
  oracle table. That is `honest_wins_everywhere` below — the anti-vacuity companion, which must
  land with the theorem, not after it.

* **Accept while knowing nothing.** Not a cheat on the *extractor* but on the *game*: if the
  adversary may choose the Schnorr commitment `δ` after seeing the challenge `c`, then
  `VerifierAcceptsAt` is satisfiable with `z1 = z2 = 0` and no witness at all
  (`verifierAcceptsAt_of_deferred_delta`, proved below), so no extractor could succeed and the
  measure bound would be false. `DecodesFromPrefixes` — commit-then-challenge, ironwood's
  `hdecode` for our proof shape — is what rules it out, and it is a *hypothesis of the theorem*,
  not an informal reading of the protocol.

* **Always answer `some` with a fabricated break.** Blocked twice over. `kimchiExtract` is a
  plain `def`, not `noncomputable`, so Lean's compiler rejects a `Classical.choice`-conjured
  witness — the distinction ironwood draws as "in a prime-order group a relation *exists*; the
  security break is *computing* its coefficients". And it is stated for an arbitrary
  `[AddCommGroup G] [Module F G]`, where no relation exists to be found, so no closed form can
  satisfy the type. The same genericity blocks a fabricated opening.

Both guards are cheap to keep honest: the extractor must stay computable, must stay generic in
`G`, and should be `#eval`'d on a fixture the way `kimchiOpeningOrBreak` already is
(`scripts/check_extractor_computes.sh`).

## How to prove it: the oracle codomain is `Pre`, and that is fine

The apparent obstacle is that ironwood's fork engine uses **one** type for both the oracle's
answers and the certificate's challenges (`Recursive.lean`, `variable … [Field F]`), whereas ours
must differ: the oracle answers with prechallenges, the certificate carries field challenges. We
cannot model the oracle as returning uniform field elements — that would claim `3/|F| ≈ 2⁻²⁵⁴`
security for a challenge space of size `2¹²⁸`, i.e. a *better* bound than the truth.

The split is nonetheless cheap, because the field-locking is confined to the certificate builder:

* the **measure/escape machinery is codomain-generic** — `escapesDuringC_measure_le'`
  (`OracleComp.lean:728`) asks only `[Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]`, the
  staged-decode layer only `[Zero F]`, and `fsWins`/`PrefixDecode` no algebra at all. All of it
  applies verbatim at `Pre`;
* only `Recursive.lean`'s `AlgebraicDForkCert`/`DeployedForkValid` need a field — and we do not
  use them: we have our own `KimchiForkCert`, and `expand` is applied at node construction, where
  `_hexp_inj` supplies the three distinct field challenges and `_hexp_ne` their nonzero-ness.

So the work is a thin recursive fork over `Pre` that emits `KimchiForkCert`, with the failure
measure discharged by ironwood's escape lemmas — not a re-derivation of `Recursive.lean`.
-/

namespace Bulletproof.Forking

open Bulletproof
open scoped ENNReal

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- What the extractor computes: an opening witness for the claim, or a nontrivial discrete-log
relation over the augmented basis `(σ.g, σ.U, σ.h)` — the break, as explicit coefficients. -/
abbrev OpeningOrBreak (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F) (v : F) : Type _ :=
  (Σ' (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ)
    ⊕' Zcash.Snark.AlgebraicRelationWitness (F := F)
        (Zcash.Snark.augmentedBasis σ.g σ.U σ.h)

variable {T Pre Pf : Type*}

/-- The challenge vector a run reads from the oracle: at each round the prefix's entry, expanded
into the field. Index `σ.k` is the Schnorr challenge — the extra round kimchi's proof-of-knowledge
layer adds, which `schnorr_fork_eq` consumes two of. -/
def oracleChallenges (σ : SRS G) (expand : Pre → F) (prefixes : Pf → Fin (σ.k + 1) → T)
    (O : T → Pre) (p : Pf) : Fin (σ.k + 1) → F :=
  fun i => expand (O (prefixes p i))

/-- **The adversary wins**: the deployed wire verifier accepts its proof at the challenges the
oracle supplies. This is `VerifierAcceptsAt` itself — the executable verifier's own equations,
with the evaluation slot at the s-vector inner product (`combinedB` for a batched claim, by
`combinedB_eq_innerProduct`) — so no parallel acceptance predicate is introduced. By
`kimchiProverAccept_iff_verifierAcceptsAt` this is equally the folded form the fork machinery
consumes. -/
def Wins (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (O : T → Pre) (p : Pf) : Prop :=
  let χ := oracleChallenges σ expand prefixes O p
  let u := fun i : Fin σ.k => χ i.castSucc
  VerifierAcceptsAt σ (proofOf p) P (innerProduct (bPolyCoefficients u) b) v (χ (Fin.last σ.k)) u

/-! ## Commit-then-challenge, and why it must be a hypothesis

`Wins` alone is **not** enough to state the game, and the gap is not subtle: without tying the
proof's group elements to the prefixes at which their challenges are read, an adversary may
choose the Schnorr commitment `δ` *after* seeing the Schnorr challenge `c`, and then
`VerifierAcceptsAt` is satisfiable carrying no knowledge whatsoever.

`verifierAcceptsAt_of_deferred_delta` records that as a checkable claim rather than a warning:
with `z1 = z2 = 0` and `δ := -(c • Q)`, the Schnorr equation reads `c•Q - c•Q = 0` and the
`sg` check holds by construction — for *any* commitment, eval vector and claimed value. So an
extractor could not possibly succeed against such an adversary, and a measure bound stated
without the ordering hypothesis would be false.

This is exactly the role ironwood's `hdecode` plays
(`recursiveAlgebraicForkFrom_realizes`, `Recursive.lean:809`): the round points are *decoded from
the prefix*, so rewinding at a prefix cannot change them. `DecodesFromPrefixes` below is that
condition for our proof shape, and it is faithful to the deployed verifier — the transcript
absorbs `Lⱼ, Rⱼ` before squeezing round `j`'s challenge, and absorbs `δ` and `sg` before
squeezing `c`. -/

/-- **Acceptance without knowledge, when `δ` may depend on `c`.** The reason the ordering
hypothesis below is not optional. -/
theorem verifierAcceptsAt_of_deferred_delta (σ : SRS G) (b0 v : F) (P : G) (u : Fin σ.k → F)
    (c : F) :
    VerifierAcceptsAt σ
      ({ lr := fun _ => (0, 0), delta := -(c • recombine σ P v u (fun _ => (0, 0))),
         z1 := 0, z2 := 0, sg := commitGen σ.g (bPolyCoefficients u) } : OpeningProof F G σ.k)
      P b0 v c u := by
  refine ⟨?_, rfl⟩
  simp

/-- **Commit-then-challenge, as a hypothesis on the adversary's transcript shape.** Every group
element of the proof is a function of the prefix at which its own challenge is read: the round-`j`
cross-terms of the prefix for round `j`, and the Schnorr commitment and folded generator of the
prefix for `c`. Since the oracle's answer *at* that prefix is drawn afterwards, the adversary
cannot make them depend on the challenge — which is precisely what makes a fork meaningful. -/
structure DecodesFromPrefixes (σ : SRS G)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T) where
  /-- The round cross-terms, as read off the round's own transcript prefix. -/
  round : T → G × G
  /-- The Schnorr commitment and folded generator, as read off the final prefix. -/
  final : T → G × G
  /-- Round `j`'s `(L, R)` is determined by round `j`'s prefix. -/
  round_eq : ∀ p (j : Fin σ.k), (proofOf p).lr j = round (prefixes p j.castSucc)
  /-- `δ` and `sg` are determined by the prefix at which the Schnorr challenge is read. -/
  final_eq : ∀ p, ((proofOf p).delta, (proofOf p).sg) = final (prefixes p (Fin.last σ.k))

/-! ## The recursive fork over the prechallenge domain

The two ingredients of the extractor body, in dependency order: the fork itself
(`kimchiForkFrom` — `def:pre_fork`), and the decision procedure that turns a candidate
certificate into a *checked* one (`decideKimchiForkValid` — `lem:fork_valid_decidable`).
Deciding validity inside the extractor is what makes the extractor's return type its own
correctness statement: a `some` answer is valid by construction, and the analytic content
("`some` happens often enough") stays in the measure bound.

The freshness scan is **not** ours: it is `Zcash.Snark.nextForkChallenge`, used verbatim at the
alphabet `Pre`, which asks only `[Zero Pre]` and `[DecidableEq Pre]` — both carried by the
deployed `Fin (2 ^ 128)` (`scripts/check_ironwood_generic.lean` §1, §3). So the fork's own
adaptation of ironwood's `recursiveAlgebraicForkFrom` is a single one, and it is structural
rather than algebraic:

* **The recursion is indexed by certificate depth, with coins one level deeper.** Ironwood's
  leaf level is the win check; ours is the Schnorr fork, which keeps *two* of three branches and
  emits `KimchiForkCert.leaf`. So both cases of the recursion are `.node`, and the base case
  does real work.

Two consequences of scanning in `Pre` rather than in the field are worth naming, because they
are where `expand`'s two properties are spent. Freshness and the zero skip are tested on
prechallenges, so the certificate's *field* challenges need `expand` injective to be distinct
(`hexp_inj`, in `kimchiForkFrom_realizes`) and `expand` nonvanishing to be nonzero (`hexp_ne`).
Neither is needed to *price* a round — see the escape-layer preamble below.

Nothing here is classical: `decideWins` and `decideKimchiForkValid` are plain `Decidable`
data, so `kimchiExtract` stays a computable `def`.
-/

section Extractor

/-- Decide the wire acceptance predicate. `Wins` *is* `VerifierAcceptsAt`, a conjunction of two
group equations, so it is decidable outright — no `Classical.dec`, which would silently make
the extractor noncomputable. -/
private def decideWins [DecidableEq G] (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (expand : Pre → F) (proofOf : Pf → OpeningProof F G σ.k)
    (prefixes : Pf → Fin (σ.k + 1) → T) (O : T → Pre) (p : Pf) :
    Decidable (Wins σ b v P expand proofOf prefixes O p) := by
  unfold Wins VerifierAcceptsAt
  infer_instance

/-- **Validity is decidable** (`lem:fork_valid_decidable`), by structural recursion on the
certificate: every leaf and node condition is a conjunction of equations and disequations in
`F` and `G`. The mirror of ironwood's `decideDeployedForkValid`. -/
private def decideKimchiForkValid [DecidableEq F] [DecidableEq G] (U H : G) (v : F) :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) →
      (cert : KimchiForkCert F G d) → Decidable (KimchiForkValid U H v g b P cert)
  | 0, g, b, P, .leaf sg δ c z1 z2 c' z1' z2' => by
      change Decidable (c ≠ c' ∧ sg = g 0 ∧
        (c • (P + v • U) + δ = z1 • sg + (z1 * b 0) • U + z2 • H) ∧
        (c' • (P + v • U) + δ = z1' • sg + (z1' * b 0) • U + z2' • H))
      infer_instance
  | d + 1, g, b, P, .node L R u₁ u₂ u₃ t₁ t₂ t₃ => by
      letI := decideKimchiForkValid U H v (foldHalves g u₁) (foldHalves b u₁)
        (P + u₁⁻¹ • L + u₁ • R) t₁
      letI := decideKimchiForkValid U H v (foldHalves g u₂) (foldHalves b u₂)
        (P + u₂⁻¹ • L + u₂ • R) t₂
      letI := decideKimchiForkValid U H v (foldHalves g u₃) (foldHalves b u₃)
        (P + u₃⁻¹ • L + u₃ • R) t₃
      change Decidable (u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        KimchiForkValid U H v (foldHalves g u₁) (foldHalves b u₁) (P + u₁⁻¹ • L + u₁ • R) t₁ ∧
        KimchiForkValid U H v (foldHalves g u₂) (foldHalves b u₂) (P + u₂⁻¹ • L + u₂ • R) t₂ ∧
        KimchiForkValid U H v (foldHalves g u₃) (foldHalves b u₃) (P + u₃⁻¹ • L + u₃ • R) t₃)
      infer_instance

/-- **RETIRED.** Scan a list of prechallenges for the first one whose attempt succeeds and whose
*field* image is fresh. This was the hand-adapted copy of ironwood's `nextForkChallenge` made
when `Pre` was assumed to carry no algebra; `kimchiForkFrom` now calls
`Zcash.Snark.nextForkChallenge` directly, which tests freshness in `Pre` and skips `q = 0` — the
skip the escape layer prices. Nothing depends on this copy or on its four lemmas below. -/
private def scanFork {α : Type*} [DecidableEq F] (expand : Pre → F) (attempt : Pre → Option α)
    (seen : List F) : List Pre → Option ((F × α) × List Pre × List F)
  | [] => none
  | q :: qs =>
      if expand q ∈ seen then scanFork expand attempt seen qs
      else
        match attempt q with
        | some r => some ((expand q, r), (qs, expand q :: seen))
        | none => scanFork expand attempt seen qs

/-- **The fork over `Pre`** (`def:pre_fork`). Indexed by certificate depth `e` with coin depth
`e + 1`, so the game's depth-`(σ.k + 1)` tape is consumed exactly: `σ.k` node levels
three-forking the round challenges, then the Schnorr level, which keeps two of three branches
and emits the leaf.

At a node (round `m`, `m + e + 1 = σ.k`), let `t` be the round's prefix and `q₁ = O t`. Recurse
on the cached run; then scan the node's order list for two further prechallenges whose
reprogrammed runs `Function.update O t q` still read their round-`m` challenge at `t` and whose
recursive attempts succeed. `dec` is what makes the reprogramming meaningful: the guard pins the
round's prefix to `t`, so `dec.round_eq` forces all three branches to carry the *same* `(L, R)`
— which is exactly the node shape `KimchiForkValid` requires, and why the node is emitted with
`dec.round t` rather than with any one branch's cross-terms.

At the leaf (the Schnorr round, index `Fin.last σ.k`) the same scan keeps *two* branches — all
`schnorr_fork_eq` consumes — and the leaf carries `dec.final t` for `(δ, sg)`, again shared
across the branches by `dec.final_eq`. -/
private def kimchiForkFrom [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes) :
    {e : ℕ} → (m : ℕ) → m + e = σ.k → (O : T → Pre) → (p : Pf) →
      Zcash.Snark.RecursiveForkCoins Pre (e + 1) →
      Zcash.Snark.RecursiveForkAttempt (KimchiForkCert F G e)
  | 0, _, _, O, p, .node order _ =>
      let j : Fin (σ.k + 1) := Fin.last σ.k
      let t : T := prefixes p j
      let q₁ : Pre := O t
      letI := decideWins σ b v P expand proofOf prefixes O p
      if Wins σ b v P expand proofOf prefixes O p then
        let attempt : Pre → Zcash.Snark.RecursiveForkAttempt (F × F) := fun q =>
          let O' := Function.update O t q
          let p' := A.run O'
          letI := decideWins σ b v P expand proofOf prefixes O' p'
          if prefixes p' j = t ∧ Wins σ b v P expand proofOf prefixes O' p' then
            { output := some ((proofOf p').z1, (proofOf p').z2), runs := 1 }
          else { output := none, runs := 1 }
        let second := Zcash.Snark.nextForkChallenge attempt [q₁] order
        match second.output with
        | none => { output := none, runs := 1 + second.runs }
        | some ((q₂, z), _) =>
            { output := some (.leaf (dec.final t).2 (dec.final t).1
                (expand q₁) (proofOf p).z1 (proofOf p).z2 (expand q₂) z.1 z.2)
              runs := 1 + second.runs }
      else { output := none, runs := 1 }
  | e + 1, m, hm, O, p, .node order child =>
      let j : Fin (σ.k + 1) := ⟨m, by omega⟩
      let t : T := prefixes p j
      let q₁ : Pre := O t
      let first := kimchiForkFrom σ b v P expand A proofOf prefixes dec (m + 1) (by omega) O p
        (child (O t))
      match first.output with
      | none => { output := none, runs := first.runs }
      | some c₁ =>
        let attempt : Pre → Zcash.Snark.RecursiveForkAttempt (KimchiForkCert F G e) := fun q =>
          let O' := Function.update O t q
          let p' := A.run O'
          if prefixes p' j = t then
            kimchiForkFrom σ b v P expand A proofOf prefixes dec (m + 1) (by omega) O' p'
              (child q)
          else { output := none, runs := 1 }
        let second := Zcash.Snark.nextForkChallenge attempt [q₁] order
        match second.output with
        | none => { output := none, runs := first.runs + second.runs }
        | some ((q₂, c₂), rest, seen) =>
          let third := Zcash.Snark.nextForkChallenge attempt seen rest
          match third.output with
          | none => { output := none, runs := first.runs + second.runs + third.runs }
          | some ((q₃, c₃), _) =>
              { output := some (.node (dec.round t).1 (dec.round t).2
                  (expand q₁) (expand q₂) (expand q₃) c₁ c₂ c₃)
                runs := first.runs + second.runs + third.runs }

end Extractor

/-- **The extractor** (body: Stage 5b). Given the oracle table and the fork tape, run the
adversary, rewind it at the round prefixes, and compute an opening or a relation — ironwood's
`recursiveAlgebraicFork` composed with `kimchiOpeningOrBreak`. `none` is the failure branch the
theorem below bounds.

Its *type* is the correctness statement: a `some` answer carries the witness or the break as
data, with their defining equations. -/
def kimchiExtract [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (pg : Fin (2 ^ σ.k) → F) (pw : F) (_hP : P = commitGen σ.g pg + pw • σ.h)
    (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (_dec : DecodesFromPrefixes σ proofOf prefixes)
    (O : T → Pre) (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) :
    Option (OpeningOrBreak σ P b v) :=
  match (kimchiForkFrom σ b v P expand A proofOf prefixes _dec 0 (Nat.zero_add σ.k) O
      (A.run O) coins).output with
  | none => none
  | some cert =>
      letI := decideKimchiForkValid σ.U σ.h v σ.g b P cert
      if h : KimchiForkValid σ.U σ.h v σ.g b P cert then
        some (kimchiOpeningOrBreak σ b v P pg pw _hP cert h)
      else none

/-- **The extractor's black-box call count**, as a projection of the *same* recursion the
extractor runs — not a second definition that could drift from it. This is what makes
`ReductionEfficient` (`Forking/KnowledgeSoundness.lean`) statable, and it is why the fork returns
`Zcash.Snark.RecursiveForkAttempt` rather than a bare `Option`: upstream counts the same way
(`ComputedAlgebraicFSFamily.ReductionEfficient`, `Algebraic.lean:1407`, over
`(instanceAttempt …).runs`).

Kept honest by construction: a separate counting `def` would typecheck and could be defined to
return `0`, advertising a zero-call reduction that nothing in the tree would catch. A projection
of the extractor's own term cannot. -/
def kimchiExtractRuns [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (O : T → Pre) (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) : ℕ :=
  (kimchiForkFrom σ b v P expand A proofOf prefixes dec 0 (Nat.zero_add σ.k) O
    (A.run O) coins).runs

/-! ## The escape layer over `Pre`

The port of ironwood's escape layer (`Forking/Adversary/Recursive.lean:1062–1425`) with the
oracle codomain `Pre` in place of the field. Everything *below* the escape layer is imported
unchanged — `escapesDuringC_measure_le'`, `queryBound_completing`, `escapesDuringC_completing`,
`PrefixDecode`, `RecursiveForkCoins` with `nodeAt`/`Complete`, and
`uniformOfFintype_toOuterMeasure_triple_le` — because none of it mentions algebra, so all of it
applies verbatim at `Pre`.

The escape layer **is** ironwood's, not a port of it: `recursiveForkEscape` asks only `[Zero F]`
of the alphabet, so it applies at `Pre` verbatim — zero clause included. That clause is not
optional here: the scan is `Zcash.Snark.nextForkChallenge`, which skips `q = 0`, so a `q = 0`
that the fork cannot use must be charged, or non-escape would not force the fork to return.
Smallness of the escape set is therefore ironwood's `recursiveForkEscape_subset_triple`, which
needs **no** injectivity of `expand`: pricing a round costs `3 / |Pre|` on the strength of the
zero clause alone. Injectivity is needed only downstream, in `kimchiForkFrom_realizes`, where
freshness is tested in `Pre` but `KimchiForkRealizes` demands the three *field* challenges be
distinct. The nonzero side conditions of `KimchiForkValid` still come from `hexp_ne`.

The `PreThreeForkSuccess` / `preForkEscape` / `scanFork` block below is the earlier hand-ported
copy of that layer. Nothing depends on it any more; it is retained only because deleting a
declaration is the user's call.
-/

section Escape

variable [Zero Pre] [DecidableEq Pre]

/-! ### The scan -/

omit [Field F] in
/-- **The scan reaches every eligible success** (`lem:scan_isSome_of_good`), the mirror of
ironwood's `nextForkChallenge_isSome_of_good`. -/
private theorem scanFork_isSome_of_good {α : Type*} [DecidableEq F] (expand : Pre → F)
    (attempt : Pre → Option α) (seen : List F) {q : Pre} {order : List Pre}
    (hmem : q ∈ order) (hseen : expand q ∉ seen) (hgood : (attempt q).isSome) :
    (scanFork expand attempt seen order).isSome := by
  induction order with
  | nil => simp at hmem
  | cons w order ih =>
      rw [scanFork]
      split
      · rename_i hstale
        refine ih ?_
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact absurd hstale hseen
        · exact hmem
      · cases hw : attempt w with
        | some r => simp
        | none =>
            simp only []
            refine ih ?_
            rcases List.mem_cons.mp hmem with rfl | hmem
            · rw [hw] at hgood; exact absurd hgood (by simp)
            · exact hmem

omit [Field F] in
/-- **The scan's output is fresh, grows the seen set by one, and comes from an actual
prechallenge** (`lem:scan_output_fresh`), the mirror of ironwood's
`nextForkChallenge_output_fresh` fused with `nextForkChallenge_output_attempt`. The final clause
is what the realization lemma needs: the returned field challenge is the image of a genuine
prechallenge whose attempt returned the recorded value. -/
private theorem scanFork_output_fresh {α : Type*} [DecidableEq F] (expand : Pre → F)
    (attempt : Pre → Option α) (seen : List F)
    {order rest : List Pre} {c : F} {r : α} {seen' : List F}
    (hout : scanFork expand attempt seen order = some ((c, r), rest, seen')) :
    c ∉ seen ∧ seen' = c :: seen ∧ ∃ q : Pre, expand q = c ∧ attempt q = some r := by
  induction order with
  | nil => rw [scanFork] at hout; exact absurd hout (by simp)
  | cons w order ih =>
      rw [scanFork] at hout
      split at hout
      · exact ih hout
      · rename_i hfresh
        cases hw : attempt w with
        | none => rw [hw] at hout; exact ih hout
        | some rw' =>
            rw [hw] at hout
            simp only [Option.some.injEq, Prod.mk.injEq] at hout
            obtain ⟨⟨hc, hr⟩, _, hseen'⟩ := hout
            subst hc; subst hr; subst hseen'
            exact ⟨hfresh, rfl, ⟨w, rfl, hw⟩⟩

omit [Field F] in
/-- **A second success survives into the unscanned suffix** (`lem:scan_other_good_mem_rest`), the
mirror of ironwood's `nextForkChallenge_other_good_mem_rest`. No duplicate-freeness of the order
list is needed: the element at which the scan returns has image `c ≠ expand q`. -/
private theorem scanFork_other_good_mem_rest {α : Type*} [DecidableEq F] (expand : Pre → F)
    (attempt : Pre → Option α) (seen : List F)
    {q : Pre} {order rest : List Pre} {c : F} {r : α} {seen' : List F}
    (hout : scanFork expand attempt seen order = some ((c, r), rest, seen'))
    (hmem : q ∈ order) (hseen : expand q ∉ seen) (hgood : (attempt q).isSome)
    (hne : expand q ≠ c) : q ∈ rest := by
  induction order with
  | nil => simp at hmem
  | cons w order ih =>
      rw [scanFork] at hout
      split at hout
      · rename_i hstale
        refine ih hout ?_
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact absurd hstale hseen
        · exact hmem
      · cases hw : attempt w with
        | none =>
            rw [hw] at hout
            refine ih hout ?_
            rcases List.mem_cons.mp hmem with rfl | hmem
            · rw [hw] at hgood; exact absurd hgood (by simp)
            · exact hmem
        | some rw' =>
            rw [hw] at hout
            simp only [Option.some.injEq, Prod.mk.injEq] at hout
            obtain ⟨⟨hc, _⟩, hrest, _⟩ := hout
            subst hc; subst hrest
            rcases List.mem_cons.mp hmem with rfl | hmem
            · exact absurd rfl hne
            · exact hmem

/-! ### The escape set over `Pre` -/

/-- **RETIRED — three-fork success over `Pre`** (`def:pre_three_fork`): three prechallenges with
pairwise distinct *images* whose attempts all succeed. Superseded by `Zcash.Snark.ThreeForkSuccess`
at `Pre`, which the escape set and the scan both use now; this copy dropped ironwood's zero clause
and so cannot price the `q = 0` branch that `nextForkChallenge` skips. Nothing depends on it. -/
def PreThreeForkSuccess (expand : Pre → F) (good : Pre → Prop) : Prop :=
  ∃ q₁ q₂ q₃, expand q₁ ≠ expand q₂ ∧ expand q₁ ≠ expand q₃ ∧ expand q₂ ≠ expand q₃ ∧
    good q₁ ∧ good q₂ ∧ good q₃

open Classical in
/-- **RETIRED — the local escape set over `Pre`** (`def:pre_escape`), ironwood's
`recursiveForkEscape` with the zero clause dropped. `kimchiForkEscapeSet` uses
`Zcash.Snark.recursiveForkEscape` directly; nothing depends on this copy. -/
noncomputable def preForkEscape (expand : Pre → F) (good : Pre → Prop) : Set Pre :=
  if PreThreeForkSuccess expand good then ∅ else {q | good q}

omit [Field F] in
/-- **The escape set fits in three points** (`lem:pre_escape_subset_triple`). This is where
injectivity of `expand` earns its place in the statement: without it many prechallenges could
share one field image, three-fork success could fail, and the set would not be small. -/
theorem preForkEscape_subset_triple [Nonempty Pre] (expand : Pre → F)
    (hinj : Function.Injective expand) (good : Pre → Prop) :
    ∃ x a b : Pre, preForkEscape expand good ⊆ {x, a, b} := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty Pre›
  by_cases hthree : PreThreeForkSuccess expand good
  · refine ⟨x₀, x₀, x₀, ?_⟩
    rw [preForkEscape, if_pos hthree]
    exact Set.empty_subset _
  · by_cases ha : ∃ a, good a
    · obtain ⟨a, hag⟩ := ha
      by_cases hb : ∃ b, b ≠ a ∧ good b
      · obtain ⟨b, hba, hbg⟩ := hb
        refine ⟨a, a, b, ?_⟩
        rw [preForkEscape, if_neg hthree]
        intro c hc
        simp only [Set.mem_setOf_eq] at hc
        by_cases hca : c = a
        · simp [hca]
        by_cases hcb : c = b
        · simp [hcb]
        exact absurd ⟨a, b, c, fun h => hba (hinj h).symm, fun h => hca (hinj h).symm,
          fun h => hcb (hinj h).symm, hag, hbg, hc⟩ hthree
      · refine ⟨a, a, a, ?_⟩
        rw [preForkEscape, if_neg hthree]
        intro c hc
        simp only [Set.mem_setOf_eq] at hc
        have hca : c = a := by
          by_contra hne
          exact hb ⟨c, hne, hc⟩
        simp [hca]
    · refine ⟨x₀, x₀, x₀, ?_⟩
      rw [preForkEscape, if_neg hthree]
      intro c hc
      exact absurd ⟨c, hc⟩ ha

omit [Field F] in
/-- **Two further challenges when three succeed** (`lem:scan_two_more`), the mirror of ironwood's
`nextForkChallenge_two_more`. -/
private theorem scanFork_two_more {α : Type*} [DecidableEq F] (expand : Pre → F)
    (attempt : Pre → Option α) (order : List Pre) (hcomplete : ∀ q : Pre, q ∈ order) (c₁ : F)
    (hthree : PreThreeForkSuccess expand fun q => (attempt q).isSome) :
    ∃ (c₂ : F) (r₂ : α) (rest : List Pre) (seen : List F),
      scanFork expand attempt [c₁] order = some ((c₂, r₂), rest, seen) ∧ c₂ ≠ c₁ ∧
        ∃ (c₃ : F) (r₃ : α) (rest₃ : List Pre) (seen₃ : List F),
          scanFork expand attempt seen rest = some ((c₃, r₃), rest₃, seen₃) ∧
            c₃ ≠ c₁ ∧ c₃ ≠ c₂ := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ := hthree
  have pick : ∃ x y : Pre, expand x ≠ expand y ∧ expand x ≠ c₁ ∧ expand y ≠ c₁ ∧
      (attempt x).isSome ∧ (attempt y).isSome := by
    by_cases hfa : c₁ = expand a
    · subst hfa
      exact ⟨b, c, hbc, fun h => hab h.symm, fun h => hac h.symm, hb, hc⟩
    · by_cases hfb : c₁ = expand b
      · subst hfb
        exact ⟨a, c, hac, hab, fun h => hbc h.symm, ha, hc⟩
      · exact ⟨a, b, hab, fun h => hfa h.symm, fun h => hfb h.symm, ha, hb⟩
  obtain ⟨x, y, hxy, hxf, hyf, hx, hy⟩ := pick
  obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp
    (scanFork_isSome_of_good expand attempt [c₁] (hcomplete x) (by simpa using hxf) hx)
  obtain ⟨⟨c₂, r₂⟩, rest, seen⟩ := out
  obtain ⟨hfresh, hseen', -⟩ := scanFork_output_fresh expand attempt [c₁] hout
  have hc₂ : c₂ ≠ c₁ := by simpa using hfresh
  set z : Pre := if expand x = c₂ then y else x with hz
  have hzNe : expand z ≠ c₂ := by
    rw [hz]; split
    · rename_i hxu; intro hyu; exact hxy (hxu.trans hyu.symm)
    · assumption
  have hzf : expand z ≠ c₁ := by rw [hz]; split <;> assumption
  have hzGood : (attempt z).isSome := by rw [hz]; split <;> assumption
  have hzMem : z ∈ rest := by
    refine scanFork_other_good_mem_rest expand attempt [c₁] hout ?_ (by simpa using hzf) hzGood
      hzNe
    rw [hz]; split <;> exact hcomplete _
  have hzSeen : expand z ∉ seen := by
    rw [hseen']
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hzNe, hzf⟩
  obtain ⟨out₃, hout₃⟩ := Option.isSome_iff_exists.mp
    (scanFork_isSome_of_good expand attempt seen hzMem hzSeen hzGood)
  obtain ⟨⟨c₃, r₃⟩, rest₃, seen₃⟩ := out₃
  obtain ⟨hfresh₃, -, -⟩ := scanFork_output_fresh expand attempt seen hout₃
  rw [hseen'] at hfresh₃
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hfresh₃
  exact ⟨c₂, r₂, rest, seen, hout, hc₂, c₃, r₃, rest₃, seen₃, hout₃, hfresh₃.2, hfresh₃.1⟩

/-! The two corollaries of `scanFork_two_more` actually consumed by the fork. They are phrased
through a *predicate* `good` and an implication `good q → (attempt q).isSome` rather than through
`attempt` directly: the fork's own attempt function is an anonymous lambda inside its body, so it
can only be named by unification against the goal, which these shapes allow. -/

omit [Field F] in
/-- The first scan of a node returns. -/
private theorem scanFork_fst_ne_none {α : Type*} [DecidableEq F] (expand : Pre → F)
    (attempt : Pre → Option α) (order : List Pre) (hcomplete : ∀ q : Pre, q ∈ order) (c₁ : F)
    (good : Pre → Prop) (hthree : PreThreeForkSuccess expand good)
    (himp : ∀ q, good q → (attempt q).isSome) :
    scanFork expand attempt [c₁] order ≠ none := by
  obtain ⟨q₁, q₂, q₃, h12, h13, h23, g1, g2, g3⟩ := hthree
  obtain ⟨c₂, r₂, rest, seen, hout, -, -⟩ := scanFork_two_more expand attempt order hcomplete c₁
    ⟨q₁, q₂, q₃, h12, h13, h23, himp _ g1, himp _ g2, himp _ g3⟩
  rw [hout]
  simp

omit [Field F] in
/-- The second scan, resuming where the first stopped, returns as well. -/
private theorem scanFork_snd_ne_none {α : Type*} [DecidableEq F] (expand : Pre → F)
    (attempt : Pre → Option α) (order : List Pre) (hcomplete : ∀ q : Pre, q ∈ order) (c₁ : F)
    (good : Pre → Prop) (hthree : PreThreeForkSuccess expand good)
    (himp : ∀ q, good q → (attempt q).isSome)
    {c₂ : F} {r₂ : α} {rest : List Pre} {seen : List F}
    (h1 : scanFork expand attempt [c₁] order = some ((c₂, r₂), rest, seen)) :
    scanFork expand attempt seen rest ≠ none := by
  obtain ⟨q₁, q₂, q₃, h12, h13, h23, g1, g2, g3⟩ := hthree
  obtain ⟨c₂', r₂', rest', seen', hout, -, c₃, r₃, rest₃, seen₃, hout₃, -, -⟩ :=
    scanFork_two_more expand attempt order hcomplete c₁
      ⟨q₁, q₂, q₃, h12, h13, h23, himp _ g1, himp _ g2, himp _ g3⟩
  rw [h1] at hout
  simp only [Option.some.injEq, Prod.mk.injEq] at hout
  obtain ⟨-, hrest, hseen⟩ := hout
  subst hrest
  subst hseen
  rw [hout₃]
  simp

/-! ### Reached tape nodes

Ironwood's `RecursiveForkReached` (`Forking/Adversary/Recursive.lean:1063`) and
`recursiveForkReached_child` (`:1074`) are consumed directly. Both carry NO instance
binders — `#check` shows signatures identical to the copies this file used to hold, up to
the variable names `F`/`P`/`k` for `Pre`/`Pf`/`N` — so they instantiate at the
prechallenge alphabet with no algebra. `scripts/check_ironwood_generic.lean` compiles that
instantiation at a payload type with no algebra at all. -/

/-! ### The operational escape set -/

/-- **The local success predicate of one round** (the `good` of `def:escape_set`): reprogramming
the table at `t` with `q` still reads round `m`'s challenge at `t`, and the residual condition
holds. The residual splits on the remaining certificate depth — this is the one place the port
deviates from ironwood, and it is forced: at depth `e + 1` (an IPA round) it is that the fork
recursed at round `m + 1` on the child tape returns, whereas at depth `0` (the Schnorr round,
`m = σ.k`) it is `Wins` itself, because our leaf level *is* the Schnorr fork while ironwood's is
the win check. -/
private def kimchiForkGood [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes) (m : ℕ) :
    {e : ℕ} → m + e = σ.k → (t : T) → (O : T → Pre) →
      (Pre → Zcash.Snark.RecursiveForkCoins Pre e) → Pre → Prop
  | 0, he, t, O, _, q =>
      prefixes (A.run (Function.update O t q)) ⟨m, by omega⟩ = t ∧
        Wins σ b v P expand proofOf prefixes (Function.update O t q)
          (A.run (Function.update O t q))
  | _ + 1, he, t, O, child, q =>
      prefixes (A.run (Function.update O t q)) ⟨m, by omega⟩ = t ∧
        (kimchiForkFrom σ b v P expand A proofOf prefixes dec (m + 1) (by omega)
          (Function.update O t q) (A.run (Function.update O t q)) (child q)).output.isSome

/-- Reprogramming at `t` does not change the round's own success predicate: the predicate only
ever consults tables of the form `Function.update _ t _`. -/
private theorem kimchiForkGood_update [DecidableEq F] [DecidableEq G] [DecidableEq T]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes) (m : ℕ) :
    {e : ℕ} → (he : m + e = σ.k) → (t : T) → (O : T → Pre) → (q : Pre) →
      (child : Pre → Zcash.Snark.RecursiveForkCoins Pre e) →
      kimchiForkGood σ b v P expand A proofOf prefixes dec m he t (Function.update O t q) child
        = kimchiForkGood σ b v P expand A proofOf prefixes dec m he t O child
  | 0, _, _, _, _, _ => by funext q'; simp only [kimchiForkGood, Function.update_idem]
  | _ + 1, _, _, _, _, _ => by funext q'; simp only [kimchiForkGood, Function.update_idem]

/-- **The operational escape set** (`def:escape_set`), ironwood's `recursiveForkEscapeSet` over
`Pre`. Follow the root tape along the path of answers at `t`'s own earlier chain points; an
absent node or a node of the wrong depth contributes nothing, and at a node of the right depth
the set is the local escape set of that round's success predicate.

Ironwood's outer guard `roundOf t < k` is subsumed here by the depth guard
`roundOf t + node.depth = σ.k`, which already forces `roundOf t ≤ σ.k`; the two definitions
therefore denote the same set. -/
noncomputable def kimchiForkEscapeSet [DecidableEq F] [DecidableEq G] [DecidableEq T]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (t : T) (O : T → Pre) : Set Pre :=
  match root.nodeAt
      ((List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt t i)).take (D.roundOf t)) with
  | none => ∅
  | some node =>
      if hd : D.roundOf t + node.depth = σ.k then
        Zcash.Snark.recursiveForkEscape
          (kimchiForkGood σ b v P expand A proofOf prefixes dec (D.roundOf t) hd t O node.child)
      else ∅

/-- **The escape set is blind at its own point** (`lem:escape_blind`) — the `hblind` hypothesis of
the imported measure lemma, and the only place `PrefixDecode` is used in this subsection. -/
theorem kimchiForkEscapeSet_blind [DecidableEq F] [DecidableEq G] [DecidableEq T]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (t : T) (O : T → Pre) (q : Pre) :
    kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec D root t (Function.update O t q)
      = kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec D root t O := by
  have hpath :
      (List.ofFn fun i : Fin (σ.k + 1) => Function.update O t q (D.chainAt t i)).take
          (D.roundOf t)
        = (List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt t i)).take (D.roundOf t) := by
    refine List.ext_getElem (by simp) (fun i hi hi' => ?_)
    rw [List.getElem_take, List.getElem_take, List.getElem_ofFn, List.getElem_ofFn,
      Function.update_apply, if_neg]
    refine D.chainAt_ne t _ ?_
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at hi
    exact hi.1
  rw [kimchiForkEscapeSet, kimchiForkEscapeSet, hpath]
  cases hnode : root.nodeAt
      ((List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt t i)).take (D.roundOf t)) with
  | none => rfl
  | some node =>
      by_cases hd : D.roundOf t + node.depth = σ.k
      · simp only [dif_pos hd]
        rw [kimchiForkGood_update]
      · simp only [dif_neg hd]

/-- **Each escape set has measure at most `3 / |Pre|`** (`lem:escape_measure_le`), by the imported
bound on the uniform measure of a set inside three points. Since the escape layer is now
ironwood's own, smallness comes from `recursiveForkEscape_subset_triple` — whose three points are
`0` and the at most two successful challenges — so injectivity of `expand` is **not** used. The
binder is kept (as `_hexp_inj`) because the call site in `kimchiExtract_failure_measure_le` is
positional. -/
theorem kimchiForkEscapeSet_measure_le [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Fintype Pre] [Nonempty Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (_hexp_inj : Function.Injective expand)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (t : T) (O : T → Pre) :
    (PMF.uniformOfFintype Pre).toOuterMeasure
        (kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec D root t O)
      ≤ 3 / Fintype.card Pre := by
  rw [kimchiForkEscapeSet]
  cases hnode : root.nodeAt
      ((List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt t i)).take (D.roundOf t)) with
  | none => simp
  | some node =>
      by_cases hd : D.roundOf t + node.depth = σ.k
      · simp only [dif_pos hd]
        obtain ⟨a, c, hsub⟩ := Zcash.Snark.recursiveForkEscape_subset_triple
          (kimchiForkGood σ b v P expand A proofOf prefixes dec (D.roundOf t) hd t O node.child)
        exact Zcash.Snark.uniformOfFintype_toOuterMeasure_triple_le hsub
      · simp only [dif_neg hd]
        simp

/-- **At a real round prefix the escape set is the local one** (`lem:escape_prefix`): the path of
the definition is the run's own first `m` answers, so reachedness rewrites `nodeAt` to the current
tape node and the depth guard holds by arithmetic. -/
theorem kimchiForkEscapeSet_prefix [DecidableEq F] [DecidableEq G] [DecidableEq T]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1))
    {e m : ℕ} (hmk : m + (e + 1) = σ.k + 1) (O : T → Pre) (p : Pf) (order : List Pre)
    (child : Pre → Zcash.Snark.RecursiveForkCoins Pre e)
    (hreach : Zcash.Snark.RecursiveForkReached (σ.k + 1) prefixes root m hmk O p
      (.node order child)) :
    kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec D root
        (prefixes p ⟨m, by omega⟩) O
      = Zcash.Snark.recursiveForkEscape
        (kimchiForkGood σ b v P expand A proofOf prefixes dec m (by omega)
          (prefixes p ⟨m, by omega⟩) O child) := by
  rw [kimchiForkEscapeSet,
    show D.roundOf (prefixes p (⟨m, by omega⟩ : Fin (σ.k + 1))) = m from
      D.roundOf_prefixes p _]
  have hpath :
      (List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt (prefixes p ⟨m, by omega⟩) i)).take m
        = (List.ofFn fun i : Fin (σ.k + 1) => O (prefixes p i)).take m := by
    refine List.ext_getElem (by simp) (fun i hi hi' => ?_)
    rw [List.getElem_take, List.getElem_take, List.getElem_ofFn, List.getElem_ofFn,
      D.chainAt_prefixes]
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at hi
    exact Nat.le_of_lt hi.1
  rw [hpath, hreach]
  simp only [dif_pos (show m + e = σ.k by omega)]

/-! ### Non-escape forces a certificate

The two corollaries of ironwood's `nextForkChallenge_two_more` that the fork actually consumes.
They are phrased through a *predicate* `good` and an implication
`good q → (attempt q).output.isSome` rather than through `attempt` directly: the fork's own
attempt function is an anonymous lambda inside its body, so it can only be named by unification
against the goal, which these shapes allow. -/

/-- The first scan of a node returns. -/
private theorem nextFork_fst_ne_none {α : Type*}
    (attempt : Pre → Zcash.Snark.RecursiveForkAttempt α) (order : List Pre)
    (hcomplete : ∀ q : Pre, q ∈ order) (q₁ : Pre)
    (good : Pre → Prop) (hthree : Zcash.Snark.ThreeForkSuccess good)
    (himp : ∀ q, good q → (attempt q).output.isSome) :
    (Zcash.Snark.nextForkChallenge attempt [q₁] order).output ≠ none := by
  obtain ⟨a, c, d, hac, had, hcd, ha0, hc0, hd0, ga, gc, gd⟩ := hthree
  obtain ⟨q₂, r₂, rest, seen, hout, -⟩ :=
    Zcash.Snark.nextForkChallenge_two_more attempt order hcomplete q₁
      ⟨a, c, d, hac, had, hcd, ha0, hc0, hd0, himp _ ga, himp _ gc, himp _ gd⟩
  rw [hout]
  simp

/-- The second scan, resuming where the first stopped, returns as well. -/
private theorem nextFork_snd_ne_none {α : Type*}
    (attempt : Pre → Zcash.Snark.RecursiveForkAttempt α) (order : List Pre)
    (hcomplete : ∀ q : Pre, q ∈ order) (q₁ : Pre)
    (good : Pre → Prop) (hthree : Zcash.Snark.ThreeForkSuccess good)
    (himp : ∀ q, good q → (attempt q).output.isSome)
    {q₂ : Pre} {r₂ : α} {rest seen : List Pre}
    (h1 : (Zcash.Snark.nextForkChallenge attempt [q₁] order).output
      = some ((q₂, r₂), rest, seen)) :
    (Zcash.Snark.nextForkChallenge attempt seen rest).output ≠ none := by
  obtain ⟨a, c, d, hac, had, hcd, ha0, hc0, hd0, ga, gc, gd⟩ := hthree
  obtain ⟨q₂', r₂', rest', seen', hout, hthird⟩ :=
    Zcash.Snark.nextForkChallenge_two_more attempt order hcomplete q₁
      ⟨a, c, d, hac, had, hcd, ha0, hc0, hd0, himp _ ga, himp _ gc, himp _ gd⟩
  rw [h1] at hout
  simp only [Option.some.injEq, Prod.mk.injEq] at hout
  obtain ⟨-, hrest, hseen⟩ := hout
  subst hrest
  subst hseen
  intro hnone
  rw [hnone] at hthird
  simp at hthird

omit [Zero Pre] [DecidableEq Pre] in
/-- **Non-escape forces the fork to return** (`lem:isSome_of_not_escape`), the port of ironwood's
`recursiveAlgebraicForkFrom_isSome_of_not_escape`. -/
private theorem kimchiForkFrom_isSome_of_not_escape [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Fintype Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) :
    {e : ℕ} → (m : ℕ) → (hme : m + e = σ.k) → (O : T → Pre) → (p : Pf) →
      (coins : Zcash.Snark.RecursiveForkCoins Pre (e + 1)) →
      p = A.run O →
      Zcash.Snark.RecursiveForkReached (σ.k + 1) prefixes root m (by omega) O p coins →
      coins.Complete → Wins σ b v P expand proofOf prefixes O p →
      ¬ (A.completing prefixes).escapesDuringC
          (kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec D root) O →
      (kimchiForkFrom σ b v P expand A proofOf prefixes dec m hme O p coins).output.isSome
  | 0, m, hme, O, p, .node order child, hp, hreach, hcomplete, hwin, hnoescape => by
      subst hp
      have hm : m = σ.k := by omega
      subst hm
      -- the global escape set at the Schnorr prefix is the local one
      have hesc : kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec D root
            (prefixes (A.run O) (Fin.last σ.k)) O
          = Zcash.Snark.recursiveForkEscape (kimchiForkGood σ b v P expand A proofOf prefixes dec
            σ.k (by omega) (prefixes (A.run O) (Fin.last σ.k)) O child) :=
        kimchiForkEscapeSet_prefix σ b v P expand A proofOf prefixes dec D root
          (e := 0) (m := σ.k) (by omega) O (A.run O) order child hreach
      -- the cached challenge is not exceptional
      have hlocal : O (prefixes (A.run O) (Fin.last σ.k)) ∉
          Zcash.Snark.recursiveForkEscape (kimchiForkGood σ b v P expand A proofOf prefixes dec
            σ.k (by omega) (prefixes (A.run O) (Fin.last σ.k)) O child) := by
        intro hu
        exact hnoescape (Zcash.Snark.OracleComp.escapesDuringC_completing _ prefixes
          (j := Fin.last σ.k) (by rw [hesc]; exact hu))
      -- reprogramming at `t` with the cached answer is the identity on tables
      have hupd : Function.update O (prefixes (A.run O) (Fin.last σ.k))
          (O (prefixes (A.run O) (Fin.last σ.k))) = O := by
        funext x
        by_cases hx : x = prefixes (A.run O) (Fin.last σ.k)
        · subst hx; simp
        · simp [hx]
      -- hence the cached challenge is itself good
      have hgood₁ : kimchiForkGood σ b v P expand A proofOf prefixes dec σ.k (by omega)
          (prefixes (A.run O) (Fin.last σ.k)) O child
          (O (prefixes (A.run O) (Fin.last σ.k))) := by
        rw [kimchiForkGood, hupd]
        exact ⟨rfl, hwin⟩
      -- hence three-fork success: were there not three, the escape set would be everything good
      have hthree : Zcash.Snark.ThreeForkSuccess
          (kimchiForkGood σ b v P expand A proofOf prefixes dec σ.k (by omega)
            (prefixes (A.run O) (Fin.last σ.k)) O child) := by
        by_contra hno
        exact hlocal (by rw [Zcash.Snark.recursiveForkEscape, if_neg hno]; exact Or.inr hgood₁)
      -- so the single further scan returns, and the leaf is emitted
      rw [kimchiForkFrom, if_pos hwin]
      simp only []
      split
      · rename_i hnone
        refine absurd hnone (nextFork_fst_ne_none _ order hcomplete.1 _ _ hthree ?_)
        intro q hq
        rw [kimchiForkGood] at hq
        split
        · rfl
        · rename_i hno
          exact absurd hq hno
      · rfl
  | e + 1, m, hme, O, p, .node order child, hp, hreach, hcomplete, hwin, hnoescape => by
      subst hp
      have hesc : kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec D root
            (prefixes (A.run O) ⟨m, by omega⟩) O
          = Zcash.Snark.recursiveForkEscape (kimchiForkGood σ b v P expand A proofOf prefixes dec m
            (by omega) (prefixes (A.run O) ⟨m, by omega⟩) O child) :=
        kimchiForkEscapeSet_prefix σ b v P expand A proofOf prefixes dec D root
          (e := e + 1) (m := m) (by omega) O (A.run O) order child hreach
      have hlocal : O (prefixes (A.run O) ⟨m, by omega⟩) ∉
          Zcash.Snark.recursiveForkEscape (kimchiForkGood σ b v P expand A proofOf prefixes dec m
            (by omega) (prefixes (A.run O) ⟨m, by omega⟩) O child) := by
        intro hu
        exact hnoescape (Zcash.Snark.OracleComp.escapesDuringC_completing _ prefixes
          (j := ⟨m, by omega⟩) (by rw [hesc]; exact hu))
      have hupd : Function.update O (prefixes (A.run O) ⟨m, by omega⟩)
          (O (prefixes (A.run O) ⟨m, by omega⟩)) = O := by
        funext x
        by_cases hx : x = prefixes (A.run O) ⟨m, by omega⟩
        · subst hx; simp
        · simp [hx]
      have hreachChild : Zcash.Snark.RecursiveForkReached (σ.k + 1) prefixes root (m + 1)
          (by omega) O (A.run O) (child (O (prefixes (A.run O) ⟨m, by omega⟩))) :=
        Zcash.Snark.recursiveForkReached_child (σ.k + 1) prefixes root (by omega) O (A.run O)
          order child hreach
      -- the cached branch: the induction hypothesis at round `m + 1`
      have hfirst : (kimchiForkFrom σ b v P expand A proofOf prefixes dec (m + 1) (by omega) O
          (A.run O) (child (O (prefixes (A.run O) ⟨m, by omega⟩)))).output.isSome :=
        kimchiForkFrom_isSome_of_not_escape σ b v P expand A proofOf prefixes dec D root
          (m + 1) (by omega) O (A.run O) (child (O (prefixes (A.run O) ⟨m, by omega⟩)))
          rfl hreachChild (hcomplete.2 _) hwin hnoescape
      have hgood₁ : kimchiForkGood σ b v P expand A proofOf prefixes dec m (by omega)
          (prefixes (A.run O) ⟨m, by omega⟩) O child (O (prefixes (A.run O) ⟨m, by omega⟩)) := by
        rw [kimchiForkGood, hupd]
        exact ⟨rfl, hfirst⟩
      have hthree : Zcash.Snark.ThreeForkSuccess
          (kimchiForkGood σ b v P expand A proofOf prefixes dec m (by omega)
            (prefixes (A.run O) ⟨m, by omega⟩) O child) := by
        by_contra hno
        exact hlocal (by rw [Zcash.Snark.recursiveForkEscape, if_neg hno]; exact Or.inr hgood₁)
      -- the attempt succeeds wherever the round's success predicate holds
      have himp : ∀ q : Pre,
          kimchiForkGood σ b v P expand A proofOf prefixes dec m (by omega)
              (prefixes (A.run O) ⟨m, by omega⟩) O child q →
            (if prefixes (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q))
                  (⟨m, by omega⟩ : Fin (σ.k + 1)) = prefixes (A.run O) ⟨m, by omega⟩ then
                kimchiForkFrom σ b v P expand A proofOf prefixes dec (m + 1) (by omega)
                  (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)
                  (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)) (child q)
              else { output := none, runs := 1 }).output.isSome := by
        intro q hq
        rw [kimchiForkGood] at hq
        split
        · exact hq.2
        · rename_i hno
          exact absurd hq.1 hno
      rw [kimchiForkFrom]
      simp only []
      split
      · rename_i hnone
        rw [hnone] at hfirst
        exact absurd hfirst (by simp)
      · split
        · rename_i hn2
          exact absurd hn2 (nextFork_fst_ne_none _ order hcomplete.1 _ _ hthree himp)
        · rename_i hout
          split
          · rename_i hn3
            exact absurd hn3 (nextFork_snd_ne_none _ order hcomplete.1 _ _ hthree himp hout)
          · rfl

/-- **Root form** (`lem:isSome_of_not_escape_root`): a winning table on which the completing
machine does not escape yields a certificate from the fork started at round `0` with the root
tape, which is reached by definition (its path is empty). -/
private theorem kimchiForkFrom_isSome_of_not_escape_root [DecidableEq F] [DecidableEq G]
    [DecidableEq T] [Fintype Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcomplete : coins.Complete)
    (O : T → Pre) (hwin : Wins σ b v P expand proofOf prefixes O (A.run O))
    (hnoescape : ¬ (A.completing prefixes).escapesDuringC
      (kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec D coins) O) :
    (kimchiForkFrom σ b v P expand A proofOf prefixes dec 0 (Nat.zero_add σ.k) O (A.run O)
      coins).output.isSome := by
  refine kimchiForkFrom_isSome_of_not_escape σ b v P expand A proofOf prefixes dec D coins
    0 (Nat.zero_add σ.k) O (A.run O) coins rfl ?_ hcomplete hwin hnoescape
  cases coins with
  | node order child => rfl

end Escape

/-! ## A raw proof as a challenge-independent strategy

The algebraic half of the argument speaks about the *flat* wire acceptance of several different
runs' proofs at several different challenge vectors, and must convert each into the *folded* shape
`KimchiForkValid` uses. That conversion is proved once and for all in the frozen
`Forking/Prover.lean` — but only for a `KimchiProver` strategy. The bridge is that a raw opening
proof **is** a strategy: a constant one. Nothing about the flat recombination sum is re-derived
here; `kimchiProverAccept_iff_verifierAcceptsAt` already reassociated it. -/

section ProverOfProof

/-- **A proof as a constant strategy** (`def:prover_of_proof`): at each round emit the proof's own
cross-terms and continue, ignoring the challenge, on the tail of the proof; at the leaf emit
`(sg, δ)` and answer every Schnorr challenge with `(z1, z2)`. -/
def proverOfProof : {d : ℕ} → OpeningProof F G d → KimchiProver F G d
  | 0, π => .leaf π.sg π.delta fun _ => (π.z1, π.z2)
  | _ + 1, π =>
      .node (π.lr 0).1 (π.lr 0).2 fun _ =>
        proverOfProof
          { lr := fun j => π.lr j.succ, delta := π.delta, z1 := π.z1, z2 := π.z2, sg := π.sg }

omit [Field F] [AddCommGroup G] [Module F G] in
/-- The constant strategy emits the proof's own cross-terms along every branch. -/
private theorem lrAt_proverOfProof : {d : ℕ} → (π : OpeningProof F G d) → (χ : Fin (d + 1) → F) →
    (proverOfProof π).lrAt χ = π.lr
  | 0, π, _ => by funext i; exact i.elim0
  | _ + 1, π, χ => by
      rw [proverOfProof, KimchiProver.lrAt, lrAt_proverOfProof]
      funext i
      refine Fin.cases ?_ (fun q => ?_) i
      · simp
      · simp

omit [Field F] [AddCommGroup G] [Module F G] in
/-- The constant strategy emits the proof's own leaf data along every branch. -/
private theorem leafAt_proverOfProof : {d : ℕ} → (π : OpeningProof F G d) →
    (χ : Fin (d + 1) → F) → (proverOfProof π).leafAt χ = (π.sg, π.delta, π.z1, π.z2)
  | 0, _, _ => rfl
  | _ + 1, π, χ => by rw [proverOfProof, KimchiProver.leafAt, leafAt_proverOfProof]

omit [Field F] [AddCommGroup G] [Module F G] in
/-- **The constant strategy reassembles the proof** (`lem:proof_at_of_proof`). -/
theorem proofAt_proverOfProof {d : ℕ} (π : OpeningProof F G d) (χ : Fin (d + 1) → F) :
    (proverOfProof π).proofAt χ = π := by
  rw [KimchiProver.proofAt, lrAt_proverOfProof, leafAt_proverOfProof]

/-- **Flat equals folded, for a raw proof** (`lem:flat_folded_bridge`): the wire verifier's
acceptance of `π` at `(u, c)` is the folded acceptance of `proverOfProof π` at `Fin.snoc u c`.
This is the whole of the flat↔folded bridge that the realization argument needs. -/
theorem verifierAcceptsAt_iff_proverOfProof_accept (σ : SRS G) (π : OpeningProof F G σ.k)
    (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (u : Fin σ.k → F) (c : F) :
    VerifierAcceptsAt σ π P (innerProduct (bPolyCoefficients u) b) v c u ↔
      kimchiProverAccept (proverOfProof π) σ.g b σ.U σ.h v P (Fin.snoc u c) := by
  rw [kimchiProverAccept_iff_verifierAcceptsAt σ (proverOfProof π) b v P u c,
    proofAt_proverOfProof]

end ProverOfProof

/-! ## From a returned certificate to a valid one

The algebraic half of the argument. `KimchiForkRealizes` records that a certificate's data really
came from winning adversary runs; `KimchiForkRealizes.forkValid` then converts that into
`KimchiForkValid` by an induction that performs **no algebraic manipulation at all**: the fold on
the certificate side and the recursion of `kimchiProverAccept` are the same rewriting, and the flat
sum was already reassociated once, in `verifierAcceptsAt_iff_proverOfProof_accept`. -/

section Realization

/-- `Fin.tail` commutes with `Fin.snoc` when the head survives. (`Forking/Prover.lean` proves the
same fact but keeps it `private`, hence invisible here; the families must be pinned to the
constant one or the dependent `snoc`/`tail` do not elaborate against each other bare.) -/
private theorem tail_snoc' {n : ℕ} {α : Sort*} (u : Fin (n + 1) → α) (c : α) :
    Fin.tail (α := fun _ => α) (Fin.snoc (α := fun _ => α) u c)
      = Fin.snoc (α := fun _ => α) (Fin.tail (α := fun _ => α) u) c := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.tail, Fin.succ_last, Fin.snoc_last]
  · simp only [Fin.tail, Fin.succ_castSucc, Fin.snoc_castSucc]

/-! Run history is ironwood's `RecursiveRunHistory` (`Recursive.lean:780`), consumed
directly: same signature up to variable naming, no instance binders. -/

/-- **The runs a subtree represents** (`def:run_suffix`): the winning runs that agree with the
fork points already fixed above round `m`, read off at the transcript points `ts`, the
prechallenges `qs`, and the leaf data `(sg, δ, c, z1, z2)`.

Ironwood's extra `stable` parameter is instantiated at the trivially-true predicate here: our
claim is fixed structurally (`P`, `b`, `v` are parameters and the adversary outputs only an
opening proof), so there is no claim-stability side condition to carry. -/
def KimchiRunSuffix (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf) (proofOf : Pf → OpeningProof F G σ.k)
    (prefixes : Pf → Fin (σ.k + 1) → T) (m e : ℕ) (hme : m + e = σ.k)
    (history : Fin m → T × Pre) :
    (Fin e → T) → (Fin e → Pre) → G → G → F → F → F → Prop :=
  fun ts qs sg δ c z1 z2 => ∃ (O : T → Pre) (p : Pf), p = A.run O ∧
    Wins σ b v P expand proofOf prefixes O p ∧
    Zcash.Snark.RecursiveRunHistory _ m (by omega) prefixes O p history ∧
    (∀ i : Fin e, prefixes p ⟨m + i.val, by omega⟩ = ts i) ∧
    (∀ i, O (ts i) = qs i) ∧
    (proofOf p).sg = sg ∧ (proofOf p).delta = δ ∧
    expand (O (prefixes p (Fin.last σ.k))) = c ∧
    (proofOf p).z1 = z1 ∧ (proofOf p).z2 = z2

/-- **Realization** (`def:kimchi_realizes`), ironwood's `AlgebraicForkRealizes` adapted twice:
our leaf carries *two* Schnorr transcripts (theirs carries one, their leaf level being the last
forked round), and a node records its challenges together with the prechallenges they came from,
since the accumulator lives over `Pre` while the certificate lives over `F`. There is no inverse
in the `cons`, because our fold convention already agrees with `KimchiForkValid`'s. -/
def KimchiForkRealizes (expand : Pre → F) (round : T → G × G) :
    {e : ℕ} → ((Fin e → T) → (Fin e → Pre) → G → G → F → F → F → Prop) →
      KimchiForkCert F G e → Prop
  | 0, acc, .leaf sg δ c z1 z2 c' z1' z2' =>
      c ≠ c' ∧ acc Fin.elim0 Fin.elim0 sg δ c z1 z2 ∧ acc Fin.elim0 Fin.elim0 sg δ c' z1' z2'
  | _ + 1, acc, .node L R u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        ∃ (t : T) (q₁ q₂ q₃ : Pre), (L, R) = round t ∧
          expand q₁ = u₁ ∧ expand q₂ = u₂ ∧ expand q₃ = u₃ ∧
          KimchiForkRealizes expand round
            (fun ts qs => acc (Fin.cons t ts) (Fin.cons q₁ qs)) t₁ ∧
          KimchiForkRealizes expand round
            (fun ts qs => acc (Fin.cons t ts) (Fin.cons q₂ qs)) t₂ ∧
          KimchiForkRealizes expand round
            (fun ts qs => acc (Fin.cons t ts) (Fin.cons q₃ qs)) t₃

omit [AddCommGroup G] [Module F G] in
/-- **Realization is monotone** (`lem:realizes_mono`) in its leaf relation. -/
theorem KimchiForkRealizes.mono (expand : Pre → F) (round : T → G × G) :
    {e : ℕ} → {acc acc' : (Fin e → T) → (Fin e → Pre) → G → G → F → F → F → Prop} →
    {cert : KimchiForkCert F G e} →
    (∀ ts qs sg δ c z1 z2, acc ts qs sg δ c z1 z2 → acc' ts qs sg δ c z1 z2) →
    KimchiForkRealizes expand round acc cert → KimchiForkRealizes expand round acc' cert
  | 0, _, _, .leaf _ _ _ _ _ _ _ _, h, hreal =>
      ⟨hreal.1, h _ _ _ _ _ _ _ hreal.2.1, h _ _ _ _ _ _ _ hreal.2.2⟩
  | _ + 1, _, _, .node _ _ _ _ _ _ _ _, h, hreal => by
      obtain ⟨h12, h13, h23, hu1, hu2, hu3, t, q₁, q₂, q₃, hLR, he1, he2, he3, hr1, hr2, hr3⟩ :=
        hreal
      exact ⟨h12, h13, h23, hu1, hu2, hu3, t, q₁, q₂, q₃, hLR, he1, he2, he3,
        KimchiForkRealizes.mono expand round (fun _ _ _ _ _ _ _ hl => h _ _ _ _ _ _ _ hl) hr1,
        KimchiForkRealizes.mono expand round (fun _ _ _ _ _ _ _ hl => h _ _ _ _ _ _ _ hl) hr2,
        KimchiForkRealizes.mono expand round (fun _ _ _ _ _ _ _ hl => h _ _ _ _ _ _ _ hl) hr3⟩

omit [Field F] in
/-- The head of the challenge vector a node hands its children: the `Fin.snoc` of the expanded
`Fin.cons` reads the head prechallenge at index `0`. -/
private theorem snoc_expand_cons_zero {e : ℕ} (expand : Pre → F) (q : Pre) (qs : Fin e → Pre)
    (c : F) :
    (Fin.snoc (α := fun _ => F) (fun i => expand (Fin.cons (α := fun _ => Pre) q qs i)) c)
        (0 : Fin (e + 2)) = expand q := by
  rw [show (0 : Fin (e + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
  simp

omit [Field F] in
/-- ... and its tail is the child's own challenge vector. -/
private theorem snoc_expand_cons_tail {e : ℕ} (expand : Pre → F) (q : Pre) (qs : Fin e → Pre)
    (c : F) :
    Fin.tail (α := fun _ => F)
        (Fin.snoc (α := fun _ => F)
          (fun i => expand (Fin.cons (α := fun _ => Pre) q qs i)) c)
      = Fin.snoc (α := fun _ => F) (fun i => expand (qs i)) c := by
  rw [tail_snoc']
  congr 1

/-- **A realized certificate is valid** (`lem:realizes_forkValid`). The induction folds `(g, b, P)`
as it descends; at a node, `kimchiProverAccept` at depth `e + 1` unfolds to *exactly* the same
predicate at the folded data, because the constant strategy's round-`0` cross-terms are the
certificate's `(L, R)` — which they are, since realization supplies `(L, R) = round t`. No
algebraic manipulation is performed at all. -/
theorem KimchiForkRealizes.forkValid (U H : G) (v : F) (expand : Pre → F) (round : T → G × G) :
    {e : ℕ} → (g : Fin (2 ^ e) → G) → (bb : Fin (2 ^ e) → F) → (P : G) →
    (acc : (Fin e → T) → (Fin e → Pre) → G → G → F → F → F → Prop) →
    (cert : KimchiForkCert F G e) → KimchiForkRealizes expand round acc cert →
    (∀ ts qs sg δ c z1 z2, acc ts qs sg δ c z1 z2 →
      kimchiProverAccept (proverOfProof
          ({ lr := fun j => round (ts j), delta := δ, z1 := z1, z2 := z2, sg := sg } :
            OpeningProof F G e)) g bb U H v P (Fin.snoc (fun i => expand (qs i)) c)) →
    KimchiForkValid U H v g bb P cert
  | 0, g, bb, P, acc, .leaf sg δ c z1 z2 c' z1' z2', hreal, hyp => by
      obtain ⟨hne, ha, ha'⟩ := hreal
      have h1 := hyp Fin.elim0 Fin.elim0 sg δ c z1 z2 ha
      have h2 := hyp Fin.elim0 Fin.elim0 sg δ c' z1' z2' ha'
      rw [proverOfProof, kimchiProverAccept] at h1 h2
      rw [show (Fin.snoc (α := fun _ => F) (fun i : Fin 0 => expand (Fin.elim0 i)) c)
          (0 : Fin 1) = c from by
        rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]] at h1
      rw [show (Fin.snoc (α := fun _ => F) (fun i : Fin 0 => expand (Fin.elim0 i)) c')
          (0 : Fin 1) = c' from by
        rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]] at h2
      exact ⟨hne, h1.1, h1.2, h2.2⟩
  | e + 1, g, bb, P, acc, .node L R u₁ u₂ u₃ t₁ t₂ t₃, hreal, hyp => by
      obtain ⟨h12, h13, h23, hu1, hu2, hu3, t, q₁, q₂, q₃, hLR, he1, he2, he3, hr1, hr2, hr3⟩ :=
        hreal
      -- the parent hypothesis, pushed through one round of the recursion: the constant strategy's
      -- round-`0` cross-terms are `(L, R)`, so `kimchiProverAccept` unfolds to the folded data
      have key : ∀ (u : F) (q : Pre), expand q = u →
          ∀ (ts : Fin e → T) (qs : Fin e → Pre) (sg δ : G) (c z1 z2 : F),
            acc (Fin.cons t ts) (Fin.cons q qs) sg δ c z1 z2 →
            kimchiProverAccept (proverOfProof
                ({ lr := fun j => round (ts j), delta := δ, z1 := z1, z2 := z2, sg := sg } :
                  OpeningProof F G e))
              (foldHalves g u) (foldHalves bb u) U H v (P + u⁻¹ • L + u • R)
              (Fin.snoc (fun i => expand (qs i)) c) := by
        intro u q hq ts qs sg δ c z1 z2 hacc
        have h := hyp (Fin.cons t ts) (Fin.cons q qs) sg δ c z1 z2 hacc
        rw [proverOfProof, kimchiProverAccept] at h
        rw [snoc_expand_cons_zero, snoc_expand_cons_tail, hq] at h
        simp only [Fin.cons_zero, Fin.cons_succ, ← hLR] at h
        exact h
      exact ⟨h12, h13, h23, hu1, hu2, hu3,
        KimchiForkRealizes.forkValid U H v expand round _ _ _ _ t₁ hr1 (key u₁ q₁ he1),
        KimchiForkRealizes.forkValid U H v expand round _ _ _ _ t₂ hr2 (key u₂ q₂ he2),
        KimchiForkRealizes.forkValid U H v expand round _ _ _ _ t₃ hr3 (key u₃ q₃ he3)⟩

omit [Field F] [AddCommGroup G] [Module F G] in
/-- **Reprogramming at round `m`'s own prefix preserves agreement with the history fixed above
round `m`** — the one genuinely delicate point of `lem:fork_realizes`. Two facts do it: the
earlier round prefixes are `chainAt` of the pinned prefix (`chainAt_prefixes`, used twice, with
the pinned-prefix guard in the middle), and they differ from the reprogrammed point
(`chainAt_ne`). -/
private theorem kimchiRunHistory_update [DecidableEq T] {N : ℕ} {prefixes : Pf → Fin N → T}
    (D : Zcash.Snark.PrefixDecode T N prefixes) {m : ℕ} (hm : m < N) (hmN : m ≤ N)
    {O : T → Pre} {p p' : Pf} {history : Fin m → T × Pre}
    (hhist : Zcash.Snark.RecursiveRunHistory _ m hmN prefixes O p history) (q : Pre)
    (ht' : prefixes p' ⟨m, hm⟩ = prefixes p ⟨m, hm⟩) :
    Zcash.Snark.RecursiveRunHistory _ m hmN prefixes
      (Function.update O (prefixes p ⟨m, hm⟩) q) p' history := by
  intro i
  have hi : (i : ℕ) < m := i.isLt
  have hle : ((⟨(i : ℕ), by omega⟩ : Fin N) : ℕ) ≤ ((⟨m, hm⟩ : Fin N) : ℕ) := by simp
  have hprefix : prefixes p' ⟨(i : ℕ), by omega⟩ = prefixes p ⟨(i : ℕ), by omega⟩ := by
    calc prefixes p' (⟨(i : ℕ), by omega⟩ : Fin N)
        = D.chainAt (prefixes p' ⟨m, hm⟩) ⟨(i : ℕ), by omega⟩ :=
          (D.chainAt_prefixes p' ⟨m, hm⟩ ⟨(i : ℕ), by omega⟩ hle).symm
      _ = D.chainAt (prefixes p ⟨m, hm⟩) ⟨(i : ℕ), by omega⟩ := by rw [ht']
      _ = prefixes p ⟨(i : ℕ), by omega⟩ :=
          D.chainAt_prefixes p ⟨m, hm⟩ ⟨(i : ℕ), by omega⟩ hle
  have hne : (history i).1 ≠ prefixes p ⟨m, hm⟩ := by
    rw [← (hhist i).1, ← D.chainAt_prefixes p ⟨m, hm⟩ ⟨(i : ℕ), by omega⟩ hle]
    refine D.chainAt_ne _ _ ?_
    rw [D.roundOf_prefixes]
    simp
  exact ⟨hprefix.trans (hhist i).1, by rw [Function.update_apply, if_neg hne]; exact (hhist i).2⟩

/-- **The fork returns a realized certificate** (`lem:fork_realizes`): if the fork started at round
`m` on a history-agreeing run returns a certificate, that certificate realizes
`KimchiRunSuffix`.

`hexp_inj` is load-bearing here and nowhere else in the escape/counting layer: the scan is
`Zcash.Snark.nextForkChallenge`, whose freshness test lives in `Pre`, so what it hands back is
three *distinct prechallenges* — while `KimchiForkRealizes` (and through it `KimchiForkValid`)
demands the three *field* challenges `expand qᵢ` be distinct. Injectivity is the only bridge.
Nonzero-ness of those field challenges still comes from `hexp_ne`, not from the scan's own zero
skip. -/
private theorem kimchiForkFrom_realizes [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (hexp_ne : ∀ q : Pre, expand q ≠ 0) (hexp_inj : Function.Injective expand)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes) :
    {e : ℕ} → (m : ℕ) → (hme : m + e = σ.k) → (O : T → Pre) → (p : Pf) →
      (coins : Zcash.Snark.RecursiveForkCoins Pre (e + 1)) → (cert : KimchiForkCert F G e) →
      (history : Fin m → T × Pre) → p = A.run O →
      Zcash.Snark.RecursiveRunHistory _ m (by omega) prefixes O p history →
      (kimchiForkFrom σ b v P expand A proofOf prefixes dec m hme O p coins).output
          = some cert →
      KimchiForkRealizes expand dec.round
        (KimchiRunSuffix σ b v P expand A proofOf prefixes m e hme history) cert
  | 0, m, hme, O, p, .node order child, cert, history, hp, hhist, hout => by
      subst hp
      have hm : m = σ.k := by omega
      subst hm
      rw [kimchiForkFrom] at hout
      simp only [] at hout
      split at hout
      · rename_i hwin
        split at hout
        · simp at hout
        · rename_i q₂ z snd hsc
          simp only [Option.some.injEq] at hout
          subst hout
          obtain ⟨-, hfresh, -⟩ := Zcash.Snark.nextForkChallenge_output_fresh _ [_] hsc
          have hattq := Zcash.Snark.nextForkChallenge_output_attempt _ [_] hsc
          have hq₂₁ : q₂ ≠ O (prefixes (A.run O) (Fin.last σ.k)) := by simpa using hfresh
          split at hattq
          · rename_i hcond
            simp only [Option.some.injEq] at hattq
            have hf := dec.final_eq (A.run O)
            have hf' := dec.final_eq (A.run (Function.update O
              (prefixes (A.run O) (Fin.last σ.k)) q₂))
            rw [hcond.1] at hf'
            refine ⟨fun h => hq₂₁ (hexp_inj h.symm), ?_, ?_⟩
            · exact ⟨O, A.run O, rfl, hwin, hhist, fun i => i.elim0, fun i => i.elim0,
                congrArg Prod.snd hf, congrArg Prod.fst hf, rfl, rfl, rfl⟩
            · refine ⟨Function.update O (prefixes (A.run O) (Fin.last σ.k)) q₂,
                A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q₂), rfl, hcond.2,
                kimchiRunHistory_update D (by omega) (by omega) hhist q₂ hcond.1,
                fun i => i.elim0, fun i => i.elim0,
                congrArg Prod.snd hf', congrArg Prod.fst hf', ?_,
                congrArg Prod.fst hattq, congrArg Prod.snd hattq⟩
              rw [hcond.1, Function.update_self]
          · simp at hattq
      · simp at hout
  | e + 1, m, hme, O, p, .node order child, cert, history, hp, hhist, hout => by
      subst hp
      have hmlt : m < σ.k + 1 := by omega
      rw [kimchiForkFrom] at hout
      simp only [] at hout
      split at hout
      · simp at hout
      · rename_i c₁ hfirst
        split at hout
        · simp at hout
        · rename_i q₂ c₂ rest seen hsecond
          split at hout
          · simp at hout
          · rename_i q₃ c₃ rest₃ hthird
            simp only [Option.some.injEq] at hout
            subst hout
            obtain ⟨-, hfresh₂, hseen₂⟩ := Zcash.Snark.nextForkChallenge_output_fresh _ [_] hsecond
            have hatt₂ := Zcash.Snark.nextForkChallenge_output_attempt _ [_] hsecond
            obtain ⟨-, hfresh₃, -⟩ := Zcash.Snark.nextForkChallenge_output_fresh _ seen hthird
            have hatt₃ := Zcash.Snark.nextForkChallenge_output_attempt _ seen hthird
            rw [hseen₂] at hfresh₃
            have hq₂₁ : q₂ ≠ O (prefixes (A.run O) ⟨m, hmlt⟩) := by simpa using hfresh₂
            have hq₃₂ : q₃ ≠ q₂ ∧ q₃ ≠ O (prefixes (A.run O) ⟨m, hmlt⟩) := by simpa using hfresh₃
            split at hatt₂
            · rename_i hcond₂
              split at hatt₃
              · rename_i hcond₃
                -- histories for the three branches
                have hh₁ : Zcash.Snark.RecursiveRunHistory _ (m + 1) (by omega) prefixes O
                    (A.run O) (Fin.snoc history (prefixes (A.run O) ⟨m, hmlt⟩,
                      O (prefixes (A.run O) ⟨m, hmlt⟩))) := by
                  intro i
                  refine Fin.lastCases ?_ (fun j => ?_) i
                  · rw [Fin.snoc_last]
                    exact ⟨rfl, rfl⟩
                  · rw [Fin.snoc_castSucc]
                    exact hhist j
                have hh₂ : Zcash.Snark.RecursiveRunHistory _ (m + 1) (by omega) prefixes
                    (Function.update O (prefixes (A.run O) ⟨m, hmlt⟩) q₂)
                    (A.run (Function.update O (prefixes (A.run O) ⟨m, hmlt⟩) q₂))
                    (Fin.snoc history (prefixes (A.run O) ⟨m, hmlt⟩, q₂)) := by
                  intro i
                  refine Fin.lastCases ?_ (fun j => ?_) i
                  · rw [Fin.snoc_last]
                    exact ⟨hcond₂, Function.update_self _ _ _⟩
                  · rw [Fin.snoc_castSucc]
                    exact kimchiRunHistory_update D hmlt (by omega) hhist q₂ hcond₂ j
                have hh₃ : Zcash.Snark.RecursiveRunHistory _ (m + 1) (by omega) prefixes
                    (Function.update O (prefixes (A.run O) ⟨m, hmlt⟩) q₃)
                    (A.run (Function.update O (prefixes (A.run O) ⟨m, hmlt⟩) q₃))
                    (Fin.snoc history (prefixes (A.run O) ⟨m, hmlt⟩, q₃)) := by
                  intro i
                  refine Fin.lastCases ?_ (fun j => ?_) i
                  · rw [Fin.snoc_last]
                    exact ⟨hcond₃, Function.update_self _ _ _⟩
                  · rw [Fin.snoc_castSucc]
                    exact kimchiRunHistory_update D hmlt (by omega) hhist q₃ hcond₃ j
                -- the induction hypothesis on each branch
                have hr₁ := kimchiForkFrom_realizes σ b v P expand hexp_ne hexp_inj A proofOf
                  prefixes dec D (m + 1) (by omega) O (A.run O)
                  (child (O (prefixes (A.run O) ⟨m, hmlt⟩))) c₁ _ rfl hh₁ hfirst
                have hr₂ := kimchiForkFrom_realizes σ b v P expand hexp_ne hexp_inj A proofOf
                  prefixes dec D (m + 1) (by omega)
                  (Function.update O (prefixes (A.run O) ⟨m, hmlt⟩) q₂) _ (child q₂) c₂ _ rfl
                  hh₂ hatt₂
                have hr₃ := kimchiForkFrom_realizes σ b v P expand hexp_ne hexp_inj A proofOf
                  prefixes dec D (m + 1) (by omega)
                  (Function.update O (prefixes (A.run O) ⟨m, hmlt⟩) q₃) _ (child q₃) c₃ _ rfl
                  hh₃ hatt₃
                -- move the head of the extended history into the `(ts, qs)` slots
                have step : ∀ (q : Pre) (cc : KimchiForkCert F G e),
                    KimchiForkRealizes expand dec.round
                      (KimchiRunSuffix σ b v P expand A proofOf prefixes (m + 1) e (by omega)
                        (Fin.snoc history (prefixes (A.run O) ⟨m, hmlt⟩, q))) cc →
                    KimchiForkRealizes expand dec.round
                      (fun ts qs => KimchiRunSuffix σ b v P expand A proofOf prefixes m (e + 1)
                        hme history (Fin.cons (prefixes (A.run O) ⟨m, hmlt⟩) ts)
                        (Fin.cons q qs)) cc := by
                  intro q cc hcc
                  refine KimchiForkRealizes.mono expand dec.round ?_ hcc
                  rintro ts qs sg δ c z1 z2
                    ⟨O', p', hp', hwin', hhist', hts, hqs, hsg, hδ, hc, hz1, hz2⟩
                  have hlast := hhist' (Fin.last m)
                  rw [Fin.snoc_last] at hlast
                  refine ⟨O', p', hp', hwin', ?_, ?_, ?_, hsg, hδ, hc, hz1, hz2⟩
                  · intro j
                    have hj := hhist' j.castSucc
                    rw [Fin.snoc_castSucc] at hj
                    exact hj
                  · intro i
                    refine Fin.cases ?_ (fun j => ?_) i
                    · rw [Fin.cons_zero]
                      exact hlast.1
                    · rw [Fin.cons_succ]
                      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hts j
                  · intro i
                    refine Fin.cases ?_ (fun j => ?_) i
                    · rw [Fin.cons_zero, Fin.cons_zero]
                      exact hlast.2
                    · rw [Fin.cons_succ, Fin.cons_succ]
                      exact hqs j
                exact ⟨fun h => hq₂₁ (hexp_inj h.symm), fun h => hq₃₂.2 (hexp_inj h.symm),
                  fun h => hq₃₂.1 (hexp_inj h.symm),
                  hexp_ne _, hexp_ne _, hexp_ne _,
                  prefixes (A.run O) ⟨m, hmlt⟩, O (prefixes (A.run O) ⟨m, hmlt⟩), q₂, q₃,
                  rfl, rfl, rfl, rfl, step _ _ hr₁, step _ _ hr₂, step _ _ hr₃⟩
              · simp at hatt₃
            · simp at hatt₂

/-- **The extractor answers `some`** (`lem:extract_isSome`): on a winning table on which the
completing machine does not escape, the fork returns a certificate, that certificate realizes
`KimchiRunSuffix`, and every run it records satisfies the folded acceptance — by the flat↔folded
bridge — so the validity decision takes the positive branch. -/
private theorem kimchiExtract_isSome_of_not_escape [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Fintype Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (pg : Fin (2 ^ σ.k) → F) (pw : F) (hP : P = commitGen σ.g pg + pw • σ.h)
    (expand : Pre → F) (hexp_ne : ∀ q : Pre, expand q ≠ 0)
    (hexp_inj : Function.Injective expand)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcomplete : coins.Complete)
    (O : T → Pre) (hwin : Wins σ b v P expand proofOf prefixes O (A.run O))
    (hnoescape : ¬ (A.completing prefixes).escapesDuringC
      (kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec D coins) O) :
    (kimchiExtract σ b v P pg pw hP expand A proofOf prefixes dec O coins).isSome := by
  obtain ⟨cert, hcert⟩ := Option.isSome_iff_exists.mp
    (kimchiForkFrom_isSome_of_not_escape_root σ b v P expand A proofOf prefixes dec D coins
      hcomplete O hwin hnoescape)
  have hreal := kimchiForkFrom_realizes σ b v P expand hexp_ne hexp_inj A proofOf prefixes dec D
    0 (Nat.zero_add σ.k) O (A.run O) coins cert Fin.elim0 rfl (fun i => i.elim0) hcert
  -- every run the certificate records satisfies the folded acceptance at the root data
  have hyp : ∀ (ts : Fin σ.k → T) (qs : Fin σ.k → Pre) (sg δ : G) (c z1 z2 : F),
      KimchiRunSuffix σ b v P expand A proofOf prefixes 0 σ.k (Nat.zero_add σ.k) Fin.elim0
          ts qs sg δ c z1 z2 →
        kimchiProverAccept (proverOfProof
          ({ lr := fun j => dec.round (ts j), delta := δ, z1 := z1, z2 := z2, sg := sg } :
            OpeningProof F G σ.k)) σ.g b σ.U σ.h v P (Fin.snoc (fun i => expand (qs i)) c) := by
    rintro ts qs sg δ c z1 z2 ⟨O', p', -, hwin', -, hts, hqs, hsg, hδ, hc, hz1, hz2⟩
    subst hsg; subst hδ; subst hz1; subst hz2; subst hc
    have hidx : ∀ j : Fin σ.k, ts j = prefixes p' j.castSucc := by
      intro j
      rw [← hts j]
      congr 1
      exact Fin.ext (by simp)
    have hproof :
        ({ lr := fun j => dec.round (ts j), delta := (proofOf p').delta,
            z1 := (proofOf p').z1, z2 := (proofOf p').z2,
            sg := (proofOf p').sg } : OpeningProof F G σ.k) = proofOf p' := by
      have hlr : (fun j => dec.round (ts j)) = (proofOf p').lr := by
        funext j
        rw [dec.round_eq p' j, hidx j]
      rw [hlr]
    have hu : (fun i : Fin σ.k => expand (qs i))
        = fun i : Fin σ.k => oracleChallenges σ expand prefixes O' p' i.castSucc := by
      funext i
      rw [← hqs i, hidx i]
      rfl
    rw [hproof, hu]
    exact (verifierAcceptsAt_iff_proverOfProof_accept σ (proofOf p') b v P
      (fun i : Fin σ.k => oracleChallenges σ expand prefixes O' p' i.castSucc)
      (oracleChallenges σ expand prefixes O' p' (Fin.last σ.k))).mp hwin'
  have hvalid : KimchiForkValid σ.U σ.h v σ.g b P cert :=
    KimchiForkRealizes.forkValid σ.U σ.h v expand dec.round σ.g b P _ cert hreal hyp
  rw [kimchiExtract, hcert]
  simp only []
  rw [dif_pos hvalid]
  rfl

end Realization

/-- **THE STATEMENT.** An algebraic, bounded-query adversary that convinces the deployed kimchi
IPA verifier hands over an opening witness — or a computed discrete-log break — except on a set
of oracle tables of measure at most `(Q + k + 1) · 3 / |Pre|`.

The error is the operational query-loss slice: one `3/|Pre|` per adversary query and per forked
round, over the `2¹²⁸` prechallenge domain. Nothing else is assumed: no `hbind` (a binding
violation is *returned*, in the right disjunct), no Fiat–Shamir axiom (the oracle is the model),
and no claim-adaptivity beyond the fixed-claim scope stated in the preamble.

Discharging this deletes `poseidon_fiat_shamir_{vesta,pallas}` from the trust surface without
introducing any replacement axiom. -/
theorem kimchiExtract_failure_measure_le [DecidableEq F] [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (pg : Fin (2 ^ σ.k) → F) (pw : F) (hP : P = commitGen σ.g pg + pw • σ.h)
    -- the challenge map: injective and nonvanishing (theorems at Pasta, `EndoChallenge.lean`)
    (expand : Pre → F) (_hexp_inj : Function.Injective expand) (_hexp_ne : ∀ p, expand p ≠ 0)
    -- the adversary, its query budget, and the transcript data it commits to per run
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (_hQ : A.QueryBound Q)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    -- COMMIT-THEN-CHALLENGE. Without this the theorem is FALSE, by
    -- `verifierAcceptsAt_of_deferred_delta`: an adversary free to pick δ after seeing c
    -- accepts while knowing nothing, so no extractor can succeed against it.
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    -- the round prefixes are distinct and chronological (a *theorem* about our transcript
    -- encoding, by length — never assumed as injectivity of an abstract encoding)
    (_D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    -- the fork tape supplies enough fresh challenges
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (_hcoins : coins.Complete) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | Wins σ b v P expand proofOf prefixes O (A.run O) ∧
          kimchiExtract σ b v P pg pw hP expand A proofOf prefixes dec O coins = none}
      ≤ (Q + σ.k + 1) * (3 / Fintype.card Pre) := by
  -- the failure set is contained in the escape event of the completing machine
  have hsub : {O : T → Pre | Wins σ b v P expand proofOf prefixes O (A.run O) ∧
      kimchiExtract σ b v P pg pw hP expand A proofOf prefixes dec O coins = none}
      ⊆ {O : T → Pre | (A.completing prefixes).escapesDuringC
        (kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec _D coins) O} := by
    rintro O ⟨hwin, hfail⟩
    by_contra hno
    have h := kimchiExtract_isSome_of_not_escape σ b v P pg pw hP expand _hexp_ne _hexp_inj
      A proofOf prefixes dec _D coins _hcoins O hwin hno
    rw [hfail] at h
    simp at h
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  -- and that event is priced by the imported measure lemma: blindness, the per-point bound, and
  -- the completing machine's query budget `Q + (k + 1)`
  refine le_trans (Zcash.Snark.escapesDuringC_measure_le'
    (kimchiForkEscapeSet σ b v P expand A proofOf prefixes dec _D coins)
    (kimchiForkEscapeSet_blind σ b v P expand A proofOf prefixes dec _D coins)
    (kimchiForkEscapeSet_measure_le σ b v P expand _hexp_inj A proofOf prefixes dec _D coins)
    (Zcash.Snark.OracleComp.queryBound_completing prefixes _hQ)) (le_of_eq ?_)
  push_cast
  ring

/-! ## The honest adversary — the anti-vacuity companion

Everything in this section serves `honest_wins_everywhere` below. It has three parts:

* the *algebra*: the one-round fold identity carrying the `U` slot, and the honest
  `KimchiProver` strategy built from an opening witness, accepted along **every** challenge
  vector with nonzero round challenges (`honestProver_accept` — the invariant of the chapter's
  `lem:honest_invariant`);
* the *machine*: `σ.k + 1` nested `.query`s over a final `.pure`, reading the round `j`
  challenge at the prefix `⟨j, (the first j answers)⟩` (`HonestPrefix`), and returning the
  vector of answers it read (`honestAdv`, `honestAdv_run`);
* the *ordering*: the honest proof's `(L, R)` at round `j` and its `(δ, sg)` genuinely are
  functions of the corresponding prefix (`KimchiProver.lrAt_congr`, `leafAt_congr` — the two
  congruences that say `lrAt`/`leafAt` read only the challenges *strictly before* their own),
  which is what supplies the `DecodesFromPrefixes` witness.
-/

section Honest

/-! ### `commitGen` bilinearity and the fold identity, restated

`Forking/Triviality.lean` proves exactly the fold identity we need
(`commitGen_fold_identity`, its `lem:fold_identity_U`), but that file is frozen and the helper
is `private` there, hence invisible. The four bilinearity steps and the split are restated here
verbatim; the proofs are the same three-line `simp only`s. -/

/-- Additivity of `commitGen` in the generators. -/
private theorem commitGen_add_gen {n : ℕ} (g g' : Fin n → G) (a : Fin n → F) :
    commitGen (g + g') a = commitGen g a + commitGen g' a := by
  simp only [commitGen, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- `commitGen` pulls a scalar out of the generators. -/
private theorem commitGen_smul_gen {n : ℕ} (s : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen (s • g) a = s • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (a i) s (g i)

/-- Additivity of `commitGen` in the coefficients. -/
private theorem commitGen_add_coeff {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a + a') = commitGen g a + commitGen g a' := by
  simp only [commitGen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- `commitGen` pulls a scalar out of the coefficients. -/
private theorem commitGen_smul_coeff {n : ℕ} (s : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen g (s • a) = s • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- A length-`2^{d+1}` commitment splits over the two halves. -/
private theorem commitGen_split {d : ℕ} (g : Fin (2 ^ (d + 1)) → G)
    (a : Fin (2 ^ (d + 1)) → F) :
    commitGen g a = commitGen (loHalf g) (loHalf a) + commitGen (hiHalf g) (hiHalf a) := by
  have e : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by rw [pow_succ]; ring
  let φ : Fin (2 ^ d) ⊕ Fin (2 ^ d) ≃ Fin (2 ^ (d + 1)) := finSumFinEquiv.trans (finCongr e)
  simp only [commitGen]
  rw [← φ.sum_comp (fun j => a j • g j), Fintype.sum_sum_type]
  congr 1

/-- **One-round fold identity** (`lem:fold_identity_U`). Committing the honest sub-witness
`loHalf a + u⁻¹ • hiHalf a` against the folded generators `foldHalves g u` recovers the parent
commitment plus the two blinded cross-terms. Stated over the section's module `G`; it is used
at `G` (the generator commitment) *and* at `F` (the inner product) — the two halves of
`lem:fold_identity_U`. -/
private theorem commitGen_fold_identity {d : ℕ}
    (g : Fin (2 ^ (d + 1)) → G) (a : Fin (2 ^ (d + 1)) → F) (u : F) (hu : u ≠ 0) :
    commitGen (foldHalves g u) (loHalf a + u⁻¹ • hiHalf a) =
      commitGen g a + u⁻¹ • commitGen (loHalf g) (hiHalf a)
        + u • commitGen (hiHalf g) (loHalf a) := by
  rw [commitGen_split g a]
  simp only [foldHalves, commitGen_add_gen, commitGen_smul_gen, commitGen_add_coeff,
    commitGen_smul_coeff, smul_add, smul_smul, inv_mul_cancel₀ hu, one_smul]
  abel

/-- `commitGen` over a singleton index family. -/
private theorem commitGen_one (g : Fin (2 ^ 0) → G) (a : Fin (2 ^ 0) → F) :
    commitGen g a = a 0 • g 0 :=
  Fin.sum_univ_one fun i => a i • g i

/-! ### The honest prover strategy and its acceptance -/

/-- **The honest prover strategy from an opening witness.** At each round it commits to the
cross-terms `L = ⟨a_hi, g_lo⟩ + ⟨a_hi, b_lo⟩ • U` and `R = ⟨a_lo, g_hi⟩ + ⟨a_lo, b_hi⟩ • U` —
the `U` components are mandatory, they absorb the inner-product cross terms while the claimed
value `v` stays fixed — and continues on the folded data. The Schnorr layer is taken with zero
blinding: `δ = 0`, `z1 = c · a₀`, `z2 = c · ρ`. -/
private def honestProver (U : G) (ρ : F) :
    {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → (Fin (2 ^ d) → F) → KimchiProver F G d
  | 0, g, _, a => .leaf (g 0) 0 (fun c => (c * a 0, c * ρ))
  | _ + 1, g, bb, a =>
      .node (commitGen (loHalf g) (hiHalf a) + commitGen (loHalf bb) (hiHalf a) • U)
        (commitGen (hiHalf g) (loHalf a) + commitGen (hiHalf bb) (loHalf a) • U)
        (fun u => honestProver U ρ (foldHalves g u) (foldHalves bb u)
          (loHalf a + u⁻¹ • hiHalf a))

/-- **The honest fold invariant** (`lem:honest_invariant`). If the running commitment `P`
satisfies `P + v • U = ⟨a, g⟩ + ⟨a, b⟩ • U + ρ • H`, then the honest strategy is accepted along
*every* challenge vector whose round challenges are nonzero. Note `v` is fixed while `⟨a, b⟩`
folds — that is exactly what the `U` components of `L` and `R` pay for. -/
private theorem honestProver_accept (U H : G) (ρ v : F) :
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

/-! ### The honest machine and its prefixes -/

/-- **The honest prefix type** (`def:honest_prefix`): transcript prefixes of length at most `N`,
the first component recording the round and the second the answers already read. It is finite
and decidably-equal whenever `Pre` is — so the repaired companion below lives inside the very
game the measure bound quantifies over. What matters about it is that the round-`j` read point
is a function of exactly the first `j` answers, so commit-then-challenge is honoured rather
than circumvented. -/
abbrev HonestPrefix (Pre : Type*) (N : ℕ) : Type _ := Σ j : Fin N, Fin (j : ℕ) → Pre

/-- The round-`i` prefix of an answer vector: the round index together with the answers read
strictly before it. -/
private def honestPrefixes {N : ℕ} (p : Fin N → Pre) (i : Fin N) : HonestPrefix Pre N :=
  ⟨i, fun l => p (l.castLE i.isLt.le)⟩

/-- The honest machine, with `j` answers already collected and `m` rounds still to read: query
at `⟨j, (the answers so far)⟩`, then continue; when nothing is left, return the answer vector. -/
private def honestAdvAux (N : ℕ) :
    (m j : ℕ) → j + m = N → (Fin j → Pre) →
      Zcash.Snark.OracleComp (HonestPrefix Pre N) Pre (Fin N → Pre)
  | 0, j, h, acc => .pure fun i => acc (Fin.cast (by omega) i)
  | m + 1, j, h, acc =>
      .query ⟨⟨j, by omega⟩, acc⟩ fun q => honestAdvAux N m (j + 1) (by omega) (Fin.snoc acc q)

/-- The honest machine: `N` nested queries over a final `.pure`. -/
private def honestAdv (N : ℕ) :
    Zcash.Snark.OracleComp (HonestPrefix Pre N) Pre (Fin N → Pre) :=
  honestAdvAux N N 0 (by omega) Fin.elim0

/-- The honest machine makes exactly `m` queries on every path. -/
private theorem honestAdvAux_queryBound (N : ℕ) :
    ∀ (m j : ℕ) (h : j + m = N) (acc : Fin j → Pre),
      (honestAdvAux N m j h acc).QueryBound m := by
  intro m
  induction m with
  | zero => intro j h acc; exact .pure _ _
  | succ m ih =>
      intro j h acc
      exact .query fun q => ih (j + 1) (by omega) (Fin.snoc acc q)

/-- `honestAdv N` is within the budget `N`. -/
private theorem honestAdv_queryBound (N : ℕ) :
    (honestAdv (Pre := Pre) N).QueryBound N :=
  honestAdvAux_queryBound N N 0 (by omega) Fin.elim0

/-- **The run of the honest machine.** The accumulated answers survive, and every later entry of
the output vector is the table's value at exactly the prefix of the answers before it. -/
private theorem honestAdvAux_run (N : ℕ) (O : HonestPrefix Pre N → Pre) :
    ∀ (m j : ℕ) (h : j + m = N) (acc : Fin j → Pre),
      (∀ (i : Fin N) (hi : (i : ℕ) < j), (honestAdvAux N m j h acc).run O i = acc ⟨i, hi⟩) ∧
        (∀ i : Fin N, j ≤ (i : ℕ) →
          (honestAdvAux N m j h acc).run O i
            = O (honestPrefixes ((honestAdvAux N m j h acc).run O) i)) := by
  intro m
  induction m with
  | zero =>
      intro j h acc
      refine ⟨fun i hi => rfl, fun i hi => ?_⟩
      exact absurd i.isLt (by omega)
  | succ m ih =>
      intro j h acc
      have hj : j + 1 + m = N := by omega
      have hjN : j < N := by omega
      set t : HonestPrefix Pre N := ⟨⟨j, hjN⟩, acc⟩ with ht
      have hrun : (honestAdvAux N (m + 1) j h acc).run O
          = (honestAdvAux N m (j + 1) hj (Fin.snoc acc (O t))).run O := rfl
      obtain ⟨A, B⟩ := ih (j + 1) hj (Fin.snoc acc (O t))
      have hlo : ∀ (i : Fin N) (hi : (i : ℕ) < j),
          (honestAdvAux N (m + 1) j h acc).run O i = acc ⟨i, hi⟩ := by
        intro i hi
        rw [hrun, A i (by omega)]
        rw [show (⟨(i : ℕ), Nat.lt_succ_of_lt hi⟩ : Fin (j + 1))
            = Fin.castSucc ⟨(i : ℕ), hi⟩ from rfl, Fin.snoc_castSucc]
      refine ⟨hlo, fun i hi => ?_⟩
      rcases eq_or_lt_of_le hi with heq | hlt
      · -- the current round: the answer is read exactly at `t`, and `t` is the prefix
        have hij : i = ⟨j, hjN⟩ := Fin.ext heq.symm
        subst hij
        have hL : (honestAdvAux N (m + 1) j h acc).run O ⟨j, hjN⟩ = O t := by
          rw [hrun, A ⟨j, hjN⟩ (Nat.lt_succ_self j)]
          rw [show (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) = Fin.last j from rfl, Fin.snoc_last]
        have hR : honestPrefixes ((honestAdvAux N (m + 1) j h acc).run O) (⟨j, hjN⟩ : Fin N)
            = t := by
          rw [ht]
          refine congrArg (Sigma.mk _) ?_
          funext l
          exact hlo _ (by simp)
        rw [hL, hR]
      · rw [hrun]
        exact B i (by omega)

/-- The output of `honestAdv` reads each entry at its own prefix. -/
private theorem honestAdv_run (N : ℕ) (O : HonestPrefix Pre N → Pre) (i : Fin N) :
    (honestAdv N).run O i = O (honestPrefixes ((honestAdv (Pre := Pre) N).run O) i) :=
  (honestAdvAux_run N O N 0 (by omega) Fin.elim0).2 i (Nat.zero_le _)

/-! ### The honest proof is prefix-determined

The two congruences that make the `DecodesFromPrefixes` witness available: `lrAt` at round `j`
reads only the challenges strictly before round `j`, and the leaf's `(sg, δ)` read only the
round challenges — never the Schnorr challenge. -/

/-- Pad a partial challenge vector out to full length by zeros. Only the entries below `m` are
ever consulted (by the two congruences below), so the filler is immaterial; using `0 : F`
avoids needing an inhabitant of `Pre`. -/
private def padChal {m N : ℕ} (w : Fin m → F) : Fin N → F :=
  fun i => if h : (i : ℕ) < m then w ⟨i, h⟩ else 0

omit [Field F] [AddCommGroup G] [Module F G] in
/-- Round `j`'s cross-terms depend only on the challenges strictly before round `j`. -/
private theorem lrAt_congr :
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
private theorem leafAt_congr :
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

end Honest

/-- **The anti-vacuity companion — must land with the theorem above, not after it.** From a
genuine opening witness, an adversary exists that wins on *every* oracle table: it reads its
challenges, folds honestly, and answers the Schnorr challenge. So the win set can have measure
`1`, and an extractor that always returns `none` cannot satisfy the bound.

This is the same discipline as `Forking/Triviality.lean`'s `ipaAcceptV_of_witness`: state
completeness of the acceptance predicate alongside its soundness, so that the soundness theorem
is known to be about a non-empty game.

## Why this signature differs from the one first written (do not "restore" it)

The statement used to quantify universally over the transcript type `T` and the adversary
output type `Pf` — they were section variables — while asserting the *existence* of an
`OracleComp T Pre Pf`. **That statement is false**, and no proof effort could have closed it:

* take `Pf := Empty`. `OracleComp T Pre Pf` has only `pure (a : Pf)` and
  `query (t : T) (k : Pre → OracleComp …)`; a `pure` node needs an element of `Pf` and a
  `query` node needs a strictly smaller element of the same type, so by well-founded induction
  the type is **empty** — while the hypotheses stay satisfiable (`σ.k = 0`, any `a`, `ρ`, and
  `P`, `v` the commitment and inner product they define).
* non-emptiness of `Pf` does not rescue it. At `Pf := Unit` the maps `proofOf`/`prefixes` are
  constant, yet `Wins` demands `(proofOf p).sg = commitGen σ.g (bPolyCoefficients u)` for
  *every* table, and the right-hand side already varies with `u` at `σ.k = 1`
  (there it is `g 0 + u 0 • g 1`).

The content of the statement is that the honest adversary *reads* its challenges and answers as
a function of them, so `Pf` must be rich enough to record the challenge vector and `T` rich
enough that the round-`j` read point determines the first `j` answers. Both are therefore part
of the conclusion here: `Pf := Fin (σ.k + 1) → Pre` and `T := HonestPrefix Pre (σ.k + 1)`.
Everything else is unchanged — same `Wins` (the deployed verifier's own equation), same
`DecodesFromPrefixes` obligation, still a win on *every* table, `QueryBound (σ.k + 1)`.

The one hypothesis added, `hexp_ne`, is the same one the measure bound above already carries
(and a *theorem* at the deployed parameters, `Forking/EndoChallenge.lean`), and it is likewise
forced rather than convenient: a round challenge `u = 0` collapses `foldHalves g u` onto the low
half while leaving the recombination `P + u⁻¹ • L + u • R` untouched, so with `k = 1`, free
generators and `a = (0, 1)` no proof whose `(L, R)` and `(δ, sg)` are prefix-determined can
accept at both `c = 0` and any `c ≠ 0`. Without it the statement is false again. -/
theorem honest_wins_everywhere
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (expand : Pre → F) (hexp_ne : ∀ p, expand p ≠ 0)
    (a : Fin (2 ^ σ.k) → F) (ρ : F) (hopen : openingRelationB σ P b v a ρ) :
    ∃ (A : Zcash.Snark.OracleComp (HonestPrefix Pre (σ.k + 1)) Pre (Fin (σ.k + 1) → Pre))
      (proofOf : (Fin (σ.k + 1) → Pre) → OpeningProof F G σ.k)
      (prefixes : (Fin (σ.k + 1) → Pre) → Fin (σ.k + 1) → HonestPrefix Pre (σ.k + 1))
      (_dec : DecodesFromPrefixes σ proofOf prefixes),
      A.QueryBound (σ.k + 1) ∧
        ∀ O : HonestPrefix Pre (σ.k + 1) → Pre,
          Wins σ b v P expand proofOf prefixes O (A.run O) := by
  obtain ⟨hP1, hv1⟩ := hopen
  set pr : KimchiProver F G σ.k := honestProver σ.U ρ σ.g b a with hpr
  have hcb : commitGen b a = v := by
    rw [hv1]
    simp only [commitGen, innerProduct, smul_eq_mul]
  have hinv : P + v • σ.U = commitGen σ.g a + commitGen b a • σ.U + ρ • σ.h := by
    rw [hcb, ← hP1]
    show commitGen σ.g a + ρ • σ.h + v • σ.U = _
    abel
  refine ⟨honestAdv (σ.k + 1), fun p => pr.proofAt (fun i => expand (p i)), honestPrefixes,
    ⟨fun t => if h : ((t.1 : Fin (σ.k + 1)) : ℕ) < σ.k then
        pr.lrAt (padChal fun l => expand (t.2 l)) ⟨(t.1 : Fin (σ.k + 1)), h⟩ else (0, 0),
     fun t => ((pr.leafAt (padChal fun l => expand (t.2 l))).2.1,
        (pr.leafAt (padChal fun l => expand (t.2 l))).1),
     ?_, ?_⟩,
    honestAdv_queryBound _, ?_⟩
  · -- round `j`'s `(L, R)` is a function of round `j`'s prefix
    intro p j
    have hlt : ((j.castSucc : Fin (σ.k + 1)) : ℕ) < σ.k := by simp
    simp only [honestPrefixes, dif_pos hlt]
    rw [show (⟨(j.castSucc : Fin (σ.k + 1)), hlt⟩ : Fin σ.k) = j from Fin.ext (by simp)]
    refine lrAt_congr pr _ _ j (fun i hi => ?_)
    have hi' : ((i.castSucc : Fin (σ.k + 1)) : ℕ) < ((j.castSucc : Fin (σ.k + 1)) : ℕ) := by
      simpa using hi
    simp only [padChal, dif_pos hi']
    exact congrArg expand (congrArg p (Fin.ext (by simp)))
  · -- `δ` and `sg` are functions of the prefix at which the Schnorr challenge is read
    intro p
    simp only [honestPrefixes]
    have hcong := leafAt_congr pr (fun i => expand (p i))
      (padChal fun l => expand (p (l.castLE (Fin.last σ.k).isLt.le))) (fun i => by
        have hi' : ((i.castSucc : Fin (σ.k + 1)) : ℕ) < ((Fin.last σ.k : Fin (σ.k + 1)) : ℕ) := by
          simp
        simp only [padChal, dif_pos hi']
        exact congrArg expand (congrArg p (Fin.ext (by simp))))
    have h1 : (pr.leafAt (fun i => expand (p i))).1
        = (pr.leafAt (padChal fun l => expand (p (l.castLE (Fin.last σ.k).isLt.le)))).1 :=
      (Prod.ext_iff.mp hcong).1
    have h2 : (pr.leafAt (fun i => expand (p i))).2.1
        = (pr.leafAt (padChal fun l => expand (p (l.castLE (Fin.last σ.k).isLt.le)))).2.1 :=
      (Prod.ext_iff.mp hcong).2
    show ((pr.leafAt (fun i => expand (p i))).2.1, (pr.leafAt (fun i => expand (p i))).1) = _
    rw [h1, h2]
  · -- the honest run wins on every table
    intro O
    set p : Fin (σ.k + 1) → Pre := (honestAdv (σ.k + 1)).run O with hp
    set χ : Fin (σ.k + 1) → F := oracleChallenges σ expand honestPrefixes O p with hχ
    have hchi : (fun i => expand (p i)) = χ := by
      funext i
      rw [hχ, oracleChallenges, hp, honestAdv_run]
    have hsnoc : Fin.snoc (fun i : Fin σ.k => χ i.castSucc) (χ (Fin.last σ.k)) = χ :=
      Fin.snoc_init_self χ
    have hacc : kimchiProverAccept pr σ.g b σ.U σ.h v P χ :=
      honestProver_accept σ.U σ.h ρ v σ.g b a P χ
        (fun i => by rw [hχ, oracleChallenges]; exact hexp_ne _) hinv
    have key := (kimchiProverAccept_iff_verifierAcceptsAt σ pr b v P
      (fun i : Fin σ.k => χ i.castSucc) (χ (Fin.last σ.k))).mp (by rw [hsnoc]; exact hacc)
    rw [hsnoc] at key
    show VerifierAcceptsAt σ (pr.proofAt (fun i => expand (p i))) P
      (innerProduct (bPolyCoefficients fun i : Fin σ.k => χ i.castSucc) b) v
      (χ (Fin.last σ.k)) (fun i : Fin σ.k => χ i.castSucc)
    rw [hchi]
    exact key

end Bulletproof.Forking
