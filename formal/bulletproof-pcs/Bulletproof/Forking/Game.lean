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

The three ingredients of the extractor body, in dependency order: the freshness scan
(`scanFork`), the fork itself (`kimchiForkFrom` — `def:pre_fork`), and the decision procedure
that turns a candidate certificate into a *checked* one (`decideKimchiForkValid` —
`lem:fork_valid_decidable`). Deciding validity inside the extractor is what makes the
extractor's return type its own correctness statement: a `some` answer is valid by
construction, and the analytic content ("`some` happens often enough") stays in the measure
bound.

Two adaptations of ironwood's `recursiveAlgebraicForkFrom` are forced, and are the design:

* **Distinctness is tested in the field, not in `Pre`.** The signature carries `DecidableEq F`
  but not `DecidableEq Pre`, so the scan's freshness test is "`expand u` not already selected".
  That is exactly the distinctness the certificate needs, so no appeal to injectivity of
  `expand` is required inside the extractor.
* **No zero test on `Pre`.** `Pre` carries no algebra. `KimchiForkValid`'s nonzero side
  conditions are about the *field* challenges, and are discharged by the validity decision.

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

/-- Scan a list of prechallenges for the first one whose attempt succeeds and whose *field*
image is fresh, returning the selected challenge and result together with the unscanned suffix
and the grown seen-set, so a second scan resumes where the first stopped. This is ironwood's
`nextForkChallenge` with the two forced adaptations: freshness in `F` through `expand` (there is
no `DecidableEq Pre`) and no zero test (there is no `Zero Pre`). The run counter is dropped —
`kimchiExtract`'s type carries no run budget. -/
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
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes) :
    {e : ℕ} → (m : ℕ) → m + e = σ.k → (O : T → Pre) → (p : Pf) →
      Zcash.Snark.RecursiveForkCoins Pre (e + 1) → Option (KimchiForkCert F G e)
  | 0, _, _, O, p, .node order _ =>
      let j : Fin (σ.k + 1) := Fin.last σ.k
      let t : T := prefixes p j
      let c₁ : F := expand (O t)
      letI := decideWins σ b v P expand proofOf prefixes O p
      if Wins σ b v P expand proofOf prefixes O p then
        let attempt : Pre → Option (F × F) := fun q =>
          let O' := Function.update O t q
          let p' := A.run O'
          letI := decideWins σ b v P expand proofOf prefixes O' p'
          if prefixes p' j = t ∧ Wins σ b v P expand proofOf prefixes O' p' then
            some ((proofOf p').z1, (proofOf p').z2)
          else none
        match scanFork expand attempt [c₁] order with
        | none => none
        | some ((c₂, z), _) =>
            some (.leaf (dec.final t).2 (dec.final t).1
              c₁ (proofOf p).z1 (proofOf p).z2 c₂ z.1 z.2)
      else none
  | e + 1, m, hm, O, p, .node order child =>
      let j : Fin (σ.k + 1) := ⟨m, by omega⟩
      let t : T := prefixes p j
      let u₁ : F := expand (O t)
      match kimchiForkFrom σ b v P expand A proofOf prefixes dec (m + 1) (by omega) O p
          (child (O t)) with
      | none => none
      | some c₁ =>
        let attempt : Pre → Option (KimchiForkCert F G e) := fun q =>
          let O' := Function.update O t q
          let p' := A.run O'
          if prefixes p' j = t then
            kimchiForkFrom σ b v P expand A proofOf prefixes dec (m + 1) (by omega) O' p'
              (child q)
          else none
        match scanFork expand attempt [u₁] order with
        | none => none
        | some ((u₂, c₂), rest, seen) =>
          match scanFork expand attempt seen rest with
          | none => none
          | some ((u₃, c₃), _) =>
              some (.node (dec.round t).1 (dec.round t).2 u₁ u₂ u₃ c₁ c₂ c₃)

end Extractor

/-- **The extractor** (body: Stage 5b). Given the oracle table and the fork tape, run the
adversary, rewind it at the round prefixes, and compute an opening or a relation — ironwood's
`recursiveAlgebraicFork` composed with `kimchiOpeningOrBreak`. `none` is the failure branch the
theorem below bounds.

Its *type* is the correctness statement: a `some` answer carries the witness or the break as
data, with their defining equations. -/
def kimchiExtract [DecidableEq F] [DecidableEq G] [DecidableEq T]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (pg : Fin (2 ^ σ.k) → F) (pw : F) (_hP : P = commitGen σ.g pg + pw • σ.h)
    (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (_dec : DecodesFromPrefixes σ proofOf prefixes)
    (O : T → Pre) (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) :
    Option (OpeningOrBreak σ P b v) :=
  match kimchiForkFrom σ b v P expand A proofOf prefixes _dec 0 (Nat.zero_add σ.k) O
      (A.run O) coins with
  | none => none
  | some cert =>
      letI := decideKimchiForkValid σ.U σ.h v σ.g b P cert
      if h : KimchiForkValid σ.U σ.h v σ.g b P cert then
        some (kimchiOpeningOrBreak σ b v P pg pw _hP cert h)
      else none

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
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre]
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
  sorry

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
