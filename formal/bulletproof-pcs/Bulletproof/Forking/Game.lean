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
  sorry

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

/-- **The anti-vacuity companion — must land with the theorem above, not after it.** From a
genuine opening witness, an adversary exists that wins on *every* oracle table: it reads its
challenges, folds honestly, and answers the Schnorr challenge. So the win set can have measure
`1`, and an extractor that always returns `none` cannot satisfy the bound.

This is the same discipline as `Forking/Triviality.lean`'s `ipaAcceptV_of_witness`: state
completeness of the acceptance predicate alongside its soundness, so that the soundness theorem
is known to be about a non-empty game. -/
theorem honest_wins_everywhere [DecidableEq T]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (expand : Pre → F)
    (a : Fin (2 ^ σ.k) → F) (ρ : F) (_hopen : openingRelationB σ P b v a ρ) :
    ∃ (A : Zcash.Snark.OracleComp T Pre Pf) (proofOf : Pf → OpeningProof F G σ.k)
      (prefixes : Pf → Fin (σ.k + 1) → T) (_dec : DecodesFromPrefixes σ proofOf prefixes),
      A.QueryBound (σ.k + 1) ∧
        ∀ O : T → Pre, Wins σ b v P expand proofOf prefixes O (A.run O) := by
  sorry

end Bulletproof.Forking
