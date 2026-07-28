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

/-! ## Claim stability — the parameter that lifts the fixed-claim scope

The preamble records the fixed claim as *structural*: `P`, `b`, `v` are parameters bound before
the oracle table, and the adversary outputs only an opening proof. Ironwood does not bind its
claim that way. `recursiveAlgebraicForkFrom_realizes`
(`Forking/Adversary/Recursive.lean:796`) carries an abstract predicate `stable` together with an
update law `stable_update`, and threads both through the recursion; the present development
instantiates that parameter at the trivially-true predicate. The generalization consists in
instantiating it at *claim stability* instead, and this section states that instance once,
independently of the fork, so that it can be discharged at the deployed transcript on its own.

The shape of the update law is dictated by the fork and by nothing else: `kimchiForkFrom`
reprograms the table only at `t = prefixes (A.run O) j`, and it only recurses when the
reprogrammed run still reads round `j`'s challenge at `t`. So a chain of exactly such steps is
all that can separate a certificate's runs from the root run, and `PreservedUpdateChain` is that
chain; `claim_eq_of_runSuffix_of_stable` collapses it.

Nothing here mentions the group, the field, or acceptance: stability is a statement about the
transcript schedule, which is why it can be a hypothesis of the game rather than a fact about it.
-/

section ClaimStability

variable {ClaimData : Type*}

/-- **Claim stability** (`def:claim-stable`). A *claim map* `κ` sends an adversary output and an
oracle table to the claim that run opens — the adaptive replacement for the fixed `(b, v, P)` of
the game above. It is **stable** for `A` and `prefixes` when reprogramming the table at the node
`t` where the current run reads round `j`'s challenge leaves the claim unchanged, *provided* the
reprogrammed run still reads round `j` at `t`.

That proviso is not a convenience: it is exactly the guard the fork already tests before it
recurses, so a stable claim map is precisely one whose stability the fork can consume. Project
local because ironwood's `stable_update` (`Recursive.lean:803`) is phrased for an abstract
predicate on `(table, run)` pairs, and we need the claim-map instance as a named `Prop` to hang
the transport lemma and the deployed discharge off. -/
def ClaimStable [DecidableEq T] {N : ℕ} (A : Zcash.Snark.OracleComp T Pre Pf)
    (prefixes : Pf → Fin N → T) (κ : Pf → (T → Pre) → ClaimData) : Prop :=
  ∀ (j : Fin N) (O : T → Pre) (u : Pre),
    prefixes (A.run (Function.update O (prefixes (A.run O) j) u)) j = prefixes (A.run O) j →
      κ (A.run (Function.update O (prefixes (A.run O) j) u))
          (Function.update O (prefixes (A.run O) j) u) = κ (A.run O) O

/-- **Base stability** (`def:base-stable`). The mirror of `ClaimStable` at a *base map*
`uOf : Pf → (T → Pre) → G`, which names the group element at which a run's opening argument is
checked. It is **base-stable** for `A` and `prefixes` when reprogramming the table at the node `t`
where the current run reads round `j`'s challenge leaves the base unchanged, *provided* the
reprogrammed run still reads round `j` at `t` — the same three binders, the same guard and the
same shape of conclusion as `ClaimStable`, with the claim replaced by the base.

It is not merely a copy of that predicate: `ClaimStable` is already stated for an arbitrary
`ClaimData`, so base stability *is* claim stability at `ClaimData := G`, and this definition is
that instance rather than a duplicate of it. The identification is deliberate and load-bearing —
the whole existing stability toolkit (`claim_eq_of_runSuffix_of_stable` for transport along the
fork chain, `claimStable_of_preData` for the sufficient condition in the shape the deployed
transcript supplies it) is `ClaimData`-generic, so it applies to a base map verbatim, with no
transport lemma of its own.

Base stability is the weakest opening-base hypothesis the fork can consume: the guard is again
exactly the test the fork performs before it recurses. It is strictly weaker than "the base
factors through the claimed value" (`baseStable_of_claimStable`), and that matters — the deployed
kimchi base is the group-map image of the *warm* Fiat–Shamir state, continued past the evaluation
challenge, which is not a function of the claim but is stable under the fork's reprogrammings,
all of which happen strictly later in the transcript. -/
def BaseStable [DecidableEq T] {N : ℕ} (A : Zcash.Snark.OracleComp T Pre Pf)
    (prefixes : Pf → Fin N → T) (uOf : Pf → (T → Pre) → G) : Prop :=
  ClaimStable A prefixes uOf

/-- **The tables a subtree's runs can be read at**: those reachable from the root table by a chain
of single-point updates, each at the node where the run of the table it updates reads some round's
challenge, and each preserving that node. This is the relation that `kimchiForkFrom`'s recursion
maintains between the root table and the tables of the runs its certificate records.

Project local: ironwood keeps the chain implicit inside the induction of
`recursiveAlgebraicForkFrom_realizes`, so there is no reusable name upstream for it. -/
inductive PreservedUpdateChain [DecidableEq T] {N : ℕ} (A : Zcash.Snark.OracleComp T Pre Pf)
    (prefixes : Pf → Fin N → T) (O : T → Pre) : (T → Pre) → Prop
  /-- The empty chain: the root table is reachable from itself. -/
  | refl : PreservedUpdateChain A prefixes O O
  /-- One further reprogramming, at the node where the current run reads round `j`'s challenge,
  under the hypothesis that the reprogrammed run still reads round `j` there. -/
  | step {O' : T → Pre} (h : PreservedUpdateChain A prefixes O O') (j : Fin N) (u : Pre)
      (hpres : prefixes (A.run (Function.update O' (prefixes (A.run O') j) u)) j
        = prefixes (A.run O') j) :
      PreservedUpdateChain A prefixes O (Function.update O' (prefixes (A.run O') j) u)

/-- Chains compose. -/
theorem PreservedUpdateChain.trans [DecidableEq T] {N : ℕ}
    {A : Zcash.Snark.OracleComp T Pre Pf} {prefixes : Pf → Fin N → T} {O₁ O₂ O₃ : T → Pre}
    (h₁ : PreservedUpdateChain A prefixes O₁ O₂)
    (h₂ : PreservedUpdateChain A prefixes O₂ O₃) :
    PreservedUpdateChain A prefixes O₁ O₃ := by
  induction h₂ with
  | refl => exact h₁
  | step _ j u hpres ih => exact ih.step j u hpres

/-- **Stability transports along the fork chain** (`lem:claim-stable-transport`). If `κ` is stable
then every table reachable from `O` by a chain of preserved single-point updates carries the same
claim as `O` — the statement the fixed-claim arguments need in order to apply, at one common
claim, to every run a certificate records.

The proof is an induction on the chain with no probabilistic content whatsoever: the whole of the
work is that the chain's ``preserved node'' clause is literally the antecedent of `ClaimStable`. -/
theorem claim_eq_of_runSuffix_of_stable [DecidableEq T] {N : ℕ}
    {A : Zcash.Snark.OracleComp T Pre Pf} {prefixes : Pf → Fin N → T}
    {κ : Pf → (T → Pre) → ClaimData} (hstable : ClaimStable A prefixes κ)
    {O O' : T → Pre} (hchain : PreservedUpdateChain A prefixes O O') :
    κ (A.run O') O' = κ (A.run O) O := by
  induction hchain with
  | refl => rfl
  | step _ j u hpres ih => exact (hstable j _ u hpres).trans ih

/-- **The fixed-claim game is the trivially stable instance.** A constant claim map is stable, so
nothing is lost by stating the game over a stable claim map: the present `kimchiExtract`
statements are recovered at `κ := fun _ _ => c`. -/
theorem claimStable_const [DecidableEq T] {N : ℕ} (A : Zcash.Snark.OracleComp T Pre Pf)
    (prefixes : Pf → Fin N → T) (c : ClaimData) :
    ClaimStable A prefixes (fun _ _ => c) := fun _ _ _ _ => rfl

/-- **Factoring through the claim implies base stability** (`lem:base-stable-of-claim-stable`).
This is the one-step argument the varying-base proofs used to perform inline, isolated as the
recovery instance: if the claim map is stable and the base is a function `uBase` of the claim,
then the base is stable too, because both of its occurrences in the conclusion sit at a run's own
output, where the factorization applies and stability of the claim equates the two claims.

The factorization is demanded **only along `p = A.run O`**, not for all `p`. `BaseStable` names
`uOf` at run outputs and nowhere else, so this is the weakest form that suffices; it is also the
form the run-level statements of the game already carry, and a consumer holding the pointwise
`∀ p O, uOf p O = uBase (κ p O)` supplies `fun O => huOf (A.run O) O`. Stating it pointwise would
make the `_of_runRep` corollaries underivable from it.

`uBase` is taken on the whole claim rather than on a distinguished component: a consumer whose
base is a function of the claimed *value* alone passes `fun c => uBase c.2.1`. -/
theorem baseStable_of_claimStable [DecidableEq T] {N : ℕ}
    {A : Zcash.Snark.OracleComp T Pre Pf} {prefixes : Pf → Fin N → T}
    {κ : Pf → (T → Pre) → ClaimData} (hstable : ClaimStable A prefixes κ)
    {uOf : Pf → (T → Pre) → G} (uBase : ClaimData → G)
    (huOf : ∀ O : T → Pre, uOf (A.run O) O = uBase (κ (A.run O) O)) :
    BaseStable A prefixes uOf := by
  intro j O u hpres
  rw [huOf, huOf, hstable j O u hpres]

/-- **A constant base map is base-stable** (`lem:base-stable-const`). The fixed-base instance:
both sides of the conclusion are the same `U`, so nothing has to be checked. This is what recovers
the fixed-base adaptive-claim bound from the varying-base one at `uOf := fun _ _ => σ.U`, the way
`claimStable_const` recovers the fixed-claim statements. -/
theorem baseStable_const [DecidableEq T] {N : ℕ} (A : Zcash.Snark.OracleComp T Pre Pf)
    (prefixes : Pf → Fin N → T) (U : G) :
    BaseStable A prefixes (fun _ _ => U) := fun _ _ _ _ => rfl

/-- **A sufficient condition for stability, in the shape the deployed transcript supplies it**
(the abstract half of `lem:kimchi-claim-stable`). Suppose the claim is a function `claimOf` of

* some pre-opening data `preData p` of the run, and
* the table's answers at finitely many nodes `preNodes (preData p)` determined by that data,

that the pre-opening data is recoverable from *any* round node the run reads (`hdet` — for the
kimchi transcript, because a node's payload carries the whole absorbed pre-opening state), and
that no such node is itself a node at which a round challenge is read (`hdisj` — for the kimchi
transcript, by the squeeze index, which separates pre-opening nodes from opening-round nodes by a
decidable comparison rather than by an appeal to the absorbed data).

Then `κ` is stable. Project local: it is the abstract skeleton of the deployed discharge, isolated
here so that the transcript-specific facts are the only thing left to prove downstream. -/
theorem claimStable_of_preData [DecidableEq T] {N r : ℕ} {Data : Type*}
    (A : Zcash.Snark.OracleComp T Pre Pf) (prefixes : Pf → Fin N → T)
    (preData : Pf → Data) (preNodes : Data → Fin r → T)
    (claimOf : Data → (Fin r → Pre) → ClaimData) {κ : Pf → (T → Pre) → ClaimData}
    (hκ : ∀ p O, κ p O = claimOf (preData p) (fun i => O (preNodes (preData p) i)))
    (hdet : ∀ (j : Fin N) (p p' : Pf), prefixes p j = prefixes p' j → preData p = preData p')
    (hdisj : ∀ (j : Fin N) (p : Pf) (i : Fin r), preNodes (preData p) i ≠ prefixes p j) :
    ClaimStable A prefixes κ := by
  intro j O u hpres
  have hdata : preData (A.run (Function.update O (prefixes (A.run O) j) u))
      = preData (A.run O) := hdet j _ _ hpres
  rw [hκ, hκ, hdata]
  refine congrArg _ (funext fun i => ?_)
  exact Function.update_of_ne (hdisj j (A.run O) i) _ _

/-- **The adaptive win event**: the verifier accepts the run's proof at the claim *that run*
opens, rather than at a claim fixed before the oracle table was drawn. A claim is the triple
`(b, v, P)`; the commitment's representation is not part of it, since the game needs one only at
the root.

Project local because it is `Wins` with its claim arguments read off a claim map — the shape the
fixed-claim game takes once the claim is allowed to move. -/
def WinsAt (σ : SRS G) (expand : Pre → F) (proofOf : Pf → OpeningProof F G σ.k)
    (prefixes : Pf → Fin (σ.k + 1) → T)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G) (O : T → Pre) (p : Pf) : Prop :=
  Wins σ (κ p O).1 (κ p O).2.1 (κ p O).2.2 expand proofOf prefixes O p

/-- **A stable claim map makes the adaptive and the fixed-claim win events agree along a chain.**

This is the reason the existing fork machinery is already the right machinery for an adaptive but
stable claim, and it isolates what still has to change: the fork's acceptance test at a rewound
run is `Wins` at the *root* claim, whereas the adaptive game asks that run to win at its *own*
claim, and stability identifies the two on precisely the tables the fork reaches. What does not
survive the instantiation is the escape set, which would become table-dependent — that is the
remaining obstruction, and it lives in `kimchiForkEscapeSet`, not here. -/
theorem winsAt_iff_wins_of_stable [DecidableEq T] (σ : SRS G) (expand : Pre → F)
    {A : Zcash.Snark.OracleComp T Pre Pf} {proofOf : Pf → OpeningProof F G σ.k}
    {prefixes : Pf → Fin (σ.k + 1) → T}
    {κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G}
    (hstable : ClaimStable A prefixes κ) {Oroot O : T → Pre}
    (hchain : PreservedUpdateChain A prefixes Oroot O) :
    WinsAt σ expand proofOf prefixes κ O (A.run O) ↔
      Wins σ (κ (A.run Oroot) Oroot).1 (κ (A.run Oroot) Oroot).2.1
        (κ (A.run Oroot) Oroot).2.2 expand proofOf prefixes O (A.run O) := by
  rw [WinsAt, claim_eq_of_runSuffix_of_stable hstable hchain]

end ClaimStability

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

**SUPERSEDED, same caveat.** Since `kimchiExtract_failure_measure_le` became the
`claimStable_const` instance of `kimchiExtract_failure_measure_le_of_stable` (see "The game over
a stable claim map"), this whole fixed-claim escape chain — `kimchiForkGood`,
`kimchiForkGood_update`, `kimchiForkEscapeSet` and its three lemmas,
`kimchiForkFrom_isSome_of_not_escape{,_root}` and `kimchiExtract_isSome_of_not_escape` — is no
longer reached from any root: the live path runs through the `…At` twins, which differ only in
reading the claim off the reprogrammed run. It is left standing because deleting a declaration is
the user's call, not because anything consumes it.
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

Where ironwood carries an abstract `stable` predicate, the relation records instead the
*syntactic* fact from which every such predicate follows: the run's table `O` is reachable from
the root table `Oroot` by a `PreservedUpdateChain`. Acceptance is still tested at the fixed claim
`(b, v, P)`, so this by itself changes nothing about the game; what it adds is the premise of
`claim_eq_of_runSuffix_of_stable`, so that a *stable* claim map can be shown constant along every
run the certificate records (`winsAt_of_kimchiRunSuffix`). At the top level `Oroot` is the
table the extractor was called at, and the chain there is `PreservedUpdateChain.refl`. -/
def KimchiRunSuffix [DecidableEq T] (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf) (proofOf : Pf → OpeningProof F G σ.k)
    (prefixes : Pf → Fin (σ.k + 1) → T) (Oroot : T → Pre) (m e : ℕ) (hme : m + e = σ.k)
    (history : Fin m → T × Pre) :
    (Fin e → T) → (Fin e → Pre) → G → G → F → F → F → Prop :=
  fun ts qs sg δ c z1 z2 => ∃ (O : T → Pre) (p : Pf), p = A.run O ∧
    PreservedUpdateChain A prefixes Oroot O ∧
    Wins σ b v P expand proofOf prefixes O p ∧
    Zcash.Snark.RecursiveRunHistory _ m (by omega) prefixes O p history ∧
    (∀ i : Fin e, prefixes p ⟨m + i.val, by omega⟩ = ts i) ∧
    (∀ i, O (ts i) = qs i) ∧
    (proofOf p).sg = sg ∧ (proofOf p).delta = δ ∧
    expand (O (prefixes p (Fin.last σ.k))) = c ∧
    (proofOf p).z1 = z1 ∧ (proofOf p).z2 = z2

/-- **Every run a subtree represents carries the root run's claim, and wins at it**
(`lem:claim-stable-transport`, read at the fork's own run relation). Let `κ` be a stable claim
map and state the game at the claim `κ` gives the root run. Then each run the relation records
opens *that same* claim, and its proof is accepted at it — so the fixed-claim acceptance test the
fork performs on rewound runs *is* the adaptive one.

This is the payoff of carrying `PreservedUpdateChain` in `KimchiRunSuffix`: the chain is the only
thing that relates a recorded run's table to the root's, and it is available nowhere else — the
existential over `O` in the run relation is otherwise unconstrained. -/
theorem winsAt_of_kimchiRunSuffix [DecidableEq T] {σ : SRS G} {expand : Pre → F}
    {A : Zcash.Snark.OracleComp T Pre Pf} {proofOf : Pf → OpeningProof F G σ.k}
    {prefixes : Pf → Fin (σ.k + 1) → T}
    {κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G}
    (hstable : ClaimStable A prefixes κ) {Oroot : T → Pre} {m e : ℕ} {hme : m + e = σ.k}
    {history : Fin m → T × Pre} {ts : Fin e → T} {qs : Fin e → Pre} {sg δ : G} {c z1 z2 : F}
    (h : KimchiRunSuffix σ (κ (A.run Oroot) Oroot).1 (κ (A.run Oroot) Oroot).2.1
      (κ (A.run Oroot) Oroot).2.2 expand A proofOf prefixes Oroot m e hme history
      ts qs sg δ c z1 z2) :
    ∃ O : T → Pre, PreservedUpdateChain A prefixes Oroot O ∧
      κ (A.run O) O = κ (A.run Oroot) Oroot ∧
      WinsAt σ expand proofOf prefixes κ O (A.run O) := by
  obtain ⟨O, p, hp, hchain, hwin, -, -, -, -, -, -, -, -⟩ := h
  subst hp
  exact ⟨O, hchain, claim_eq_of_runSuffix_of_stable hstable hchain,
    (winsAt_iff_wins_of_stable σ expand hstable hchain).mpr hwin⟩

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
        (KimchiRunSuffix σ b v P expand A proofOf prefixes O m e hme history) cert
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
            · exact ⟨O, A.run O, rfl, .refl, hwin, hhist, fun i => i.elim0, fun i => i.elim0,
                congrArg Prod.snd hf, congrArg Prod.fst hf, rfl, rfl, rfl⟩
            · refine ⟨Function.update O (prefixes (A.run O) (Fin.last σ.k)) q₂,
                A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q₂), rfl,
                PreservedUpdateChain.refl.step (Fin.last σ.k) q₂ hcond.1, hcond.2,
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
                have step : ∀ (Ochild : T → Pre) (q : Pre) (cc : KimchiForkCert F G e),
                    PreservedUpdateChain A prefixes O Ochild →
                    KimchiForkRealizes expand dec.round
                      (KimchiRunSuffix σ b v P expand A proofOf prefixes Ochild (m + 1) e
                        (by omega)
                        (Fin.snoc history (prefixes (A.run O) ⟨m, hmlt⟩, q))) cc →
                    KimchiForkRealizes expand dec.round
                      (fun ts qs => KimchiRunSuffix σ b v P expand A proofOf prefixes O m (e + 1)
                        hme history (Fin.cons (prefixes (A.run O) ⟨m, hmlt⟩) ts)
                        (Fin.cons q qs)) cc := by
                  intro Ochild q cc hch hcc
                  refine KimchiForkRealizes.mono expand dec.round ?_ hcc
                  rintro ts qs sg δ c z1 z2
                    ⟨O', p', hp', hchain', hwin', hhist', hts, hqs, hsg, hδ, hc, hz1, hz2⟩
                  have hlast := hhist' (Fin.last m)
                  rw [Fin.snoc_last] at hlast
                  refine ⟨O', p', hp', hch.trans hchain', hwin', ?_, ?_, ?_, hsg, hδ, hc,
                    hz1, hz2⟩
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
                  rfl, rfl, rfl, rfl,
                  step _ _ _ PreservedUpdateChain.refl hr₁,
                  step _ _ _ (PreservedUpdateChain.refl.step ⟨m, hmlt⟩ q₂ hcond₂) hr₂,
                  step _ _ _ (PreservedUpdateChain.refl.step ⟨m, hmlt⟩ q₃ hcond₃) hr₃⟩
              · simp at hatt₃
            · simp at hatt₂

/-- **A returned certificate is a valid one, so the extractor answers `some`** — the half of
`lem:extract_isSome` that says nothing about escape: the certificate realizes `KimchiRunSuffix`,
every run it records satisfies the folded acceptance (by the flat↔folded bridge), and so the
validity decision inside `kimchiExtract` takes the positive branch.

Project local, and split out of `kimchiExtract_isSome_of_not_escape` because it is claim-agnostic:
the adaptive game (`kimchiExtract_isSome_of_not_escape_of_stable`) reaches the same fork output by
a different route and reuses this step verbatim. -/
private theorem kimchiExtract_isSome_of_fork_isSome [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (pg : Fin (2 ^ σ.k) → F) (pw : F) (hP : P = commitGen σ.g pg + pw • σ.h)
    (expand : Pre → F) (hexp_ne : ∀ q : Pre, expand q ≠ 0)
    (hexp_inj : Function.Injective expand)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (O : T → Pre)
    (hfork : (kimchiForkFrom σ b v P expand A proofOf prefixes dec 0 (Nat.zero_add σ.k) O
      (A.run O) coins).output.isSome) :
    (kimchiExtract σ b v P pg pw hP expand A proofOf prefixes dec O coins).isSome := by
  obtain ⟨cert, hcert⟩ := Option.isSome_iff_exists.mp hfork
  have hreal := kimchiForkFrom_realizes σ b v P expand hexp_ne hexp_inj A proofOf prefixes dec D
    0 (Nat.zero_add σ.k) O (A.run O) coins cert Fin.elim0 rfl (fun i => i.elim0) hcert
  -- every run the certificate records satisfies the folded acceptance at the root data
  have hyp : ∀ (ts : Fin σ.k → T) (qs : Fin σ.k → Pre) (sg δ : G) (c z1 z2 : F),
      KimchiRunSuffix σ b v P expand A proofOf prefixes O 0 σ.k (Nat.zero_add σ.k) Fin.elim0
          ts qs sg δ c z1 z2 →
        kimchiProverAccept (proverOfProof
          ({ lr := fun j => dec.round (ts j), delta := δ, z1 := z1, z2 := z2, sg := sg } :
            OpeningProof F G σ.k)) σ.g b σ.U σ.h v P (Fin.snoc (fun i => expand (qs i)) c) := by
    rintro ts qs sg δ c z1 z2 ⟨O', p', -, -, hwin', -, hts, hqs, hsg, hδ, hc, hz1, hz2⟩
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
    (kimchiExtract σ b v P pg pw hP expand A proofOf prefixes dec O coins).isSome :=
  kimchiExtract_isSome_of_fork_isSome σ b v P pg pw hP expand hexp_ne hexp_inj A proofOf prefixes
    dec D coins O
    (kimchiForkFrom_isSome_of_not_escape_root σ b v P expand A proofOf prefixes dec D coins
      hcomplete O hwin hnoescape)

end Realization

/-! ## The game over a stable claim map

Everything above states the game at a claim bound *before* the oracle table. This section
restates the three moves of `kimchiExtract_failure_measure_le` with the claim read off the run
itself, `κ (A.run O) O`, and a `ClaimStable` hypothesis in place of the structural fixing.

**The one place the generalization is not free, and how it is paid.** The naive adaptive escape
set — `kimchiForkEscapeSet` with `(b, v, P) := κ (A.run O) O` at the table `O` the set is
evaluated at — is **not blind**: `escapesDuringC_measure_le'` demands
`esc t (Function.update O t q) = esc t O` for *every* `t`, `O`, `q`, whereas `ClaimStable` gives
`κ (A.run (Function.update O t q)) (Function.update O t q) = κ (A.run O) O` only when `t` is the
node at which the current run reads some round's challenge *and* the reprogrammed run still reads
that round there. So the blueprint's reading of the second move ("the escape set's blindness does
not mention the claim") is false as stated for that formulation, and it is what forces the shape
below.

The repair is to read the claim off the *reprogrammed* run rather than off the outer table:
`kimchiForkGoodAt` consults `κ` at `Function.update O t q`, exactly the table its own success
condition is about. Then the whole predicate is a function of `Function.update O t q` alone, and
blindness is `Function.update_idem` — the same one-line argument as the fixed-claim case, with no
appeal to stability at all. Blindness and the per-point triple bound are therefore genuinely
claim-insensitive, and the corrected reading of the blueprint's sentence is: *the escape set may
mention the claim only through the table it is already reprogramming*.

Stability is then spent in the **first** move instead, at precisely two points inside
`kimchiForkFromAt_isSome_of_not_escape`: the cached branch (where the run's own claim is the root
claim by hypothesis) and the scan (where the guard `prefixes (A.run (update O t q)) j = t` is
literally the antecedent of `ClaimStable`, so the reprogrammed run's claim is the root claim too).
That is the whole content of the generalization.
-/

section AdaptiveClaim

/-- **The round's local success predicate, read at the run's own claim** — the adaptive twin of
`kimchiForkGood`. At depth `0` (the Schnorr round) the residual is `WinsAt`, at depth `e + 1` it
is that the fork started at round `m + 1` *for the reprogrammed run's own claim* returns.

Project local, and deliberately not `kimchiForkGood` at a claim argument: the claim is consulted
at `Function.update O t q`, never at `O`, which is exactly what makes
`kimchiForkEscapeSetAt_blind` provable without any stability hypothesis. -/
private def kimchiForkGoodAt [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G) (m : ℕ) :
    {e : ℕ} → m + e = σ.k → (t : T) → (O : T → Pre) →
      (Pre → Zcash.Snark.RecursiveForkCoins Pre e) → Pre → Prop
  | 0, he, t, O, _, q =>
      prefixes (A.run (Function.update O t q)) ⟨m, by omega⟩ = t ∧
        WinsAt σ expand proofOf prefixes κ (Function.update O t q)
          (A.run (Function.update O t q))
  | _ + 1, he, t, O, child, q =>
      prefixes (A.run (Function.update O t q)) ⟨m, by omega⟩ = t ∧
        (kimchiForkFrom σ
            (κ (A.run (Function.update O t q)) (Function.update O t q)).1
            (κ (A.run (Function.update O t q)) (Function.update O t q)).2.1
            (κ (A.run (Function.update O t q)) (Function.update O t q)).2.2
            expand A proofOf prefixes dec (m + 1) (by omega)
            (Function.update O t q) (A.run (Function.update O t q)) (child q)).output.isSome

/-- Reprogramming at `t` does not change the adaptive success predicate: like its fixed-claim
twin it only ever consults tables of the form `Function.update _ t _`, and now that includes the
claim it is read at. -/
private theorem kimchiForkGoodAt_update [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G) (m : ℕ) :
    {e : ℕ} → (he : m + e = σ.k) → (t : T) → (O : T → Pre) → (q : Pre) →
      (child : Pre → Zcash.Snark.RecursiveForkCoins Pre e) →
      kimchiForkGoodAt σ expand A proofOf prefixes dec κ m he t (Function.update O t q) child
        = kimchiForkGoodAt σ expand A proofOf prefixes dec κ m he t O child
  | 0, _, _, _, _, _ => by funext q'; simp only [kimchiForkGoodAt, Function.update_idem]
  | _ + 1, _, _, _, _, _ => by funext q'; simp only [kimchiForkGoodAt, Function.update_idem]

/-- **The operational escape set over a claim map** — `kimchiForkEscapeSet` with its round
predicate replaced by the adaptive one. Note that no claim appears in the signature: the set is a
function of `κ` alone, so it is a legitimate `esc : T → (T → Pre) → Set Pre` for
`escapesDuringC_measure_le'`, which the naive "claim read at the outer table" formulation is
not. -/
noncomputable def kimchiForkEscapeSetAt [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (t : T) (O : T → Pre) : Set Pre :=
  match root.nodeAt
      ((List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt t i)).take (D.roundOf t)) with
  | none => ∅
  | some node =>
      if hd : D.roundOf t + node.depth = σ.k then
        Zcash.Snark.recursiveForkEscape
          (kimchiForkGoodAt σ expand A proofOf prefixes dec κ (D.roundOf t) hd t O node.child)
      else ∅

/-- **The adaptive escape set is blind at its own point** — and, as the section preamble records,
this is provable with *no* stability hypothesis precisely because `kimchiForkGoodAt` reads the
claim at the reprogrammed table. -/
theorem kimchiForkEscapeSetAt_blind [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (t : T) (O : T → Pre) (q : Pre) :
    kimchiForkEscapeSetAt σ expand A proofOf prefixes dec D κ root t (Function.update O t q)
      = kimchiForkEscapeSetAt σ expand A proofOf prefixes dec D κ root t O := by
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
  rw [kimchiForkEscapeSetAt, kimchiForkEscapeSetAt, hpath]
  cases hnode : root.nodeAt
      ((List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt t i)).take (D.roundOf t)) with
  | none => rfl
  | some node =>
      by_cases hd : D.roundOf t + node.depth = σ.k
      · simp only [dif_pos hd]
        rw [kimchiForkGoodAt_update]
      · simp only [dif_neg hd]

/-- **Each adaptive escape set has measure at most `3 / |Pre|`** — verbatim the fixed-claim
argument, since `recursiveForkEscape_subset_triple` is a statement about an arbitrary
predicate. -/
theorem kimchiForkEscapeSetAt_measure_le [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Fintype Pre] [Nonempty Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (t : T) (O : T → Pre) :
    (PMF.uniformOfFintype Pre).toOuterMeasure
        (kimchiForkEscapeSetAt σ expand A proofOf prefixes dec D κ root t O)
      ≤ 3 / Fintype.card Pre := by
  rw [kimchiForkEscapeSetAt]
  cases hnode : root.nodeAt
      ((List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt t i)).take (D.roundOf t)) with
  | none => simp
  | some node =>
      by_cases hd : D.roundOf t + node.depth = σ.k
      · simp only [dif_pos hd]
        obtain ⟨a, c, hsub⟩ := Zcash.Snark.recursiveForkEscape_subset_triple
          (kimchiForkGoodAt σ expand A proofOf prefixes dec κ (D.roundOf t) hd t O node.child)
        exact Zcash.Snark.uniformOfFintype_toOuterMeasure_triple_le hsub
      · simp only [dif_neg hd]
        simp

/-- **At a real round prefix the adaptive escape set is the local one** — the twin of
`kimchiForkEscapeSet_prefix`, proved by the same rewriting of the tape path. -/
theorem kimchiForkEscapeSetAt_prefix [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1))
    {e m : ℕ} (hmk : m + (e + 1) = σ.k + 1) (O : T → Pre) (p : Pf) (order : List Pre)
    (child : Pre → Zcash.Snark.RecursiveForkCoins Pre e)
    (hreach : Zcash.Snark.RecursiveForkReached (σ.k + 1) prefixes root m hmk O p
      (.node order child)) :
    kimchiForkEscapeSetAt σ expand A proofOf prefixes dec D κ root
        (prefixes p ⟨m, by omega⟩) O
      = Zcash.Snark.recursiveForkEscape
        (kimchiForkGoodAt σ expand A proofOf prefixes dec κ m (by omega)
          (prefixes p ⟨m, by omega⟩) O child) := by
  rw [kimchiForkEscapeSetAt,
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

/-- **Non-escape forces the fork to return, over a stable claim map.** The adaptive twin of
`kimchiForkFrom_isSome_of_not_escape`, and the only declaration in this section where
`ClaimStable` is used.

The fork itself is unchanged: it is still run at *one* claim `(b, v, P)`, carried here as the
hypothesis `hcl : κ (A.run O) O = (b, v, P)` (at the top level `(b, v, P)` is the root run's own
claim, and `hcl` is `rfl`). Stability enters exactly twice, and both times through the guard
`prefixes (A.run (Function.update O t q)) j = t` that the adaptive success predicate carries:
once to see that the cached branch's own claim is `(b, v, P)`, and once, inside `himp`, to see
that each scanned reprogrammed run's claim is `(b, v, P)` as well — so the fork's fixed-claim
attempt succeeds wherever the adaptive predicate holds. No chain induction is needed: the
recursive call is at the *same* table, so `hcl` is simply carried. -/
private theorem kimchiForkFromAt_isSome_of_not_escape [DecidableEq F] [DecidableEq G]
    [DecidableEq T] [Fintype Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G) (hstable : ClaimStable A prefixes κ)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) :
    {e : ℕ} → (m : ℕ) → (hme : m + e = σ.k) → (O : T → Pre) → (p : Pf) →
      (coins : Zcash.Snark.RecursiveForkCoins Pre (e + 1)) →
      p = A.run O →
      κ (A.run O) O = (b, v, P) →
      Zcash.Snark.RecursiveForkReached (σ.k + 1) prefixes root m (by omega) O p coins →
      coins.Complete → Wins σ b v P expand proofOf prefixes O p →
      ¬ (A.completing prefixes).escapesDuringC
          (kimchiForkEscapeSetAt σ expand A proofOf prefixes dec D κ root) O →
      (kimchiForkFrom σ b v P expand A proofOf prefixes dec m hme O p coins).output.isSome
  | 0, m, hme, O, p, .node order child, hp, hcl, hreach, hcomplete, hwin, hnoescape => by
      subst hp
      have hm : m = σ.k := by omega
      subst hm
      have hesc : kimchiForkEscapeSetAt σ expand A proofOf prefixes dec D κ root
            (prefixes (A.run O) (Fin.last σ.k)) O
          = Zcash.Snark.recursiveForkEscape (kimchiForkGoodAt σ expand A proofOf prefixes dec κ
            σ.k (by omega) (prefixes (A.run O) (Fin.last σ.k)) O child) :=
        kimchiForkEscapeSetAt_prefix σ expand A proofOf prefixes dec D κ root
          (e := 0) (m := σ.k) (by omega) O (A.run O) order child hreach
      have hlocal : O (prefixes (A.run O) (Fin.last σ.k)) ∉
          Zcash.Snark.recursiveForkEscape (kimchiForkGoodAt σ expand A proofOf prefixes dec κ
            σ.k (by omega) (prefixes (A.run O) (Fin.last σ.k)) O child) := by
        intro hu
        exact hnoescape (Zcash.Snark.OracleComp.escapesDuringC_completing _ prefixes
          (j := Fin.last σ.k) (by rw [hesc]; exact hu))
      have hupd : Function.update O (prefixes (A.run O) (Fin.last σ.k))
          (O (prefixes (A.run O) (Fin.last σ.k))) = O := by
        funext x
        by_cases hx : x = prefixes (A.run O) (Fin.last σ.k)
        · subst hx; simp
        · simp [hx]
      have hgood₁ : kimchiForkGoodAt σ expand A proofOf prefixes dec κ σ.k (by omega)
          (prefixes (A.run O) (Fin.last σ.k)) O child
          (O (prefixes (A.run O) (Fin.last σ.k))) := by
        rw [kimchiForkGoodAt, hupd]
        refine ⟨rfl, ?_⟩
        show Wins σ (κ (A.run O) O).1 (κ (A.run O) O).2.1 (κ (A.run O) O).2.2
          expand proofOf prefixes O (A.run O)
        rw [hcl]
        exact hwin
      have hthree : Zcash.Snark.ThreeForkSuccess
          (kimchiForkGoodAt σ expand A proofOf prefixes dec κ σ.k (by omega)
            (prefixes (A.run O) (Fin.last σ.k)) O child) := by
        by_contra hno
        exact hlocal (by rw [Zcash.Snark.recursiveForkEscape, if_neg hno]; exact Or.inr hgood₁)
      rw [kimchiForkFrom, if_pos hwin]
      simp only []
      split
      · rename_i hnone
        refine absurd hnone (nextFork_fst_ne_none _ order hcomplete.1 _ _ hthree ?_)
        intro q hq
        rw [kimchiForkGoodAt] at hq
        have hcl' : κ (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q))
            (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q) = (b, v, P) :=
          (hstable (Fin.last σ.k) O q hq.1).trans hcl
        split
        · rfl
        · rename_i hno
          refine absurd ⟨hq.1, ?_⟩ hno
          have h2 : Wins σ
              (κ (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q))
                (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q)).1
              (κ (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q))
                (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q)).2.1
              (κ (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q))
                (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q)).2.2
              expand proofOf prefixes (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q)
              (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q)) := hq.2
          rw [hcl'] at h2
          exact h2
      · rfl
  | e + 1, m, hme, O, p, .node order child, hp, hcl, hreach, hcomplete, hwin, hnoescape => by
      subst hp
      have hesc : kimchiForkEscapeSetAt σ expand A proofOf prefixes dec D κ root
            (prefixes (A.run O) ⟨m, by omega⟩) O
          = Zcash.Snark.recursiveForkEscape (kimchiForkGoodAt σ expand A proofOf prefixes dec κ m
            (by omega) (prefixes (A.run O) ⟨m, by omega⟩) O child) :=
        kimchiForkEscapeSetAt_prefix σ expand A proofOf prefixes dec D κ root
          (e := e + 1) (m := m) (by omega) O (A.run O) order child hreach
      have hlocal : O (prefixes (A.run O) ⟨m, by omega⟩) ∉
          Zcash.Snark.recursiveForkEscape (kimchiForkGoodAt σ expand A proofOf prefixes dec κ m
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
      have hfirst : (kimchiForkFrom σ b v P expand A proofOf prefixes dec (m + 1) (by omega) O
          (A.run O) (child (O (prefixes (A.run O) ⟨m, by omega⟩)))).output.isSome :=
        kimchiForkFromAt_isSome_of_not_escape σ b v P expand A proofOf prefixes dec D κ hstable
          root (m + 1) (by omega) O (A.run O)
          (child (O (prefixes (A.run O) ⟨m, by omega⟩)))
          rfl hcl hreachChild (hcomplete.2 _) hwin hnoescape
      have hgood₁ : kimchiForkGoodAt σ expand A proofOf prefixes dec κ m (by omega)
          (prefixes (A.run O) ⟨m, by omega⟩) O child (O (prefixes (A.run O) ⟨m, by omega⟩)) := by
        rw [kimchiForkGoodAt, hupd, hcl]
        exact ⟨rfl, hfirst⟩
      have hthree : Zcash.Snark.ThreeForkSuccess
          (kimchiForkGoodAt σ expand A proofOf prefixes dec κ m (by omega)
            (prefixes (A.run O) ⟨m, by omega⟩) O child) := by
        by_contra hno
        exact hlocal (by rw [Zcash.Snark.recursiveForkEscape, if_neg hno]; exact Or.inr hgood₁)
      have himp : ∀ q : Pre,
          kimchiForkGoodAt σ expand A proofOf prefixes dec κ m (by omega)
              (prefixes (A.run O) ⟨m, by omega⟩) O child q →
            (if prefixes (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q))
                  (⟨m, by omega⟩ : Fin (σ.k + 1)) = prefixes (A.run O) ⟨m, by omega⟩ then
                kimchiForkFrom σ b v P expand A proofOf prefixes dec (m + 1) (by omega)
                  (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)
                  (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)) (child q)
              else { output := none, runs := 1 }).output.isSome := by
        intro q hq
        rw [kimchiForkGoodAt] at hq
        have hcl' : κ (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q))
            (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q) = (b, v, P) :=
          (hstable ⟨m, by omega⟩ O q hq.1).trans hcl
        split
        · have h2 := hq.2
          rw [hcl'] at h2
          exact h2
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

/-- **Root form of the adaptive non-escape lemma.** The fork is started at the root run's own
claim, so the claim hypothesis is `rfl` (up to the structure eta of the claim triple) and the
tape is reached by definition. -/
private theorem kimchiForkFromAt_isSome_of_not_escape_root [DecidableEq F] [DecidableEq G]
    [DecidableEq T] [Fintype Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G) (hstable : ClaimStable A prefixes κ)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcomplete : coins.Complete)
    (O : T → Pre) (hwin : WinsAt σ expand proofOf prefixes κ O (A.run O))
    (hnoescape : ¬ (A.completing prefixes).escapesDuringC
      (kimchiForkEscapeSetAt σ expand A proofOf prefixes dec D κ coins) O) :
    (kimchiForkFrom σ (κ (A.run O) O).1 (κ (A.run O) O).2.1 (κ (A.run O) O).2.2 expand A
      proofOf prefixes dec 0 (Nat.zero_add σ.k) O (A.run O) coins).output.isSome := by
  refine kimchiForkFromAt_isSome_of_not_escape σ (κ (A.run O) O).1 (κ (A.run O) O).2.1
    (κ (A.run O) O).2.2 expand A proofOf prefixes dec D κ hstable coins
    0 (Nat.zero_add σ.k) O (A.run O) coins rfl rfl ?_ hcomplete hwin hnoescape
  cases coins with
  | node order child => rfl

/-- **The extractor answers `some`, over a stable claim map** (`thm:adaptive-failure-measure`,
first move). On a table where the run wins *at its own claim* and the completing machine does not
escape the adaptive escape set, the extractor run at that claim returns.

This is the adaptive twin of `kimchiExtract_isSome_of_not_escape`: only the route to the fork's
`isSome` changes: the conversion of a returned certificate into a valid one
(`kimchiExtract_isSome_of_fork_isSome`) is claim-agnostic and is reused verbatim. -/
theorem kimchiExtract_isSome_of_not_escape_of_stable [DecidableEq F] [DecidableEq G]
    [DecidableEq T] [Fintype Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F) (hexp_ne : ∀ q : Pre, expand q ≠ 0)
    (hexp_inj : Function.Injective expand)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (rep : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F)
    (hrep : ∀ (p : Pf) (O : T → Pre),
      (κ p O).2.2 = commitGen σ.g (rep p O).1 + (rep p O).2 • σ.h)
    (hstable : ClaimStable A prefixes κ)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcomplete : coins.Complete)
    (O : T → Pre) (hwin : WinsAt σ expand proofOf prefixes κ O (A.run O))
    (hnoescape : ¬ (A.completing prefixes).escapesDuringC
      (kimchiForkEscapeSetAt σ expand A proofOf prefixes dec D κ coins) O) :
    (kimchiExtract σ (κ (A.run O) O).1 (κ (A.run O) O).2.1 (κ (A.run O) O).2.2
      (rep (A.run O) O).1 (rep (A.run O) O).2 (hrep (A.run O) O)
      expand A proofOf prefixes dec O coins).isSome :=
  kimchiExtract_isSome_of_fork_isSome σ (κ (A.run O) O).1 (κ (A.run O) O).2.1
    (κ (A.run O) O).2.2 (rep (A.run O) O).1 (rep (A.run O) O).2 (hrep (A.run O) O)
    expand hexp_ne hexp_inj A proofOf prefixes dec D coins O
    (kimchiForkFromAt_isSome_of_not_escape_root σ expand A proofOf prefixes dec D κ hstable
      coins hcomplete O hwin hnoescape)

/-! ### The transcript-derived base varies with the run

Everything above still fixes the *setup* `σ` before the oracle table, and that is not a
notational convenience: `σ` carries the base `U` against which the opening argument's Schnorr
equation is checked, and the extractor's return type mentions it. In the deployed kimchi verifier
`U` is derived from the run's own transcript — the group-map image of a Fiat–Shamir squeeze — and
the transcript is adversary output, so the base at which a run is checked, and at which its
extraction runs, is a function of the oracle table.

The repair is exactly the one that lifted the fixed claim: make the varying datum an argument of
the statement and read it, like the claim, at the **reprogrammed** table inside the escape set,
where blindness is again `Function.update_idem`. What the tower then needs of the base is not that
it be derived from any particular datum but only `BaseStable` — that the fork's own reprogrammings
do not move it.

Only the base varies. The generators, the blinding base and the round count are the sampled
setup's, so the varying setup is the record update `srsAt` of a fixed `σ` and every *type-level*
occurrence (`Fin (2 ^ σ.k)`, `OpeningProof F G σ.k`, `Fin (σ.k + 1)`,
`RecursiveForkCoins Pre (σ.k + 1)`) is unchanged. The one thing the elaborator does *not* accept
verbatim is `DecodesFromPrefixes`: it is a structure whose first parameter is the setup itself,
so a `dec` at `σ` is not a `dec` at `srsAt …` even though every field mentions `σ` only through
`σ.k`. `DecodesFromPrefixes.setBase` is that (definitionally trivial) transport.
-/

/-- **The run's setup** (`def:srs-at`): the fixed sampled setup `σ` with its base replaced by the
run's own `uOf p O`. Generators, blinding base and round count are `σ`'s, so every type-level
occurrence of the setup is unchanged.

Project local: `SRS` has no such "with base" combinator upstream, and naming the record update is
what lets the tower below quantify over the varying base without a dependent transport. -/
def srsAt (σ : SRS G) (uOf : Pf → (T → Pre) → G) (p : Pf) (O : T → Pre) : SRS G :=
  { σ with U := uOf p O }

/-- The round count of the run's setup is the sampled setup's — by `rfl`, and stated so that the
`omega` goals of the fork's arithmetic can be discharged after a `show`. -/
@[simp] theorem srsAt_k (σ : SRS G) (uOf : Pf → (T → Pre) → G) (p : Pf) (O : T → Pre) :
    (srsAt σ uOf p O).k = σ.k := rfl

/-- The committing generators of the run's setup are the sampled setup's. Stated for the consumer,
whose commitment hypotheses are phrased at `σ`. -/
@[simp] theorem srsAt_g (σ : SRS G) (uOf : Pf → (T → Pre) → G) (p : Pf) (O : T → Pre) :
    (srsAt σ uOf p O).g = σ.g := rfl

/-- The blinding base of the run's setup is the sampled setup's. -/
@[simp] theorem srsAt_h (σ : SRS G) (uOf : Pf → (T → Pre) → G) (p : Pf) (O : T → Pre) :
    (srsAt σ uOf p O).h = σ.h := rfl

/-- The base of the run's setup is the run's own — the single component that moves. -/
@[simp] theorem srsAt_U (σ : SRS G) (uOf : Pf → (T → Pre) → G) (p : Pf) (O : T → Pre) :
    (srsAt σ uOf p O).U = uOf p O := rfl

/-- **Commit-then-challenge does not mention the base.** Every field of `DecodesFromPrefixes`
mentions the setup only through its round count, so a decoding structure at `σ` is one at any
rebasing of `σ`. Needed because the structure's *parameter* is the setup itself, which the
elaborator will not identify across a differing base. -/
def DecodesFromPrefixes.setBase {σ : SRS G} {proofOf : Pf → OpeningProof F G σ.k}
    {prefixes : Pf → Fin (σ.k + 1) → T} (dec : DecodesFromPrefixes σ proofOf prefixes) (u : G) :
    DecodesFromPrefixes { σ with U := u } proofOf prefixes where
  round := dec.round
  final := dec.final
  round_eq := dec.round_eq
  final_eq := dec.final_eq

/-- **The round's local success predicate at the run's own setup** — `kimchiForkGoodAt` with every
value-level occurrence of the setup replaced by `srsAt`, read (like the claim) at the reprogrammed
table `Function.update O t q` and never at `O`. That is what keeps
`kimchiForkEscapeSetAtU_blind` a one-line `Function.update_idem` argument. -/
private def kimchiForkGoodAtU [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (uOf : Pf → (T → Pre) → G) (m : ℕ) :
    {e : ℕ} → m + e = σ.k → (t : T) → (O : T → Pre) →
      (Pre → Zcash.Snark.RecursiveForkCoins Pre e) → Pre → Prop
  | 0, he, t, O, _, q =>
      prefixes (A.run (Function.update O t q)) ⟨m, by omega⟩ = t ∧
        WinsAt (srsAt σ uOf (A.run (Function.update O t q)) (Function.update O t q))
          expand proofOf prefixes κ (Function.update O t q) (A.run (Function.update O t q))
  | _ + 1, he, t, O, child, q =>
      prefixes (A.run (Function.update O t q)) ⟨m, by omega⟩ = t ∧
        (kimchiForkFrom
            (srsAt σ uOf (A.run (Function.update O t q)) (Function.update O t q))
            (κ (A.run (Function.update O t q)) (Function.update O t q)).1
            (κ (A.run (Function.update O t q)) (Function.update O t q)).2.1
            (κ (A.run (Function.update O t q)) (Function.update O t q)).2.2
            expand A proofOf prefixes
            (dec.setBase (uOf (A.run (Function.update O t q)) (Function.update O t q)))
            (m + 1) (by show m + 1 + _ = σ.k; omega)
            (Function.update O t q) (A.run (Function.update O t q)) (child q)).output.isSome

/-- Reprogramming at `t` does not change the varying-base success predicate: like both of its
predecessors it only ever consults tables of the form `Function.update _ t _`, and now that
includes the base it is read at. -/
private theorem kimchiForkGoodAtU_update [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (uOf : Pf → (T → Pre) → G) (m : ℕ) :
    {e : ℕ} → (he : m + e = σ.k) → (t : T) → (O : T → Pre) → (q : Pre) →
      (child : Pre → Zcash.Snark.RecursiveForkCoins Pre e) →
      kimchiForkGoodAtU σ expand A proofOf prefixes dec κ uOf m he t (Function.update O t q) child
        = kimchiForkGoodAtU σ expand A proofOf prefixes dec κ uOf m he t O child
  | 0, _, _, _, _, _ => by
      funext q'; simp only [kimchiForkGoodAtU]; rw [Function.update_idem]
  | _ + 1, _, _, _, _, _ => by
      funext q'; simp only [kimchiForkGoodAtU]; rw [Function.update_idem]

/-- **The operational escape set over a claim map and a varying base**
(`def:adaptive-escape-set-u`) — `kimchiForkEscapeSetAt` with its round predicate replaced by
`kimchiForkGoodAtU`. As there, neither a claim nor a base appears in the signature: the set is a
function of `κ` and `uOf` alone, hence a legitimate `esc : T → (T → Pre) → Set Pre` for
`escapesDuringC_measure_le'`. -/
noncomputable def kimchiForkEscapeSetAtU [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G) (uOf : Pf → (T → Pre) → G)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (t : T) (O : T → Pre) : Set Pre :=
  match root.nodeAt
      ((List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt t i)).take (D.roundOf t)) with
  | none => ∅
  | some node =>
      if hd : D.roundOf t + node.depth = σ.k then
        Zcash.Snark.recursiveForkEscape
          (kimchiForkGoodAtU σ expand A proofOf prefixes dec κ uOf (D.roundOf t) hd t O node.child)
      else ∅

/-- **The varying-base escape set is blind at its own point** (`lem:adaptive-escape-blind-u`).
Verbatim `kimchiForkEscapeSetAt_blind`: the tape path is about `D.chainAt`, which does not mention
the setup, and the round predicate is closed under a second update by
`kimchiForkGoodAtU_update`. -/
theorem kimchiForkEscapeSetAtU_blind [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G) (uOf : Pf → (T → Pre) → G)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (t : T) (O : T → Pre) (q : Pre) :
    kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf root t
        (Function.update O t q)
      = kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf root t O := by
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
  rw [kimchiForkEscapeSetAtU, kimchiForkEscapeSetAtU, hpath]
  cases hnode : root.nodeAt
      ((List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt t i)).take (D.roundOf t)) with
  | none => rfl
  | some node =>
      by_cases hd : D.roundOf t + node.depth = σ.k
      · simp only [dif_pos hd]
        rw [kimchiForkGoodAtU_update]
      · simp only [dif_neg hd]

/-- **Each varying-base escape set has measure at most `3 / |Pre|`**
(`lem:adaptive-escape-measure-u`) — verbatim the fixed-base argument, since
`recursiveForkEscape_subset_triple` is a statement about an arbitrary predicate and never inspects
the setup. -/
theorem kimchiForkEscapeSetAtU_measure_le [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Fintype Pre] [Nonempty Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G) (uOf : Pf → (T → Pre) → G)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (t : T) (O : T → Pre) :
    (PMF.uniformOfFintype Pre).toOuterMeasure
        (kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf root t O)
      ≤ 3 / Fintype.card Pre := by
  rw [kimchiForkEscapeSetAtU]
  cases hnode : root.nodeAt
      ((List.ofFn fun i : Fin (σ.k + 1) => O (D.chainAt t i)).take (D.roundOf t)) with
  | none => simp
  | some node =>
      by_cases hd : D.roundOf t + node.depth = σ.k
      · simp only [dif_pos hd]
        obtain ⟨a, c, hsub⟩ := Zcash.Snark.recursiveForkEscape_subset_triple
          (kimchiForkGoodAtU σ expand A proofOf prefixes dec κ uOf (D.roundOf t) hd t O
            node.child)
        exact Zcash.Snark.uniformOfFintype_toOuterMeasure_triple_le hsub
      · simp only [dif_neg hd]
        simp

/-- **At a real round prefix the varying-base escape set is the local one** — the twin of
`kimchiForkEscapeSetAt_prefix`, proved by the same rewriting of the tape path. -/
theorem kimchiForkEscapeSetAtU_prefix [DecidableEq F] [DecidableEq G] [DecidableEq T]
    [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G) (uOf : Pf → (T → Pre) → G)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1))
    {e m : ℕ} (hmk : m + (e + 1) = σ.k + 1) (O : T → Pre) (p : Pf) (order : List Pre)
    (child : Pre → Zcash.Snark.RecursiveForkCoins Pre e)
    (hreach : Zcash.Snark.RecursiveForkReached (σ.k + 1) prefixes root m hmk O p
      (.node order child)) :
    kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf root
        (prefixes p ⟨m, by omega⟩) O
      = Zcash.Snark.recursiveForkEscape
        (kimchiForkGoodAtU σ expand A proofOf prefixes dec κ uOf m (by omega)
          (prefixes p ⟨m, by omega⟩) O child) := by
  rw [kimchiForkEscapeSetAtU,
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

/-- **Rebasing congruence for the win event.** Equal bases and equal claims give the same win
event. Stated over a bare base `u : G` rather than over `srsAt`, so that the four equations can be
`subst`ed: rewriting the setup argument of `Wins` in place is not available, the coefficient
vector's type mentioning it. -/
private theorem Wins_setBase_congr (σ : SRS G) (expand : Pre → F)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    {u₁ u₂ : G} (hu : u₁ = u₂) {b₁ b₂ : Fin (2 ^ σ.k) → F} (hb : b₁ = b₂)
    {v₁ v₂ : F} (hv : v₁ = v₂) {P₁ P₂ : G} (hP : P₁ = P₂) (O : T → Pre) (p : Pf) :
    Wins { σ with U := u₁ } b₁ v₁ P₁ expand proofOf prefixes O p
      ↔ Wins { σ with U := u₂ } b₂ v₂ P₂ expand proofOf prefixes O p := by
  subst hu; subst hb; subst hv; subst hP; exact Iff.rfl

/-- **Rebasing congruence for the fork's success.** The companion of `Wins_setBase_congr` for the
fork itself; the decoding structure is transported along the base by `DecodesFromPrefixes.setBase`
on both sides, so the two calls differ only in data that `subst` removes. -/
private theorem kimchiForkFrom_setBase_isSome_congr [DecidableEq F] [DecidableEq G]
    [DecidableEq T] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F) (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    {u₁ u₂ : G} (hu : u₁ = u₂) {b₁ b₂ : Fin (2 ^ σ.k) → F} (hb : b₁ = b₂)
    {v₁ v₂ : F} (hv : v₁ = v₂) {P₁ P₂ : G} (hP : P₁ = P₂)
    {e : ℕ} (m : ℕ) (hme : m + e = σ.k) (O : T → Pre) (p : Pf)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (e + 1)) :
    (kimchiForkFrom { σ with U := u₁ } b₁ v₁ P₁ expand A proofOf prefixes (dec.setBase u₁)
        m hme O p coins).output.isSome
      = (kimchiForkFrom { σ with U := u₂ } b₂ v₂ P₂ expand A proofOf prefixes (dec.setBase u₂)
        m hme O p coins).output.isSome := by
  subst hu; subst hb; subst hv; subst hP; rfl

/-- **Non-escape forces the fork to return, over a stable claim map and a varying base.** The
varying-base twin of `kimchiForkFromAt_isSome_of_not_escape`.

The recursion never changes the table, so the setup it runs the fork at —
`srsAt σ uOf (A.run O) O` — is a single value throughout, and the fork is the fixed-setup one.
What has to be paid is that the reprogrammed runs the adaptive predicate speaks about carry
*their own* setup: `hbase` says the base does not move under a reprogramming whose guard holds,
and the guard is precisely what the fork has just tested. That is the only new step over the
fixed-base proof. -/
private theorem kimchiForkFromAtU_isSome_of_not_escape [DecidableEq F] [DecidableEq G]
    [DecidableEq T] [Fintype Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (uOf : Pf → (T → Pre) → G) (hbase : BaseStable A prefixes uOf)
    (hstable : ClaimStable A prefixes κ)
    (root : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) :
    {e : ℕ} → (m : ℕ) → (hme : m + e = σ.k) → (O : T → Pre) → (p : Pf) →
      (coins : Zcash.Snark.RecursiveForkCoins Pre (e + 1)) →
      p = A.run O →
      κ (A.run O) O = (b, v, P) →
      Zcash.Snark.RecursiveForkReached (σ.k + 1) prefixes root m (by omega) O p coins →
      coins.Complete →
      Wins (srsAt σ uOf (A.run O) O) b v P expand proofOf prefixes O p →
      ¬ (A.completing prefixes).escapesDuringC
          (kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf root) O →
      (kimchiForkFrom (srsAt σ uOf (A.run O) O) b v P expand A proofOf prefixes
        (dec.setBase (uOf (A.run O) O)) m hme O p coins).output.isSome
  | 0, m, hme, O, p, .node order child, hp, hcl, hreach, hcomplete, hwin, hnoescape => by
      subst hp
      have hm : m = σ.k := by omega
      subst hm
      have hesc : kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf root
            (prefixes (A.run O) (Fin.last σ.k)) O
          = Zcash.Snark.recursiveForkEscape (kimchiForkGoodAtU σ expand A proofOf prefixes dec κ
            uOf σ.k (by omega) (prefixes (A.run O) (Fin.last σ.k)) O child) :=
        kimchiForkEscapeSetAtU_prefix σ expand A proofOf prefixes dec D κ uOf root
          (e := 0) (m := σ.k) (by omega) O (A.run O) order child hreach
      have hlocal : O (prefixes (A.run O) (Fin.last σ.k)) ∉
          Zcash.Snark.recursiveForkEscape (kimchiForkGoodAtU σ expand A proofOf prefixes dec κ
            uOf σ.k (by omega) (prefixes (A.run O) (Fin.last σ.k)) O child) := by
        intro hu
        exact hnoescape (Zcash.Snark.OracleComp.escapesDuringC_completing _ prefixes
          (j := Fin.last σ.k) (by rw [hesc]; exact hu))
      have hupd : Function.update O (prefixes (A.run O) (Fin.last σ.k))
          (O (prefixes (A.run O) (Fin.last σ.k))) = O := by
        funext x
        by_cases hx : x = prefixes (A.run O) (Fin.last σ.k)
        · subst hx; simp
        · simp [hx]
      have hgood₁ : kimchiForkGoodAtU σ expand A proofOf prefixes dec κ uOf σ.k (by omega)
          (prefixes (A.run O) (Fin.last σ.k)) O child
          (O (prefixes (A.run O) (Fin.last σ.k))) := by
        rw [kimchiForkGoodAtU, hupd]
        refine ⟨rfl, ?_⟩
        show Wins (srsAt σ uOf (A.run O) O) (κ (A.run O) O).1 (κ (A.run O) O).2.1
          (κ (A.run O) O).2.2 expand proofOf prefixes O (A.run O)
        rw [hcl]
        exact hwin
      have hthree : Zcash.Snark.ThreeForkSuccess
          (kimchiForkGoodAtU σ expand A proofOf prefixes dec κ uOf σ.k (by omega)
            (prefixes (A.run O) (Fin.last σ.k)) O child) := by
        by_contra hno
        exact hlocal (by rw [Zcash.Snark.recursiveForkEscape, if_neg hno]; exact Or.inr hgood₁)
      rw [kimchiForkFrom, if_pos hwin]
      simp only []
      split
      · rename_i hnone
        refine absurd hnone (nextFork_fst_ne_none _ order hcomplete.1 _ _ hthree ?_)
        intro q hq
        rw [kimchiForkGoodAtU] at hq
        have hcl' : κ (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q))
            (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q) = (b, v, P) :=
          (hstable (Fin.last σ.k) O q hq.1).trans hcl
        have hu : uOf (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q))
            (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q)
            = uOf (A.run O) O := hbase (Fin.last σ.k) O q hq.1
        split
        · rfl
        · rename_i hno
          refine absurd ⟨hq.1, ?_⟩ hno
          have hb' : (κ (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q))
              (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q)).1 = b := by rw [hcl']
          have hv' : (κ (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q))
              (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q)).2.1 = v := by rw [hcl']
          have hP' : (κ (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q))
              (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q)).2.2 = P := by rw [hcl']
          exact (Wins_setBase_congr σ expand proofOf prefixes hu hb' hv' hP'
            (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q)
            (A.run (Function.update O (prefixes (A.run O) (Fin.last σ.k)) q))).mp hq.2
      · rfl
  | e + 1, m, hme, O, p, .node order child, hp, hcl, hreach, hcomplete, hwin, hnoescape => by
      subst hp
      have hesc : kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf root
            (prefixes (A.run O) ⟨m, by omega⟩) O
          = Zcash.Snark.recursiveForkEscape (kimchiForkGoodAtU σ expand A proofOf prefixes dec κ
            uOf m (by omega) (prefixes (A.run O) ⟨m, by omega⟩) O child) :=
        kimchiForkEscapeSetAtU_prefix σ expand A proofOf prefixes dec D κ uOf root
          (e := e + 1) (m := m) (by omega) O (A.run O) order child hreach
      have hlocal : O (prefixes (A.run O) ⟨m, by omega⟩) ∉
          Zcash.Snark.recursiveForkEscape (kimchiForkGoodAtU σ expand A proofOf prefixes dec κ
            uOf m (by omega) (prefixes (A.run O) ⟨m, by omega⟩) O child) := by
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
      have hfirst : (kimchiForkFrom (srsAt σ uOf (A.run O) O) b v P expand A proofOf prefixes
          (dec.setBase (uOf (A.run O) O)) (m + 1) (by simp only [srsAt_k]; omega) O (A.run O)
          (child (O (prefixes (A.run O) ⟨m, by omega⟩)))).output.isSome :=
        kimchiForkFromAtU_isSome_of_not_escape σ b v P expand A proofOf prefixes dec D κ
          uOf hbase hstable root (m + 1) (by omega) O (A.run O)
          (child (O (prefixes (A.run O) ⟨m, by omega⟩)))
          rfl hcl hreachChild (hcomplete.2 _) hwin hnoescape
      have hgood₁ : kimchiForkGoodAtU σ expand A proofOf prefixes dec κ uOf m (by omega)
          (prefixes (A.run O) ⟨m, by omega⟩) O child
          (O (prefixes (A.run O) ⟨m, by omega⟩)) := by
        rw [kimchiForkGoodAtU, hupd, hcl]
        exact ⟨rfl, hfirst⟩
      have hthree : Zcash.Snark.ThreeForkSuccess
          (kimchiForkGoodAtU σ expand A proofOf prefixes dec κ uOf m (by omega)
            (prefixes (A.run O) ⟨m, by omega⟩) O child) := by
        by_contra hno
        exact hlocal (by rw [Zcash.Snark.recursiveForkEscape, if_neg hno]; exact Or.inr hgood₁)
      have himp : ∀ q : Pre,
          kimchiForkGoodAtU σ expand A proofOf prefixes dec κ uOf m (by omega)
              (prefixes (A.run O) ⟨m, by omega⟩) O child q →
            (if prefixes (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q))
                  (⟨m, by omega⟩ : Fin (σ.k + 1)) = prefixes (A.run O) ⟨m, by omega⟩ then
                kimchiForkFrom (srsAt σ uOf (A.run O) O) b v P expand A proofOf prefixes
                  (dec.setBase (uOf (A.run O) O)) (m + 1) (by simp only [srsAt_k]; omega)
                  (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)
                  (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)) (child q)
              else { output := none, runs := 1 }).output.isSome := by
        intro q hq
        rw [kimchiForkGoodAtU] at hq
        have hcl' : κ (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q))
            (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q) = (b, v, P) :=
          (hstable ⟨m, by omega⟩ O q hq.1).trans hcl
        have hu : uOf (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q))
            (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)
            = uOf (A.run O) O := hbase ⟨m, by omega⟩ O q hq.1
        have hb' : (κ (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q))
            (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)).1 = b := by rw [hcl']
        have hv' : (κ (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q))
            (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)).2.1 = v := by rw [hcl']
        have hP' : (κ (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q))
            (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)).2.2 = P := by rw [hcl']
        split
        · exact (kimchiForkFrom_setBase_isSome_congr σ expand A proofOf prefixes dec hu
            hb' hv' hP' (m + 1) (show m + 1 + e = σ.k by omega)
            (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q)
            (A.run (Function.update O (prefixes (A.run O) ⟨m, by omega⟩) q))
            (child q)).symm.trans hq.2
        · rename_i hno
          exact absurd hq.1 hno
      rw [kimchiForkFrom]
      simp only []
      split
      · rename_i hnone
        -- the two occurrences differ only in the `hme` proof term, so match up to defeq
        exact absurd hnone (Option.isSome_iff_ne_none.mp hfirst)
      · split
        · rename_i hn2
          exact absurd hn2 (nextFork_fst_ne_none _ order hcomplete.1 _ _ hthree himp)
        · rename_i hout
          split
          · rename_i hn3
            exact absurd hn3 (nextFork_snd_ne_none _ order hcomplete.1 _ _ hthree himp hout)
          · rfl

/-- **Root form of the varying-base non-escape lemma.** The fork is started at the root run's own
claim and its own base, so the claim hypothesis is `rfl` and the tape is reached by definition. -/
private theorem kimchiForkFromAtU_isSome_of_not_escape_root [DecidableEq F] [DecidableEq G]
    [DecidableEq T] [Fintype Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (uOf : Pf → (T → Pre) → G) (hbase : BaseStable A prefixes uOf)
    (hstable : ClaimStable A prefixes κ)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcomplete : coins.Complete)
    (O : T → Pre)
    (hwin : WinsAt (srsAt σ uOf (A.run O) O) expand proofOf prefixes κ O (A.run O))
    (hnoescape : ¬ (A.completing prefixes).escapesDuringC
      (kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf coins) O) :
    (kimchiForkFrom (srsAt σ uOf (A.run O) O) (κ (A.run O) O).1 (κ (A.run O) O).2.1
      (κ (A.run O) O).2.2 expand A proofOf prefixes (dec.setBase (uOf (A.run O) O)) 0
      (Nat.zero_add σ.k) O (A.run O) coins).output.isSome := by
  refine kimchiForkFromAtU_isSome_of_not_escape σ (κ (A.run O) O).1 (κ (A.run O) O).2.1
    (κ (A.run O) O).2.2 expand A proofOf prefixes dec D κ uOf hbase hstable coins
    0 (Nat.zero_add σ.k) O (A.run O) coins rfl rfl ?_ hcomplete hwin hnoescape
  cases coins with
  | node order child => rfl

/-- **The extractor answers `some`, over a stable claim map and a base-stable varying base**
(`thm:adaptive-failure-measure-u`, first move). Here the table `O` is *fixed*, so the run's setup
`srsAt σ uOf (A.run O) O` is a single value and the whole fixed-setup chain — in particular
`kimchiExtract_isSome_of_fork_isSome`, which is setup-generic — applies at it verbatim. Only the
route to the fork's `isSome` is the varying-base one. -/
theorem kimchiExtract_isSome_of_not_escape_of_stableBase [DecidableEq F] [DecidableEq G]
    [DecidableEq T] [Fintype Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F) (hexp_ne : ∀ q : Pre, expand q ≠ 0)
    (hexp_inj : Function.Injective expand)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (rep : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F)
    (hrep : ∀ (p : Pf) (O : T → Pre),
      (κ p O).2.2 = commitGen σ.g (rep p O).1 + (rep p O).2 • σ.h)
    (uOf : Pf → (T → Pre) → G) (hbase : BaseStable A prefixes uOf)
    (hstable : ClaimStable A prefixes κ)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcomplete : coins.Complete)
    (O : T → Pre)
    (hwin : WinsAt (srsAt σ uOf (A.run O) O) expand proofOf prefixes κ O (A.run O))
    (hnoescape : ¬ (A.completing prefixes).escapesDuringC
      (kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf coins) O) :
    (kimchiExtract (srsAt σ uOf (A.run O) O) (κ (A.run O) O).1 (κ (A.run O) O).2.1
      (κ (A.run O) O).2.2 (rep (A.run O) O).1 (rep (A.run O) O).2 (hrep (A.run O) O)
      expand A proofOf prefixes (dec.setBase (uOf (A.run O) O)) O coins).isSome :=
  kimchiExtract_isSome_of_fork_isSome (srsAt σ uOf (A.run O) O) (κ (A.run O) O).1
    (κ (A.run O) O).2.1 (κ (A.run O) O).2.2 (rep (A.run O) O).1 (rep (A.run O) O).2
    (hrep (A.run O) O) expand hexp_ne hexp_inj A proofOf prefixes
    (dec.setBase (uOf (A.run O) O)) D coins O
    (kimchiForkFromAtU_isSome_of_not_escape_root σ expand A proofOf prefixes dec D κ uOf
      hbase hstable coins hcomplete O hwin hnoescape)

/-- **The extractor answers `some`, over a base that factors through the claimed value.** The
present-day form of `kimchiExtract_isSome_of_not_escape_of_stableBase`, kept verbatim for its
consumers: a base map obeying `huOf` is base-stable by `baseStable_of_claimStable`, so this is
that theorem with its base hypothesis discharged rather than a separate result. -/
theorem kimchiExtract_isSome_of_not_escape_of_stableU [DecidableEq F] [DecidableEq G]
    [DecidableEq T] [Fintype Pre] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G) (expand : Pre → F) (hexp_ne : ∀ q : Pre, expand q ≠ 0)
    (hexp_inj : Function.Injective expand)
    (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (rep : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F)
    (hrep : ∀ (p : Pf) (O : T → Pre),
      (κ p O).2.2 = commitGen σ.g (rep p O).1 + (rep p O).2 • σ.h)
    (uBase : F → G) (uOf : Pf → (T → Pre) → G)
    (huOf : ∀ (p : Pf) (O : T → Pre), uOf p O = uBase (κ p O).2.1)
    (hstable : ClaimStable A prefixes κ)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcomplete : coins.Complete)
    (O : T → Pre)
    (hwin : WinsAt (srsAt σ uOf (A.run O) O) expand proofOf prefixes κ O (A.run O))
    (hnoescape : ¬ (A.completing prefixes).escapesDuringC
      (kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf coins) O) :
    (kimchiExtract (srsAt σ uOf (A.run O) O) (κ (A.run O) O).1 (κ (A.run O) O).2.1
      (κ (A.run O) O).2.2 (rep (A.run O) O).1 (rep (A.run O) O).2 (hrep (A.run O) O)
      expand A proofOf prefixes (dec.setBase (uOf (A.run O) O)) O coins).isSome :=
  kimchiExtract_isSome_of_not_escape_of_stableBase σ expand hexp_ne hexp_inj A proofOf prefixes
    dec D κ rep hrep uOf
    (baseStable_of_claimStable hstable (fun c => uBase c.2.1) fun O => huOf (A.run O) O)
    hstable coins hcomplete O hwin hnoescape

/-- **THE STATEMENT, over a stable claim map and a base-stable varying base**
(`thm:adaptive-failure-measure-u`). Same hypotheses as `kimchiExtract_failure_measure_le_of_stable`
plus the base map `uOf`, which is required only to be *stable under the fork's own
reprogrammings* — the deployed kimchi base, read off the warm Fiat–Shamir state, is such a map and
is not a function of the claim. The event measured is the one arm (1) of the deployed cover
actually presents: the run wins *at its own setup* while the extractor *at that same setup*
returns nothing.

`kimchiExtract_failure_measure_le_of_stable` is derived from this at the constant base map
`uOf := fun _ _ => σ.U` (`baseStable_const`), and `kimchiExtract_failure_measure_le_of_stableU` at
a base factoring through the claimed value (`baseStable_of_claimStable`) — which is what certifies
that the generalization is genuine rather than a restatement that happens to be easier. -/
theorem kimchiExtract_failure_measure_le_of_stableBase [DecidableEq F] [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    (σ : SRS G)
    -- the claim the run opens, and its AGM representation, both read off the run
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (rep : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F)
    (hrep : ∀ (p : Pf) (O : T → Pre),
      (κ p O).2.2 = commitGen σ.g (rep p O).1 + (rep p O).2 • σ.h)
    -- THE BASE THE RUN IS CHECKED AT
    (uOf : Pf → (T → Pre) → G)
    -- the challenge map: injective and nonvanishing (theorems at Pasta, `EndoChallenge.lean`)
    (expand : Pre → F) (hexp_inj : Function.Injective expand) (hexp_ne : ∀ p, expand p ≠ 0)
    -- the adversary, its query budget, and the transcript data it commits to per run
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    -- COMMIT-THEN-CHALLENGE, as in the fixed-claim theorem
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    -- NEITHER THE BASE NOR THE CLAIM MOVES UNDER THE FORK'S OWN REPROGRAMMINGS
    (hbase : BaseStable A prefixes uOf)
    (hstable : ClaimStable A prefixes κ)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | WinsAt (srsAt σ uOf (A.run O) O) expand proofOf prefixes κ O (A.run O) ∧
          kimchiExtract (srsAt σ uOf (A.run O) O) (κ (A.run O) O).1 (κ (A.run O) O).2.1
              (κ (A.run O) O).2.2 (rep (A.run O) O).1 (rep (A.run O) O).2 (hrep (A.run O) O)
              expand A proofOf prefixes (dec.setBase (uOf (A.run O) O)) O coins = none}
      ≤ (Q + σ.k + 1) * (3 / Fintype.card Pre) := by
  -- the failure set is contained in the escape event of the completing machine
  have hsub : {O : T → Pre |
      WinsAt (srsAt σ uOf (A.run O) O) expand proofOf prefixes κ O (A.run O) ∧
      kimchiExtract (srsAt σ uOf (A.run O) O) (κ (A.run O) O).1 (κ (A.run O) O).2.1
          (κ (A.run O) O).2.2 (rep (A.run O) O).1 (rep (A.run O) O).2 (hrep (A.run O) O)
          expand A proofOf prefixes (dec.setBase (uOf (A.run O) O)) O coins = none}
      ⊆ {O : T → Pre | (A.completing prefixes).escapesDuringC
        (kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf coins) O} := by
    rintro O ⟨hwin, hfail⟩
    by_contra hno
    have h := kimchiExtract_isSome_of_not_escape_of_stableBase σ expand hexp_ne hexp_inj
      A proofOf prefixes dec D κ rep hrep uOf hbase hstable coins hcoins O hwin hno
    rw [hfail] at h
    simp at h
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  -- and that event is priced by the imported measure lemma, exactly as in the fixed-base case
  refine le_trans (Zcash.Snark.escapesDuringC_measure_le'
    (kimchiForkEscapeSetAtU σ expand A proofOf prefixes dec D κ uOf coins)
    (kimchiForkEscapeSetAtU_blind σ expand A proofOf prefixes dec D κ uOf coins)
    (kimchiForkEscapeSetAtU_measure_le σ expand A proofOf prefixes dec D κ uOf coins)
    (Zcash.Snark.OracleComp.queryBound_completing prefixes hQ)) (le_of_eq ?_)
  push_cast
  ring

/-- **THE STATEMENT, over a base that factors through the claimed value**
(`cor:game-over-base-stable-recovery`). The present-day form of
`kimchiExtract_failure_measure_le_of_stableBase`, kept verbatim for its consumers: `huOf` says the
base is a function of the claim's value — that is what a claim-derived kimchi base does, where `U`
is the group-map image of the claim's combined inner product — and such a base is base-stable by
`baseStable_of_claimStable`, the stability of the claim carrying the base along with it.

Factoring through the claim is strictly stronger than what the proof consumes, which is why this
is now a corollary rather than the theorem. -/
theorem kimchiExtract_failure_measure_le_of_stableU [DecidableEq F] [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    (σ : SRS G)
    -- the claim the run opens, and its AGM representation, both read off the run
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (rep : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F)
    (hrep : ∀ (p : Pf) (O : T → Pre),
      (κ p O).2.2 = commitGen σ.g (rep p O).1 + (rep p O).2 • σ.h)
    -- THE BASE THE RUN IS CHECKED AT, a function of the claim's value
    (uBase : F → G) (uOf : Pf → (T → Pre) → G)
    (huOf : ∀ (p : Pf) (O : T → Pre), uOf p O = uBase (κ p O).2.1)
    -- the challenge map: injective and nonvanishing (theorems at Pasta, `EndoChallenge.lean`)
    (expand : Pre → F) (hexp_inj : Function.Injective expand) (hexp_ne : ∀ p, expand p ≠ 0)
    -- the adversary, its query budget, and the transcript data it commits to per run
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    -- COMMIT-THEN-CHALLENGE, as in the fixed-claim theorem
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    -- THE CLAIM DOES NOT MOVE UNDER THE FORK'S OWN REPROGRAMMINGS
    (hstable : ClaimStable A prefixes κ)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | WinsAt (srsAt σ uOf (A.run O) O) expand proofOf prefixes κ O (A.run O) ∧
          kimchiExtract (srsAt σ uOf (A.run O) O) (κ (A.run O) O).1 (κ (A.run O) O).2.1
              (κ (A.run O) O).2.2 (rep (A.run O) O).1 (rep (A.run O) O).2 (hrep (A.run O) O)
              expand A proofOf prefixes (dec.setBase (uOf (A.run O) O)) O coins = none}
      ≤ (Q + σ.k + 1) * (3 / Fintype.card Pre) :=
  kimchiExtract_failure_measure_le_of_stableBase σ κ rep hrep uOf expand hexp_inj hexp_ne A hQ
    proofOf prefixes dec D
    (baseStable_of_claimStable hstable (fun c => uBase c.2.1) fun O => huOf (A.run O) O)
    hstable coins hcoins

/-- **The base-stable failure bound with the run-level hypotheses only.**
`kimchiExtract_failure_measure_le_of_stableBase` with `hrep` demanded *only at the run's own
proof* `p = A.run O`, which is the honest shape of what an algebraic-group adversary supplies: the
AGM gives a representation of the commitment the adversary itself emitted, and says nothing about
a claim map evaluated at a proof no run produced.

The re-packaging is exact rather than a genuine weakening, and that is worth recording: since `κ`,
`rep` and `uOf` are unconstrained off the run, replacing each by its own value at the run
(`fun _ O => κ (A.run O) O`, and likewise for the other two) satisfies the pointwise hypotheses
and leaves every occurrence in the statement — all of which are at `p = A.run O` — definitionally
unchanged. So a consumer holding only the run-level facts need not perform that substitution by
hand; it is performed once, here.

The base hypothesis needs no reindexing: base stability names `uOf` only at run outputs, so
`BaseStable A prefixes (fun _ O => uOf (A.run O) O)` and `BaseStable A prefixes uOf` differ by a
β-step, and `hbase` is passed straight through (`rem:base-stable-run-beta`). -/
theorem kimchiExtract_failure_measure_le_of_stableBase_of_runRep [DecidableEq F] [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    (σ : SRS G) (A : Zcash.Snark.OracleComp T Pre Pf)
    -- the claim the run opens, and its AGM representation, both read at the run's own proof
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (rep : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F)
    (hrep : ∀ O : T → Pre,
      (κ (A.run O) O).2.2 = commitGen σ.g (rep (A.run O) O).1 + (rep (A.run O) O).2 • σ.h)
    -- THE BASE THE RUN IS CHECKED AT
    (uOf : Pf → (T → Pre) → G)
    (expand : Pre → F) (hexp_inj : Function.Injective expand) (hexp_ne : ∀ p, expand p ≠ 0)
    {Q : ℕ} (hQ : A.QueryBound Q)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (hbase : BaseStable A prefixes uOf)
    (hstable : ClaimStable A prefixes κ)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | WinsAt (srsAt σ uOf (A.run O) O) expand proofOf prefixes κ O (A.run O) ∧
          kimchiExtract (srsAt σ uOf (A.run O) O) (κ (A.run O) O).1 (κ (A.run O) O).2.1
              (κ (A.run O) O).2.2 (rep (A.run O) O).1 (rep (A.run O) O).2 (hrep O)
              expand A proofOf prefixes (dec.setBase (uOf (A.run O) O)) O coins = none}
      ≤ (Q + σ.k + 1) * (3 / Fintype.card Pre) :=
  kimchiExtract_failure_measure_le_of_stableBase σ (fun _ O => κ (A.run O) O)
    (fun _ O => rep (A.run O) O) (fun _ O => hrep O) (fun _ O => uOf (A.run O) O)
    expand hexp_inj hexp_ne A hQ proofOf prefixes dec D hbase hstable coins hcoins

/-- **The varying-base failure bound with the run-level hypotheses only.**
`kimchiExtract_failure_measure_le_of_stableU` with `hrep` and `huOf` demanded *only at the run's
own proof* `p = A.run O`, which is the honest shape of what an algebraic-group adversary supplies:
the AGM gives a representation of the commitment the adversary itself emitted, and says nothing
about a claim map evaluated at a proof no run produced.

The re-packaging is exact rather than a genuine weakening, and that is worth recording: since `κ`,
`rep` and `uOf` are unconstrained off the run, replacing each by its own value at the run
(`fun _ O => κ (A.run O) O`, and likewise for the other two) satisfies the pointwise hypotheses
and leaves every occurrence in the statement — all of which are at `p = A.run O` — definitionally
unchanged. So a consumer holding only the run-level facts need not perform that substitution by
hand; it is performed once, here. -/
theorem kimchiExtract_failure_measure_le_of_stableU_of_runRep [DecidableEq F] [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    (σ : SRS G) (A : Zcash.Snark.OracleComp T Pre Pf)
    -- the claim the run opens, and its AGM representation, both read at the run's own proof
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (rep : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F)
    (hrep : ∀ O : T → Pre,
      (κ (A.run O) O).2.2 = commitGen σ.g (rep (A.run O) O).1 + (rep (A.run O) O).2 • σ.h)
    -- THE BASE THE RUN IS CHECKED AT, a function of the claim's value at the run's own proof
    (uBase : F → G) (uOf : Pf → (T → Pre) → G)
    (huOf : ∀ O : T → Pre, uOf (A.run O) O = uBase (κ (A.run O) O).2.1)
    (expand : Pre → F) (hexp_inj : Function.Injective expand) (hexp_ne : ∀ p, expand p ≠ 0)
    {Q : ℕ} (hQ : A.QueryBound Q)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    (hstable : ClaimStable A prefixes κ)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | WinsAt (srsAt σ uOf (A.run O) O) expand proofOf prefixes κ O (A.run O) ∧
          kimchiExtract (srsAt σ uOf (A.run O) O) (κ (A.run O) O).1 (κ (A.run O) O).2.1
              (κ (A.run O) O).2.2 (rep (A.run O) O).1 (rep (A.run O) O).2 (hrep O)
              expand A proofOf prefixes (dec.setBase (uOf (A.run O) O)) O coins = none}
      ≤ (Q + σ.k + 1) * (3 / Fintype.card Pre) :=
  kimchiExtract_failure_measure_le_of_stableBase_of_runRep σ A κ rep hrep uOf expand hexp_inj
    hexp_ne hQ proofOf prefixes dec D
    (baseStable_of_claimStable hstable (fun c => uBase c.2.1) huOf) hstable coins hcoins

/-- **THE STATEMENT, over a stable claim map** (`thm:adaptive-failure-measure`). Same hypotheses
as `kimchiExtract_failure_measure_le` — an injective, nonvanishing expansion map, a `Q`-query
adversary, commit-then-challenge, chronological distinct round prefixes, a complete fork tape —
except that the claim is no longer a parameter bound before the oracle table: it is
`κ (A.run O) O`, read off the run, with `ClaimStable` supplied as a hypothesis and the
commitment's AGM representation supplied pointwise by `rep`/`hrep`.

`kimchiExtract_failure_measure_le` is now *derived* from this, at `κ := fun _ _ => (b, v, P)` and
`claimStable_const` — which is what certifies that the generalization is genuine and not a
restatement that happens to be easier. Neither statement mentions the escape set, so the fact that
the two proofs run over different ones (`kimchiForkEscapeSet` and `kimchiForkEscapeSetAt`, equal
only after an induction on the round predicate) costs nothing.

**Anti-vacuity** is inherited through the same instance: `honest_wins_everywhere` builds an
adversary that wins on *every* table at a fixed claim, and at a constant `κ` that is exactly
`WinsAt`, so the win set here can likewise have measure `1` and an extractor that always answers
`none` cannot satisfy the bound. -/
theorem kimchiExtract_failure_measure_le_of_stable [DecidableEq F] [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    (σ : SRS G)
    -- the claim the run opens, and its AGM representation, both read off the run
    (κ : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F × G)
    (rep : Pf → (T → Pre) → (Fin (2 ^ σ.k) → F) × F)
    (hrep : ∀ (p : Pf) (O : T → Pre),
      (κ p O).2.2 = commitGen σ.g (rep p O).1 + (rep p O).2 • σ.h)
    -- the challenge map: injective and nonvanishing (theorems at Pasta, `EndoChallenge.lean`)
    (expand : Pre → F) (hexp_inj : Function.Injective expand) (hexp_ne : ∀ p, expand p ≠ 0)
    -- the adversary, its query budget, and the transcript data it commits to per run
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    -- COMMIT-THEN-CHALLENGE, as in the fixed-claim theorem
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (D : Zcash.Snark.PrefixDecode T (σ.k + 1) prefixes)
    -- THE CLAIM DOES NOT MOVE UNDER THE FORK'S OWN REPROGRAMMINGS
    (hstable : ClaimStable A prefixes κ)
    (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | WinsAt σ expand proofOf prefixes κ O (A.run O) ∧
          kimchiExtract σ (κ (A.run O) O).1 (κ (A.run O) O).2.1 (κ (A.run O) O).2.2
              (rep (A.run O) O).1 (rep (A.run O) O).2 (hrep (A.run O) O)
              expand A proofOf prefixes dec O coins = none}
      ≤ (Q + σ.k + 1) * (3 / Fintype.card Pre) :=
  -- the `uOf := fun _ _ => σ.U` instance of `kimchiExtract_failure_measure_le_of_stableBase`
  -- (`cor:fixed-base-unchanged`): at a constant base map the run's setup is
  -- `{ σ with U := σ.U }`, which is `σ` by structure eta, and `dec.setBase σ.U` is `dec` by the
  -- same eta — so every occurrence matches definitionally, and `baseStable_const` discharges the
  -- base hypothesis.
  kimchiExtract_failure_measure_le_of_stableBase σ κ rep hrep (fun _ _ => σ.U) expand hexp_inj
    hexp_ne A hQ proofOf prefixes dec D (baseStable_const A prefixes σ.U) hstable coins hcoins

end AdaptiveClaim

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
      ≤ (Q + σ.k + 1) * (3 / Fintype.card Pre) :=
  -- the `claimStable_const` instance of `kimchiExtract_failure_measure_le_of_stable`: a constant
  -- claim map is stable, and at it `WinsAt` *is* `Wins` and the adaptive extractor call *is*
  -- this one, definitionally. This is what certifies that the adaptive game above genuinely
  -- subsumes the fixed-claim one rather than merely resembling it.
  kimchiExtract_failure_measure_le_of_stable σ (fun _ _ => (b, v, P)) (fun _ _ => (pg, pw))
    (fun _ _ => hP) expand _hexp_inj _hexp_ne A _hQ proofOf prefixes dec _D
    (claimStable_const A prefixes (b, v, P)) coins _hcoins

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

/-! ## The adaptive Schwartz–Zippel charge

The endpoint's fourth summand prices the event that one of the run's *own* pre-opening challenges
lands in an exclusion set which the adversary's own algebraic data determines. The imported
adaptive bound (`Zcash.Snark.fsAdvantageFull_zero_slice_le`) proves only the special case where
the exclusion set is the constant singleton `{0}`, so that blindness is `rfl`. The two lemmas
below are that argument with the constant singleton replaced by an arbitrary *blind* family of
`Finset`s of bounded cardinality — which is all
`Zcash.Snark.escapesDuringC_measure_le'` ever asks for, since both of its hypotheses are about
the family and neither is about the game.

**Blindness is the whole content of the hypothesis**, and it is genuinely restrictive: it
quantifies over *every* node `t`, table `O` and answer `q`, so a family that reads its data off
the outer table `O` at points other than `t` is fine, but one that reads it off `O t` is not. The
two ways to satisfy it in practice are the two recorded in the chapter's subsection "The
blindness question": evaluate the set at the reprogrammed table (then blindness is
`Function.update_idem`, exactly as for `kimchiForkEscapeSetAt_blind` above), or exhibit the set's
data as a function of the transcript prefix at `t`, which by `PrefixDecode.chainAt_ne` never
includes `t` itself. -/

section AdaptiveBadSet

/-- **The generic adaptive Schwartz–Zippel charge** (`lem:adaptive-sz-charge`). For a `Q`-query
adversary `A`, a node selector `node` picking one transcript point out of a run, and a *blind*
family `bad` of exclusion sets of size at most `c`, the probability that the run's own answer at
its own node lies in its own exclusion set is at most `(Q + 1) · c / |Pre|`.

Project local: ironwood proves this only for `bad := fun _ _ => {0}`
(`Zcash.Snark.fsAdvantageFull_zero_slice_le`), where blindness is free. Our exclusion sets are
the adversary-dependent Schwartz–Zippel bad sets of the endpoint's fourth summand, so the family
must be a parameter. The proof is the same twelve lines: complete the machine with one extra
query at `node`, observe that the event *is* an escape during the completion phase, and price it
by `Zcash.Snark.escapesDuringC_measure_le'`. -/
theorem adaptive_badSet_measure_le [Fintype T] [DecidableEq T] [Fintype Pre] [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (node : Pf → T) (bad : T → (T → Pre) → Finset Pre)
    (hblind : ∀ (t : T) (O : T → Pre) (q : Pre), bad t (Function.update O t q) = bad t O)
    {c : ℕ} (hcard : ∀ (t : T) (O : T → Pre), (bad t O).card ≤ c) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | O (node (A.run O)) ∈ bad (node (A.run O)) O}
      ≤ (Q + 1 : ℕ) * (c / Fintype.card Pre) := by
  set esc : T → (T → Pre) → Set Pre := fun t O => ↑(bad t O) with hesc_def
  have hblind' : ∀ (t : T) (O : T → Pre) (q : Pre), esc t (Function.update O t q) = esc t O :=
    fun t O q => by simp only [hesc_def, hblind t O q]
  have hmeas : ∀ (t : T) (O : T → Pre),
      (PMF.uniformOfFintype Pre).toOuterMeasure (esc t O)
        ≤ (c : ℝ≥0∞) / Fintype.card Pre := by
    intro t O
    simp only [hesc_def]
    rw [Zcash.Snark.uniformOfFintype_toOuterMeasure_finset]
    gcongr
    exact Nat.cast_le.mpr (hcard t O)
  set zc : Pf → Fin 1 → T := fun p _ => node p with hzc_def
  have hsub : {O : T → Pre | O (node (A.run O)) ∈ bad (node (A.run O)) O}
      ⊆ {O : T → Pre | (A.completing zc).escapesDuringC esc O} := fun O hO =>
    Zcash.Snark.OracleComp.escapesDuringC_completing esc zc (j := 0)
      (show O (zc (A.run O) 0) ∈ esc (zc (A.run O) 0) O from Finset.mem_coe.mpr hO)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  exact Zcash.Snark.escapesDuringC_measure_le' esc hblind' hmeas
    (Zcash.Snark.OracleComp.queryBound_completing zc hQ)

/-- **The same charge with the exclusion set on the challenge side**
(`lem:adaptive-sz-expand`). The deployed transcript squeezes a prechallenge and endo-expands it,
so an exclusion set produced by a Schwartz–Zippel argument is a set of *field* elements. Pulling
it back along the injective expansion map costs nothing: the preimage of a `c`-element set under
an injection has at most `c` elements, and blindness is inherited because the preimage is taken
pointwise in `(t, O)`.

Project local for the same reason as `adaptive_badSet_measure_le`. -/
theorem adaptive_badSet_expand_measure_le [DecidableEq F] [Fintype T] [DecidableEq T]
    [Fintype Pre] [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (node : Pf → T) (expand : Pre → F) (hexp_inj : Function.Injective expand)
    (bad : T → (T → Pre) → Finset F)
    (hblind : ∀ (t : T) (O : T → Pre) (q : Pre), bad t (Function.update O t q) = bad t O)
    {c : ℕ} (hcard : ∀ (t : T) (O : T → Pre), (bad t O).card ≤ c) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | expand (O (node (A.run O))) ∈ bad (node (A.run O)) O}
      ≤ (Q + 1 : ℕ) * (c / Fintype.card Pre) := by
  classical
  refine le_trans (le_of_eq ?_)
    (adaptive_badSet_measure_le A hQ node
      (fun t O => (bad t O).preimage expand hexp_inj.injOn)
      (fun t O q => by simp only [hblind t O q])
      (c := c) (fun t O => ?_))
  · refine congrArg _ (Set.ext fun O => ?_)
    simp only [Set.mem_setOf_eq, Finset.mem_preimage]
  · exact le_trans (Finset.card_le_card_of_injOn expand
      (fun q hq => Finset.mem_preimage.mp hq) hexp_inj.injOn) (hcard t O)

/-- **The charge for a bad set determined by the node itself** — the shape the kimchi consumer
wants, and the reason the transcript nodes are `Option`-gated. When the exclusion set is a
function of the transcript point alone, blindness is `rfl`: no table appears, so reprogramming
cannot move the set. Deployed, "a function of the transcript point alone" is the second of the
two repairs in the chapter's subsection "The blindness question" — the set's data must have been
absorbed by the node at which the challenge it guards is read. -/
theorem adaptive_badSet_ofNode_measure_le [Fintype T] [DecidableEq T] [Fintype Pre]
    [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (node : Pf → T) (bad : T → Finset Pre) {c : ℕ} (hcard : ∀ t : T, (bad t).card ≤ c) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | O (node (A.run O)) ∈ bad (node (A.run O))}
      ≤ (Q + 1 : ℕ) * (c / Fintype.card Pre) :=
  adaptive_badSet_measure_le A hQ node (fun t _ => bad t) (fun _ _ _ => rfl)
    (fun t _ => hcard t)

/-- **The challenge-side charge for a node-determined bad set** —
`adaptive_badSet_ofNode_measure_le` composed with the injective expansion, which is how a
Schwartz–Zippel exclusion set (a set of field elements) is priced against a uniform
prechallenge. -/
theorem adaptive_badSet_ofNode_expand_measure_le [DecidableEq F] [Fintype T] [DecidableEq T]
    [Fintype Pre] [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (node : Pf → T) (expand : Pre → F) (hexp_inj : Function.Injective expand)
    (bad : T → Finset F) {c : ℕ} (hcard : ∀ t : T, (bad t).card ≤ c) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | expand (O (node (A.run O))) ∈ bad (node (A.run O))}
      ≤ (Q + 1 : ℕ) * (c / Fintype.card Pre) :=
  adaptive_badSet_expand_measure_le A hQ node expand hexp_inj (fun t _ => bad t)
    (fun _ _ _ => rfl) (fun t _ => hcard t)

/-- **The union of finitely many adaptive charges**, at the *sum* of their cardinality budgets and
a single query factor. This is the shape the endpoint's fourth summand has: six challenges, each
read at its own node with its own exclusion set, priced together by
`(Q + 1) · szBudget / |Pre|` — and it is a bound on the sum of the budgets rather than on their
maximum precisely because `∑ᵢ (Q+1)·cᵢ/|Pre| = (Q+1)·(∑ᵢ cᵢ)/|Pre|`. -/
theorem adaptive_badSet_union_measure_le {ι : Type*} [Fintype ι] [Fintype T] [DecidableEq T]
    [Fintype Pre] [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (node : ι → Pf → T) (bad : ι → T → (T → Pre) → Finset Pre)
    (hblind : ∀ (i : ι) (t : T) (O : T → Pre) (q : Pre),
      bad i t (Function.update O t q) = bad i t O)
    (c : ι → ℕ) (hcard : ∀ (i : ι) (t : T) (O : T → Pre), (bad i t O).card ≤ c i) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | ∃ i : ι, O (node i (A.run O)) ∈ bad i (node i (A.run O)) O}
      ≤ (Q + 1 : ℕ) * (((∑ i : ι, c i : ℕ) : ℝ≥0∞) / Fintype.card Pre) := by
  have hset : {O : T → Pre | ∃ i : ι, O (node i (A.run O)) ∈ bad i (node i (A.run O)) O}
      = ⋃ i : ι, {O : T → Pre | O (node i (A.run O)) ∈ bad i (node i (A.run O)) O} := by
    ext O
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  refine le_trans (MeasureTheory.measure_iUnion_fintype_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ =>
    adaptive_badSet_measure_le A hQ (node i) (bad i) (hblind i) (hcard i)) (le_of_eq ?_)
  rw [← Finset.mul_sum]
  refine congrArg _ ?_
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  push_cast
  rfl

/-- **The charge when the exclusion set reads finitely many strictly earlier nodes**
(`lem:adaptive-sz-prefix-nodes`). The set guarding the challenge read at `node p` is allowed to
depend on the transcript point itself *and* on the oracle's answers at nodes `pre i t`, each a
function of `t`; blindness is then `Function.update_of_ne`, because reprogramming touches the
table only at `t` and no `pre i t` is `t`.

Distinctness is only ever available at the transcript points a run actually reaches, so it is
asked for under a `guard` that the node selector is required to satisfy — the exact shape of
ironwood's `Zcash.Snark.FullDecode.chainPre_ne` (`guard t → chainPre t i ≠ t`) together with
`guard_prefixes`. Passing `guard := fun _ => True` recovers the bare `∀ i t, pre i t ≠ t` form.

Project local: `adaptive_badSet_measure_le` asks for blindness as a hypothesis, and this is the
one way the deployed exclusion sets discharge it — the `γ`, `α`, `ζ` and evalscale sets each read
the challenges squeezed strictly before their own. -/
theorem adaptive_badSet_ofPrefix_measure_le {ι : Type*} [Fintype T] [DecidableEq T]
    [Fintype Pre] [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (node : Pf → T) (guard : T → Prop) (hnode : ∀ p : Pf, guard (node p))
    (pre : ι → T → T) (hpre : ∀ t : T, guard t → ∀ i : ι, pre i t ≠ t)
    (bad : T → (ι → Pre) → Finset Pre)
    {c : ℕ} (hcard : ∀ (t : T) (w : ι → Pre), (bad t w).card ≤ c) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | O (node (A.run O)) ∈
          bad (node (A.run O)) fun i => O (pre i (node (A.run O)))}
      ≤ (Q + 1 : ℕ) * (c / Fintype.card Pre) := by
  classical
  refine le_trans (le_of_eq ?_)
    (adaptive_badSet_measure_le A hQ node
      (fun t O => if guard t then bad t (fun i => O (pre i t)) else ∅) ?_ (c := c) ?_)
  · refine congrArg _ (Set.ext fun O => ?_)
    simp only [Set.mem_setOf_eq, if_pos (hnode (A.run O))]
  · intro t O q
    by_cases ht : guard t
    · simp only [if_pos ht]
      exact congrArg _ (funext fun i => Function.update_of_ne (hpre t ht i) q O)
    · simp only [if_neg ht]
  · intro t O
    by_cases ht : guard t
    · simpa only [if_pos ht] using hcard t _
    · simp only [if_neg ht, Finset.card_empty]
      exact Nat.zero_le c

/-- **The challenge-side form of `adaptive_badSet_ofPrefix_measure_le`** — the same charge with
the exclusion set given as a set of *field* elements, pulled back along the injective endo
expansion exactly as `adaptive_badSet_expand_measure_le` does. This is the form a Schwartz–Zippel
argument produces, so it is the one the deployed consumer calls. -/
theorem adaptive_badSet_ofPrefix_expand_measure_le {ι : Type*} [DecidableEq F] [Fintype T]
    [DecidableEq T] [Fintype Pre] [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (node : Pf → T) (guard : T → Prop) (hnode : ∀ p : Pf, guard (node p))
    (pre : ι → T → T) (hpre : ∀ t : T, guard t → ∀ i : ι, pre i t ≠ t)
    (expand : Pre → F) (hexp_inj : Function.Injective expand)
    (bad : T → (ι → Pre) → Finset F)
    {c : ℕ} (hcard : ∀ (t : T) (w : ι → Pre), (bad t w).card ≤ c) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | expand (O (node (A.run O))) ∈
          bad (node (A.run O)) fun i => O (pre i (node (A.run O)))}
      ≤ (Q + 1 : ℕ) * (c / Fintype.card Pre) := by
  classical
  refine le_trans (le_of_eq ?_)
    (adaptive_badSet_ofPrefix_measure_le A hQ node guard hnode pre hpre
      (fun t w => (bad t w).preimage expand hexp_inj.injOn) (c := c) (fun t w => ?_))
  · refine congrArg _ (Set.ext fun O => ?_)
    simp only [Set.mem_setOf_eq, Finset.mem_preimage]
  · exact le_trans (Finset.card_le_card_of_injOn expand
      (fun q hq => Finset.mem_preimage.mp hq) hexp_inj.injOn) (hcard t w)

/-- **`adaptive_badSet_ofPrefix_measure_le` at ironwood's own prefix chain.** A
`Zcash.Snark.FullDecode` is exactly a `pre`/`guard` pair for the case where the guarded node is an
IPA *round* prefix and the nodes read are the *pre-IPA* ones: `chainPre_ne` is the distinctness
hypothesis, `guard_prefixes` says every round prefix is guarded, and `chainPre_prefixes` identifies
what the set then reads as the run's own pre-IPA challenges.

Note the scope: `guard_prefixes` covers the round prefixes only, so this instantiation prices a
*round* challenge against a set reading the pre-IPA challenges. The six deployed Schwartz–Zippel
sets guard pre-IPA challenges against *earlier pre-IPA* challenges, a chain `FullDecode` does not
carry; those go through `adaptive_badSet_ofPrefix_measure_le` directly, with the consumer's own
re-gating retraction as `pre`. -/
theorem adaptive_badSet_ofChainPre_measure_le {m k : ℕ} [Fintype T] [DecidableEq T]
    [Fintype Pre] [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    {prefixesPre : Pf → Fin m → T} {prefixes : Pf → Fin k → T}
    (FD : Zcash.Snark.FullDecode T m k prefixesPre prefixes) (j : Fin k)
    (bad : T → (Fin m → Pre) → Finset Pre)
    {c : ℕ} (hcard : ∀ (t : T) (w : Fin m → Pre), (bad t w).card ≤ c) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | O (prefixes (A.run O) j) ∈
          bad (prefixes (A.run O) j) fun i => O (prefixesPre (A.run O) i)}
      ≤ (Q + 1 : ℕ) * (c / Fintype.card Pre) := by
  refine le_trans (le_of_eq ?_)
    (adaptive_badSet_ofPrefix_measure_le A hQ (fun p => prefixes p j) FD.guard
      (fun p => FD.guard_prefixes p j) (fun i t => FD.chainPre t i)
      (fun t ht i => FD.chainPre_ne t ht i) bad hcard)
  refine congrArg _ (Set.ext fun O => ?_)
  simp only [Set.mem_setOf_eq, FD.chainPre_prefixes]

/-- **Finitely many prefix-determined charges, summed** — `adaptive_badSet_union_measure_le` with
each exclusion set read off the transcript point and the oracle's answers at strictly earlier
nodes, as in `adaptive_badSet_ofPrefix_measure_le`. The blindness bookkeeping is done once here so
that a consumer holding six such sets does not repeat it six times, and the charge is a *single*
query factor times the *sum* of the six budgets. -/
theorem adaptive_badSet_ofPrefix_union_measure_le {ι κ : Type*} [Fintype ι] [Fintype T]
    [DecidableEq T] [Fintype Pre] [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (node : ι → Pf → T) (guard : T → Prop) (hnode : ∀ (i : ι) (p : Pf), guard (node i p))
    (pre : ι → κ → T → T) (hpre : ∀ (i : ι) (t : T), guard t → ∀ j : κ, pre i j t ≠ t)
    (bad : ι → T → (κ → Pre) → Finset Pre)
    (c : ι → ℕ) (hcard : ∀ (i : ι) (t : T) (w : κ → Pre), (bad i t w).card ≤ c i) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | ∃ i : ι, O (node i (A.run O)) ∈
          bad i (node i (A.run O)) fun j => O (pre i j (node i (A.run O)))}
      ≤ (Q + 1 : ℕ) * (((∑ i : ι, c i : ℕ) : ℝ≥0∞) / Fintype.card Pre) := by
  classical
  refine le_trans (le_of_eq ?_)
    (adaptive_badSet_union_measure_le A hQ node
      (fun i t O => if guard t then bad i t (fun j => O (pre i j t)) else ∅) ?_ c ?_)
  · refine congrArg _ (Set.ext fun O => ?_)
    simp only [Set.mem_setOf_eq, if_pos (hnode _ (A.run O))]
  · intro i t O q
    by_cases ht : guard t
    · simp only [if_pos ht]
      exact congrArg _ (funext fun j => Function.update_of_ne (hpre i t ht j) q O)
    · simp only [if_neg ht]
  · intro i t O
    by_cases ht : guard t
    · simpa only [if_pos ht] using hcard i t _
    · simp only [if_neg ht, Finset.card_empty]
      exact Nat.zero_le (c i)

/-- **The endpoint's fourth summand, in the shape it is consumed.** Finitely many challenges, each
squeezed at its own transcript node, each guarded by a set of *field* elements determined by that
node together with strictly earlier ones, and each read into the field by its own injective map —
the deployed `β`, `γ` challenges are a plain cast of the prechallenge while the opening-argument
challenges are the endomorphism expansion, so the expansion is indexed by `ι` rather than fixed.
The total charge is one query factor times the sum of the budgets. -/
theorem adaptive_badSet_ofPrefix_union_expand_measure_le {ι κ : Type*} [DecidableEq F] [Fintype ι]
    [Fintype T] [DecidableEq T] [Fintype Pre] [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (node : ι → Pf → T) (guard : T → Prop) (hnode : ∀ (i : ι) (p : Pf), guard (node i p))
    (pre : ι → κ → T → T) (hpre : ∀ (i : ι) (t : T), guard t → ∀ j : κ, pre i j t ≠ t)
    (expand : ι → Pre → F) (hexp_inj : ∀ i : ι, Function.Injective (expand i))
    (bad : ι → T → (κ → Pre) → Finset F)
    (c : ι → ℕ) (hcard : ∀ (i : ι) (t : T) (w : κ → Pre), (bad i t w).card ≤ c i) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | ∃ i : ι, expand i (O (node i (A.run O))) ∈
          bad i (node i (A.run O)) fun j => O (pre i j (node i (A.run O)))}
      ≤ (Q + 1 : ℕ) * (((∑ i : ι, c i : ℕ) : ℝ≥0∞) / Fintype.card Pre) := by
  classical
  refine le_trans (le_of_eq ?_)
    (adaptive_badSet_ofPrefix_union_measure_le A hQ node guard hnode pre hpre
      (fun i t w => (bad i t w).preimage (expand i) (hexp_inj i).injOn) c (fun i t w => ?_))
  · refine congrArg _ (Set.ext fun O => ?_)
    simp only [Set.mem_setOf_eq, Finset.mem_preimage]
  · exact le_trans (Finset.card_le_card_of_injOn (expand i)
      (fun q hq => Finset.mem_preimage.mp hq) (hexp_inj i).injOn) (hcard i t w)

/-- **The union charge from a run-level agreement law**
(`lem:adaptive-sz-prefix-union-agree`). `adaptive_badSet_ofPrefix_union_expand_measure_le` with
the exclusion sets given *at the run* — as functions `badRun i : (T → Pre) → Finset F` of the
whole oracle table — rather than at a transcript point. The only thing asked of them is an
agreement law: two tables that give the same node at index `i` and the same answers at every
retracted node `pre i j` have the same set there.

Project local, and stated in this shape on purpose: every deployed consumer builds its exclusion
sets out of data the *run* produces (the adversary's representations, its commitments, its earlier
challenges), so they are naturally functions of the table, while the charge above wants them as
functions of a transcript point. Turning one into the other is a choice-function argument that
would otherwise be repeated verbatim in each consumer; it is done once here. Expect
`Classical.choice` in the axiom list — the witnessing table is chosen, and the agreement law is
exactly what makes the choice immaterial.

Note the two events are *equal*, not merely nested: at a table `O` the pair
`(node i (A.run O), fun j => O (pre i j (node i (A.run O))))` is witnessed by `O` itself. -/
theorem adaptive_badSet_ofPrefix_union_expand_measure_le_of_agree {ι κ : Type*} [DecidableEq F]
    [Fintype ι] [Fintype T] [DecidableEq T] [Fintype Pre] [Nonempty Pre]
    (A : Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : A.QueryBound Q)
    (node : ι → Pf → T) (guard : T → Prop) (hnode : ∀ (i : ι) (p : Pf), guard (node i p))
    (pre : ι → κ → T → T) (hpre : ∀ (i : ι) (t : T), guard t → ∀ j : κ, pre i j t ≠ t)
    (expand : ι → Pre → F) (hexp_inj : ∀ i : ι, Function.Injective (expand i))
    (badRun : ι → (T → Pre) → Finset F)
    (hagree : ∀ (i : ι) (O O' : T → Pre),
      node i (A.run O) = node i (A.run O') →
      (∀ j : κ, O (pre i j (node i (A.run O))) = O' (pre i j (node i (A.run O')))) →
      badRun i O = badRun i O')
    (c : ι → ℕ) (hcard : ∀ (i : ι) (O : T → Pre), (badRun i O).card ≤ c i) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | ∃ i : ι, expand i (O (node i (A.run O))) ∈ badRun i O}
      ≤ (Q + 1 : ℕ) * (((∑ i : ι, c i : ℕ) : ℝ≥0∞) / Fintype.card Pre) := by
  classical
  obtain ⟨bad, hkey, hcard'⟩ :
      ∃ bad : ι → T → (κ → Pre) → Finset F,
        (∀ (i : ι) (O : T → Pre),
            bad i (node i (A.run O)) (fun j => O (pre i j (node i (A.run O)))) = badRun i O) ∧
          ∀ (i : ι) (t : T) (w : κ → Pre), (bad i t w).card ≤ c i := by
    refine ⟨fun i t w =>
      if h : ∃ O : T → Pre, node i (A.run O) = t ∧ ∀ j : κ, O (pre i j t) = w j then
        badRun i h.choose else ∅, ?_, ?_⟩
    · intro i O
      have hex : ∃ O' : T → Pre, node i (A.run O') = node i (A.run O) ∧
          ∀ j : κ, O' (pre i j (node i (A.run O))) = O (pre i j (node i (A.run O))) :=
        ⟨O, rfl, fun _ => rfl⟩
      simp only [dif_pos hex]
      have h1 := hex.choose_spec.1
      exact hagree i _ O h1 fun j => by rw [h1]; exact hex.choose_spec.2 j
    · intro i t w
      dsimp only
      split
      · exact hcard i _
      · simp only [Finset.card_empty]
        exact Nat.zero_le (c i)
  refine le_trans (le_of_eq ?_)
    (adaptive_badSet_ofPrefix_union_expand_measure_le A hQ node guard hnode pre hpre
      expand hexp_inj bad c hcard')
  exact congrArg _ (Set.ext fun O => by simp only [Set.mem_setOf_eq, hkey])

end AdaptiveBadSet

/-! ## From a per-basis bound to the joint measure

Every bound above is *per oracle table*, at a fixed setup basis; the endpoint's measure is joint,
over the uniformly sampled basis together with the table. The step between the two is ironwood's
right-fibre Fubini bound, which needs no adaptation — only the predicate packaging below, so that
a consumer whose event is stated as a two-argument predicate on the pair (which is what a game
whose SRS itself depends on the basis produces) can hand it over without a `Set.ext`. -/

section FibreLift

/-- **A per-fibre bound lifts to the joint uniform measure** (`lem:fibre-lift`). If for every
`s` the uniform measure over `Ω` of `{ω | p s ω}` is at most `β`, then the uniform measure over
pairs of `{x | p x.1 x.2}` is at most `β`: the joint measure of a set is the average of its fibre
measures, and bounding every fibre bounds the average.

Project local only in its *packaging*: the mathematics is
`Zcash.Snark.uniformOfFintype_prod_fiber_bound_right`, whose event is a membership
`{x | x.2 ∈ S x.1}` in a fibre family. The endpoint's events are predicates on the pair whose
first component also determines the SRS, and unifying those against a membership is a
higher-order match that `refine` will not do; supplying the predicate directly is what makes the
lemma applicable at the game. -/
theorem measure_prod_le_of_forall_fibre {S Ω : Type*} [Fintype S] [Fintype Ω] [Nonempty S]
    [Nonempty Ω] (p : S → Ω → Prop) {β : ℝ≥0∞}
    (hfib : ∀ s : S, (PMF.uniformOfFintype Ω).toOuterMeasure {ω | p s ω} ≤ β) :
    (PMF.uniformOfFintype (S × Ω)).toOuterMeasure {x : S × Ω | p x.1 x.2} ≤ β :=
  Zcash.Snark.uniformOfFintype_prod_fiber_bound_right (fun s => {ω | p s ω}) hfib

/-- **The adaptive-claim failure bound over the joint measure** — `measure_prod_le_of_forall_fibre`
instantiated at `kimchiExtract_failure_measure_le_of_stable`, with *the SRS itself* (and hence the
claim map, the adversary, the transcript data and the fork tape) depending on the sampled index
`s`. This is arm (1) of the deployed cover, as far as it can be stated in this package: the kimchi
vocabulary that says which `σ s` the basis induces lives downstream.

The round count is allowed to vary with `s` and is priced at any common upper bound `k`, so a
consumer never has to transport a dependent `Fin (2 ^ (σ s).k)` across an equation of round
counts. -/
theorem kimchiExtract_failure_measure_prod_le_of_stable [DecidableEq F] [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    {S : Type*} [Fintype S] [Nonempty S]
    (σ : S → SRS G)
    (κ : ∀ s : S, Pf → (T → Pre) → (Fin (2 ^ (σ s).k) → F) × F × G)
    (rep : ∀ s : S, Pf → (T → Pre) → (Fin (2 ^ (σ s).k) → F) × F)
    (hrep : ∀ (s : S) (p : Pf) (O : T → Pre),
      (κ s p O).2.2 = commitGen (σ s).g (rep s p O).1 + (rep s p O).2 • (σ s).h)
    (expand : Pre → F) (hexp_inj : Function.Injective expand) (hexp_ne : ∀ p, expand p ≠ 0)
    (A : S → Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : ∀ s : S, (A s).QueryBound Q)
    (proofOf : ∀ s : S, Pf → OpeningProof F G (σ s).k)
    (prefixes : ∀ s : S, Pf → Fin ((σ s).k + 1) → T)
    (dec : ∀ s : S, DecodesFromPrefixes (σ s) (proofOf s) (prefixes s))
    (D : ∀ s : S, Zcash.Snark.PrefixDecode T ((σ s).k + 1) (prefixes s))
    (hstable : ∀ s : S, ClaimStable (A s) (prefixes s) (κ s))
    (coins : ∀ s : S, Zcash.Snark.RecursiveForkCoins Pre ((σ s).k + 1))
    (hcoins : ∀ s : S, (coins s).Complete)
    {k : ℕ} (hk : ∀ s : S, (σ s).k ≤ k) :
    (PMF.uniformOfFintype (S × (T → Pre))).toOuterMeasure
        {x | WinsAt (σ x.1) expand (proofOf x.1) (prefixes x.1) (κ x.1) x.2 ((A x.1).run x.2) ∧
          kimchiExtract (σ x.1) (κ x.1 ((A x.1).run x.2) x.2).1
              (κ x.1 ((A x.1).run x.2) x.2).2.1 (κ x.1 ((A x.1).run x.2) x.2).2.2
              (rep x.1 ((A x.1).run x.2) x.2).1 (rep x.1 ((A x.1).run x.2) x.2).2
              (hrep x.1 ((A x.1).run x.2) x.2) expand (A x.1) (proofOf x.1) (prefixes x.1)
              (dec x.1) x.2 (coins x.1) = none}
      ≤ (Q + k + 1) * (3 / Fintype.card Pre) := by
  refine measure_prod_le_of_forall_fibre
    (fun (s : S) (O : T → Pre) =>
      WinsAt (σ s) expand (proofOf s) (prefixes s) (κ s) O ((A s).run O) ∧
        kimchiExtract (σ s) (κ s ((A s).run O) O).1 (κ s ((A s).run O) O).2.1
            (κ s ((A s).run O) O).2.2 (rep s ((A s).run O) O).1 (rep s ((A s).run O) O).2
            (hrep s ((A s).run O) O) expand (A s) (proofOf s) (prefixes s) (dec s) O
            (coins s) = none)
    fun s => le_trans
      (kimchiExtract_failure_measure_le_of_stable (σ s) (κ s) (rep s) (hrep s) expand hexp_inj
        hexp_ne (A s) (hQ s) (proofOf s) (prefixes s) (dec s) (D s) (hstable s) (coins s)
        (hcoins s)) ?_
  gcongr
  exact hk s

/-- **The base-stable failure bound over the joint measure**
(`thm:adaptive-failure-measure-u-prod`) — `measure_prod_le_of_forall_fibre` instantiated at
`kimchiExtract_failure_measure_le_of_stableBase`, with the SRS, the claim map, *the base map*, the
adversary, the transcript data and the fork tape all depending on the sampled index `s`, and base
stability demanded fibrewise.

This is arm (1) of the deployed cover in the shape it is actually presented: the deployed
`runSrs` overrides the sampled setup's base per run, so the setup at which the win is checked and
the extraction is performed moves with the oracle table, and the fixed-base
`kimchiExtract_failure_measure_prod_le_of_stable` does not apply to it. -/
theorem kimchiExtract_failure_measure_prod_le_of_stableBase [DecidableEq F] [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    {S : Type*} [Fintype S] [Nonempty S]
    (σ : S → SRS G)
    (κ : ∀ s : S, Pf → (T → Pre) → (Fin (2 ^ (σ s).k) → F) × F × G)
    (rep : ∀ s : S, Pf → (T → Pre) → (Fin (2 ^ (σ s).k) → F) × F)
    (hrep : ∀ (s : S) (p : Pf) (O : T → Pre),
      (κ s p O).2.2 = commitGen (σ s).g (rep s p O).1 + (rep s p O).2 • (σ s).h)
    (uOf : S → Pf → (T → Pre) → G)
    (expand : Pre → F) (hexp_inj : Function.Injective expand) (hexp_ne : ∀ p, expand p ≠ 0)
    (A : S → Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : ∀ s : S, (A s).QueryBound Q)
    (proofOf : ∀ s : S, Pf → OpeningProof F G (σ s).k)
    (prefixes : ∀ s : S, Pf → Fin ((σ s).k + 1) → T)
    (dec : ∀ s : S, DecodesFromPrefixes (σ s) (proofOf s) (prefixes s))
    (D : ∀ s : S, Zcash.Snark.PrefixDecode T ((σ s).k + 1) (prefixes s))
    (hbase : ∀ s : S, BaseStable (A s) (prefixes s) (uOf s))
    (hstable : ∀ s : S, ClaimStable (A s) (prefixes s) (κ s))
    (coins : ∀ s : S, Zcash.Snark.RecursiveForkCoins Pre ((σ s).k + 1))
    (hcoins : ∀ s : S, (coins s).Complete)
    {k : ℕ} (hk : ∀ s : S, (σ s).k ≤ k) :
    (PMF.uniformOfFintype (S × (T → Pre))).toOuterMeasure
        {x | WinsAt (srsAt (σ x.1) (uOf x.1) ((A x.1).run x.2) x.2) expand (proofOf x.1)
              (prefixes x.1) (κ x.1) x.2 ((A x.1).run x.2) ∧
          kimchiExtract (srsAt (σ x.1) (uOf x.1) ((A x.1).run x.2) x.2)
              (κ x.1 ((A x.1).run x.2) x.2).1 (κ x.1 ((A x.1).run x.2) x.2).2.1
              (κ x.1 ((A x.1).run x.2) x.2).2.2
              (rep x.1 ((A x.1).run x.2) x.2).1 (rep x.1 ((A x.1).run x.2) x.2).2
              (hrep x.1 ((A x.1).run x.2) x.2) expand (A x.1) (proofOf x.1) (prefixes x.1)
              ((dec x.1).setBase (uOf x.1 ((A x.1).run x.2) x.2)) x.2 (coins x.1) = none}
      ≤ (Q + k + 1) * (3 / Fintype.card Pre) := by
  refine measure_prod_le_of_forall_fibre
    (fun (s : S) (O : T → Pre) =>
      WinsAt (srsAt (σ s) (uOf s) ((A s).run O) O) expand (proofOf s) (prefixes s) (κ s) O
          ((A s).run O) ∧
        kimchiExtract (srsAt (σ s) (uOf s) ((A s).run O) O) (κ s ((A s).run O) O).1
            (κ s ((A s).run O) O).2.1 (κ s ((A s).run O) O).2.2 (rep s ((A s).run O) O).1
            (rep s ((A s).run O) O).2 (hrep s ((A s).run O) O) expand (A s) (proofOf s)
            (prefixes s) ((dec s).setBase (uOf s ((A s).run O) O)) O (coins s) = none)
    fun s => le_trans
      (kimchiExtract_failure_measure_le_of_stableBase (σ s) (κ s) (rep s) (hrep s)
        (uOf s) expand hexp_inj hexp_ne (A s) (hQ s) (proofOf s) (prefixes s) (dec s)
        (D s) (hbase s) (hstable s) (coins s) (hcoins s)) ?_
  gcongr
  exact hk s

/-- **The varying-base failure bound over the joint measure**
(`cor:game-over-base-stable-recovery`). The present-day form of
`kimchiExtract_failure_measure_prod_le_of_stableBase`, kept verbatim for its consumers: each
fibre's base factors through that fibre's claimed value, hence is base-stable by
`baseStable_of_claimStable`. -/
theorem kimchiExtract_failure_measure_prod_le_of_stableU [DecidableEq F] [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    {S : Type*} [Fintype S] [Nonempty S]
    (σ : S → SRS G)
    (κ : ∀ s : S, Pf → (T → Pre) → (Fin (2 ^ (σ s).k) → F) × F × G)
    (rep : ∀ s : S, Pf → (T → Pre) → (Fin (2 ^ (σ s).k) → F) × F)
    (hrep : ∀ (s : S) (p : Pf) (O : T → Pre),
      (κ s p O).2.2 = commitGen (σ s).g (rep s p O).1 + (rep s p O).2 • (σ s).h)
    (uBase : S → F → G) (uOf : S → Pf → (T → Pre) → G)
    (huOf : ∀ (s : S) (p : Pf) (O : T → Pre), uOf s p O = uBase s (κ s p O).2.1)
    (expand : Pre → F) (hexp_inj : Function.Injective expand) (hexp_ne : ∀ p, expand p ≠ 0)
    (A : S → Zcash.Snark.OracleComp T Pre Pf) {Q : ℕ} (hQ : ∀ s : S, (A s).QueryBound Q)
    (proofOf : ∀ s : S, Pf → OpeningProof F G (σ s).k)
    (prefixes : ∀ s : S, Pf → Fin ((σ s).k + 1) → T)
    (dec : ∀ s : S, DecodesFromPrefixes (σ s) (proofOf s) (prefixes s))
    (D : ∀ s : S, Zcash.Snark.PrefixDecode T ((σ s).k + 1) (prefixes s))
    (hstable : ∀ s : S, ClaimStable (A s) (prefixes s) (κ s))
    (coins : ∀ s : S, Zcash.Snark.RecursiveForkCoins Pre ((σ s).k + 1))
    (hcoins : ∀ s : S, (coins s).Complete)
    {k : ℕ} (hk : ∀ s : S, (σ s).k ≤ k) :
    (PMF.uniformOfFintype (S × (T → Pre))).toOuterMeasure
        {x | WinsAt (srsAt (σ x.1) (uOf x.1) ((A x.1).run x.2) x.2) expand (proofOf x.1)
              (prefixes x.1) (κ x.1) x.2 ((A x.1).run x.2) ∧
          kimchiExtract (srsAt (σ x.1) (uOf x.1) ((A x.1).run x.2) x.2)
              (κ x.1 ((A x.1).run x.2) x.2).1 (κ x.1 ((A x.1).run x.2) x.2).2.1
              (κ x.1 ((A x.1).run x.2) x.2).2.2
              (rep x.1 ((A x.1).run x.2) x.2).1 (rep x.1 ((A x.1).run x.2) x.2).2
              (hrep x.1 ((A x.1).run x.2) x.2) expand (A x.1) (proofOf x.1) (prefixes x.1)
              ((dec x.1).setBase (uOf x.1 ((A x.1).run x.2) x.2)) x.2 (coins x.1) = none}
      ≤ (Q + k + 1) * (3 / Fintype.card Pre) :=
  kimchiExtract_failure_measure_prod_le_of_stableBase σ κ rep hrep uOf expand hexp_inj hexp_ne A
    hQ proofOf prefixes dec D
    (fun s => baseStable_of_claimStable (hstable s) (fun c => uBase s c.2.1)
      fun O => huOf s ((A s).run O) O)
    hstable coins hcoins hk

/-- **The base-stable failure bound over the joint measure, with the run-level hypotheses only** —
`kimchiExtract_failure_measure_prod_le_of_stableBase` with `hrep` demanded only at the run's own
proof `p = (A s).run O`, the shape in which an algebraic-group adversary supplies it. See
`kimchiExtract_failure_measure_le_of_stableBase_of_runRep` for why the re-packaging is exact:
`κ s`, `rep s` and `uOf s` are unconstrained off the run, so replacing each by its value there
changes nothing in the statement, and the fibrewise base hypothesis passes through by a β-step. -/
theorem kimchiExtract_failure_measure_prod_le_of_stableBase_of_runRep [DecidableEq F]
    [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    {S : Type*} [Fintype S] [Nonempty S]
    (σ : S → SRS G) (A : S → Zcash.Snark.OracleComp T Pre Pf)
    (κ : ∀ s : S, Pf → (T → Pre) → (Fin (2 ^ (σ s).k) → F) × F × G)
    (rep : ∀ s : S, Pf → (T → Pre) → (Fin (2 ^ (σ s).k) → F) × F)
    (hrep : ∀ (s : S) (O : T → Pre), (κ s ((A s).run O) O).2.2 =
      commitGen (σ s).g (rep s ((A s).run O) O).1 + (rep s ((A s).run O) O).2 • (σ s).h)
    (uOf : S → Pf → (T → Pre) → G)
    (expand : Pre → F) (hexp_inj : Function.Injective expand) (hexp_ne : ∀ p, expand p ≠ 0)
    {Q : ℕ} (hQ : ∀ s : S, (A s).QueryBound Q)
    (proofOf : ∀ s : S, Pf → OpeningProof F G (σ s).k)
    (prefixes : ∀ s : S, Pf → Fin ((σ s).k + 1) → T)
    (dec : ∀ s : S, DecodesFromPrefixes (σ s) (proofOf s) (prefixes s))
    (D : ∀ s : S, Zcash.Snark.PrefixDecode T ((σ s).k + 1) (prefixes s))
    (hbase : ∀ s : S, BaseStable (A s) (prefixes s) (uOf s))
    (hstable : ∀ s : S, ClaimStable (A s) (prefixes s) (κ s))
    (coins : ∀ s : S, Zcash.Snark.RecursiveForkCoins Pre ((σ s).k + 1))
    (hcoins : ∀ s : S, (coins s).Complete)
    {k : ℕ} (hk : ∀ s : S, (σ s).k ≤ k) :
    (PMF.uniformOfFintype (S × (T → Pre))).toOuterMeasure
        {x | WinsAt (srsAt (σ x.1) (uOf x.1) ((A x.1).run x.2) x.2) expand (proofOf x.1)
              (prefixes x.1) (κ x.1) x.2 ((A x.1).run x.2) ∧
          kimchiExtract (srsAt (σ x.1) (uOf x.1) ((A x.1).run x.2) x.2)
              (κ x.1 ((A x.1).run x.2) x.2).1 (κ x.1 ((A x.1).run x.2) x.2).2.1
              (κ x.1 ((A x.1).run x.2) x.2).2.2
              (rep x.1 ((A x.1).run x.2) x.2).1 (rep x.1 ((A x.1).run x.2) x.2).2
              (hrep x.1 x.2) expand (A x.1) (proofOf x.1) (prefixes x.1)
              ((dec x.1).setBase (uOf x.1 ((A x.1).run x.2) x.2)) x.2 (coins x.1) = none}
      ≤ (Q + k + 1) * (3 / Fintype.card Pre) :=
  kimchiExtract_failure_measure_prod_le_of_stableBase σ (fun s _ O => κ s ((A s).run O) O)
    (fun s _ O => rep s ((A s).run O) O) (fun s _ O => hrep s O)
    (fun s _ O => uOf s ((A s).run O) O) expand hexp_inj hexp_ne A hQ
    proofOf prefixes dec D hbase hstable coins hcoins hk

/-- **The varying-base failure bound over the joint measure, with the run-level hypotheses only** —
`kimchiExtract_failure_measure_prod_le_of_stableU` with `hrep` and `huOf` demanded only at the
run's own proof `p = (A s).run O`, the shape in which an algebraic-group adversary supplies them.
See `kimchiExtract_failure_measure_le_of_stableU_of_runRep` for why the re-packaging is exact:
`κ s`, `rep s` and `uOf s` are unconstrained off the run, so replacing each by its value there
changes nothing in the statement. -/
theorem kimchiExtract_failure_measure_prod_le_of_stableU_of_runRep [DecidableEq F] [DecidableEq G]
    [Fintype T] [DecidableEq T] [Fintype Pre] [DecidableEq Pre] [Nonempty Pre] [Zero Pre]
    {S : Type*} [Fintype S] [Nonempty S]
    (σ : S → SRS G) (A : S → Zcash.Snark.OracleComp T Pre Pf)
    (κ : ∀ s : S, Pf → (T → Pre) → (Fin (2 ^ (σ s).k) → F) × F × G)
    (rep : ∀ s : S, Pf → (T → Pre) → (Fin (2 ^ (σ s).k) → F) × F)
    (hrep : ∀ (s : S) (O : T → Pre), (κ s ((A s).run O) O).2.2 =
      commitGen (σ s).g (rep s ((A s).run O) O).1 + (rep s ((A s).run O) O).2 • (σ s).h)
    (uBase : S → F → G) (uOf : S → Pf → (T → Pre) → G)
    (huOf : ∀ (s : S) (O : T → Pre),
      uOf s ((A s).run O) O = uBase s (κ s ((A s).run O) O).2.1)
    (expand : Pre → F) (hexp_inj : Function.Injective expand) (hexp_ne : ∀ p, expand p ≠ 0)
    {Q : ℕ} (hQ : ∀ s : S, (A s).QueryBound Q)
    (proofOf : ∀ s : S, Pf → OpeningProof F G (σ s).k)
    (prefixes : ∀ s : S, Pf → Fin ((σ s).k + 1) → T)
    (dec : ∀ s : S, DecodesFromPrefixes (σ s) (proofOf s) (prefixes s))
    (D : ∀ s : S, Zcash.Snark.PrefixDecode T ((σ s).k + 1) (prefixes s))
    (hstable : ∀ s : S, ClaimStable (A s) (prefixes s) (κ s))
    (coins : ∀ s : S, Zcash.Snark.RecursiveForkCoins Pre ((σ s).k + 1))
    (hcoins : ∀ s : S, (coins s).Complete)
    {k : ℕ} (hk : ∀ s : S, (σ s).k ≤ k) :
    (PMF.uniformOfFintype (S × (T → Pre))).toOuterMeasure
        {x | WinsAt (srsAt (σ x.1) (uOf x.1) ((A x.1).run x.2) x.2) expand (proofOf x.1)
              (prefixes x.1) (κ x.1) x.2 ((A x.1).run x.2) ∧
          kimchiExtract (srsAt (σ x.1) (uOf x.1) ((A x.1).run x.2) x.2)
              (κ x.1 ((A x.1).run x.2) x.2).1 (κ x.1 ((A x.1).run x.2) x.2).2.1
              (κ x.1 ((A x.1).run x.2) x.2).2.2
              (rep x.1 ((A x.1).run x.2) x.2).1 (rep x.1 ((A x.1).run x.2) x.2).2
              (hrep x.1 x.2) expand (A x.1) (proofOf x.1) (prefixes x.1)
              ((dec x.1).setBase (uOf x.1 ((A x.1).run x.2) x.2)) x.2 (coins x.1) = none}
      ≤ (Q + k + 1) * (3 / Fintype.card Pre) :=
  kimchiExtract_failure_measure_prod_le_of_stableBase_of_runRep σ A κ rep hrep uOf expand
    hexp_inj hexp_ne hQ proofOf prefixes dec D
    (fun s => baseStable_of_claimStable (hstable s) (fun c => uBase s c.2.1) (huOf s))
    hstable coins hcoins hk

end FibreLift

end Bulletproof.Forking
