# The locked target

One statement. It does not change. Everything else in `Forking/` is justified only by whether it
is needed to reach it.

## Source in ironwood

`Zcash.Snark.ComputedAlgebraicFSFamily.acceptExtractionFailure_measure_le`,
`Zcash/Snark/Soundness/Forking/Adversary/Algebraic.lean:1176-1179`:

```lean
theorem acceptExtractionFailure_measure_le (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure (family.acceptExtractionFailure basis)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp)
```

Success-side exit: `DeployedAlgebraicForkingInstance.runToSnark` (`Algebraic.lean:825-837`),
returning `S ⊕' AlgebraicRelationWitness (F := Fp) basis`.

Why this and not `Soundness/Main.lean`: `FiatShamirTree` is labelled "**Legacy** interface"
(`Main.lean:189-192`); every deployed theorem there is `_of_forked` and takes
`fs : ForkedTranscript` as a hypothesis (`:253`, `:279`), i.e. assumes the fork already happened;
and the module docstring says "The computed route is in `Forking.Adversary.Algebraic`;
`KnowledgeSoundness` records its computational boundary" (`Main.lean:46`, echoed at
`KnowledgeSoundness.lean:10-12`).

## The target

`Bulletproof.Ipa.Forking.deployedExtract_failure_measure_le`, at
`bulletproof-pcs/Bulletproof/Forking/Deployed.lean:795`. This text is frozen:

```lean
theorem deployedExtract_failure_measure_le
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hinj : Function.Injective (expandPre C)) (hne : ∀ q, expandPre C q ≠ 0)
    (σ : SRS C.Point) (claim : Ipa.Input C σ.k m p)
    (pg : Fin (2 ^ σ.k) → C.ScalarField) (pw : C.ScalarField)
    (hP : combinedCommitment claim.polyscale claim.commitmentFn
      = commitGen σ.g pg + pw • σ.h)
    (A : Zcash.Snark.OracleComp (IpaNode C σ.k) Prechallenge (Ipa.Proof C σ.k))
    {Q : ℕ} (hQ : A.QueryBound Q)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (σ.k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype (IpaNode C σ.k → Prechallenge)).toOuterMeasure
        {O | wireWins σ claim O (A.run O) ∧
          deployedExtract σ (Ipa.cipOf claim)
              (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn)
              (Ipa.cipOf claim) (combinedCommitment claim.polyscale claim.commitmentFn)
              pg pw hP A O coins = none}
      ≤ (Q + σ.k + 1) * (3 / (2 ^ 128 : ℕ))
```

The extractor it measures is `deployedExtract` (`Deployed.lean:775`) — a plain `def`, returning
`Option (OpeningOrBreak {σ with U := uBaseOf C cip} P b v)`, where `OpeningOrBreak` is an `abbrev`
(`Game.lean:110`):

```lean
abbrev OpeningOrBreak (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F) (v : F) : Type _ :=
  (Σ' (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ)
    ⊕' Zcash.Snark.AlgebraicRelationWitness (F := F)
        (Zcash.Snark.augmentedBasis σ.g σ.U σ.h)
```

## Correspondence

| ironwood | here |
| --- | --- |
| `fsWinsFull … (fullAlgebraicAcceptZ …) coins.1` | `wireWins σ claim O (A.run O)` |
| `¬ (instanceAttempt basis coins).output.isSome` | `deployedExtract … = none` |
| `family.Q + shape.k` | `Q + σ.k + 1` |
| `3 / Fintype.card Fp` | `3 / (2 ^ 128 : ℕ)` |
| `S ⊕' AlgebraicRelationWitness basis` | `OpeningOrBreak` |
| one AGM root representation per `basis` | `pg`, `pw`, `hP` |

The win condition here is strictly tighter than upstream's: theirs is an `accept` predicate applied
to challenge values, ours is `Ipa.verifyWith … = true`, the executable wire verifier's own `Bool`
(`Wire.lean:262`), wrapped as the win event this measure is taken at (`def wireWins`,
`Deployed.lean:412`). Our `Wins` equals `fsWinsFull` at `m = 0` by `Iff.rfl`, pinned in
`bulletproof-pcs/scripts/check_ironwood_generic.lean` §7.

## Three deliberate differences from upstream

1. `Q + σ.k + 1` rather than `Q + shape.k` — the `+1` is kimchi's Schnorr wrapper round, which
   halo2 does not have.
2. `3 / 2 ^ 128` rather than `3 / Fintype.card Fp` — the challenges are 128-bit prechallenges
   pushed through `endoExpand`. Dividing by `|F| ≈ 2 ^ 254` understates the per-round cost by
   about `2 ^ 126`; that is the defect that condemned kimchi's `Forking/GuardEscape.lean`, since
   deleted on exactly that reasoning (step 1 of `forking-consolidation-plan.md`). This is the
   corrected analogue, not a weakened one.
3. No `z = 0` slice. Upstream carries an extra `(family.Q + 1) * (1 / Fintype.card Fp)` summand for
   the adaptive zero-challenge case (`snarkNonRelationFailure_measure_le`,
   `Algebraic.lean:1198-1202`).
   Here `hne` makes that slice empty.

## Deliberately out of scope

Upstream reaches `S` through `SnarkRelation` (`KnowledgeSoundness.lean:35-38`), which bundles the
IPA opening *and* `circuitSat`. `bulletproof-pcs` is a polynomial commitment, not a SNARK, so the
conclusion here carries only the opening half. The circuit half is kimchi's, and it is where the
Fiat–Shamir boundary lives — as `structure FSFaithful`
(`kimchi/Kimchi/Verifier/Forking/Bridge.lean:93`), a per-statement hypothesis bundle. (The
`hencodes` hypothesis and the four `poseidon_fiat_shamir_*` use sites this section once named are
both gone *as declarations*: `hencodes` occurs in no Lean source of the five packages, and
`poseidon_fiat_shamir_*` survives only as retrospective prose — the five surviving mentions are
enumerated in *It closed, and the retirement landed better than planned* below. The scope
statement itself stands.)

## Every hypothesis is discharged by an existing theorem

The statement is not conditional on anything un-witnessed — the failure mode this project has hit
before.

| hypothesis | discharged by |
| --- | --- |
| `hinj` | `expandPre_{vesta,pallas}_injective` (`Deployed.lean:105`, `:110`) |
| `hne` | `expandPre_{vesta,pallas}_ne_zero` (`Deployed.lean:116`, `:120`) |
| `hsmul` | `Pasta.{vesta,pallas}_smul_val` (`pasta/Pasta/Basic.lean:148`, `:152`) |
| `[Module C.ScalarField C.Point]` | `{vesta,pallas}PointModule` (`pasta/Pasta/Basic.lean:135`, `:141`) |
| `hcoins` | `RecursiveForkTape.toCoins_complete` (`Recursive.lean:147`) |

There is **no `hbind`**. Binding failures are returned as `AlgebraicRelationWitness` in the right
disjunct — which is what removed the hypothesis the former `ipaVesta_sound` carried. That chain no
longer exists: `Bulletproof/Reflection.lean` is 174 lines and contributes the reflection layer
alone, recording the retirement in its own preamble (`Reflection.lean:29-31`).

## What makes it non-vacuous

The bound is satisfiable by an extractor that always answers `none` if the win set is empty, and it
would be false if the win condition were reachable without knowledge. Both are excluded, and both
exclusions are part of the target:

* `honestNode_wireWins_everywhere` (`Honest.lean:706`) — the honest machine wins on every table,
  stated at the `wireWins` event the measure is about.
* `verifyWith_of_deferred_delta` (`Deployed.lean:939`) — with `δ` chosen after reading `c`, the wire
  verifier accepts at any claim while knowing nothing. Commit-then-challenge
  (`decodesFromPrefixes_nodes`, `Deployed.lean:226`) is what excludes it.

Deleting either one voids the target even if the bound still compiles.

## It closed, and the retirement landed better than planned

The target is proved, and the retirement it was for — the point of the exercise, not the bound
itself — happened *differently* from the plan recorded here. The plan was two per-curve corollaries
replacing the `poseidon_fiat_shamir_{vesta,pallas}` **axioms** at four kimchi use sites. What
actually landed:

* The two axioms are **0 declarations**. They were not swapped for corollaries; they were deleted.
  The five surviving `poseidon_fiat_shamir` mentions in the tree are all retrospective prose
  (`Bulletproof/Reflection.lean:29`, `Forking/{Game,Transcript}.lean`,
  `bulletproof-pcs/scripts/check_axioms.lean:72`) recording that deletion.
* The Fiat–Shamir boundary is now `structure FSFaithful`
  (`kimchi/Kimchi/Verifier/Forking/Bridge.lean:93`) — a hypothesis bundle discharged per statement,
  which is why the whole tree declares **zero** axioms. A hypothesis on the statements that need it
  is strictly better than an axiom in the environment: it cannot leak into a statement that does
  not name it.
* The per-curve endpoints are `ipa{Vesta,Pallas}_knowledge_sound`
  (`bulletproof-pcs/Bulletproof/Forking/KnowledgeSoundness.lean:902`, `:920`), not corollaries of
  this theorem's hypothesis-discharge alone.
* The four cited use sites were in `kimchi/…/Capstone/Standard.lean`, which **does not exist**
  anywhere in the tree — the kimchi capstone landed as `Capstone/{Algebraic,Reflection}.lean` (see
  `kimchi-reorg.md`).

So the goal this section set was exceeded, not merely met. Nothing below the bound is conditional on
an axiom.

## Regeneration policy (external-audit A-4)

Re-pinning an `.expected` file (`--regen`) is a statement change. It lands as an **isolated
commit** whose message quotes the statement diff verbatim — never folded into a lint,
refactor or feature commit — so the change of WHAT is proved is reviewable on its own.
Same-PR regeneration is inherently invisible to the gate itself (it is textual); the
isolated-commit rule is what makes it visible to review.
