# A primitive set for completeness proofs

## What this proposes

Eight rules for `Complete`, replacing the current situation in which 55 of the tree's 68
`_complete` laws unfold the definition and manipulate `Runs` and `Sat` by hand.

The proposal is scoped deliberately. It fixes the **plumbing spiral** — state bookkeeping,
`Runs`/`Sat` construction, monotonicity threading — and it comes with a mechanism that
makes "no further plumbing rules" enforceable rather than hoped for. It does **not** fix
the **interface spiral** — the growth of postcondition shapes and the adapters between
them. Section 7 says why not, and why that is a different problem.

## 1. The measurement

| | |
| --- | --- |
| `_complete` laws in the tree | 68 |
| files using the existing combinators | 4 |
| laws that unfold `Complete` | ~55 |
| files outside `Prover.lean` naming `Runs` or `Sat` | 19 |
| `Sat.` uses outside `Prover.lean` | 150 |
| `Mono` vocabulary | `and`, `readsAs`, `onCurveAs` |

The current API is `seq`, `imp`, `pure_of`, `pure`, `post`. `seq` is bind fused with the
frame rule, which is why `Mono` appears at every call site rather than in one place.

## 2. The rules

### Interpretation — one per constructor

`CircuitM` has exactly three:

```lean
inductive CircuitM (F c : Type u) (α : Type v)
  | pure (a : α)
  | addConstraintOp (con : c) (k : CircuitM F c α)
  | existsOp (n : Nat) (wit : AsProver F (Vector F n)) (k : Vector Variable n → CircuitM F c α)
```

so there are three interpretation rules, and the count is forced by the type rather than
chosen.

```lean
/-- `pure` at a postcondition the entry state already satisfies. -/
theorem Complete.pure_of (h : ∀ st, pre st → post a st) :
    Complete pre (pure a : CircuitM F c α) post                        -- EXISTS

/-- One emitted row, whose obligation is the caller's, at every extension of the table
the run lands in. -/
theorem Complete.addConstraint {con : c}
    (h : ∀ st, pre st → ∀ stf : ProverState F, st.env.Le stf.env →
      ConstraintHolds.Holds stf.env.get con) :
    Complete pre (Snarky.addConstraint con) fun _ st => pre st        -- MISSING

/-- A witnessed bundle: the computation succeeds at the entry table, and the fresh cells
read as its value. -/
theorem Complete.witness [CircuitType F val var] [CheckedType F c val var]
    (compute : AsProver F val) (v : val)
    (hv : CheckedType.Valid (F := F) (c := c) (var := var) v) :
    Complete (fun st => compute.run st.env = .ok v)
      (witness (c := c) (val := val) compute)
      (fun r st' => CircuitType.ReadsAs st' r v)                       -- EXISTS, BELOW THE
                                                                        -- ABSTRACTION
```

`witness_complete` today concludes a raw
`∃ r st', Runs … ∧ Sat … ∧ st.nv ≤ st'.nv ∧ st.env.Le st'.env ∧ Scoped … ∧ Reads …`.
The two order facts are exposed because callers use them to transport their own context
across the witness — that is `frame`, done by hand. With `frame` available they are not
needed, and the statement collapses to the `Complete` above.

### Structural — one per way of relating specifications

```lean
/-- Sequencing. The head's post IS the tail's pre, stated at the head's own final state,
so nothing has to cross the run — and there is no side condition. -/
theorem Complete.bind (hg : Complete pre g mid) (hk : ∀ a, Complete (mid a) (k a) post) :
    Complete pre (g >>= k) post

/-- The rule of consequence. -/
theorem Complete.imp (hpre : ∀ st, pre' st → pre st)
    (hpost : ∀ a st, post a st → post' a st) (h : Complete pre g post) :
    Complete pre' g post'

/-- The frame rule: a monotone fact the program does not disturb crosses it. The only
rule that mentions `Mono`. -/
theorem Complete.frame (hR : Mono (F := F) R) (h : Complete pre g post) :
    Complete (fun st => pre st ∧ R st) g fun a st' => post a st' ∧ R st'
```

### The precondition as a set

Two rules, dual to each other, about what the precondition *ranges over* rather than what
the program does.

```lean
/-- A precondition nothing satisfies is complete for any program. -/
theorem Complete.of_false (h : ∀ st, ¬ pre st) : Complete pre g post

/-- A precondition that determines a parameter the law is indexed by. -/
theorem Complete.instantiate {ι : Type} {P : ι → ProverState F → Prop}
    (h : ∀ st, pre st → ∃ i, P i st) (hg : ∀ i, Complete (P i) g post) :
    Complete pre g post
```

`instantiate` is what lets a law whose precondition carries only *scope* call a law indexed
by *values*: every scoped cell reads as something, and the something is chosen per state.
`powGo_complete` is that case — it recurses carrying `x.Scoped st`, while `mul_complete` is
indexed by `xv yv`. Without this rule that proof has to unfold.

## 3. Why this set and not another

**Layer 1 is forced.** Any proof must eventually say what the program *is*, and it is one
of three things. Fewer rules and some shape has no rule, so the author unfolds — which is
exactly what has happened. `addConstraint` has no rule, so `DSL/Assert.lean` and
`DSL/Boolean.lean` build `Runs.addConstraint` and `Sat.addConstraint` by hand, and every
law above them inherits the habit. More rules and a derived theorem is masquerading as a
primitive.

**`bind` needs no side condition.** In the current `seq`, `Mono pre` is consumed at
exactly one place:

```lean
hk a st₁ ⟨hpre _ _ hrun₁.nv_le hrun₁.le hpre₀, hmid⟩
        -- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

turning `pre st` into `pre st₁`, needed only because `hk`'s precondition is
`pre st ∧ mid a st`. When the continuation's precondition is `mid a`, that step does not
exist. The monotonicity requirement was never bind's; it was framing's, fused in.

**`imp` is Hoare's rule of consequence.** Without it every law must be stated in the exact
currency its caller holds. Five of the local `have`s in `Schnorr/Laws.lean` — `habs`,
`hpkAs`, `huAs`, `hzAs`, `hlow` — are `imp` written by hand.

**`of_false` is forced by state-dependent relations**, and the alternative was measured.
A law recursing on `bs` while the postcondition mentions `bvs`, tied only by
`Forall₂ (ReadsAs s) bs bvs`, has branches the precondition rules out — and the relation
lives *inside* the precondition, so it cannot index the recursion. Making the length
relation a state-free hypothesis does delete both branches, but then `update_complete`
needs `(toBlocksVar xs).length = (toBlocks vs).length`, whose only source is
`Forall₂.length_eq` on its own precondition — state-dependent again. The hypothesis
propagates through every caller up to `verifyCircuit_complete`. One local rule beats a
viral hypothesis.

**The set is closed at the top, and that is checked, not asserted.** `seq` — the rule four
files already depend on — is now derived:

```lean
theorem Complete.seq (hpre : Mono (F := F) pre) (hg : Complete pre g mid)
    (hk : ∀ a, Complete (fun st => pre st ∧ mid a st) (k a) post) :
    Complete pre (g >>= k) post :=
  Complete.bind
    (Complete.imp (fun _ h => ⟨h, h⟩) (fun _ _ h => ⟨h.2, h.1⟩) (Complete.frame hpre hg))
    hk
```

Five lines, no unfolding; the whole tree builds unchanged.

## 4. What existing proofs look like under it

`RandomOracle.lean`, all five laws, retrofitted and building:

| law | shape |
| --- | --- |
| `updateBlock_complete` | `imp` |
| `foldBlocks_complete` nil | `imp ∘ pure_of`, `of_false` on the vacuous branch |
| `foldBlocks_complete` cons | `bind (imp (frame Mono.forall₂ …)) (fun r => recurse)` |
| `update_complete` | `imp` |
| `hash2_complete`, `hashVec_complete` | `bind … (fun r => pure_of …)` |

The fold's cons case, before:

```lean
    rintro s ⟨hst, hbs⟩
    cases hbs with
    | cons hb hrest =>
      obtain ⟨r₁, s₁, hrun₁, hsat₁, hR₁⟩ := updateBlock_complete p hsize st b sv _ s ⟨hst, hb⟩
      obtain ⟨r₂, s₂, hrun₂, hsat₂, hR₂⟩ :=
        foldBlocks_complete p hsize bs _ r₁ _ s₁
          ⟨hR₁, hrest.imp fun _ _ h => h.mono hrun₁.nv_le hrun₁.le⟩
      refine ⟨r₂, s₂, hrun₁.bind hrun₂, fun hnv hle =>
        Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
          (hsat₂ hnv hle), ?_⟩
      simpa using hR₂
```

after:

```lean
      exact Complete.bind
        (Complete.imp (fun _ h => ⟨⟨h.1, (List.forall₂_cons.mp h.2).1⟩,
            (List.forall₂_cons.mp h.2).2⟩) (fun _ _ h => h)
          (Complete.frame Mono.forall₂ (updateBlock_complete p hsize st b sv bv)))
        fun r => foldBlocks_complete p hsize bs bvs r _
```

The deleted lines were `Complete.bind`'s own proof, inlined. `hrest.imp fun _ _ h =>
h.mono hrun₁.nv_le hrun₁.le` was `Mono` on `Forall₂ ReadsAs`, inlined because the lemma
did not exist.

File-level: `Sat` 6 → 0, `Runs` 0 → 0, 395 → 391 lines.

## 5. What it buys

`Runs` and `Sat` become `private` to `Prover.lean`, with seven consumers, all in that
file. `Mono` appears in one signature, `frame`'s. Targets:

| | now | after |
| --- | --- | --- |
| `Sat.` outside `Prover.lean` | 150 | 0 |
| `Runs` outside `Prover.lean` | 34 | 0 |
| files naming either | 19 | 1 |

Progress at time of writing: `Assert.lean`, `RandomOracle.lean` and `Field.lean` are
converted and at zero. 16 files remain.

## 6. Why the plumbing will not spiral

Not discipline — the module system.

The three interpretation rules are pinned to the constructor count: adding a fourth means
adding a constructor to `CircuitM`, which is a visible change to the language. The
structural rules are the standard Hoare set, and `seq` deriving from them is evidence the
set is adequate for the composition patterns already in the tree.

The enforcement is `private`. Once `Runs` and `Sat` are private to `Prover.lean`, a new
rule cannot be added anywhere else — any lemma needing them must be written in that file,
in a diff a reviewer sees. Convenience combinators (`Complete.foldl`, `Complete.forM`, and
so on) remain possible, but they must be *derived* from the seven, and the compiler
enforces that rather than a convention.

Two honest data points against complacency. `of_false` was **not** predicted by the a
priori analysis — the first retrofitted file found it. `Complete.instantiate` was not
predicted either — `powGo_complete`, the last law of the third file, found it. The bound on
layer 2 is therefore "small and reviewable", not "provably eight", and the discovery rate
is about one rule per two files converted. Both additions were duals of rules already
present rather than new machinery, which is weak evidence the set is converging.

## 7. What this does not fix, and why saying so matters

`Complete.bind` requires an intermediate assertion `mid`. One always exists — the
strongest postcondition — but it mentions `Runs`, so it cannot be written once `Runs` is
private. What makes the framework usable in practice is that each gadget law supplies a
*value-level* `mid`, phrased in `ReadsAs` / `OnCurveAs`. Nothing guarantees a given law's
`mid` is strong enough for a given consumer.

So privatising `Runs` converts "my `mid` is too weak" from a problem you can work around
by unfolding into a problem you must fix by restating the law. That is the right trade,
but it should be entered with eyes open: it makes interface debt *unavoidable* rather than
*absent*.

And interface debt is where the real growth has been. `Mono.readsAs`, `Mono.onCurveAs`,
`Mono.forall₂`, `Mono.const`; the `hbitsAs`, `habs`, `hcx` adapters — every one of these
is a postcondition shape or a bridge between two shapes. Seven rules do not reduce that
count by one. A separate answer is needed there, and the evidence so far says it is about
stating each law at the type its gadget actually operates on, not about adding lemmas.

## 8. What would settle adoption

The probe covered layers 2 and 3 only: `RandomOracle.lean` has no leaf laws, so
`Complete.addConstraint` and `Complete.witness` are still unwritten. Those are the rules
that decide whether `Runs`/`Sat` can actually go private, because they are the only
proposed consumers of them outside `Prover.lean`'s own proofs.

The test is `DSL/Assert.lean`: 9 laws, `Runs=3`, `Sat=8`, and the file where
`Runs.addConstraint` and `Sat.addConstraint` are constructed by hand today. If its
leakage reaches zero with the two new rules and no third one appears, the layer picture
holds and the remaining ~50 laws are mechanical. If a third leaf rule is needed, that is
the signal to stop and re-derive the set before touching the rest.
