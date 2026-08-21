# A frame rule for the prover-side `Complete` triples

**Status: PROPOSED, PROTOTYPE-VALIDATED — drafted 2026-08-21 out of the PR #313 review
discussion; validated the same day in the course repo (`~/code/lean`,
`Hoare/Frame.lean`), whose Chapter 7 `ProverSpec` is the same CPS encoding as
`Complete`, on the same toolchain and `Std.Do`. No snarky code started; see
"Prototype findings" below.** Scope: `formal/snarky` backend/law layer. The Sound
side, the gadget circuit definitions, and the plain-run-form export doctrine are
untouched.

## The problem

The snarky package's law pairs live in two program logics over the two interpreters:

- **`Sound`** runs the *builder* — total, effect-poor (bump a counter, append
  constraints). The valuation `V` in a Sound triple is a ghost object: universally
  quantified, static, never touched by the run. The triple assumes constraint
  satisfaction and harvests facts. Every harvested fact is about the one static `V`, so
  facts are ambient — established once, usable forever. `mvcgen` automates this side
  almost completely.
- **`Complete`** runs the *prover* — partial, operational (read/extend the concrete
  assignment table, run each decidable check as it goes). The triple is a progress
  proof about one execution trace: every operation's success condition must be
  established at the *current, evolving* state.

The prover's state evolution is monotone — `Assignments.Le` says the table only gains
entries — so almost every fact a completeness proof needs is *stable*: once true, true
at every later state. `x.eval env = .ok a` is the canonical case (`CVar.eval_le` is its
transport lemma); `Reads` (`Reads.le`) and `Readable` likewise. But the logic does not
know this. Every gadget spec's continuation hands the proof author a fresh
`hle : st.env.Le st'.env`, and the author re-transports each old fact forward by hand,
per fact, per step:

```lean
-- schnorr/Schnorr/Laws.lean:553-558 (actual shape)
have hux₄ := CVar.eval_le hle₆ (CVar.eval_le hle₅ (CVar.eval_le hle₄
  (CVar.eval_le hle₃ (CVar.eval_le hle₂ (CVar.eval_le hle₁ hux)))))
```

With `n` sequential gadgets this is O(n²) proof text. In the schnorr exemplar
(`verifyCircuit_complete_spec`, 9 sequential gadgets) the transport bookkeeping — the
`eval_le` towers, the `hle₁.trans (hle₂.trans …)` closers at `Laws.lean:603-604` — is
the dominant proof-text cost. The same pattern recurs in `unpack_complete_spec`,
`unpackFull_complete_spec`, and `ltBitstringValue_complete_spec`. The pickles fragments
will run dozens of sequential gadgets per circuit; the current style does not scale
there.

This is also why `mvcgen` pays off asymmetrically. Its two residual burdens on the
Complete side are (a) transporting old facts to the current state and (b) assembling
each gadget's precondition from facts scattered across several earlier states. A VC
generator can do neither without a frame rule, so its marginal value collapses to
"unfold the binds" — which `simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]`
does one step at a time, more predictably and without the prover-side normalization
hazard (the wp matches on the actual run; forcing it unfolds concrete-field circuits —
the whnf-bomb finding recorded in the PR #313 arc).

## The design

Transplant the standard mechanism for monotone-state programs: separation logic's
frame rule, in the form F* gives it for monotonic state (`witness`/`recall`, Ahman et
al., *Recalling a Witness*, POPL 2018; Iris's persistent propositions are the same
idea). The `Assignments.Le` order makes the prover interpreter exactly the setting
where this mechanism is complete.

### 1. The stable fragment

```lean
/-- An assignment-table predicate that survives table growth. -/
def Stable (P : Assignments F → Prop) : Prop :=
  ∀ env env', env.Le env' → P env → P env'
```

Plus a closure kit, each lemma trivial, tagged for automation:

- `stable_eval : Stable (fun env => x.eval env = .ok a)` — wraps `CVar.eval_le`
- `stable_reads : Stable (fun env => Reads env stv sv)` — wraps `Reads.le`
- `stable_readable`, `stable_isOk`
- `stable_le : Stable (fun env => a.Le env)` — wraps `Le.trans`. Frame the entry
  state's own `Le` and the composed extension witness is a projection at exit; the
  `hle₁.trans (hle₂.trans …)` closers go with the towers. (Prototype finding 1.)
- closure under `∧`, `∀`, `→` (constant antecedent), and constant predicates

The non-stable residue is deliberately small and stays outside the mechanism:
`FreshFrom`, the variable counter, and anything mentioning "unassigned".

### 2. The frame theorem

Target shape:

```lean
theorem Complete.frame {R : Assignments F → Prop} (hR : Stable R) :
    ⦃Complete pre post Q⦄ prog ⦃Q⦄ →
    ⦃Complete (fun env => pre env ∧ R env)
              (fun env r env' => post env r env' ∧ R env') Q⦄ prog ⦃Q⦄
```

Any stable fact holding at entry holds at exit — and, applied per bind, at every
intermediate state — without the proof author mentioning it.

Expected cost: near zero. The `Complete` precondition is CPS-shaped — destructuring
gives `⟨assumptions, hk⟩` where the continuation `hk` receives the result, the new
state, the post facts, and the `Le` witness. With that encoding the frame theorem
should be a two-line proof: instantiate the base triple with a continuation that
re-packs `R` transported through the handed-back `hle`:

```lean
intro st ⟨⟨hpre, hr⟩, hk⟩
exact base st ⟨hpre, fun r st' hpost hle => hk r st' ⟨hpost, hR _ _ hle hr⟩ hle⟩
```

**Validated:** the prototype's `ProverSpec.frame` compiled exactly as this sketch,
first try, sorry-free — and `Complete` (`Snarky/Backend/WP.lean:328`) is the same
CPS encoding, so the two-line proof transfers as written.

### 3. The `recall` tactic

Not built-in — ours to make; the name is F*'s. The seed version needs no
metaprogramming:

```lean
macro "recall" : tactic =>
  `(tactic| solve_by_elim (maxDepth := 16)
      [CVar.eval_le, Reads.le, Assignments.Le.trans, Assignments.Le.refl,
       And.intro, isOk_of_eq])
```

(The config precedes the lemma list — the validated form; the first draft here had
it after, which does not parse.)

Backward search over the hypotheses synthesizes exactly the `eval_le`/`trans` terms the
proofs currently write by hand. A polished `TacticM` version — index hypotheses by the
`env` they mention, compose the `Le` chain deterministically — is ~100 lines and only
worth writing if search proves slow at pickles scale. An `aesop` rule set
(`@[aesop safe]` on the transport lemmas) is the alternative zero-effort route.

### 4. Spec-statement conventions

Restate the `_complete_spec` house style so the mechanism composes:

- **Preconditions** stay as now (conjunctions of stable facts + the few genuinely
  semantic side conditions), but call sites discharge the stable conjuncts with
  `recall` instead of hand-lifted terms.
- **Postconditions** are already stated about the exit `env'` and are stable — no
  change needed to their content, only `Stable` instances so consumers may recall them
  arbitrarily later.
- The continuation shape `fun r st' hout hle => …` can stay; proofs simply stop
  *using* `hle` by hand. A later cosmetic pass could hide it.

### 5. Optional: `mvcgen` integration

If the Std.Do wp admits a registered frame lemma (`wp_frame_stable`), `mvcgen` can
auto-frame stable conjuncts across binds, and its generated VCs for a gadget call
reduce to the semantic side conditions — restoring symmetric value on both sides of
the law pairs. This is strictly optional: the frame theorem + `recall` deliver the
proof-text collapse even with the current manual/`mvcgen -trivial` hybrid style.
Treat as a stretch goal pending a look at how Std.Do's spec composition is extended.

## What proofs look like after

Before (current house style, one leg):

```lean
have hux₄ := CVar.eval_le hle₆ (CVar.eval_le hle₅ (… hux))
refine addFast_complete_spec … st₆ ⟨⟨isOk_of_eq hux₄, …⟩, fun rhs st₇ hout₇ hle₇ => ?_⟩
```

After:

```lean
refine addFast_complete_spec … ⟨by recall, fun rhs st₇ hout₇ _ => ?_⟩
```

The residual obligations per step are the semantic ones (on-curve, `toNat` bounds,
nonzero, the checker accepting an actual field identity) — the same content the Sound
proof also confronts. Both directions converge on the same texture: step through the
binds mechanically, discharge semantic side conditions, combine at the end.

## Prototype findings (2026-08-21)

The design was prototyped in the course repo (`~/code/lean`, new module
`Hoare/Frame.lean`, uncommitted): the stable fragment, the frame theorem, the
`recall` seed, `select` (three calls) proved by hand / by `recall` / framed under one
statement, and `isZero` (eight calls and a return) with zero hand-written transports.
The frame theorem is sorry-free; the pilots inherit the course's exercise `sorry`s
through its `WPMonad` instance, nothing else.

1. **Frame the origin's `Le` itself** (`stable_le`, now in the §1 kit). It subsumes
   the `hle₁.trans (hle₂.trans …)` closers: the composed witness is a projection at
   the end of the walk. The first draft of this doc missed it.
2. **`recall` alone already collapses the text.** Its search is effectively
   deterministic — at each state exactly one `Le` witness in scope has the right
   endpoint, so backward chaining does not branch — and it closed a seven-state
   transport in `isZero` with no guidance and no measurable elaboration cost. The
   frame's marginal value over the tactic is determinism plus never naming
   intermediate states; its call-site combinator form pays a constant per-call
   packaging overhead (choose `R`, seed it, re-pack the token), so below the
   crossover — facts travelling only a call or two — the `recall` style is the
   *shorter* proof, and at course scale it wins outright. Migration consequence:
   `recall` is the vehicle; the frame theorem lands as library substrate (the
   semantic justification, the fallback if search degrades at pickles scale, and the
   lemma any `mvcgen` auto-framing would register), not as surface syntax.
3. **Value-parameterized specs are load-bearing.** With `env x = some xv` as a
   statement parameter, every stable precondition conjunct is a `recall`-shaped goal
   and the postcondition is immediately usable. The `isSome`-plus-implication house
   shape — which `Complete`'s docstring mandates for `mvcgen` unification at call
   sites — forces a per-call `evalOk`/`injection`/`subst` dance that neither the
   frame nor `recall` can absorb (in `scaleRound_complete_spec`, ten facts re-pinned
   by hand). The two shapes trade registry compatibility against manual-application
   ergonomics; the transport collapse happens under either, the dance survives
   wherever the registry shape is kept.
4. **The residue is exactly the stated non-goal.** After the collapse what remains
   is: witness computations shown to succeed, and the returned value shown intended
   (the field case split at the end). The prototype left nothing else.

The measured snarky "before" for finding 2:
`Snarky/Kimchi/Circuit/VarBaseMul.lean`'s `scaleRound_complete_spec` — 164 lines,
41 `CVar.eval_le` applications, 61 hand-composed `.trans`es; the five bit rounds do
identical work but no two are textually identical (each differs by one more
`.trans`), and 22 of the final row assembly's 26 bullets are pure transport, each
tower's length the fact's birth-distance. Under `recall` the rounds become
copy-paste equal and the bullets one `by recall`.

## Staging

1. **Validate the encoding.** DONE — the prototype's carrier is the same encoding,
   and `Complete` was checked directly; the frame sketch compiled unchanged.
2. **Land the fragment.** `Stable` + closure kit + per-atom instances
   (`stable_eval`, `stable_reads`, …) in a small new module beside the triples
   (e.g. `Snarky/Backend/Stable.lean`). Wholesale-vs-targeted imports per the
   backend's existing convention.
3. **Land `Complete.frame`** and the `recall` seed macro.
4. **Pilot migration:** rewrite `unpack_complete_spec` or `unpackFull_complete_spec`
   (each ~60 lines, representative) using the mechanism. Measure proof-text delta and
   elaboration time before/after; abandon cheaply if either regresses.
5. **The payoff target:** `verifyCircuit_complete_spec` in the schnorr package — the
   9-gadget walk whose transport tax motivated this. Acceptance: zero hand-written
   `CVar.eval_le` chains in the proof body.
6. **Gates:** new public names into `snarky/roots.txt` (dead=0), axiom gate re-run
   (standard axioms only — nothing here touches the Pasta certs), style script, lint
   (docBlame on any new structure fields).
7. **Optional:** the `mvcgen` frame-lemma integration (step 5 above), as its own
   follow-up.

## Non-goals and caveats

- **Does not remove the operational core of completeness.** Witness computations must
  still be shown to succeed and each decidable check to accept; framing removes the
  bookkeeping, not the semantics.
- **Orthogonal to the plain-run-form export doctrine.** Concrete-field complete
  endpoints still export as `∃ out, prove … = .ok out ∧ Le` via `complete_spec_iff`;
  the whnf hazard around normalizing the prover wp's scrutinee is unchanged, and the
  one-bind-at-a-time `simp only [wp_bind]` stepping discipline stays where it is used.
- **The Sound side is untouched** — it has no transport problem to fix.
- **Risk: `solve_by_elim` search cost** on large contexts. The prototype did not
  reproduce it — the search is endpoint-deterministic (finding 2) — so the risk is
  confined to pickles-scale contexts. Mitigations, in order: the frame (constant-cost,
  searchless), then the deterministic `TacticM` version; the pilot (step 4) is where
  this gets measured on real contexts.
- ~~Risk: the actual triple encoding differs from the sketch~~ — discharged; see
  "Prototype findings".

## Why this is worth a library investment

It is a one-time cost in `Snarky/Backend` that changes the asymptotics of every
completeness proof afterward. The schnorr exemplar already pays O(n²) transport on 9
gadgets as the dominant proof-text cost; the pickles fragments (the architecture doc's
layers 3-6, `formal/docs/circuit-verifier-faithfulness.md`) will run dozens of
sequential gadgets per circuit, and their completeness walks are exactly this shape.
Per-proof effort forever versus one frame rule and a tactic.
