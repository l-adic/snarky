# Lean v4.35: the toolchain experiment

Four questions about moving the tree from Lean v4.30.0 to v4.35.0, asked in order: does the tree
build; does `vcgen` make the registration wrapper unnecessary; does a frame procedure carry
readings across a run; do the scalar-multiplication ladders' rounds still close. All four are
yes. The recommendation, at the end, is to bump now on `mvcgen` and move to `vcgen` next. Nothing
from the experiment lands but this note; its code is in the appendix.

Heartbeats are thousands of `maxHeartbeats` units, counted by `#count_heartbeats` under
`set_option Elab.async false`, on v4.35.0 unless marked.

## 1. The tree builds on v4.35.0, with two theorems open

Lean v4.35.0, Mathlib v4.35.0, CompPoly main, and the CompElliptic fork moved to both (one proof
repaired). Everything builds, the fixtures and the 13 executables included, with two theorems
stubbed. The repair took about two and a quarter hours and touches 44 Lean files (+267 −168) and
19 build files. Most of the build-file diff is Lake package manifests whose stale locks pinned
v4.30 revisions and overrode resolution; `require mathlib` moves last and the locks go.

What broke, by cause:

- **The transparency redesign.** The `instance` command now marks instances
  `[instance_reducible]`, so `simp` no longer reduces instance projections (`pure` of
  `CircuitM`'s monad, instance arguments); the fix cites the reducts (`build_pure`, unfolded
  definitions). Implicit arguments are compared at `implicit` transparency, so a semireducible
  definition in a type position no longer unfolds while matching: `SpongeStateVal` and
  `MaxProofsVerified` take `@[implicit_reducible]`. Without it, `Prover.poseidon_spec`'s `simpa`
  unfolds a 55-entry `Vector.ofFn` into 417k `List.rec` steps.
- **`simpa … using h` closes at reducible transparency.** `using!` keeps the old close.
- **Proofs inside definitions become `_proof_n` constants.** Rewriting under one (the size proof of
  a `#v[…]`) left the kernel a lazy-delta comparison that unfolds commitments and sponges:
  two kernel deterministic timeouts, in the verifier's stream (`runStreamP`) and in `lagrangeAt`.
  Rewriting whole `Vector.mk` blocks with `Vector.mk.injEq` removes both, with no heartbeat raise.
- **`do`-loop state is `Prod`**, not `MProd`: two fold lemmas restated.
- **Elaboration order** now fixes an implicit curve from an `rfl` argument: pinned with
  `(W := C.E.toAffine)`.
- **API.** CompPoly `CRingHom` is `CHom` and `Domain` lost `natCast_ne_zero`; Mathlib dropped
  `linear_combination'`, `deriving Fintype` fails on one enumeration, `HasSubset.Subset.trans` is
  deprecated; core `Vector.toList_toArray` is no longer `simp`; the core `Std.WP` `assert` shadows
  `Snarky.assert`.

Open:

- `Snarky.Kimchi.Prover.endoInv_spec`: `grind` fails on five `mvcgen` goals. v4.35's `mvcgen`
  presents a destructured pair as `(fst, snd) = r` with a `let`, and `grind` derives the scope of
  `r.2` but not of `r.1`.
- `Pickles.Application.WrapRun.terminal_group`: the closing `exact` times out in `isDefEq`.

A full build reports 1,061 warnings: 398 are the `mvcgen` deprecation ("use `vcgen` instead"),
376 renamed lemmas (`if_neg` 164, `if_pos` 110, `dif_pos` 37, `if_true` 23, `if_false` 18,
`dif_neg` 16, `push_neg` 7, one other), 61 the new `defProp` linter on the 61 `_reg` definitions,
and the rest linters. `scripts/check_reg_needed.lean`'s `#guard_msgs` trips on an extra
deprecation line.

## 2. The control passes under `vcgen`

`vcgen` reads only `Std.WP` goals (`Std.WP.wp`, `pre ⊑ wp …`, `Std.WP.Triple`); v4.35 has no
bridge from `Std.Do`, where the laws are stated. The experiment gives `CircuitM F (Prover c)` a
`Std.WP` interpretation over the existing `proverWP`, at `Prop`-valued state predicates, and a
bridge from the library's laws (appendix). With `mul`'s law registered bare (entry ghost `st₀`,
`st₀ ≤ s'`, no `Prover.Reg`), the control `twoMulLastU` closes under `vcgen` with the in-tree
`grind` line; standard axioms. The trace shows why: each application leaves the ghost a fresh
metavariable in its precondition goal, solved there, never by unifying the postcondition.

```
Applying spec Snarky.Prover.mulU_spec for mulU x y. Excess args: [s✝]
🎯 Target: ⊤ ⊑ (s✝ = ?m.76 ∧ CVar.Scoped ?m.76 x ∧ CVar.Scoped ?m.76 y)
Applying spec Snarky.Prover.mulU_spec for mulU y y. Excess args: [s✝]
🎯 Target: ⊤ ⊑ (s✝ = ?m.92 ∧ CVar.Scoped ?m.92 y ∧ CVar.Scoped ?m.92 y)
```

`mvcgen` on v4.35 still captures the ghost, so `Prover.Reg` goes only with the move to `vcgen`.

## 3. A frame procedure carries the readings

The frame is `CellsAt s₀ vs`: the cells `vs`, in scope at the entry `s₀`, are in scope at a later
state and read there what they read at `s₀`. One lemma, `Prover.frames_cellsAt`, shows that every
program frames it, by induction on the program; it is the one place `read_of_le` appears. The
`@[frameproc]` for `CircuitM` reads the call's context (the `Scoped` facts at the current state
or at a state equated with it, and the frame already carried there), frames those cells at their
current readings, and proves the entry obligation itself, so no frame goal reaches the user.
The leaves are the library's laws without `st₀ ≤ s'`.

GroupMap's candidates stage (`gmCandidates`, ten steps), with the in-tree statement less its order
conjunct:

```lean
  unfold gmCandidatesQ
  vcgen
  all_goals first
    | exact Prover.frames_cellsAt _ _ _
    | ((try simp only [CellsAt] at *)
       grind only [CVar.val, CVar.val_add_, CVar.val_sub_, CVar.Scoped.add_, CVar.Scoped.sub_,
         CVar.scoped_const, Kimchi.potentialXs])
```

No `le_chain`, no `read_of_le`, no carrying lemma; standard axioms. The frame grows a cell per
step, `[t]`, `[t2, t]`, `[alphaInv, t2, t]`, … up to
`[temp2a, t2PlusFuSq, t2Inv, temp1, t4Alpha, t4, alpha, alphaInv, t2, t]` at the tenth.

| Proof | Toolchain | Heartbeats | Tactic lines |
|---|---|---|---|
| in-tree, `le_chain` ([reading-transport.md](reading-transport.md)) | v4.30 | 53k | 33 |
| the same proof, verbatim | v4.35 | 34.8k | 33 |
| frame and `vcgen` | v4.35 | 19.0k | 7 |

Of the 19.0k, `vcgen` with the frame procedure is 1.6k, the ten `Frames` goals 0.2k, the ten
operand-scope preconditions 8.7k, and the readings goal the rest. The toolchain alone takes 53k to
34.8k; the frame takes 34.8k to 19.0k.

## 4. The ladders' rounds close as written

`Prover.scaleRound_spec`, `Prover.endoMulRound_spec` and `Prover.endoScalarRound_spec` close under
`vcgen` and the frame with their statements unchanged and no `round_readings`. `Prover.ScanStep`
keeps its order conjunct, now from a lemma about every run (`Prover.std_le`: a run's entry lies
below its exit) rather than from the leaves. The loop instances go through as written: the scan
corollary, unchanged, takes the `vcgen` round through a bridge back to `Std.Do`, its four
transports as in the tree. The corollary needs no restating; its triple form follows the laws'
move to `Std.WP`, like every other law's.

What the rounds need beyond §3:

- `vcgen simplifying_assumptions [ReadsAs.eq_1, scoped_prod', reads_prod', scoped_fvar,
  reads_fvar, …]` flattens a witness's postcondition into cell facts as it is introduced.
  `vcgen` splits a tuple result into variables, so two pair-projection lemmas join the list.
- `simplifying_assumptions` reaches neither the lifted entry precondition nor the frame
  hypotheses, which arrive through the frame rule's implication split. Each proof opens its
  precondition before `vcgen` (two lines), and the closer unfolds `CellsAt` and the round
  vocabulary itself; `grind` does not unfold them.
- One flattening lemma per `∀`-shaped bundle: `bitsScoped` (VarBaseMul, EndoMul), and
  `crumbsScoped` with the eight-entry `Vector.toList` (EndoScalar).

| Round | Calls | In-tree law and `round_readings` | Frame and `vcgen` | Lines | Loop instance |
|---|---|---|---|---|---|
| VarBaseMul | 6 | 29.1k | 34.3k | 79 → 37 | 0.8k → 0.5k |
| EndoMul | 1 | 11.0k | 7.5k | 54 → 35 | 0.8k → 0.4k |
| EndoScalar | 1 | 4.0k | 6.5k | 48 → 38 | 0.6k → 0.2k |

Lines count the law and its carrying lemma in the tree against the law and its flattening lemma
under the frame. The frame column runs the heavy closer on the final goal only; one closer for
every goal costs more (VarBaseMul 63.1k). VarBaseMul's 34.3k is 3.5k of `vcgen` and the frame
procedure and about 24k for the final goal: a 26-field row read across six frames.

## What the move would delete

| Item | Size | Needs |
|---|---|---|
| `Prover.Reg`, `Prover.Reg.iff`, `Prover.register` (`Snarky/Prover/WP.lean`) | 34 lines | `vcgen` |
| the `_reg` definitions | 61, 373 lines | `vcgen` |
| `Prover.Reg.iff` in `simp` and `grind` calls | 142 | `vcgen` |
| `Prover.register` wrappings | 95 | `vcgen` |
| `scripts/check_reg_needed.lean`, its CI step and README line | 59 + 2 lines | `vcgen` |
| order conjuncts in law postconditions | 76, in 21 files | `vcgen`, frame |
| `le_chain` | 15 lines; 46 uses (RangeCheck 21, GroupMap 16, AddComplete 9) | `vcgen`, frame |
| `round_readings` | 59 lines (VarBaseMul 28, EndoMul 17, EndoScalar 14) | `vcgen`, frame |
| carrying-lemma uses (`read_of_le`, `val_of_le`, `of_le`, …) | up to 247 | `vcgen`, frame |

What stays: the carrying lemmas themselves, which the frames lemma and the loop transports use;
`scaleRound_read_of_le` and the two `roundRead_of_le`, the loops' transports; `ScanStep`'s order
conjunct, free through `std_le`; the four transport premises of each loop instance. What is
added: the `Std.WP` interpretations (the prover's is about 50 lines; the `Builder` one was not
built), the frame and its lemma (about 60 lines), the frame procedure (about 90 lines of meta
code), the generic lemmas (about 70), and a flattening lemma per `∀`-shaped bundle. §3 and §4
tested four sites: the last four rows are what the tree has, not what the experiment removed.

## Recommendation: bump now, move to `vcgen` next

Bump now, as its own PR, on `mvcgen`. The bump is cheap (§1); Mathlib and CompPoly have moved
on; the one proof measured on both toolchains got a third cheaper from the toolchain alone; and
`mvcgen` is deprecated, so every proof written on v4.30 adds to the move. None of the deletions
comes with the bump, since `mvcgen` on v4.35 still captures the ghost (§2). The bump repairs
the two stubbed theorems, keeps `check_reg_needed.lean`'s guard on the capture, pins
CompElliptic's v4.35 main, renames the 376 deprecated lemmas to their replacements, and carries
none of the experiment's code.

Move to `vcgen` next, starting with a pilot. The move restates about 400 triples (811 lines) from
`Std.Do` to `Std.WP`, re-runs 398 `mvcgen` calls in 46 files (234 in pickles, 164 in snarky),
and needs a `Std.WP` interpretation of `Builder`, which this experiment did not build. `vcgen`
names its goals, orders hypotheses and lifts preconditions differently, so a proof that reaches
into `mvcgen`'s goals with `rename_i` or `case vcN` breaks; how many do is the open number. A
pilot on one file covering both sides (`Snarky/DSL/Field.lean`) measures it: mostly mechanical
means one follow-up PR, otherwise the move goes package by package. `Prover.Reg` and the rows
that need only `vcgen` go with the move itself. The frame procedure is a separate decision: it
removes the reading transport, but it sits on internal API of a tactic still opt-in and labelled
experimental, and its cost is uneven (GroupMap −45%, EndoMul −32%, VarBaseMul +18%,
EndoScalar +62%).

### Left for the move to `vcgen`

The bump leaves these in place on purpose; the move clears them.

- The 398 warnings that `mvcgen` is deprecated, in 46 files: every call becomes `vcgen` over a
  `Std.WP` triple.
- The 61 `defProp` warnings, one per `_reg` definition, and the 27 `scripts/nolints.json` entries
  for the public registrations and `le_chain` (`defLemma`, `defsWithUnderscore`): they go with
  `Prover.Reg` and, under the frame, with `le_chain`.
- `scripts/check_reg_needed.lean`, its CI step and README line: the expiry signal for the wrapper.
- The `Std.WP` interpretation of `Builder`, which the move needs and this experiment did not build.

## Appendix: the experiment's code

As run, on v4.35.0 with `set_option experimental.vcgen true`.

### The prover's reading in `Std.WP`

```lean
/-- The transformer is monotone in both conditions. -/
theorem proverWP_mono₂ [Zero F] [ConstraintHolds F c] {α : Type} {x : CircuitM F c α}
    {Q₁ Q₂ : α → ProverState F → ULift Prop} {E₁ E₂ : EvalError → ProverState F → ULift Prop}
    (hQ : ∀ a s, (Q₁ a s).down → (Q₂ a s).down) (hE : ∀ e s, (E₁ e s).down → (E₂ e s).down)
    {st : ProverState F} (hx : (proverWP x Q₁ E₁ st).down) : (proverWP x Q₂ E₂ st).down := by
  induction x generalizing st with
  | pure a => exact hQ a st hx
  | addConstraintOp con k ih =>
    simp only [proverWP] at hx ⊢
    exact ⟨hx.1, hx.2.1, ih hx.2.2⟩
  | existsOp n wit k ih =>
    simp only [proverWP] at hx ⊢
    rcases hr : wit.run st.env with e | xs <;> rw [hr] at hx
    · exact hE e st hx
    · exact ih _ hx

/-- The prover's reading as a `Std.WP` interpretation. -/
instance Prover.instStdWP [Zero F] [ConstraintHolds F c] {α : Type} :
    Std.WP.WP (CircuitM F (Prover c) α) α (ProverState F → Prop)
      (EvalError → ProverState F → Prop) where
  wpTrans x := ⟨fun post epost st =>
    (proverWP.{0} (c := Prover c) x (fun a s => ULift.up.{0} (post a s))
      (fun e s => ULift.up.{0} (epost e s)) st).down⟩
  wp_trans_monotone _ := fun _ _ _ _ hE hQ _ h =>
    proverWP_mono₂ (fun a s => hQ a s) (fun e s => hE e s) h

/-- The reading is a monad morphism. -/
instance Prover.instStdWPMonad [Zero F] [ConstraintHolds F c] :
    Std.WP.WPMonad (CircuitM F (Prover c)) (ProverState F → Prop)
      (EvalError → ProverState F → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := fun _ h => h
  bind_le_wp_bind x f post epost := fun st h => by
    show (proverWP.{0} (c := Prover c) (x >>= f) _ _ st).down
    rw [proverWP_bind]
    exact h

/-- The bridge: a law at the prover's reading, as the transformer it unfolds to, is a `Std.WP`
triple. -/
theorem Prover.std_of_wp [Zero F] [ConstraintHolds F c] {α : Type} {x : CircuitM F (Prover c) α}
    {P : ProverState F → Prop} {Q : α → ProverState F → Prop}
    (h : ∀ st, P st → (proverWP.{0} (c := Prover c) x (fun r s => ULift.up.{0} (Q r s))
      (fun _ _ => ULift.up.{0} False) st).down) :
    ⦃P⦄ x ⦃Q⦄ :=
  ⟨fun st hp => proverWP_mono₂ (fun _ _ h => h) (fun _ _ (h : False) => h.elim) (h st hp)⟩
```

### The frame, its lemma, and the order fact

```lean
/-- A run carries any predicate that survives table growth: the one transport fact, by
induction on the program. -/
theorem proverWP_frame [Zero F] [ConstraintHolds F c] {α : Type} {x : CircuitM F c α}
    {Fr : ProverState F → Prop} (hmono : ∀ s s', s ≤ s' → Fr s → Fr s')
    {Q₁ Q₂ : α → ProverState F → ULift Prop} {E : EvalError → ProverState F → ULift Prop}
    (hQ : ∀ a s, Fr s → (Q₁ a s).down → (Q₂ a s).down) {st : ProverState F} (hF : Fr st)
    (hx : (proverWP x Q₁ E st).down) : (proverWP x Q₂ E st).down := by
  induction x generalizing st with
  | pure a => exact hQ a st hF hx
  | addConstraintOp con k ih =>
    simp only [proverWP] at hx ⊢
    exact ⟨hx.1, hx.2.1, ih hF hx.2.2⟩
  | existsOp n wit k ih =>
    simp only [proverWP] at hx ⊢
    rcases hr : wit.run st.env with e | xs <;> rw [hr] at hx
    · exact hx
    · exact ih _ (hmono st (st.alloc xs) (st.dom.le_extendList _) hF) hx

/-- The cells `vs`, in scope at the entry `s₀`, are in scope at `s` and read there what they
read at `s₀`. -/
def CellsAt [Add F] [Mul F] [Zero F] (s₀ : ProverState F) : List (CVar F) → ProverState F → Prop
  | [], _ => True
  | v :: vs, s => (v.Scoped s ∧ s.read v = s₀.read v) ∧ CellsAt s₀ vs s

/-- Table growth keeps the frame. -/
theorem CellsAt.mono [Add F] [Mul F] [Zero F] {s₀ : ProverState F} :
    ∀ {vs : List (CVar F)} {s s' : ProverState F}, s ≤ s' → CellsAt s₀ vs s → CellsAt s₀ vs s'
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, hle, ⟨⟨hv, hr⟩, h⟩ =>
    ⟨⟨hv.of_le hle, (ProverState.read_of_le hle hv).trans hr⟩, CellsAt.mono hle h⟩

/-- Every program at the prover's reading frames `CellsAt s₀ vs`. -/
theorem Prover.frames_cellsAt [Field F] [ConstraintHolds F c] {α : Type}
    (x : CircuitM F (Prover c) α) (s₀ : ProverState F) (vs : List (CVar F)) :
    WP.Frames (@Lean.Order.meet (ProverState F → Prop) _) x (CellsAt s₀ vs) := by
  constructor
  intro Q E st h
  rw [meet_apply, meet_prop_eq_and] at h
  exact proverWP_frame (fun _ _ => CellsAt.mono) (Q₁ := fun a s => ULift.up.{0} (Q a s))
    (fun a s hF hq => show Lean.Order.meet (CellsAt s₀ vs) (Q a) s by
      rw [meet_apply, meet_prop_eq_and]; exact ⟨hF, hq⟩) h.1 h.2

/-- A run's entry lies below its exit: a property of every run, added to any law whose
precondition names the entry. -/
theorem Prover.std_le [Zero F] [ConstraintHolds F c] {α : Type} {x : CircuitM F (Prover c) α}
    {st₀ : ProverState F} {P : ProverState F → Prop} {Q : α → ProverState F → Prop}
    (h : ⦃fun s => s = st₀ ∧ P s⦄ x ⦃Q⦄) :
    ⦃fun s => s = st₀ ∧ P s⦄ x ⦃fun r s' => Q r s' ∧ st₀ ≤ s'⦄ :=
  ⟨fun st hp => proverWP_frame (Fr := (st₀ ≤ ·)) (fun _ _ h1 h2 => le_trans h2 h1)
    (Q₁ := fun r s => ULift.up.{0} (Q r s))
    (Q₂ := fun r s => ULift.up.{0} (Q r s ∧ st₀ ≤ s)) (fun _ _ hF hq => ⟨hq, hF⟩)
    (le_of_eq hp.1.symm) (h.le_wp st hp)⟩
```

### The frame procedure

```lean
/-! The frame procedure's proof that the entry state satisfies the frame it infers. -/

theorem CellsAt.rebase [Add F] [Mul F] [Zero F] {s₀ s : ProverState F} :
    ∀ {vs : List (CVar F)}, CellsAt s₀ vs s → CellsAt s vs s
  | [], _ => trivial
  | _ :: _, ⟨⟨hv, _⟩, h⟩ => ⟨⟨hv, rfl⟩, CellsAt.rebase h⟩

theorem CellsAt.nil_self [Add F] [Mul F] [Zero F] (s : ProverState F) : CellsAt s [] s := trivial

theorem CellsAt.cons_self [Add F] [Mul F] [Zero F] {s : ProverState F} {v : CVar F}
    {vs : List (CVar F)} (hv : v.Scoped s) (h : CellsAt s vs s) : CellsAt s (v :: vs) s :=
  ⟨⟨hv, rfl⟩, h⟩

theorem CVar.scoped_of_eq {s b : ProverState F} {v : CVar F} (h : s = b) (hv : v.Scoped b) :
    v.Scoped s :=
  h ▸ hv

namespace Q3

open Lean Meta Lean.Meta.Sym Lean.Meta.Sym.Internal Lean.Elab.Tactic.VCGen

/-- A hypothesis's conjuncts, each with its proof. -/
partial def facts (prop proof : Expr) : MetaM (Array (Expr × Expr)) := do
  let prop ← instantiateMVars prop
  match_expr prop with
  | And a b =>
    return (← facts a (← mkAppM ``And.left #[proof])) ++ (← facts b (← mkAppM ``And.right #[proof]))
  | _ => return #[(prop, proof)]

/-- The frame at the state `s` with its proof at `s`: the cells in scope there, read off the
local context (the `Scoped` facts at `s` or at a state equated with it, and the frame already
carried to `s`), each at its reading at `s`. -/
def cellsFrame (s : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut fs : Array (Expr × Expr) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless ← isProp decl.type do continue
    fs := fs ++ (← facts decl.type decl.toExpr)
  let mut aliases : Array (Expr × Expr) := #[]
  for (p, h) in fs do
    match_expr p with
    | Eq _ a b =>
      if a == s && b.isFVar then aliases := aliases.push (b, h)
      else if b == s && a.isFVar then aliases := aliases.push (a, ← mkEqSymm h)
    | _ => pure ()
  let mut old : Option (List Expr × Expr) := none
  for (p, h) in fs do
    match_expr p with
    | Snarky.CellsAt _ _ _ _ _ vs st =>
      if st == s then
        if let some (_, vs) := vs.listLit? then old := some (vs, h)
    | _ => pure ()
  let oldVs := (old.map (·.1)).getD []
  let mut new : Array (Expr × Expr) := #[]
  for (p, h) in fs do
    match_expr p with
    | Snarky.CVar.Scoped _ st v =>
      if oldVs.contains v || new.any (·.1 == v) then continue
      if st == s then new := new.push (v, h)
      else if let some (_, he) := aliases.find? (·.1 == st) then
        new := new.push (v, ← mkAppM ``Snarky.CVar.scoped_of_eq #[he, h])
    | _ => pure ()
  if new.isEmpty && old.isNone then return none
  let mut proof ← match old with
    | some (_, h) => mkAppM ``Snarky.CellsAt.rebase #[h]
    | none => mkAppM ``Snarky.CellsAt.nil_self #[s]
  for (_, hv) in new.reverse do
    proof ← mkAppM ``Snarky.CellsAt.cons_self #[hv, proof]
  let F := (← whnfR (← inferType s)).appArg!
  let vs := new.toList.map (·.1) ++ oldVs
  let frame ← mkAppM ``Snarky.CellsAt #[s, ← mkListLit (← mkAppM ``Snarky.CVar #[F]) vs]
  return some (frame, proof)

/-- Frame the cells in scope at the call's entry state, with their entry readings, and prove
the entry state satisfies the frame: no frame obligation reaches the user. -/
def cellsFrameProc : FrameInferenceProc := fun i => do
  let #[s] := i.unframedApp.excessArgs | return .decline
  let s ← instantiateMVars s
  let some (frame, proof) ← cellsFrame s | return .decline
  trace[Elab.Tactic.Do.vcgen] "cells frame: {frame}"
  return .commit i.unframedApp.excessArgs fun goal => do
    let frame ← shareCommon frame
    goal.frame.assign frame
    goal.footprint.assign i.pre
    let rhs ← mkAppNS (← mkAppNS (← i.mkOpApp) #[frame, goal.framedApp.wp]) i.unframedApp.excessArgs
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS i.le #[i.pre, rhs])
    let some gs ← goal.splitLatticeOp? m.mvarId!
      | throwError "frameproc: no lattice split applies to{indentExpr (← m.mvarId!.getType)}"
    -- the split leaves `pre ⊑ W s`, which the spec proves, and `pre ⊑ frame s`, which the
    -- frame's own proof does
    for g in gs do
      if (isWPApp? (← g.getType).appArg!).isSome then g.assign goal.specProof
      else
        let hle ← mkAppM ``Lean.Order.le_of_right #[i.pre, mkApp frame s, proof]
        unless ← isDefEq (← g.getType) (← Meta.inferType hle) do
          throwError "frameproc: the frame proof does not fit{indentExpr (← g.getType)}"
        g.assign hle
    return { splitVCProof := m, subgoals := [] }

/-- `CircuitM`'s frame procedure: the meet frame, inferred as the cells in scope. -/
@[frameproc] def cellsFP : FrameProc where
  prog := ``Snarky.CircuitM
  mkOpAppM := fun info => Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]
  mkResourceTy := fun info => pure info.Pred
  opHead := ``Lean.Order.meet
  proc := cellsFrameProc
end Q3
```
