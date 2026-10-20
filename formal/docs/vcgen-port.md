# The move to `vcgen`, pass 1: the Builder side

`mvcgen` is deprecated on v4.35.0 in favour of `vcgen`, which reads only `Std.WP` triples. The
tree's laws are `Std.Do` triples at two tags, the soundness reading `Builder V c` and the
prover's reading `Prover c`. The two are independent law families: a proof at one tag consumes
laws at that tag alone. This pass moves the Builder family and nothing else, as one PR.

## Scope

In: the `Std.WP` interpretation of `build` (`Snarky/WP.lean`), the Builder-side primitive
specs, the `builder_spec_*` combinators, every Builder-side law and proof in `snarky` (19 files)
and in `pickles` (29 files, the whole package), the two gates that read the old shape (the
spec-locality marker, the axiom gate's tag check), and the docs.

Out, for the Prover pass: every law at the `Prover c` tag, `Prover.Reg` and the `_reg`
registrations, `scripts/check_reg_needed.lean` with its CI step and README line, the 27
`nolints.json` entries, and the `mvcgen` warnings those proofs keep. Out, as its own decision
after both passes: the frame procedure, and with it `le_chain`, `round_readings` and the order
conjuncts ([toolchain-4.35.md](toolchain-4.35.md), §3 and the recommendation).

One PR because `pickles` consumes `snarky`'s Builder laws: porting `snarky` first would need a
`Std.Do` form of each ported law for `pickles`, deleted when `pickles` follows.

## What v4.35.0 provides

Checked against the toolchain's sources and on scratch files against the built tree.

- `Std.WP.WP Prog Value Pred EPred` is keyed on the program type, with `wpTrans : Prog →
  PredTrans Pred EPred Value` and monotonicity as its two fields. `PredTrans` is one field,
  `apply : (Value → Pred) → EPred → Pred`; there is no conjunctivity obligation. `Pred` and
  `EPred` are any `CompleteLattice`; `Nat → Prop` is one pointwise, and `EStack⟨⟩`, the
  exception type of a monad that never throws, is `Unit` with its lattice (`Id`'s instance is
  `WP (Id α) α Prop EStack⟨⟩`).
- `Std.WP.WPMonad m Pred EPred` extends `LawfulMonad m` and asks for `toWP`, `pure_le_wp_pure`
  and `bind_le_wp_bind`, each one direction of the old equations.
- `Std.WP.Triple x pre post epost` is a structure with one field `le_wp : pre ⊑ wp x post
  epost`. The notation is `⦃P⦄ x ⦃Q⦄` (`epost` defaults to `⊥`) and `⦃P⦄ x ⦃Q; E⦄`, with
  `Q : Value → Pred` a plain function: `⇓` is `Std.Do`'s.
- Both libraries' triple notations are `scoped`, and `Std.Do` scopes `⌜⌝` too, so a scope opens
  one metatheory. A mixed file works with `open … in` per declaration or one `section` per
  metatheory; a `Std.Do` law proved by `mvcgen` and a `Std.WP` law proved by `vcgen` then sit in
  one file, verified both ways on a scratch file over `Snarky.DSL.Field`.
- `Std.Tactic.Do` provides `vcgen` but does not import `Std.WP`; `Snarky/WP.lean` imports both,
  and consumers reach them through it, as every `pickles` file reaches `mvcgen` today.
- `vcgen` is a `grind`-mode step: a VC its E-graph settles (a `True` conclusion, a hypothesis)
  closes during generation and the rest are left as goals. There is no trivial pass to skip.
- `Spec.forIn'_list` takes an `Invariant α β Pred`, a function of the consumed prefix, the
  remaining suffix and the accumulator; at `Nat → Prop` the counter is a fourth argument.
- `@[spec]` is one attribute over two databases: a `Std.Do` triple goes to `mvcgen`'s, a
  `Std.WP` triple or `⊑ wp` fact to `vcgen`'s, and neither tactic sees the other's. Both may
  hold a law for the same program, verified the same way with `div`.
- `vcgen` takes `[specs]`, `until pat`, `frames | f a => F`, `invariants`,
  `simplifying_assumptions [thms]` and `with step`; the `trivial` and `leave` config flags are
  accepted and ignored with a warning, so `-trivial` goes. Without `set_option
  experimental.vcgen true` every call warns.
- `Triple.and`, `Triple.mp` and `observe` need `[WPConjunctive x]`, which the library gives
  `Id`, `Option`, `Except`, `StateT`, `ReaderT` and `EStateM` only. There is no `mapM` spec;
  loops have `Spec.forIn'_list` and `Spec.foldlM_list`.
- `⌜p⌝` in `Lean.Order` is `if p then ⊤ else ⊥`; a precondition written that way reduces only
  through `ofProp_true`. The Builder preconditions are written `fun _ => True`.

## The pieces

### 1. `Snarky/WP.lean`: the interpretation

The transformer is the one in the tree, as a `PredTrans` built directly; monotonicity is one
application. The exception type is `EStack⟨⟩`, which `build` never reaches.

```lean
instance Builder.instWP {V : Valuation F} [ConstraintHolds F c] {α : Type} :
    WP (CircuitM F (Builder V c) α) α (Nat → Prop) EStack⟨⟩ where
  wpTrans x := ⟨fun post _ nv =>
    (∀ con ∈ (build x nv).constraints, ConstraintHolds.Holds V con) →
      post (build x nv).result (build x nv).nextVar⟩
  wp_trans_monotone _ := fun _ _ _ _ _ hpost nv h hsat => hpost _ _ (h hsat)

instance Builder.instWPMonad {V : Valuation F} [ConstraintHolds F c] :
    WPMonad (CircuitM F (Builder V c)) (Nat → Prop) EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := ...   -- `build (pure a) nv` emits nothing
  bind_le_wp_bind x f _ _ := ... -- `build_bind` splits the list: today's second bullet
```

The old `conjunctiveRaw` field and the `wp_pure`/`wp_bind` equations go. No `WPConjunctive`
instance: the combinators below are proved through `builder_spec_iff`, as today, so nothing
needs `Triple.and`. The two instances, `builder_spec_iff`, the schematic `addConstraint_spec`
and `builder_spec_mapM` under `vcgen` compile as written here on a scratch file against the
tree, axiom-clean, with the `mapM` proof's `rename_i` line unchanged.

### 2. The combinators: same names, same statements

They are consumer API, not helpers: `builder_spec_true` 114 uses, `_iff` 81, `_imp` 55,
`_vector_mapM_get` 22, `_and` 16, `_forall` 14, `_mapM` 6, `_bind_of` 3, `_of_map` 3, in about
20 files. Every one keeps its name and its statement up to notation, so a consumer changes by
notation alone. `builder_spec_iff` is the soundness lemma and the proof route for the rest:

```lean
theorem builder_spec_iff (g : CircuitM F (Builder V c) α) (post : α → Prop) :
    (⦃fun _ => True⦄ g ⦃fun r _ => post r⦄) ↔
      ∀ nv, (∀ con ∈ (build g nv).constraints, ConstraintHolds.Holds V con) →
        post (build g nv).result :=
  ⟨fun h nv hsat => h.le_wp nv trivial hsat, fun h => ⟨fun nv _ hsat => h nv hsat⟩⟩
```

`builder_spec_mapM` is the one combinator proved by the VC generator itself; its `mvcgen [hf,
ih]` becomes `vcgen [hf, ih]`. `builder_spec_of_map` and `builder_spec_bind_of` stay although
`vcgen` steps `<$>` and `>>=` itself: three uses each, and a consumer calling them is not
running the generator.

### 3. The primitive specs

`addConstraint_spec` takes the library's own shape for primitives (`Spec.get_StateT : Triple
get (fun s => post s s) post epost`): the postcondition schematic, the precondition the exact
weakest one, so a call leaves no entailment behind.

```diff
 @[spec] theorem addConstraint_spec {V : Valuation F} [ConstraintHolds F c]
-    (con : Builder V c) :
-    ⦃⌜True⌝⦄
-    addConstraint (F := F) (c := Builder V c) con
-    ⦃⇓ _ _ => ⌜ConstraintHolds.Holds V con⌝⦄ := by
-  intro nv _ hsat
-  exact hsat con (List.mem_cons_self ..)
+    (con : Builder V c) (Q : Unit → Nat → Prop) :
+    ⦃fun nv => ConstraintHolds.Holds V con → Q () nv⦄
+    addConstraint (F := F) (c := Builder V c) con
+    ⦃Q⦄ :=
+  ⟨fun _ h hsat => h (hsat con (List.mem_cons_self ..))⟩
```

`witness_spec` (`Snarky/Witness.lean`) keeps its forward form, `⦃fun _ => True⦄ witness compute
⦃fun r _ => S.post V r⦄`: its postcondition is the fact every consumer takes, and a schematic
form would quantify over a result for nothing.

### 4. The laws and proofs

Statements: `⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜p r⌝⦄` becomes `⦃fun _ => True⦄ g ⦃fun r _ => p r⦄`.
`pickles` opens `Std.Do` per file, which becomes `open Std.WP`; `snarky` opens it per Builder
law with `open Std.Do in`, which becomes `open Std.WP in`, and the Prover sections keep theirs.
`Snarky/WP.lean` imports `Std.WP`; consumers get the notation through it, and shake decides any
other import.

Proofs: `mvcgen` becomes `vcgen`, `mvcgen [..]` becomes `vcgen [..]`, `mvcgen -trivial` loses the
flag. Four kinds of repair go beyond that:

- Goal names and hypothesis order: `pickles` has 155 `rename_i` lines and 33 `case`/`next`
  lines after `mvcgen` calls, each a place a proof can break past the rename.
- Loop invariants, nine sites (`MessageHash` 4, `WrapVerify` 3, `Verify` 2): `⇓⟨xs, sv⟩ =>
  ⌜… xs.prefix …⌝` becomes a function of the consumed prefix, the suffix, the accumulator and
  the counter, and the preservation branch is re-proved against the new shape.
- Proofs that `intro` straight into the triple, about twenty in nine files (`witness_spec`, the
  traversal base cases, `GroupMap`, five `pickles` files): `Triple` is a structure, so they open
  with `⟨fun nv _ hsat => …⟩` or go through `builder_spec_iff` as the others already do.
- VCs the old trivial pass closed and `vcgen` leaves: counted when met.

`FinalizeOtherProof.lean` clears a concrete triple before one call because the trivial pass
unfolded its `wp` at great cost; `vcgen` internalises every hypothesis into its E-graph, so
that site gets a timing check before the rest of the file. The `with` clause, one `grind` step
sharing the generator's E-graph, is available where `all_goals grind [..]` follows the call
today, but is not part of the port.

Files, `snarky`: `WP.lean`, `Witness.lean`, `Traverse.lean`, `DSL/{Assert, Bits, Boolean, Field,
Utils}.lean` and `Kimchi/Circuit/{AddComplete, CheckedPoint, EndoMul, EndoScalar, GroupMap,
Point, Poseidon, RandomOracle, RangeCheck, Sponge, VarBaseMul}.lean`, most of them also holding
the Prover reading. `pickles`: the 29 files with a triple or an `mvcgen` call, and the three that
open `Std.Do` without one (`ShiftedClaims`, `TwoHalves`, `WrapScalarHalf`), whose `open` is
revisited.

`experimental.vcgen` is set once per package, in the `snarky` and `pickles` lakefiles'
`leanOptions`, as the style linter is. The `set_option mvcgen.warning false` lines stay: every
file that has one keeps a Prover section.

### 5. The gate and the docs

`scripts/check-spec-locality.sh` finds a triple statement by the literal `⦃⌜True⌝⦄`; the marker
becomes `⦃fun _ => True⦄` and the header's two `mvcgen` sentences are reworded. It checks 202
conclusions today and rejects only a count of zero, so a marker that missed half the statements
would pass: the count after the change must be 202 again, the floor rises to 200, and a foreign
gadget's spec restated on a scratch file must still fail it. `snarky/scripts/check_axioms.lean`
checks that `Std.Do.WP` resolves at the tag `Builder V c` and not at the bare carrier; both
checks move to `Std.WP.WP` at `CircuitM Nat (Builder … (Basic Nat)) Unit`, keeping the guard
against a generic instance. `CLAUDE.md`'s "composed by `mvcgen`" now names both generators
until the Prover pass; the README's `check_reg_needed` line and `toolchain-4.35.md` stay, the
latter as the record of the experiment.

## Order of work

Four commits, each a review halt, each naming what builds: the interpretation, combinators and
primitives (pieces 1–3; `lake build Snarky.WP Snarky.Witness`); `snarky`'s Builder laws
(`lake build Snarky`); `pickles` (the CI target list); the gates and docs (the Gates job's
steps). The first two leave their dependents unbuilt, since a consumer's `Std.Do` triple has
no `Builder` instance once `WP.lean` has moved, and the PR head is what CI checks. No bridges: a
bridge would be deleted two commits later.

Within the second and third commits the order is a pilot: `DSL/Field.lean` first, then
`Traverse.lean` for the traversal combinators, then in `pickles` `MessageHash.lean` for the
loops and `FinalizeOtherProof.lean` for a large assembly with its timing check, before the rest.

## Acceptance

The build with no `sorry`; every Gates step, the style check, the kernel replay and the heavy
fixtures locally as CI runs them, the locality gate at 202 again; `check-cs` and `check-tags`
untouched, since no circuit changes. The PR description reports the count of proofs that
needed more than the tactic rename, by cause: a `rename_i` or `case` name, an invariant, a
direct-triple constructor, a VC the trivial pass closed, a lifted precondition, other. That
count sizes the Prover pass only in part: its laws add the entry ghost, the error
postcondition and the registrations.
