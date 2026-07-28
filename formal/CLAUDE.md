# AGENTS-formal.md — agent context for `formal/` (the `Kimchi` Lean library)

This directory is a **Lean 4 + Mathlib** formalization of the kimchi proof system over
the Pasta curves: the basic gate set (Generic, Poseidon, AddComplete, VarBaseMul, EndoMul,
EndoScalar), the arithmetization, the executable verifier, and per-curve knowledge
soundness of that verifier. **The modeled fragment excludes lookups, optional gates,
recursion, and the sub-SRS regime** — Mina/pickles proofs are OUTSIDE it on four axes; the
canonical fragment statement lives in `Kimchi/Verifier/KnowledgeSoundness.lean`'s preamble. The `Kimchi.*` namespace is **not** a circuit-DSL embedding: there is no `Circuit`
monad, no `FormalCircuit`/`ProvableType`/`ElaboratedCircuit`, no `circuit_proof_start`.
Gates are modelled as **plain Lean predicates over witness structures**, and proved
faithful to **Mathlib's elliptic-curve group law** (`WeierstrassCurve.Affine`). If you've
seen the Clean framework, forget its vocabulary here — none of it applies.

A second library lives in its own package **`snarky/`** (namespace `Snarky.*`, package
`snarky`, which *requires kimchi* — its `Snarky.Kimchi.*` bridge interprets reified
circuits against the verified generic-gate checker): a deep-embedded Lean port of the
PureScript circuit-building DSL
(`packages/snarky/src/Snarky/Circuit/DSL/Monad.purs`). It models how constraint systems
are *constructed*, complementing `Kimchi`'s constraint-systems-as-data view: a reified op
tree `CircuitM` (constraint type kept abstract), pure `build`/`prove` interpreters
mirroring `Snarky.Backend.Builder`/`Prover`, and the interpreter laws in
`Snarky/Laws.lean` (witness-independence of the builder, builder/prover allocation
agreement, and completeness: a successful prover run satisfies every built constraint).
It is **Mathlib-free by design** (core Lean only, builds in seconds) — keep it that way;
concrete backends live in downstream files (see `Snarky/Constraint/R1CS.lean` for the
plain R1CS model). Kernel-reducibility matters there: everything is validated by `decide`, so avoid
core functions compiled by well-founded recursion in executable paths (e.g. `Vector.map`
— use `Snarky.mapVec` from `Snarky/Vec.lean`).

Build: `make lean-build` (from repo root) or `lake build` (from `formal/`). The toolchain
is pinned in `lean-toolchain` (Lean `v4.30.0`, the official tag); deps in `lakefile.toml`
(Mathlib + `CompElliptic`, a git require pinned to daira upstream, which transitively pulls
`CompPoly`; `zcash/ironwood` for the forking machinery, sharing the same CompElliptic pin).
`import Mathlib` is used wholesale in the proof-heavy trees.

**Package layout.** `formal/` is a lake workspace of standalone path-required packages:

| Package | Lib(s) | Contents |
| --- | --- | --- |
| `pasta/` | `Pasta` | the Pasta curve trust base: the generic EC order/shape sugar, the GLV constants, the **Hasse/CM axioms** and derived orders, point-group module instances, the wire scalar-shift algebra (`Pasta.Shifted`) |
| `poseidon/` | `Poseidon`, `FixtureKit` | the Poseidon permutation + duplex sponge over both Pasta base fields, the `FqSponge` consumer layer, SvdW map-to-curve; plus the shared JSON-fixture/trace kit. Own fixtures + check scripts (`poseidon/scripts/`) |
| `bulletproof-pcs/` | `Bulletproof` | the IPA polynomial commitment: abstract scheme + soundness, the executable Pasta wire verifier (Poseidon-driven), the **`poseidon_fiat_shamir_*` axioms** + `ipa{Vesta,Pallas}_sound`, IPA fixtures + check script |
| `kimchi/` | `Kimchi`, `KimchiFixture` | the kimchi protocol: gates (arithmetization), `Quotient/` (PIOP), `Index/`, `Protocol/` (the ideal protocol + soundness), `Verifier/` (the executable verifier + capstones); plus the fixture-decoding lib, kept out of `Kimchi` |
| `snarky/` | `Snarky` | the deep-embedded circuit-DSL port + its `Snarky.Kimchi.*` bridge; sits ON TOP (requires kimchi); own axiom gate (`snarky/scripts/check_axioms.sh`) |

No package is privileged: `formal/` itself is a pure aggregator workspace (its lakefile
owns no libraries, only requires). Each package builds standalone from its own directory
and owns its scripts (axiom gate, fixture checks, `roots.txt` API manifest); building or
running gates from `formal/` puts everything in one shared workspace (one Mathlib) — how
CI drives it. The workspace-level scripts are `scripts/check-style.sh` (the formatter
contract), `scripts/deadcode.{lean,sh}` (cross-package reachability over the union of
the packages' manifests), `scripts/module-deps.sh` (the dependency-graph artifact —
`make lean-dep-graph`), `scripts/prune-stale-oleans.sh` (garbage-collect build artifacts
of deleted/renamed modules — run it after branch switches), and
`scripts/kernel-replay.sh` (the lean4checker kernel-replay gate).

Three further quality gates are community tools, all CI-enforced:

- **`lake lint`** (from `formal/`, or `make lean-lint`) — Batteries' `@[env_linter]`
  suite (docBlame, unusedArguments, synTaut, …) over every library root; the module list
  is `lintDriverArgs` in `lakefile.toml`. The nolints baseline
  (`scripts/nolints.json`, per-package copies where needed) holds ONLY derive-generated
  instances and by-design findings — fix real findings, never grow the baseline.
  Structure fields need docstrings (docBlame): document every field.
- **`lake exe shake <roots>`** (`make lean-shake`) — no redundant/removable imports;
  policy exceptions in `scripts/noshake.json` (wholesale `import Mathlib` in proof-heavy
  trees; the notation-only `Kimchi.Columns`, invisible to shake). Always pass
  `--cfg` with an ABSOLUTE path (`lake exe` runs the tool from mathlib's directory, so
  the relative default silently reads mathlib's own config). Treat `--fix` with
  suspicion: it cascades removals beyond the reported suggestions — review the diff and
  build before trusting it. Any file that uses the `Kimchi.Columns` notations must
  import it DIRECTLY (shake cannot see notation use, so it may drop transitive
  providers).
- **`scripts/kernel-replay.sh`** (`make lean-kernel-check`) — lean4checker replays every
  `.olean` through the kernel alone, catching environment tampering that the build and
  the axiom gates inherently trust.

For ad-hoc import analysis, `lake exe graph` (import-graph, via Mathlib) is available —
e.g. `--to`/`--from` slices; the committed overview graph stays `make lean-dep-graph`.

**Always run `formal/scripts/check-style.sh` before committing any change under `formal/`** —
and fix anything it reports. Lean 4 has no autoformatter, so this script is the formatter
contract: ≤100 columns, no trailing whitespace, no tabs, exactly one final newline. It's
check-only by default (non-zero exit on any violation); `check-style.sh --fix` auto-corrects
trailing whitespace and final newlines (the over-long lines you wrap by hand). CI runs the
same checks, so a clean run here is the gate for a green build.

## The layer stack

The kimchi package is a bottom-up stack (the `Circuit`/`Cycle` directories this guide once
described are gone; their content lives in `Gate/` + `Gate/Semantics/` + the pasta package):

| Layer | Dir | Models |
| --- | --- | --- |
| **Gate** | `kimchi/Kimchi/Gate/` | one gate row as a constraint predicate (`Holds`/`ok`/`ok_iff`), proved to compute the intended EC/permutation operation |
| **Semantics** | `kimchi/Kimchi/Gate/Semantics/` | multi-row chains (ladders, GLV accumulation) and the per-curve deployed entry points, with pasta's certified orders/eigenvalues in place of the old axioms |
| **Arithmetization** | `kimchi/Kimchi/{Index,Permutation,Protocol,Lift,...}` | the index, satisfiability ↔ divisibility, the linearization |
| **Verifier** | `kimchi/Kimchi/Verifier/` | the executable verifier, the wire layer, and the knowledge-soundness development |

`Main.lean` + `Kimchi/Gate/Generic.lean` are a runnable demo of "ingest a (gate, witness)
and run the verified checker".

Above the gate stack, the library has grown four further trees:

- **`Kimchi/Quotient/`** — the vanishing-argument layer (domain, divisibility engine, the
  `Argument`/`ArgumentEnv` per-gate lifts, grand-product core).
- **`Kimchi/Verifier/`** — the executable kimchi verifier, its reflection, and the
  soundness capstones. The kimchi-proof JSON decoders live in `kimchi/KimchiFixture/`,
  its OWN library (`KimchiFixture`) sitting beside the `Kimchi/` tree, deliberately NOT
  part of `Kimchi`: checking
  against recorded data is not part of the development. Same split as `FixtureKit`
  (poseidon) and `BulletproofFixture` (bulletproof-pcs). Scripts import it directly.
- The IPA commitment lives in the `bulletproof-pcs` package (`Bulletproof.*`), the sponge
  in the `poseidon` package (`Poseidon.*`); see the package table above.

**Import discipline for the executable trees**: the `poseidon` package, `Fixture/`,
`Verifier/`, `pasta/Pasta/Constants.lean`, and the `Bulletproof` def-modules use
*targeted* Mathlib imports (not
`import Mathlib`) so the `scripts/check_*` drivers load a small closure and run in seconds.
Keep new modules in these trees targeted; the proof-heavy trees keep the wholesale
convention. Also: state threaded through executable folds must be concrete data (tuples,
structures) — the compiler eta-expands function-valued definitions, making folds
exponential.

### The gate/semantics module convention

Each modelled gate is two files:

- **`Kimchi/Gate/{Name}.lean`** — the constraint model (`Witness`/`Holds`/`ok`/`ok_iff`)
  and the per-row soundness/completeness.
- **`Kimchi/Gate/Semantics/{Name}.lean`** — the multi-row development (recurrence folds,
  ladder/recoding kernels, non-degeneracy toolkit) up to the per-Pasta-curve deployed
  entry points (`pallas_endoMul`, `varBaseMul_scaleFast1`, …), tracked by
  `scripts/check_axioms.lean`.

## How a gate is modelled

There are **two gate idioms**, by purpose:

**(1) The runnable generic checker** (`Gate/Generic.lean`) — a concrete `Generic` gate over
`Assignment := Array Int`, with a `Bool` checker and its reflection:

```lean
def Generic.holds (g : Generic) (a : Assignment) : Prop := …  -- relational spec
def Generic.ok    (g : Generic) (a : Assignment) : Bool := …  -- executable checker
theorem Generic.ok_iff : g.ok a = true ↔ g.holds a
def satisfies (gs : List Generic) (a : Assignment) : Bool := …  -- run a whole circuit
theorem satisfies_iff : satisfies gs a = true ↔ Satisfies gs a
```

This is what `Main.lean` `#eval`s. It's the bridge to the JSON the PureScript dumpers emit.

**(2) The algebraic EC gates** (`Gate/AddComplete.lean`, `VarBaseMul.lean`, `EndoMul.lean`,
`EndoScalar.lean`) — each gate is a `Witness (F : Type*)` structure (one named field per
circuit column, mirroring the `.purs` column layout), plus:

```lean
structure Witness (F : Type*) where
  x1 y1 x2 y2 x3 y3 s inf : F        -- columns, named to match AddComplete.purs

def Holds [CommRing F] (w : Witness F) : Prop := …  -- the gate's constraints, as a ∧-conjunction
def ok    [CommRing F] [DecidableEq F] (w : Witness F) : Bool := …
theorem ok_iff (w : Witness F) : ok w = true ↔ Holds w := by simp [...]
```

`Holds` is the **relational spec** (a `Prop`); `ok` is the decidable `Bool` mirror; `ok_iff`
is the reflection bridge. Write new gates in this shape.

## The faithfulness pattern (the heart of the project)

For each algebraic gate, prove a progression that ends at **Mathlib's group law**:

1. **Reflection** — `ok_iff : ok w = true ↔ Holds w`. Boolean checker ↔ relational spec.
2. **Soundness** — `sound_* : Holds w → (the field-level slope/coordinate identities)`.
   The constraints pin `s = W.slope …`, `x3 = W.addX …`, etc.
3. **Point soundness** — `sound_point_* : Holds w → ∃ h3, Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3`.
   This is the payoff: the gate computes addition **in Mathlib's proven elliptic-curve group**.
4. **Completeness** — `complete_* : (curve preconditions) → ∃ w, Holds w ∧ (outputs are the group sum)`.
   The honest prover can always fill a satisfying witness.

Representative signatures (verbatim shape):

```lean
theorem sound_point_noninf (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    (w : Witness F) (h1 : W.Nonsingular w.x1 w.y1) (h2 : W.Nonsingular w.x2 w.y2)
    (hcons : Holds w) (hy1 : w.y1 ≠ 0) (htwo : (2 : F) ≠ 0) (hinf : w.inf = 0) :
    ∃ h3 : W.Nonsingular w.x3 w.y3,
      Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3

-- Circuit layer: the folded ladder result
theorem gate_scalarMul … (h : Holds w) :
    Point.some _ _ h5 = (32 : ℕ) • Point.some _ _ h0 + (16 : ℕ) • Point.some _ _ hQ0 + …

-- Per-curve entry point: the genuine scalar lives in the scalar field, via pasta's
-- certified order (no axiom)
theorem varBaseMul_scaleFast2 … / pallas_endoMul …
```

The **Spec is the semantic contract**: it must state the *intended* EC operation
(incomplete addition, `[σ]·T` scalar mul, the GLV/eigenvalue identity), **never** a restatement
of the finite-field constraint equations. The constraints are the implementation; the
group-law statement is what's being proved.

## The Mathlib EC oracle (`Curve.lean`)

Everything is checked against `WeierstrassCurve.Affine F`. Key Mathlib API in use:
`W.Equation` (on-curve), `W.Nonsingular`, `W.slope`, `W.addX`/`W.addY`, `W.negY`,
`Point.some _ _ h` (an affine nonsingular point), `•` (group scalar mul), `Point.add_some`.

**Note (Mathlib ≥ 4.30):** `Point.some` takes **explicit** `(x y : R)` args — write
`Point.some _ _ h`, not `Point.some h`.

The Pasta curves have the short-Weierstrass shape captured once here:

```lean
abbrev IsShortShape (W : WeierstrassCurve.Affine F) : Prop :=
  W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0
```

Reusable EC lemmas live in `Curve.lean` — **prefer these over re-deriving**:
- `secant_add` — one non-vertical addition: slope + output coords ⇒ the group sum is `Point.some`.
- `signed_target` — `∃ e, Point.some _ _ hQ = e • Point.some _ _ hT ∧ (e:F) = 2b−1` (the `±T` selector for bit `b`).
- `some_eq_some` — points with equal coordinates are equal (congruence past the nonsingularity proof).

## The trust surface (zero axiom declarations)

The tree contains **no `axiom` declarations at all** — the historical `Cycle/Axioms.lean` /
`CMCurve` boundary this guide once described is gone, as are the Fiat–Shamir axioms. Every
closure reduces to the three standard logical axioms (`propext`, `Classical.choice`,
`Quot.sound`) plus **certified `native_decide` witnesses**: CompElliptic's primality,
point-count, sqrt-order and eigen-anchor certificates, and pasta's two declared GLV
eigenvalue anchors in `Pasta/Endo.lean` — each trusting the compiler through
`Lean.trustCompiler`. Discrete-log hardness is a *hypothesis of the statements*; the
random-oracle idealisation enters only as the game's uniform challenge table (`FSFaithful`
names the identification with the deployed sponge).

**Axiom discipline (follow this):**
- Introduce NO axioms. A genuinely unprovable fact becomes a *hypothesis* of the statements
  that need it, never an `axiom`.
- The CI gates (`.github/workflows/lean.yml`) audit every package's surface
  (`*/scripts/check_axioms.sh` — kimchi, pasta, poseidon, bulletproof-pcs, snarky) and fail
  on `sorryAx` or any stray axiom; the sorry census pins the whole tree.
- **Avoid `native_decide` in our own proofs** — use `decide` or `reduce_mod_char`. The gates
  trust `native_decide` certificates by DEFINING MODULE (upstream CompElliptic, plus
  `Pasta/Endo.lean`'s two declared anchors) and reject any other site in this tree.

## Fixtures and compatibility checks

Everything executable is validated against proof-systems itself. The fixtures and vectors
under `fixtures/` are recorded from the production Rust code by `tools/fixture-dump`
(see its README for the binaries, output map, and regeneration workflow — regenerate on a
proof-systems bump). The drivers, each a few seconds after `lake build Kimchi`, all
CI-wired in `.github/workflows/lean.yml`:

```sh
kimchi/scripts/check_axioms.sh               # kimchi's headline theorems reduce to the allowed axiom set
pasta/scripts/check_axioms.sh                # the derived trust base (no eigen)
bulletproof-pcs/scripts/check_axioms.sh      # the PCS soundness surface over its declared FS axioms
snarky/scripts/check_axioms.sh               # the DSL interpreter laws (standard axioms only)
poseidon/scripts/check_sponge_vectors.sh     # Poseidon automaton vs mina_poseidon traces (Fq and Fp)
poseidon/scripts/check_fq_sponge.sh          # FqSponge op traces + group_map vectors (both curves)
bulletproof-pcs/scripts/check_ipa_fixture.sh # the executable IPA verifiers accept wire data
kimchi/scripts/check_perm_fixture.sh         # permutation argument row semantics on production data
kimchi/scripts/check_index_fixture.sh        # index model: build-by-decision, derived columns, satisfiability
```

(Every package-local check reads its data through an env var whose **default is relative
to the package directory** — `KIMCHI_FIXTURES_DIR`, `POSEIDON_FIXTURES_DIR`,
`BULLETPROOF_FIXTURES_DIR`, and `KIMCHI_PS_RESULTS_DIR` — so each runs standalone from
its package dir with no setup, or from `formal/` by setting that variable, which is how
CI invokes them all, sharing the aggregator workspace. Keep new checks on this
convention: a package-relative default, overridable by env var.)

New trace checks build on `FixtureKit.Parse` (element decoders) and
`FixtureKit.Trace` (the cases-x-ops driver, both in the `poseidon` package): supply an
op type, a decoder, and a `step : state -> op -> state x Bool`.

## Conventions

- **Namespacing** matches the path: `Kimchi.Gate.*`, `Kimchi.Index.*`, `Kimchi.Verifier.*`.
- **Theorem names**: `ok_iff` (reflection), `sound_*` / `sound_point_*` (soundness),
  `complete_*` (completeness), `*_faithful` (the full bridge), `chain_*` / `gate_*` (folded
  results), `*_scalar` (scalar-field analogue).
- **`F p` / `ZMod p`** for the field; `[Field F] [DecidableEq F]` (add `[CharP F p]` when the
  characteristic matters). Follow **Mathlib naming conventions** for new lemmas.
- **Docstrings are dense and that's intentional** — every gate file opens with a multi-paragraph
  preamble: the gate's source (link the `.purs` / `.rs` / proof-systems origin), the column
  layout, the constraint transcription, and a prose statement of what each theorem means
  *before* its signature. Match this house style; it's what makes the formalization auditable.
- **Files are split into `/-! ## … -/` sections** (constraint model → reflection → soundness →
  completeness → runnable `#eval` example → supporting lemmas). Keep section docstrings in sync
  with reality (see below).
- **Each modelled gate is two files** (see "The gate/semantics module convention" above):
  the constraint model in `Kimchi/Gate/{Name}.lean` and the multi-row development in
  `Kimchi/Gate/Semantics/{Name}.lean`. Do not reintroduce a scatter of per-topic
  submodules.
- **Never modify `maxHeartbeats`.** If a proof is slow, profile with `#count_heartbeats in`
  (`import Mathlib.Util.CountHeartbeats`) and fix the proof, don't raise the limit.

## Proof idioms actually used

By frequency (whole library): `ring` (the workhorse for constraint algebra), then
`linear_combination` (close a goal as a witnessed linear combo of constraint hypotheses —
the standard move for "constraint ⇒ slope identity"), `omega` (integer/index arithmetic),
`module`/`abel` (collapse a `•`-accumulation in the point group — see `gate_scalarMul`),
`obtain`/`rcases` (destructure `Holds` and `∃`-soundness outputs), `decide` (small decidable
goals), `field_simp` + `eq_div_iff` (clear slope denominators). No custom infix notation
(the `===` from Clean does **not** exist here). Proof-irrelevance of the nonsingularity
witness is used freely to line up `Point.some _ _ h` terms before `abel`/`rw`.

## Gotchas

- **`AddComplete` proves addition inline, on purpose** — it works directly against
  `W.slope`/`W.addX`/`Affine.add_some`. It is the *foundational* gate; `secant_add` and
  `signed_target` in `Curve.lean` were extracted *from* its pattern for the other gates to
  reuse. Don't "refactor" AddComplete to call them — that's backwards. Everywhere else
  (`VarBaseMul`, `EndoMul`, at both Gate and Circuit layers) already reuses the shared lemmas;
  keep doing so in new work.
- **Per-gate field names are local and deliberate** — `nPrime` is the updated scalar register
  (VarBaseMul/EndoMul); `a0..a8`/`b0..b8`/`n0..n8` are EndoScalar's per-crumb registers. These
  look different across gates because the gates *are* different; each scheme is internally
  consistent. They mirror the `.purs` column names — don't homogenize them.
- **Stale `STUB`-style comments have bitten before.** When this guide was written, `gate_scalarMul`
  was labelled "STUB" despite being a complete proof, and a since-deleted axioms file claimed "nothing
  here is used yet" after Phases 1–4 had come to depend on it. Both are fixed; the lesson stands —
  trust the proof body and `#print axioms`, not a docstring's self-description.
