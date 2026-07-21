# Reorg plan: cut `Protocol` at the PCS-free boundary, root the wire on it

**Status:** approved, NOT executed. Execute in fresh context from this doc.
**Branch:** continue on `kimchi-verifier-audit` (or a fresh branch off it). ALWAYS
`git branch --show-current` before committing — the checkout switches between sessions.

**PRECONDITION.** This plan builds on uncommitted work in
`Protocol/{Equation,Soundness}.lean` (session of 2026-07-20): the oracle-based
`piop_sound` (takes `W : Fin 15 → Polynomial F`, concludes `∃ wTab, Satisfies`),
`of_openings` rewired through it, and the `satisfies_extractTable_of_verifierEquation`
adapter deleted. **Commit that state first** (verified green: build + style + 41-root
axiom gate) so Part A has a clean anchor. If it is already committed, proceed.

## Why

Today `Kimchi.Protocol` is dishonest in two concrete ways:

1. **No named protocol definition.** The polynomial verifier's acceptance check exists
   only as an *inline hypothesis* inside `piop_sound`/`kimchiProof_sound_of_openings`. So
   `Protocol` ships *soundness of an unnamed thing* — you cannot point at "the protocol."
2. **It contains the PCS reduction.** `Protocol/{Binding,Correspond,Soundness}` all
   `import Bulletproof` (verified) — they are the *commitment compilation*, not the
   polynomial protocol.

The one boundary that is real and checkable is **PCS-free vs PCS-committed**. `Equation`
and `Linearization` import no `Bulletproof`; `Binding`/`Correspond`/`Soundness` and all of
`Verifier/` do. The current `Protocol | Verifier` split ignores that line — it separates
the *reduction* from the *wire* (which are one thing) and lumps the *polynomial protocol*
in with the *reduction*.

**Goal.** Two honest layers:

- `Kimchi.Protocol` = the polynomial protocol, PCS-free: a named acceptance predicate
  `Accepts` + its soundness `sound`. Headlines: `Kimchi.Protocol.Accepts`,
  `Kimchi.Protocol.sound`.
- `Kimchi.Verifier` = the PCS reduction **and** the wire, rooted on `Protocol`. Headlines:
  the wire `kimchiVerify` and the wire-soundness terminals; the reduction
  (`Binding`/`Correspond`/`Soundness`) moves in here.

This is exactly "Verifier rooted in Protocol" (a dependency edge `Verifier → Protocol`), not
a merge into one namespace — the PCS-free boundary is kept, because it is the only hard
structural fact and the reason `sound` is provable/reusable at all.

## Target layering

| Layer | Dir | Namespace | Contents | Imports Bulletproof? |
| --- | --- | --- | --- | --- |
| **polynomial protocol** | `Kimchi/Protocol/` | `Kimchi.Protocol[.Equation/.Linearization]` | `Accepts` (def), `sound` (thm), `verifierEquation_iff`, `evalsOf`, `extractTable`, `ftEval0`, `permScalar`, `Evals`, `satisfies_of_verifierEquation` (→ private) | **no** |
| **PCS reduction** | `Kimchi/Verifier/Reduction/` | `Kimchi.Verifier` | `Binding.*`, `Correspond.*` (`IndexComms`, `VKCorresponds`, `indexerOf`, `commitPoly[Masked]`), `Soundness.*` (`batchC`, `claimedEvals`, `wRow…selRow`, `kimchiProof_sound_of_openings`, `kimchiProof_sound`) | yes |
| **wire** | `Kimchi/Verifier/` + `Kimchi/Verifier/Capstone/` | `Kimchi.Verifier` | `kimchiVerify` (def), `Reflect`, `Capstone/{Standard,Algebraic,Reflection}` (terminals) | yes |

Dependency: `wire → reduction → Protocol`. All acyclic (measured: `Protocol/` imports
nothing from `Verifier/`; the reduction's only `Protocol` dep is `Equation`, which stays).

## Part A — give the polynomial protocol a definition, and rename its soundness

All inside `Kimchi/Protocol/`, PCS-free.

### A1. Define `Accepts` (the protocol)

New predicate — the polynomial verifier's algebraic check, over an evaluation record
`E : Evals F` (what oracle access yields; the same type `evalsOf`/`claimedEvals` produce,
so both layers can feed it), a quotient `t`, and the challenges. Home: a new
`Kimchi/Protocol/Accepts.lean`, bare `namespace Kimchi.Protocol`. Imports: copy
`Equation.lean`'s set (`Kimchi.Protocol.Linearization`, `Kimchi.Index.Aggregate`,
`Kimchi.Index.Degree`) — known sufficient for `permScalar`/`ftEval0`/`Evals`,
`idx.pubPoly`, and `Permutation.sigmaPoly`; prune what compiles without.

```lean
/-- The polynomial verifier's acceptance check: the linearized identity on an evaluation
record `E` (the oracle evaluations at ζ) and quotient `t`, at challenges `(β,γ,α,ζ)`.
PCS-free — this is the protocol. -/
def Accepts (idx : Index F n) (pub : Fin idx.publicCount → F)
    (E : Evals F) (t : Polynomial F) (β γ α ζ : F) : Prop :=
  permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) E
      * ((Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) 6).eval ζ
    - (ζ ^ n - 1) * t.eval ζ
  = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ ζ
      (-((idx.pubPoly pub).eval ζ)) E
```

Note the sigma-column term uses `Permutation.sigmaPoly` (the polynomial-layer form). The
wire-facing acceptance uses `idx.sigmaPoly 6`; they are equal via
`Index.sigmaPoly_eq_wiring`, and the reduction already performs that rewrite
(`Soundness.lean`, the `hrec`/`Index.sigmaPoly_eq_wiring` step) — no change needed there.

### A2. Restate the soundness theorem and rename it

`piop_sound` (currently `Kimchi.Protocol.Equation.piop_sound`) →
**`Kimchi.Protocol.sound`** (bare `Kimchi.Protocol` namespace; drop the poor `piop_`
prefix). Its acceptance hypothesis becomes `Accepts …`.

**Placement mechanics (load-bearing).** `sound`'s proof calls
`satisfies_of_verifierEquation`, which A3 makes `private`. In Lean 4 `private` is
FILE-scoped, so `sound` MUST stay in `Equation.lean`. To land it in the bare namespace,
place it after `end Kimchi.Protocol.Equation` in a new block:

```lean
end Kimchi.Protocol.Equation

namespace Kimchi.Protocol
open Kimchi.Protocol.Equation  -- evalsOf, extractTable

theorem sound … := by …        -- can still see the file-private SZ core

end Kimchi.Protocol
```

(`Accepts` lives in its own `Protocol/Accepts.lean`, which `Equation.lean` imports.)

```lean
theorem sound (idx : Index F n) (pub : Fin idx.publicCount → F)
    (W : Fin 15 → Polynomial F) (z : Polynomial F) (hz : z.natDegree < n) :
    ∃ badB badG badA badZ,
      (card bounds) ∧
      ∀ β γ α (t : Polynomial F) (ζ : F),
        β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
        ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
        Accepts idx pub (evalsOf idx (extractTable idx.omega W) z ζ) t β γ α ζ →
        ∃ wTab, Satisfies idx pub wTab
```

Body unchanged except the final `exact` still routes through
`satisfies_of_verifierEquation` (unfold `Accepts` if needed — it is `rfl`-equal to the old
inline equation, so the existing proof term goes through, possibly after `unfold Accepts`
/ `show`).

Optionally restate `verifierEquation_iff`'s LHS as `Accepts idx pub (evalsOf idx wTab z ζ)
t β γ α ζ` for symmetry (nice-to-have, not required).

### A3. Privatize the SZ core

`satisfies_of_verifierEquation` → `private` (its only caller is `sound`, same file). Drop
it from `check_axioms.lean` (Part C).

### A4. Fix the one in-tree caller now (keeps builds green before the move)

`Soundness.lean` calls `piop_sound idx pub W zg hzdeg` → `sound idx pub W zg hzdeg`. (This
file moves in Part B, but update the call here so Part A builds independently.) NOTE:
while `Soundness.lean` is still in `namespace Kimchi.Protocol`, bare `sound` resolves;
after Part B renames its namespace to `Kimchi.Verifier`, the call must become
`Kimchi.Protocol.sound` (or add `open Kimchi.Protocol` scoped to that file). Also: the
`himp` obtained from `sound` now expects an `Accepts …` argument — the `?_` goal at the
final `refine himp …` becomes `Accepts idx pub (evalsOf …) t β γ α ζ`; the existing
`rw [hrec, Index.sigmaPoly_eq_wiring idx 6] at h; exact h` closes it by defeq (prefix
with `show Accepts …` or `unfold Accepts` only if unification balks).

## Part B — evict the PCS reduction from `Protocol/` into the wire layer

### B1. Move the files

```
Kimchi/Protocol/Binding.lean     → Kimchi/Verifier/Reduction/Binding.lean
Kimchi/Protocol/Correspond.lean  → Kimchi/Verifier/Reduction/Correspond.lean
Kimchi/Protocol/Soundness.lean   → Kimchi/Verifier/Reduction/Soundness.lean
```

(`git mv`.) `Equation.lean`, `Linearization.lean`, and the new `Accepts.lean` stay in
`Protocol/`.

### B2. Rename namespace `Kimchi.Protocol` → `Kimchi.Verifier` in the 3 moved files

Their bare-namespace decls become `Kimchi.Verifier.*`:
`IndexComms`, `VKCorresponds`, `indexerOf`, `commitPoly`, `commitPolyMasked`,
`rowPoly`, `rowPoly_eval`, `rowPoly_natDegree_lt_two_pow`, `rowPoly_coeff_self`,
`commitPoly_eq_commit`, `bound_eval_of_commitPoly`, `bound_eval_of_commitPolyMasked`,
`wRow`, `zRow`, `sRow`, `cRow`, `selRow`, `batchC`, `claimedEvals`,
`kimchiProof_sound_of_openings`, `kimchiProof_sound` (+ the Soundness/Binding privates).

Sub-namespaced `Kimchi.Protocol.Equation.*` / `.Linearization.*` decls are untouched
(they stay in `Protocol/`).

### B3. Fix imports in the moved files

- `Binding.lean`: `import Kimchi.Protocol.Correspond` → `import Kimchi.Verifier.Reduction.Correspond`.
- `Soundness.lean`: `import Kimchi.Protocol.Binding` → `import Kimchi.Verifier.Reduction.Binding`;
  keep `import Kimchi.Protocol.Equation` (Equation stays in Protocol).
- `Correspond.lean`: imports unchanged (`Kimchi.Index.Aggregate`, `Bulletproof.Protocol`).

### B4. Fix the consumers (measured: tiny)

- **Qualified refs: ZERO in library code.** The only two hits in the whole workspace are
  scripts: `scripts/check_axioms.lean:47` (the root entry — handled in Part C) and
  `scripts/check_vk_correspond.lean:10` (a DOCSTRING mention of
  `Kimchi.Protocol.VKCorresponds` — text-only edit to `Kimchi.Verifier.VKCorresponds`).
  `check_vk_correspond.lean` already `open Kimchi.Verifier` and uses no moved decl by
  name in code, so it needs no code change.
  Verify with: `grep -rn 'Kimchi\.Protocol\.\(VKCorresponds\|kimchiProof_sound\)' --include='*.lean'`.
- **5 `open Kimchi.Protocol` sites** — all in the wire layer
  (`Verifier/{Kimchi,Reflect}.lean`, `Verifier/Capstone/{Standard,Algebraic,Reflection}.lean`).
  Since those decls now live in `Kimchi.Verifier` (the files' own namespace), the opens
  become redundant. Drop them, OR (safer, zero-risk) leave them — `open` of an existing
  namespace is harmless. Recommendation: drop, since `Kimchi.Protocol` no longer holds
  what they wanted.
- **Import lines** in the wire layer that referenced the moved modules:
  `import Kimchi.Protocol.{Binding,Correspond,Soundness}` →
  `import Kimchi.Verifier.Reduction.{Binding,Correspond,Soundness}`. Sites (measured):
  `Kimchi.lean` (root), `Verifier/Kimchi.lean`, `Verifier/Reflect.lean`,
  `Verifier/Capstone/Standard.lean`, `Verifier/Capstone/Algebraic.lean`.
  Find with: `grep -rln 'import Kimchi\.Protocol\.\(Binding\|Correspond\|Soundness\)'`.

### B5. Root aggregator

`Kimchi.lean` (repo-root aggregator — NOTE: it is a SIBLING of the `Kimchi/` dir, so
`Kimchi/**` globs and `grep -r … Kimchi/` MISS it; grep the file explicitly): repoint the
three imports to `Kimchi.Verifier.Reduction.*`, and ADD
`import Kimchi.Protocol.Accepts` (the new file) to the Side-A block.

## Part C — roots + axiom gate

- `roots.txt`: line `Kimchi.Protocol.kimchiProof_sound_of_openings` →
  `Kimchi.Verifier.kimchiProof_sound_of_openings`. **Add**
  `Kimchi.Protocol.sound`. Consider also adding
  `Kimchi.Verifier.kimchiProof_sound` (the top generic-PCS result — currently untracked;
  see the earlier finding that the *top* result is not gated while the *seam* is).
- `scripts/check_axioms.lean` roots list:
  - remove `Kimchi.Protocol.Equation.satisfies_of_verifierEquation` (now private),
  - add `` `Kimchi.Protocol.sound ``,
  - `` `Kimchi.Protocol.kimchiProof_sound_of_openings `` →
    `` `Kimchi.Verifier.kimchiProof_sound_of_openings ``,
  - keep `` `Kimchi.Protocol.Equation.verifierEquation_iff `` (headline algebraic fact,
    still public).

## Execution order (green build at every step)

1. **Part A** in `Protocol/` (add `Accepts`, rename `piop_sound`→`sound`, restate via
   `Accepts`, privatize `satisfies_of_verifierEquation`, fix the `Soundness.lean` call in
   A4). Build `Kimchi.Protocol.Equation` + `Kimchi.Protocol.Soundness`.
2. **Part B** file moves + namespace rename + import/ref/open fixes + root aggregator.
   Build `Kimchi`.
3. **Part C** roots + check_axioms. Run the gates.

## Verification checklist (all must pass)

- `lake build Kimchi` ✓
- `scripts/check-style.sh` ✓ (91 files; keep ≤100 cols, wrap the new `Accepts`/`sound`
  docstrings)
- `kimchi/scripts/check_axioms.sh` ✓ — expect the SAME axiom set; root set changes
  (satisfies_of_verifierEquation out, sound in, of_openings renamed) but every root must
  still reduce to the allowed axioms.
- `scripts/deadcode.sh` exit 0 — the moved decls stay reachable; `satisfies_of_verifierEquation`
  reachable from `sound`.
- `kimchi/scripts/check_kimchi_verifier.sh`-equivalents (`check_kimchi_verifier`,
  `check_vk_correspond`) ✓ — `check_vk_correspond` uses `VKCorresponds`, now
  `Kimchi.Verifier.VKCorresponds`; confirm it resolves.
- `refactor_baseline` gate-layer dump byte-identical (this reorg does not touch the Gate
  layer).

## Measured facts (so execution is confident)

- `Equation` + `Linearization` import **no** `Bulletproof`; `Binding`/`Correspond`/
  `Soundness` each import `Bulletproof.*` — the PCS line is exactly file-aligned.
- Consumers of the 3 reduction files: `Kimchi.lean` (root), `Verifier/Kimchi.lean`,
  `Verifier/Reflect.lean`, `Verifier/Capstone/{Standard,Algebraic}.lean` — all wire layer.
- Cross-namespace qualified refs to the moving decls: **0 in library code**; 2 script
  hits (check_axioms root entry + a check_vk_correspond docstring), see B4.
- `open Kimchi.Protocol` sites: **5**, all wire layer. After the move nothing they need
  remains in bare `Kimchi.Protocol` except the new `Accepts`/`sound` (which the wire
  layer consumes only through the reduction), so dropping them is safe.
- **No name collisions**: none of the ~21 moving bare-namespace decls
  (`IndexComms` … `kimchiProof_sound`) already exists in `Kimchi.Verifier`.
- **No refs outside the kimchi package**: `snarky/`, `pasta/`, `poseidon/`,
  `bulletproof-pcs/` contain zero `Kimchi.Protocol` references; `KimchiFixture/` is
  clean too (it was the false-positive trap in a previous audit — re-verify with a grep
  from `formal/`, not `formal/kimchi/Kimchi/`).
- `roots.txt`: 1 line to change; `check_axioms.lean`: 3 lines to change
  (45: keep `verifierEquation_iff`; 46: remove `satisfies_of_verifierEquation`;
  47: rename `of_openings` to `Kimchi.Verifier.…`; plus add `` `Kimchi.Protocol.sound ``).
- The polynomial `sound` (`piop_sound`) is the common core both reduction paths bottom out
  in: `sound → of_openings →` {`kimchiProof_sound` (standard grid, `Capstone/Standard`) |
  `of_openings` directly (AGM, `Capstone/Algebraic`,`Reflection`)} → wire terminals. It IS
  load-bearing, so its statement/axioms must be preserved through the rename.

## Open naming choices (decide at execution)

- ~~Where `sound` lives~~ — RESOLVED by the A2 mechanics: name `Kimchi.Protocol.sound`,
  physically in `Equation.lean` (bare-namespace block after `end …Equation`; required by
  file-scoped `private`), matching the `Kimchi.Gate.<G>.sound` naming convention.
- ~~Where `Accepts` lives~~ — RESOLVED: own `Protocol/Accepts.lean`, imported by
  `Equation.lean` — "the protocol definition" as a first-class artifact, mirroring the
  wire `kimchiVerify`.
- Whether to also add a single per-curve wire-soundness headline
  `kimchiVesta_sound : verify = true → guarded ∃ wTab, Satisfies` (with grid+AGM as
  internal routes) so the wire layer has one clean top result mirroring
  `Protocol.sound`. Out of scope for this reorg; note as follow-up.

## Non-goals

- No merge into a single namespace (keeps the PCS-free boundary).
- No new IOP/oracle abstraction (oracle = low-degree `Polynomial F` + degree bound,
  quantified, accessed by `.eval`; that is the model, and `sound` states its soundness).
- No touching the Gate/Circuit/Cycle arithmetization.
