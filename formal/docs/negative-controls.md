# Negative controls and standing invariants

A fixture that passes shows the model agrees with production on that data. It does not show the
fixture would catch the defect it guards: a check can agree vacuously (`0 = 0`), or exercise a
code path whose mutation it cannot observe. This file records the guards whose removal the tree
would not notice, and, for each fixture that guards a specific defect, the mutation that must
make it fail and the failure it produces.

The controls are one-time experiments, not gates; the standing protection is the fixture itself,
run in CI. To replay one: apply the mutation, rebuild the named target, run the named driver, then
`git checkout` the mutated file.

## Standing invariants

Each of these protects a property the tree would otherwise lose silently: removing it leaves every
gate green.

1. `liveGates` non-vacuity (`kimchi/scripts/check_linearization.lean`, `runFixture`). A per-gate
   check whose target is `0` agrees vacuously. The driver fails if a gate a fixture names as live
   has a zero target, and annotates zero targets `(0)` in its output.
2. The two coverage fixtures: `kimchi/fixtures/kimchi_proof_vesta_emul.json` (live EndoMul and
   VarBaseMul selectors; every other proof fixture has both identically zero) and
   `kimchi/fixtures/linearization_vesta_emul.json` (live `endoMul`/`varBaseMul` targets). Without
   them a reordering of a gate's constraint list is invisible. Controls: NC-1, NC-2.
3. The `[absorb_g_inf, absorb_fr, challenge]` sponge shape in
   `poseidon/fixtures/fq_sponge_{,pallas_}vectors.json`. It is the only shape class that
   distinguishes a one-zero from a two-zero identity absorb: a shape ending at `absorb_g_inf`, or
   squeezing immediately after it, cannot see the difference. Control: NC-3.
4. The fixture manifest `scripts/fixtures.sha256`, verified in CI by
   `scripts/check_fixtures_manifest.sh`. CI never regenerates fixtures, so the manifest is what
   makes a fixture-side change visible in review.
5. Module-based `native_decide` trust: `isTrustedNativeDecide` in every `*/scripts/check_axioms.lean`
   tests the defining module (`env.getModuleFor?` against upstream `CompElliptic.*` or
   `Pasta.Endo`), not the name. A name-prefix test is forgeable, and this tree declares names
   inside `CompElliptic` namespaces.
6. This file: a fixture that guards a specific defect carries a recorded mutation and the failure
   it produces. A fixture that cannot fail is not a control.
7. The emptied-quotient parse assertion (`kimchi/scripts/check_kimchi_verifier.lean`, the
   `emptied t comm reaches the verifier` line). The empty-quotient corruption runs through
   check-then-verify, so a reinstated `0 < t_comm.size` wire guard would keep it reading
   `✓ REJECT`; the positive parse assertion is what fails instead. Control: NC-5.

## Watch list for a proof-systems bump

Regeneration is byte-stable for unchanged sources, so a diff after regenerating is itself a drift
check. These items deserve a direct look as well:

* `endosclmul.rs` constraint order and sign. Re-diff its list against
  `kimchi/Kimchi/Gate/EndoMul.lean` position for position: the α-weighting is positional on both
  sides, so an upstream reordering silently re-targets `ft_eval0`.
* `absorb_g`'s identity encoding in `sponge.rs` (two zeros). A change is invisible to every sponge
  shape except the one in invariant 3.
* The endo roles: `endos::<G>().1` (scalar field, challenge expansion) versus
  `G::other_curve_endo() = endos::<OtherG>().0` (base field, the `ft_eval0` coefficient). The two
  differ by a squaring in the same field.
* `zk_rows`: `(16·nc + 5)/7` (3/5/19 at nc = 1/2/8), and the three-factor `zkpm` including its
  `ω^(n−1)` term, whose agreement with the full masked window holds only at `zkRows = 3`.
* arkworks' `sqrt` convention. The SvdW sign choices are fixture-pinned, not derived; a convention
  change flips the derived `U` base and is caught only by the group-map fixtures.
* Optional-gate and lookup evaluation fields. Production accepts them on a fragment VK and absorbs
  them into the fr-sponge, so they affect the transcript; the Lean wire language cannot represent
  them. If upstream changes what is absorbed when they are absent, the fragment's proof-shape
  clause moves.

## NC-1 — the live-EndoMul/VarBaseMul proof catches a reordered EndoMul constraint list

* Fixture: `kimchi/fixtures/kimchi_proof_vesta_emul.json`
* Driver: `kimchi/scripts/check_kimchi_verifier.sh` (after `lake build Kimchi`)
* Mutation: in `kimchi/Kimchi/Gate/EndoMul.lean`, reorder the constraint list away from
  production's order and sign: windows first, `inv` at position 6, booleanity at 7–10, and the
  scalar register negated.
* Observed: `kimchi_proof_vesta_emul.json: chunked verify (nc = 1): REJECT (BUG)`, driver exits
  non-zero. Every other proof fixture still accepts: without this fixture the regression is
  invisible.

## NC-2 — the emul linearization fixture localizes the same regression to the gate

* Fixture: `kimchi/fixtures/linearization_vesta_emul.json`
* Driver: `kimchi/scripts/check_linearization.sh`
* Mutation: same as NC-1.
* Observed: the mixed-gate fixtures pass unchanged; the emul fixture reports

  ```
  gates [generic: ✓ (0), poseidon: ✓ (0), completeAdd: ✓ (0),
         varBaseMul: ✓, endoMul: ✗, endoScalar: ✓ (0)],
  constant term: ✗, ft_eval0: ✗, assembled equation: ✗
  ```

  so the defect is named at the gate (`endoMul: ✗` beside `varBaseMul: ✓`) rather than surfacing
  only as a whole-proof rejection.
* Sub-control (sign only): perturbing just the scalar-register sign does not reach the driver:
  `holds_iff`'s proof in `kimchi/Kimchi/Gate/EndoMul.lean` stops compiling, because it
  cross-checks the readable conjunction against the constraint list. The sign is protected at
  compile time as well as by fixtures.

## NC-3 — the identity-absorb trace shape catches a one-zero identity absorb

* Fixture: the `[absorb_g_inf, absorb_fr, challenge]` case in
  `poseidon/fixtures/fq_sponge_{,pallas_}vectors.json`
* Driver: `poseidon/scripts/check_fq_sponge.sh`
* Mutation: in `poseidon/Poseidon/FqSponge.lean`, make `absorbG` branch on the identity —
  `if P = 0 then absorbFq spec s [0] else absorbFq spec s [P.x, P.y]`.
* Observed: the driver fails on exactly this case. Every other sponge shape still passes.

## NC-5 — the empty-quotient corruption catches a reinstated wire guard

* Fixtures: every kimchi proof fixture the driver runs without `heavy` (`kimchi_proof_vesta.json`,
  `…_vesta_pub.json`, `…_{vesta,pallas}_nc2.json`, `…_vesta_emul.json`).
* Driver: `kimchi/scripts/check_kimchi_verifier.sh`
* Why a control is needed: the empty quotient is a verify-level corruption (`verify` must return
  `false`), but `verifyWire` is check-then-verify, so a parse rejection also returns `false`. The
  corruption entry alone would keep reading `✓ REJECT` if a `0 < t_comm.size` wire guard came
  back. The driver therefore carries a positive assertion that the emptied proof parses, printed
  on its own line and folded into the pass condition.
* Mutation: insert `guard (0 < p.tComm.size)` before the `t_comm` size branch in
  `Kimchi.Verifier.Wire.KimchiProof.check` (`kimchi/Kimchi/Verifier/Wire.lean`), then
  `lake build Kimchi.Verifier.Wire KimchiFixture.Kimchi`.
* Observed: `✗ none (VACUOUS CONTROL): emptied t comm reaches the verifier`, driver exits non-zero
  on the first fixture. The corruption entry beside it still prints
  `✓ REJECT: emptied t comm (the empty quotient, parses)`: without the assertion the mutation is
  invisible, and with it the empty quotient's rejection is pinned to the ft identity rather than
  to a parse guard.

## NC-6 — the axiom gate catches a deleted root, not just a stray axiom

* Gate: every `*/scripts/check_axioms.lean`. Each `run_cmd` throws
  `axiom-check root not in environment: <name>` before it collects a closure, so the root list is
  a deletion guard as well as an axiom guard: removing a declaration together with its
  `roots.txt` line does not pass.
* Mutation: rename a root that nothing in the tree consumes by name, so the compiler cannot catch
  it — for example `theorem addConstraint_spec` → `theorem addConstraint_spec_DELETED_CONTROL` in
  `snarky/Snarky/WP.lean` — then `lake build Snarky` and, from `formal/snarky/`,
  `lake env lean scripts/check_axioms.lean`.
* Observed: `axiom-check root not in environment: Snarky.addConstraint_spec`, gate exits 1.

## What is not controlled here

The structural gates (axiom closures, dead-code reachability, the fixture manifest) fail on any
perturbation of what they pin, so they need no separate control. Self-discriminating is not
self-documenting, though: what each axiom gate pins is written in its header, and NC-6
demonstrates the deletion-guard role.
