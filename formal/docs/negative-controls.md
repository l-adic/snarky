# Negative controls — the discrimination checks behind the fixture gates

A fixture that passes proves the model agrees with production **on that data**. It does not,
by itself, prove the fixture would *catch* the defect it was added for: a check can agree
vacuously (`0 = 0`), or exercise a code path whose mutation it cannot observe. The external
audit's V-1 survived years of green drivers for exactly that reason, and its R-1 follow-up
found the residue — the per-gate linearization checks for the two gates V-1 concerned were
`0 = 0`.

This file records, for each fixture added or changed to close an audit finding, the
**mutation** that must make it fail and the **observed failure**. These are one-time
experiments, not gates: the standing protection is the fixture itself, run every CI. What is
recorded here is the discrimination evidence — replayable by anyone, in the stated steps,
without re-deriving what to perturb.

Convention: apply the mutation, `lake build Kimchi`, run the named driver, then
`git checkout` the mutated file. Every control below was run at the revision that introduced
its fixture. **Two caveats on replaying these steps in the tree as it stands** (NC-6 states the
first for its own case): the `git` steps are unavailable here, because this tree's only commit has
an empty tree and every file is untracked — restore by hand from a pre-edit copy and `cmp` instead
of `git checkout`; and the pre-reseed revisions the recipes name — NC-1's `4ff807a6` below, for
instance — are not objects in this repository (`git cat-file -t 4ff807a6` → *not a valid object
name*), so a mutation quoted as `git show <rev>…` has to be re-created from the description
beside it.

---

## NC-1 — the live-EndoMul/VarBaseMul proof catches a V-1 regression end to end

* **Fixture:** `kimchi/fixtures/kimchi_proof_vesta_emul.json` (audit V-1, C-3)
* **Driver:** `kimchi/scripts/check_kimchi_verifier.sh`
* **Mutation:** restore the pre-fix EndoMul constraint list —
  `git show 4ff807a6~1:formal/kimchi/Kimchi/Gate/EndoMul.lean > kimchi/Kimchi/Gate/EndoMul.lean`
  (the audited order/sign: windows first, `inv` at position 6, booleanity at 7–10, and the
  scalar register negated).
* **Observed:** `kimchi_proof_vesta_emul.json: chunked verify (nc = 1): REJECT (BUG)`, driver
  exits non-zero. **Every other proof fixture still ACCEPTS** — which is precisely the mask
  the audit identified: without this fixture the regression is invisible.

## NC-2 — the emul linearization fixture LOCALIZES a V-1 regression to the gate

* **Fixture:** `kimchi/fixtures/linearization_vesta_emul.json` (audit R-1)
* **Driver:** `kimchi/scripts/check_linearization.sh`
* **Mutation:** same as NC-1.
* **Observed:** the mixed-gate fixture passes unchanged; the emul fixture reports

  ```
  gates [generic: ✓ (0), poseidon: ✓ (0), completeAdd: ✓ (0),
         varBaseMul: ✓, endoMul: ✗, endoScalar: ✓ (0)],
  constant term: ✗, ft_eval0: ✗, assembled equation: ✗
  ```

  i.e. the defect is named **at the gate** — `endoMul: ✗` with `varBaseMul: ✓` beside it —
  rather than surfacing only as a whole-proof rejection. This is the localization R-1 asked
  for. The `(0)` annotations mark targets that are identically zero in a given fixture, so a
  vacuous check is visible in the driver's own output rather than reading as a pass; the
  driver additionally *fails* if a gate named in that fixture's `liveGates` has a zero target.

* **Sub-control (sign only):** perturbing just the scalar-register sign does not reach the
  driver — `holds_iff`'s proof stops compiling, because the readable conjunction and the
  constraint list are cross-checked by that theorem. Recorded because it means the sign is
  additionally protected at compile time, not only by fixtures.

## NC-3 — the identity-absorb trace shape catches a V-2 regression

* **Fixture:** the `[absorb_g_inf, absorb_fr, challenge]` case in
  `poseidon/fixtures/fq_sponge_{,pallas_}vectors.json` (audit V-2)
* **Driver:** `poseidon/scripts/check_fq_sponge.sh`
* **Mutation:** restore the one-zero identity absorb in `poseidon/Poseidon/FqSponge.lean` —
  `absorbG … := if P = 0 then absorbFq spec s [0] else absorbFq spec s [P.x, P.y]`.
* **Observed:** driver FAILS on exactly this case. Every pre-existing sponge shape still
  passes — confirming the audit's structural argument that a shape ending at `absorb_g_inf`,
  or squeezing immediately after it, cannot distinguish the two encodings.

## NC-4 — the exhibit guards catch a deleted certificate

* **Gate:** `bulletproof-pcs/scripts/check_locked_target.sh` (and its kimchi twin), the
  exhibit-existence block — added in response to the audit addendum's generalization of B-4:
  *under a dead=0 gate, any exhibit absent from `roots.txt` is by construction eligible for
  deletion, and nothing but review distinguishes an anti-vacuity certificate from dead code.*
* **Mutation:** rename any guarded exhibit, e.g. `theorem chainAt_sg` →
  `private theorem chainAt_sg_DELETED_CONTROL` in `Forking/Deployed.lean` (the shape a
  dead-code sweep would produce: the name leaves the public surface).
* **Observed:** `✗ EXHIBIT MISSING: chainAt_sg`, gate exits non-zero, with the message
  stating that removing an exhibit is a decision about what the endpoints claim. Before this
  block the same mutation passed every gate — the dead-code gate would have reported the
  declaration as *correctly* removed.
* **Replayed** when O-1a's four certificates were added to the pins — `one_le_kimchiExtractRuns`
  (`Forking/Game.lean`), `exists_complete_bounded_coins` (`Forking/Deployed.lean`) and both
  families' `exists_complete_reductionEfficient` — one at a time, each observed as
  `✗ EXHIBIT MISSING: <name>` and restored. Worth replaying per name: the two gates' matchers
  differ (only bulletproof's tolerates a dotted `DeployedFamily.` prefix), so a mis-spelled pin
  fails open on the kimchi side. **Replayed again** when both families'
  `one_le_of_reductionEfficient` were pinned — bare in the kimchi loop
  (`Kimchi/Verifier/KnowledgeSoundness.lean:1811` declares it bare inside `namespace
  KimchiFamily`), dotted as `DeployedFamily.one_le_of_reductionEfficient` in bulletproof's
  `exhibits_ks` (`Bulletproof/Forking/KnowledgeSoundness.lean:746` declares it dotted) — each
  renamed to `<name>_DELETED_CONTROL` in place, each observed as `✗ EXHIBIT MISSING: <name>` with
  the gate exiting 1, each restored and re-run green. Grep-only: no rebuild is needed.

## NC-5 — the empty-quotient corruption catches a reinstated wire guard

* **Fixture:** every kimchi proof fixture the driver runs unheavy (`kimchi_proof_vesta.json`,
  `…_vesta_pub.json`, `…_{vesta,pallas}_nc2.json`, `…_vesta_emul.json`) — audit O-2, which
  retired `KimchiFamily.htpos` and with it the `0 < t_comm.size` wire guard
* **Driver:** `kimchi/scripts/check_kimchi_verifier.sh`
* **Why a control was needed.** O-2 moved the empty quotient from the driver's `parses` array
  (parse must return `none`) to its `corrupts` array (`verify` must return `false`). But
  `verifyWire` is check-then-verify, so a parse rejection ALSO returns `false`: the corruption
  entry alone would keep reading `✓ REJECT` if the wire guard came back, agreeing vacuously
  for the wrong reason and hiding the very strengthening O-2 removed. The driver therefore
  carries a companion positive assertion — the emptied proof must PARSE — printed on its own
  line (`emptied t comm reaches the verifier`) and folded into the run's pass condition.
* **Mutation:** reinstate the retired guard — insert `guard (0 < p.tComm.size)` before the
  `t_comm` size branch in `Kimchi.Verifier.Wire.KimchiProof.check`
  (`kimchi/Kimchi/Verifier/Wire.lean:165`), then
  `lake build Kimchi.Verifier.Wire KimchiFixture.Kimchi`.
* **Observed:** `✗ none (VACUOUS CONTROL): emptied t comm reaches the verifier`, driver exits
  non-zero on the first fixture. The corruption entry beside it still printed
  `✓ REJECT: emptied t comm (the empty quotient, parses)` — confirming that without this
  assertion the mutation is invisible to the driver, and that with it the empty quotient's
  rejection is pinned to the ft identity (the quotient side of the collapse being the empty
  sum `0`) rather than to a parse guard.

## NC-6 — the axiom gate catches a deleted root, not just a stray axiom

* **Gate:** all five `*/scripts/check_axioms.lean`. Each `run_cmd` throws
  `axiom-check root not in environment: <name>` before it collects a closure, so the root list is
  a **deletion guard** as well as an axiom guard.
* **Why a control was needed.** Two consecutive review passes filed the opposite — that a rooted
  declaration absent from the locked-target scripts is "protected only by `roots.txt`", hence
  deletable by a sweep that removes the root line with it. That reading treats the axiom gate as
  a pure closure check. `kimchi/roots.txt:13–14` already said otherwise; nothing in any
  `check_axioms.lean` header did, which is how the mis-reading survived. Each header now records
  the existence-pin role, and this control is the evidence behind that sentence.
* **Mutation (a) — gate-side, no rebuild.** Rename the *root-list entry*
  `` `Bulletproof.Ipa.Forking.DeployedFamily.one_le_of_reductionEfficient `` to
  `…_DELETED_CONTROL` in `bulletproof-pcs/scripts/check_axioms.lean`. This exercises the
  `env.contains` branch directly, in seconds.
* **Observed (a):** `scripts/check_axioms.lean:91:0: error: axiom-check root not in environment:
  Bulletproof.Ipa.Forking.DeployedFamily.one_le_of_reductionEfficient_DELETED_CONTROL`, gate exits
  1. Restored: `✓ all 33 Bulletproof roots reduce to …`.
* **Mutation (b) — source-side, end to end.** The scenario as filed: delete the *declaration*.
  `snarky` is Mathlib-free and its gate has 5 roots, so this runs in seconds. Rename
  `theorem prove_build_agrees` → `theorem prove_build_agrees_DELETED_CONTROL` in
  `snarky/Snarky/Laws.lean:109` (chosen because it has no in-tree consumer, so the compiler cannot
  catch it — exactly the shape a dead-code sweep produces), then `lake build Snarky`.
* **Observed (b):** `scripts/check_axioms.lean:32:0: error: axiom-check root not in environment:
  Snarky.prove_build_agrees`, gate exits 1. Restored and rebuilt:
  `✓ all 5 Snarky roots reduce to [propext, Classical.choice, Quot.sound]`. So the scenario the
  filed finding assumed passes silently does not: it fails at the axiom gate whether or not the
  declaration is also exhibit-pinned. (Restored by hand, byte-compared — this tree's only commit
  has an empty tree, so the `git checkout` step of the convention above is unavailable.)

---

## What is *not* controlled here

The gates that are structural rather than data-driven — the axiom closures, the dead-code
reachability, the locked-target texts, the fixture manifest — are self-discriminating: each
fails on any perturbation of what it pins, and several were observed doing so during the
remediation (the sorry census was verified against a planted `sorry`; the locked-target gate
reported the `Coins` re-spelling; the dead-code gate reported two unreferenced helpers). They
need no separate control — with one qualification learned since: self-discriminating is not
self-*documenting*. The axiom gates were misread twice as pure closure checks, so what each one
pins is now written in its header and demonstrated in NC-6 above.
