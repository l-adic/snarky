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
its fixture.

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

---

## What is *not* controlled here

The gates that are structural rather than data-driven — the axiom closures, the dead-code
reachability, the locked-target texts, the fixture manifest — are self-discriminating: each
fails on any perturbation of what it pins, and several were observed doing so during the
remediation (the sorry census was verified against a planted `sorry`; the locked-target gate
reported the `Coins` re-spelling; the dead-code gate reported two unreferenced helpers). They
need no separate control.
