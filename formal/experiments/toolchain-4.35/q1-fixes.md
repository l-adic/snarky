# Q1 fix log (v4.30.0 -> v4.35.0), started 16:47:50
Infra:
- lake: six package manifests locked v4.30 transitive revs (CompPoly d458e5ce etc.) and Lake took them;
  root `require mathlib` moved last + package manifests' locked lists cleared -> resolves to Mathlib v4.35.0 pins, CompPoly 06686e4c.
- CompElliptic fork: branch toolchain-4.35 (local, e62c806 + fix): toolchain, CompPoly -> main 06686e4c (v4.35.0).
Wave 1 (8 modules, 64 errors):
- CompElliptic Fast/Projective/Core aff_smul: `simp only [if_neg huz]` no longer fires -> `simp only [aff, smul, h, huz, ↓reduceIte]`.
- Snarky/CVar ScopedBy.reduce: simpa no longer unfolds ScopedBy at `var v` -> add `CVar.ScopedBy`.
- Kimchi/Index/Basic: Mathlib `deriving Fintype` fails on GateType -> hand instance; dsimp now settles inner if -> drop 2nd `split at h`.
- Kimchi/Gate/Semantics/Poseidon: simp no longer reduces `(a::t)[0]`, `[i+1]` -> definitional `h 0 _`, `show`/`rw [Nat.add_comm]`.
- Kimchi/Gate/Semantics/VarBaseMul: rw no longer closes `match 0 with` by rfl -> `rfl` x5; `linear_combination'` removed -> `linear_combination`; seed simpa needs `[chainBuild, build]`.
- Pickles/ListLemmas: `Preorder ℕ` not reachable from imports -> `Nat.le_of_eq h.symm`.
- Pickles/Reflect/Poly: CompPoly `CRingHom` -> `CHom` (now computable); `aeval_C` simp-normal -> direct term.
- Pickles/Linearization/Map: `split` rewrites only one of two ifs (instances differ) -> by_cases + simp; private `falseCount` (Interpreter) no longer unfolds across modules -> made public, cited (3 sites).
Wave 2 (3 modules, 3 errors):
- Snarky/WP Builder.instWPMonad.wp_pure: simp no longer unfolds `build (pure a)` / `(pure a).trans` -> `show` the reduced iff, `simp`.
- Bulletproof/Wire geom_foldl: `do`-loop state is now `Prod`, not `MProd` -> restate the fold lemma over `Prod`.
- Kimchi/Index/Aggregate: `wiringPerm` simp-unfolds to private `wiringMapOf` -> `exact` (defeq) instead of `simpa`.
Wave 3 (6 modules, 11 errors):
- CompPoly API: `Domain` dropped `natCast_ne_zero` -> Kimchi/KeyDerivation + Index/InterpolationChecks constructions take 3 fields.
- Instances no longer unfold for simp (`pure` of CircuitM's Monad): Snarky/Builder gains `@[simp] build_pure` (rfl);
  Witness.witness_spec cites it; Witness's UnChecked example closes by `rfl`.
- Snarky/Kimchi/Semantics holds_congr addComplete: the membership discharger no longer reduces `#v[..].toList` ->
  state the 11-operand list by defeq, destructure.
- Snarky/Kimchi/Backend/Internal/Wiring: `wireMap_eq` restated wireMap's do-block over `MProd` -> `Classes × Nat` (14 sites).
- Kimchi/Verifier/Reflect runInput_append_zero: (kernel) deterministic timeout, also at 2x budget (75 s);
  split into per-stage lemmas: the timeout localizes to runStreamP_append_zero (Vector with dependent size proofs).
- RESOLVED Reflect kernel timeout (17:21-18:05 to diagnose): bisect -> only the stream's vector blocks.
  Cause: proofs in defs are aux constants (`runStreamP._proof_2`, the `#v[..]` size proof) typed over the
  def's args; rewriting under them (simp congruence or rw motive) leaves the kernel a defeq
  `#[(_a,..)].size =?= #[(runFtComm (pub++zs),..)].size` (resp. the olds map's size); lazy delta compares
  args first and unfolds runFtComm/runOracles (commitments + sponge) symbolically -> timeout (elaborator passes).
  Fix: block lemmas over arbitrary size proofs (`Vector.mk.injEq`), rewrite each block whole:
  runZetaOmega/runFtComm/runFtEval0P/runFrOracles/runInputP/runStreamOlds/runStreamFt _append_zero; runStreamP by unfold+rw.
  No heartbeat raise.
Wave 4 (4 modules, 55 errors) — ROOT CAUSE of most breakage identified (Init/MetaTypes.lean, v4.35):
  transparency is now `none < reducible < instances < implicit < default < all`; the `instance` command marks
  instances `[instance_reducible]` (not reducible) so simp (reducible) no longer reduces instance projections;
  implicit args are compared at `implicit`, not `default` (`backward.isDefEq.respectTransparency := true`),
  so semireducible defs in type positions (e.g. `SpongeStateVal`) no longer unfold during matching.
- Snarky/DSL/Boolean: `rw [if_neg (fun …)]`/`if_pos (by …)` no longer elaborate against the goal -> state the
  condition (`have`), `simp only [h, ↓reduceIte]` (2 sites; one needs `CVar.val` and the goal's orientation).
- Snarky/Kimchi/Circuit/Poseidon: chainHolds_window index normal form (`5*(i+1) = 5*i+5`);
  Prover.poseidon_spec: List.rec x417k blowup (simpa's closing defeq unfolding the 55-entry Vector.ofFn) ->
  `@[implicit_reducible] def SpongeStateVal` + `@[simp]` rfl lemmas varToFields_spongeState/valueToFields_spongeState.
  (`backward.isDefEq.respectTransparency false` removes the blowup too but not the projection mismatch.)
- Snarky/Kimchi/Backend/Internal/TraceSemantics: Mathlib `HasSubset.Subset.trans` now Preorder-based (deprecated) -> `List.Subset.trans` (2).
- Pickles/Linearization/Circuit: same `split` on two ifs as Map -> by_cases + simp (41 errors from one site).
Wave 5 (2 modules, 3 errors):
- Snarky/DSL/Assert assertEq soundness: cite `build_pure` in its `simp only`.
- Snarky/Kimchi/Circuit/RandomOracle hashVec: simp leaves `List.map st₀.read xs` (unapplied abbrev) vs the
  hypothesis's lambda -> simp at hr ⊢, close by `exact` (defeq).
Wave 6 (4 modules, 5 errors), all "simp no longer unfolds X":
- Pickles/OptSponge create_reads: add `RelStart`. - Snarky VarBaseMul roundBits seed: add `Pasta.Shifted.unshiftType1`.
- Snarky Backend/Internal/Direct: add `KimchiConstraint.directVars`.
- Snarky CheckedPoint WP instance: simp won't rewrite inside the instance argument of `CheckedType.post` -> `exact h` (defeq).
Wave 7 (1 module, 8 errors):
- Snarky/Kimchi/Circuit/EndoMul hws' (x2): `(w :: ws)[k+1]` not simp-reduced -> definitional term.
- OPEN: Prover.endoInv_spec: `all_goals grind [...]` fails on 5 VCs. v4.35 mvcgen presents the destructured
  pair as `h_3 : (fst, snd) = r` + let `rp`; grind derives the scope of r.2 but never r.1. Not fixed by
  respectTransparency=false nor by adding scoped_prod'/reads_prod' (186 s, still failing). Stubbed with
  `sorry` on the experiment branch to continue the build.
Wave 8 (1 module, 3 errors):
- Pickles/CheckBulletproof: elaboration order changed: `checkBulletproof_spec_success_at … rfl` now fixes the
  implicit curve `W := S.shape.ipaEndo.d.W` from the `rfl` (v4.30 took it from `hlr`), cascading into a
  simpa mismatch, a failed `AddEquiv.apply_symm_apply` rewrite and a whnf timeout -> pass `(W := C.E.toAffine)`.
Wave 9 (1 module, 2 errors):
- Pickles/Verify: core `Vector.toList_toArray` is no longer `@[simp]` (only `@[grind =_]`) -> cite it (3 simpa sites).
Wave 10 (1 module): Pickles/TwoHalves: simp now closes the goal; trailing `rfl` removed ("no goals").
Wave 11 (4 modules, 15 errors):
- Pickles/WrapVerify: v4.35 adds `Std.WP` gadget `assert`; bare `assert o.success` resolved to it (needs
  `Std.WP.Assertion (BoolVar F)`) -> `Snarky.assert` (all 9 errors were this one name).
- Pickles/Application/Proof: Fin-index normal form -> add `Fin.getElem_fin`.
- Pickles/WrapScalarHalf, StepScalarHalf: expected types keep unreduced projections of
  `GroupHalf.step/wrap`, `ScalarHalf.wrap/step` -> add them to the simpa sets (4 sites).
Wave 12 (1 module): Pickles/Soundness/WrapStep mask_rev: `Vector Bool MaxProofsVerified` vs size `= 2` no longer
  unify at implicit transparency -> `@[implicit_reducible] def MaxProofsVerified` (Statement.lean); proof unchanged.
  (Same pattern as SpongeStateVal: semireducible defs in type positions want `[implicit_reducible]` on v4.35.)
Wave 13 (1 module): Pickles/Soundness/Handover: `change (⟨_, _⟩ : AffinePoint Fq) = ⟨_, _⟩` now unfolds readVal
  through the instance (mapVec form) -> split hsg's list equality, close by coordinate extensionality.
Wave 14 (1 module, 12 errors): Pickles/Application/Verify: `simpa ... using t` closing check no longer
  identifies `producer.setup.stepSrs.k`/`wrapSrs.k` with StepIPARounds/WrapIPARounds (defeq at default, as the
  call's `rfl` arguments show) -> `have h := t; (try simp ... at h ⊢) <;> exact h` (12 sites);
  `convert hpin using 1` leaves a defeq goal -> `<;> rfl`. (`@[implicit_reducible]` on the round counts: no effect;
  respectTransparency=false: fixes 3 of 12.)
Wave 15 (2 modules, 7 errors):
- Pickles/Application/CheckedCompile lagrangeAt: second KERNEL deterministic timeout (`lagrangeAt._proof_2` = `hs`):
  `simp only` rewrote inside `domainLagrange`'s Vector.mk (dependent size proof) -> kernel unfolds
  Ipa.lagrangeBasis. Fix: unfold both vectors, `rw [Vector.mk.injEq]`, then simp at the array level.
  Module 36 s (timeout) -> 3.7 s.
- CheckedCompile public counts (2) + Application/Handover appState: simpa closing check -> have/simp/exact.
Wave 16 (1 module): Pickles/Application/MatrixRun: two `simpa only [stepValuation/wrapValuation] using hdet`
  whose types print identically (hidden instance paths) -> `(try simp only …) <;> exact hdet`.
Wave 17 (2 modules, 24 errors):
- ROOT CAUSE for "Type mismatch: After simplification": v4.35 `simpa … using h` closes at REDUCIBLE transparency
  (Lean/Elab/Tactic/Simpa.lean, `useReducible := true`); the new `simpa … using! h` keeps the old default-
  transparency close -> `using` -> `using!` (Certification 13 sites, Terminal 6). (The earlier have/simp/exact
  rewrites in Application/Verify, CheckedCompile, MatrixRun, Handover are the same fix written longhand.)
- Terminal: identical-printing dite goals after `simp only` -> trailing `rfl` (2); `split` refuses a `dite` on
  OnCurve -> by_cases + `simp only [hc, ↓reduceDIte]`.
- OPEN: Terminal WrapRun.terminal_group: closing `exact (hg b hb …)` times out in isDefEq (v4.30's exact simp
  sets via simp? don't help). Stubbed with `sorry` on the experiment branch.

# Q2 (19:15–19:25): YES under vcgen
- Sidecar tc435/sidecar/Q2.lean: Std.WP.WP/WPMonad instance for CircuitM F (Prover c) over proverWP
  (Pred = ProverState F → Prop, EPred = EvalError → ProverState F → Prop), bridge `std_of_wp` from the
  library laws; `mulU_spec` registered bare (@[spec], library shape with entry ghost st₀ and st₀ ≤ s');
  `twoMulLastU` (mul x y; mul y y) closes with `vcgen` + the in-tree grind line; axioms standard.
- Spec trace: both applications of mulU_spec leave the ghost as a fresh mvar in the pre VC
  (`⊤ ⊑ (s✝ = ?m.76 ∧ …)`, `⊤ ⊑ (s✝ = ?m.92 ∧ …)`): solved by the precondition, never by unifying
  the post; the post becomes an entailment VC.
- mvcgen on v4.35 still captures: check_reg_needed.lean reports the capture (its #guard_msgs also
  trips on an extra deprecation line).
- Deletable under vcgen: Prover.Reg / Reg.iff / register block (~35 lines, Prover/WP.lean 249–285),
  47 `_reg` definitions (~308 lines with docstrings), 142 `Prover.Reg.iff` grind/simp mentions,
  95 `Prover.register` wrappings, check_reg_needed.lean (59 lines) + CI step + README line.

# Q3 (19:30–20:40): YES — the frame carries the readings; 19.0k vs 34.8k (same toolchain)
- Sidecar tc435/sidecar/Q3.lean (404 lines; Q2's instance + new): frame `CellsAt s₀ vs s`
  (cells in scope at the entry s₀ keep scope and entry reading), `proverWP_frame` (one induction),
  `CellsAt.mono` (the ONLY read_of_le/of_le use), `Prover.frames_cellsAt : WP.Frames meet x (CellsAt s₀ vs)`
  for every program; leaves `mulQ_spec`/`divQ_spec` = library laws minus `st₀ ≤ s'` (weakened from them).
- `@[frameproc] cellsFP` (prog ``Snarky.CircuitM, meet): reads the context's conjuncts at the call's state
  (Scoped facts at s or an equated ghost, plus the previous CellsAt at s), frames `CellsAt s (new ++ old)`,
  and PROVES the entry obligation itself (rebase/cons_self/scoped_of_eq) -> no frame VC reaches the user.
- gmCandidatesQ (verbatim copy over mulQ/divQ), statement = gmCandidates_spec minus `st₀ ≤ s'`:
  `unfold; vcgen; all_goals first | exact Prover.frames_cellsAt _ _ _ | ((try simp only [CellsAt] at *);
  grind only [CVar.val, val_add_, val_sub_, Scoped.add_, Scoped.sub_, scoped_const, potentialXs])` — 7 lines,
  no le_chain, no read_of_le, no carrying lemma; axioms standard. Frames trace: tc435/q3-frames-trace.txt.
- VCs: 10 Frames (the lemma), 10 spec preconditions (scopes at the current state; div's also needs the
  divisor reading ≠ 0), 1 final readings VC.
- Heartbeats (count_heartbeats + Elab.async false): frame proof 18,986; in-tree le_chain proof verbatim on
  v4.35 34,821 (doc: 53k at v4.30). Cumulative: vcgen+frameproc 1,551; +Frames 1,792; +preconditions 10,524;
  full 18,986. Final VC alone (others sorry) 4,113 - 1,551 = 2.6k. Baseline mvcgen alone 4,431.
- Earlier variants: frameproc leaving frame VCs + blunt closer 33,757; grind can't unfold CellsAt facts by its
  equation lemmas (needs the simp at *); simp_all [CellsAt] fails (132k).

# Q4 (20:45–22:10): YES — rounds and loop instances go through as written; corollary unchanged
- Experiment module (experiment branch only, not for merge): formal/snarky/Snarky/Prover/StdWP.lean =
  Q2 instance/bridge + Q3 frame/frames lemma/proof-producing frameproc + generic Q4 pieces:
  std_post_mono, std_le (a run's entry ≤ its exit, via proverWP_frame with Fr := (st₀ ≤ ·)),
  std_witness_of_run (witness law minus ≤), ScanStep₀ + std_scanStep (round law as written from the
  ≤-free one), do_of_std (bridge back to Std.Do, to feed the scan corollary as written).
- Sidecars tc435/sidecar/Q4vbm.lean, Q4em.lean, Q4es.lean: verbatim copy of each file through its
  loop registration (in-tree proofs wrapped in count_heartbeats = v4.35 baseline) + experiment:
  wrapper leaves (nAccWitQ/bitWitQ, rowWitQ ×2) with laws minus ≤, verbatim round copy, round law
  without ≤ by vcgen + frame, the law as written by std_scanStep, the loop instance as written
  (mapAccumM_scan_spec unchanged, four transports as in the tree, round through do_of_std).
- Needed beyond Q3: (1) `vcgen simplifying_assumptions [ReadsAs.eq_1, scoped_prod', reads_prod',
  scoped_fvar, reads_fvar, tuple_fst, tuple_snd]` flattens witness posts into atoms (vcgen splits tuple
  binders, so projections of pair literals need the tuple lemmas); (2) the proof opens the precondition
  first (obtain rfl + simp only [accScoped, bitsScoped_iff']) because simplifying_assumptions does not
  reach the lifted entry precondition; (3) one flattening lemma per ∀-shaped bundle: bitsScoped_iff'
  (VBM 14 lines, EndoMul 12), crumbsScoped_iff' + vec8_toList (EndoScalar 13); (4) frame hypotheses are
  NOT reached by simplifying_assumptions (they come in through the frame rule's ⇨ split), and grind
  doesn't unfold CellsAt/rowScoped/… itself: closers `simp only [vocab] at *` then grind.
- EndoScalar leaf: std_witness_of_run elaborated against the expected type timed out (isDefEq/whnf on
  rowVal over a List); `have h := …; exact h` fixes it.
- Heartbeats (v4.35; split closer = heavy simp/grind only on the final ScanStep₀ VC):
  VBM round law in-tree 28,582 + round_readings 467 = 29.1k  → frame 34,349 (uniform closer 63,102;
    vcgen+frameproc alone 3,471; final VC ≈ 24k); scaleRound_read_of_le 8,270 (stays: loop transport)
  EndoMul in-tree 10,749 + 281 = 11.0k → frame 7,482 (uniform 8,541); roundRead_of_le 3,576 stays
  EndoScalar in-tree 3,848 + 196 = 4.0k → frame 6,547 (uniform 7,577); roundRead_of_le 838 stays
  loop instances in-tree 847 / 791 / 590 → as written over the vcgen round 479 / 431 / 228
- Lines: round law + round_readings in-tree 79 / 54 / 48 → frame law + flattening lemma 37 / 35 / 38.
- Stays under the move: ScanStep's ≤ (free via std_le), the four transport premises per loop instance,
  scaleRound_read_of_le / roundRead_of_le ×2 (loop-level transports). The corollary's content is
  unchanged; only its triple form follows the library's Std.Do → Std.WP move.
