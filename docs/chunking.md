● Chunking incremental plan

  The thesis: no checkpoint adds chunking semantics without first having an
  OCaml fixture and a witness-diff script that fails on it. Every PS change is
  then driven by a concrete byte-divergence, the way we drove the multi-branch
  work.

  I'll spec the first 4 checkpoints in real detail and sketch the rest.

  ---
  Checkpoint 0 — Reference fixture infrastructure

  Goal: have an OCaml-generated witness fixture at num_chunks=2, plus a
  witness-diff script that runs it, before changing any PureScript. Each later
  checkpoint can then point at a concrete byte that does or doesn't match.

  Tasks (~1 day):

  1. 0.a — mina/src/lib/crypto/pickles/dump_chunks2_simple_chain/dump_chunks2_si
  mple_chain.ml. Copy dump_simple_chain.ml, add ~num_chunks:2
  ~override_wrap_domain:N1 to the Pickles.compile_promise call. Same b0..b4
  chain shape so we can reuse the diff topology.
  2. 0.b — dune + a smoke test that the OCaml binary builds and runs to
  completion under KIMCHI_WITNESS_DUMP=/tmp/chunks2_oc_%c.witness, producing 10
  .witness files (b0..b4 × step+wrap).
  3. 0.c — tools/chunks2_simple_chain_witness_diff.sh, modeled on the existing
  simple_chain_witness_diff.sh. Runs the OCaml dump, then the PS test, then
  diffs all 10 pairs. PS-side files will not exist yet → all 10 pairs report
  SKIP (the script tolerates missing PS witnesses).
  4. 0.d — Capture the 10 OCaml fixtures and commit a small subset (b0_step +
  b0_wrap line counts, sigma columns of gate 0..N) for reference. Don't commit
  the multi-MB witness files themselves.

  Acceptance:
  - bash tools/chunks2_simple_chain_witness_diff.sh runs end-to-end with exit
  code 0 (10× SKIP).
  - Committed reference numbers establish "what we're aiming for".

  Why this first: it's pure scaffolding, zero PS risk, and gives us the
  unambiguous oracle every later checkpoint needs.

  ---
  Checkpoint 1 — Thread NumChunks type-level, default 1, no semantic change

  Goal: every site that will eventually need chunk awareness has a @numChunks
  type parameter (or value-level numChunks :: Int), but no code path consumes
  it. All existing witness diffs still pass byte-identical.

  Tasks (~3 days):

  1. 1.a — Pickles.Types: add type NumChunks = 1. Justify in the docstring:
  "matches OCaml Plonk_checks.num_chunks_by_default; widening it requires Phase
  2+".
  2. 1.b — Pickles.Constants: add numChunks :: Int = 1.
  3. 1.c — Thread @numChunks (defaulting to NumChunks) into CompileConfig and
  compileMulti's forall list. Currently no body references it. Match OCaml's
  choice of ?num_chunks:int (optional with default).
  4. 1.d — Touch every TODO(num_chunks) comment to reference the new parameter
  (just rewording — no behavior).

  Acceptance:
  - npx spago build clean.
  - All four witness diffs (NRR, simple_chain, tree_proof_return,
  two_phase_chain) still byte-identical with OCaml.
  - New chunks2_simple_chain_witness_diff.sh still 10× SKIP (we haven't
  implemented anything yet — sanity check that we didn't break the SKIP path).

  Why this first: the rest of the plan needs NumChunks in scope as a constraint
  variable. Doing it in isolation means later phases can't accidentally regress
  at NumChunks=1.

  Sub-checkpoints if 1.c gets gnarly (ordered by where strict-mode tends to
  bite):
  - 1.c.i: just Pickles.PlonkChecks.* signatures.
  - 1.c.ii: just Pickles.Verify / Pickles.Wrap.Verify.
  - 1.c.iii: Pickles.Prove.{Step,Wrap,Compile} public surface.

  ---
  Checkpoint 2 — Port actual_evaluation Horner as a pure helper

  Goal: a standalone tested function that does the chunk-combine math, with
  golden-value tests against OCaml. No production code calls it yet.

  Tasks (~2 days):

  1. 2.a — New module Pickles.PlonkChecks.Chunks:
  actualEvaluation
    :: forall n f. PrimeField f
    => Vector n f   -- chunked evaluations [e_0, e_1, ..., e_{n-1}]
    -> f            -- evaluation point pt
    -> Int          -- rounds (= log2 of SRS size, used to compute pt^rounds)
    -> f
  1. Direct port of
  mina/src/lib/crypto/pickles/plonk_checks/plonk_checks.ml:90-100 (OCaml
  actual_evaluation). Horner: e_{n-1} + (pt^rounds) * (e_{n-2} + (pt^rounds) *
  (... + (pt^rounds) * e_0)).
  2. 2.b — evalsOfSplitEvals companion: takes a Plonk_types.Evals of Vector n
  arrays and a pair of points (zeta, zetaOmega), produces the collapsed
  Plonk_types.Evals of scalars. Port of plonk_checks.ml:102.
  3. 2.c — Test fixture packages/pickles/test/fixtures/chunks/horner_*.json
  produced by a tiny new OCaml dump tool that calls actual_evaluation on known
  inputs at rounds=16, n∈{1,2,4,8} and emits the goldens.
  4. 2.d — Test.Pickles.PlonkChecks.Chunks spec:
    - n=1 golden ⇒ identity
    - n=2 golden ⇒ e_1 + pt^16 * e_0
    - n=4, n=8 goldens.
    - Property test: for any xs :: Vector n f, Vector.singleton
  (actualEvaluation xs pt 16) matches the result of folding via OCaml's Horner
  expressed as a manual sum.

  Acceptance:
  - New unit tests pass.
  - Witness diffs still byte-identical (no production code touched).

  Why standalone first: it's the math kernel. Get it right in isolation before
  the Type-level surgery in Checkpoint 3 changes the data shapes that feed it.

  ---
  Checkpoint 3 — Widen PointEval to Vector NumChunks, force NumChunks=1

  Goal: the data shape now carries NumChunks, but every site that consumes a
  chunked eval calls actualEvaluation to collapse it. At NumChunks=1 the call is
   identity ⇒ witnesses unchanged.

  This is the largest of the first 4 checkpoints because the type widening
  cascades through ~10 modules.

  Tasks (~1.5 weeks):

  1. 3.a — Pickles.Types.PointEval:
  newtype PointEval n a = PointEval
    { zeta :: Vector n a
    , omegaTimesZeta :: Vector n a
    }
  1. Add n as a phantom; downstream sites pin n ~ NumChunks.
  2. 3.b — Pickles.Types.StepAllEvals similarly: each field becomes PointEval n
  a.
  3. 3.c — Update FFI shapes
  (Pickles.ProofFFI.proof{Z,Witness,Coefficient,Sigma,Index}Evals):
    - Currently: proofZEvals :: Proof p f -> PointEval f (= { zeta :: f,
  omegaTimesZeta :: f }).
    - After: proofZEvals :: forall n. Proof p f -> PointEval n f where n =
  NumChunks.
    - The Rust binding already returns chunked arrays per OCaml's protocol;
  verify by reading kimchi-stubs.
  4. 3.d — Every consumer that did eval.zeta (treating it as scalar) now does
  actualEvaluation eval.zeta zeta srsLengthLog2. Sites:
    - Pickles.Prove.Step — IVP scalar combination
    - Pickles.Prove.Pure.{Step,Wrap} — expandDeferred
    - Pickles.Verify / Pickles.Wrap.Verify — sponge absorption + IVP
    - Pickles.PlonkChecks.CombinedInnerProduct — eval-list construction
    - Pickles.Verify.FqSpongeTranscript — sponge absorbs each chunk separately
  at n>1, but at n=1 the sponge sees one element (= unchanged)
  5. 3.e — Decision point on sponge absorption: at NumChunks=1 we currently
  absorb a single field. With NumChunks-shape, OCaml absorbs each chunk in array
   order. At n=1 this collapses to one absorb → byte-identical. Don't try to
  handle n>1 here; just thread the array and absorb the whole thing
  element-by-element.
  6. 3.f — Strict mode: every constraint that was Add 1 _ x for a phantom width
  still works. Constraints involving NumChunks itself (e.g., Vector NumChunks
  lengths) all resolve to Vector 1 at the default, which is well-formed.

  Acceptance:
  - npx spago build clean across pickles, pickles-codegen,
  pickles-circuit-diffs.
  - All four existing witness diffs still byte-identical.
  - The chunks2 witness diff still 10× SKIP (PS doesn't try to handle n=2 yet).

  Why this is the right size for one checkpoint: it's all type-level surgery, no
   new circuit semantics. We have the existing n=1 witness oracle to keep us
  honest. After this lands, every later checkpoint can change behavior at
  NumChunks > 1 without risking the n=1 regression suite.

  Pre-flight risk check (do this first inside the checkpoint, ~½ day):
  - Read the kimchi-stubs FFI signature for pallas_proof_z_evals etc. Confirm it
   does return chunked arrays. If it normalizes to a single field at
  num_chunks=1, we need a parallel "chunked" FFI binding instead of widening the
   existing one.

  ---
  Checkpoint 4 — Try NumChunks=2 end-to-end, witness-diff, fix-and-iterate

  Goal: instantiate the simple_chain test at NumChunks=2, run
  tools/chunks2_simple_chain_witness_diff.sh, watch it fail at a specific gate,
  fix, repeat. Same loop we used for multi-branch convergence.

  Tasks (~2-4 weeks; depends on what bites first):

  1. 4.a — Add a new test Test.Pickles.Prove.SimpleChainChunks2 that calls
  compileMulti with numChunks: 2 and an application body forced to require ≥2¹⁷
  gates (port the chunks2.ml filler trick: for _ = 0 to 1 lsl 17 do ignore
  (Field.mul (fresh ()) (fresh ())) done).
  2. 4.b — First run will diverge at the first chunk-aware codepath that's still
   hardwired to n=1. Almost certainly:
    - Most likely first divergence — Commitment_lengths: t = 7*num_chunks, so
  tComm is Vector 14 not Vector 7. Probe and confirm in
  Pickles.ProofFFI:660-668.
    - Second most likely — zk_rows = 5 for n=2 ⇒ omega_to_intermediate_powers
  non-empty ⇒ different sponge absorption order via
  vanishes_on_zero_knowledge_and_previous_rows having extra factors.
  3. 4.c — For each divergence, the witness diff tool tells us the exact (col,
  row) and we apply the proven multi-branch playbook from MEMORY.md.

  This checkpoint is open-ended — no point sub-planning until we've seen what
  actually breaks.

  ---
  Checkpoints 5+ (sketched only)

  Will fill in after Checkpoint 4 surfaces the real ordering of bugs. Probable
  order based on OCaml-side dependency graph:

  5. Commitment_lengths: widen tComm, wComm, zComm. Cascade through sponge
  order.
  6. zk_rows = (16n+5)/7: replace constant; expand
  vanishes_on_zero_knowledge_and_previous_rows polynomial.
  7. Wrap_verifier.combine: Horner over chunked commitment arrays in IVP MSM.
  Cascade WrapIvpBaseline formula 45 → f(num_chunks).
  8. Repeat witness-diff on chunks=4 and chunks=8 fixtures (to catch off-by-one
  in formulas that worked for n=2).
  9. End-to-end recursion: port the chunks2.ml recursive-over-chunks pattern and
   verify a wrapped chunked proof.

  ---
  Why I'm comfortable this can be incremental

  - Every checkpoint has a hard, byte-level acceptance criterion, not "it builds
   + I think it's right".
  - Checkpoints 0-3 cannot regress existing tests: Type widenings at NumChunks=1
   are structurally identity. The compiler enforces it.
  - OCaml fixtures are already authored: chunks{2,4,8}.ml exist; we just need to
   wrap each in a dump_*.ml analogue.
  - Witness-diff tooling is proven: we used it through 197 micro-iterations of
  multi-branch convergence. It scales.
  - The math kernels are pure: actual_evaluation, evals_of_split_evals,
  combine_split_evaluations, vanishes_on_zk_and_previous_rows are all field

  Will fill in after Checkpoint 4 surfaces the real ordering of bugs. Probable order based on
   OCaml-side dependency graph:

  5. Commitment_lengths: widen tComm, wComm, zComm. Cascade through sponge order.
  6. zk_rows = (16n+5)/7: replace constant; expand
  vanishes_on_zero_knowledge_and_previous_rows polynomial.
  7. Wrap_verifier.combine: Horner over chunked commitment arrays in IVP MSM. Cascade
  WrapIvpBaseline formula 45 → f(num_chunks).
  8. Repeat witness-diff on chunks=4 and chunks=8 fixtures (to catch off-by-one in formulas
  that worked for n=2).
  9. End-to-end recursion: port the chunks2.ml recursive-over-chunks pattern and verify a
  wrapped chunked proof.
  Will fill in after Checkpoint 4 surfaces the real ordering of bugs. Probable order based on OCaml-side dependency graph:

  5. Commitment_lengths: widen tComm, wComm, zComm. Cascade through sponge order.
  6. zk_rows = (16n+5)/7: replace constant; expand vanishes_on_zero_knowledge_and_previous_rows polynomial.

  Will fill in after Checkpoint 4 surfaces the real ordering of bugs. Probable order based on OCaml-side dependency graph:

  5. Commitment_lengths: widen tComm, wComm, zComm. Cascade through sponge order.
  6. zk_rows = (16n+5)/7: replace constant; expand vanishes_on_zero_knowledge_and_previous_rows polynomial.
  7. Wrap_verifier.combine: Horner over chunked commitment arrays in IVP MSM. Cascade WrapIvpBaseline formula 45 → f(num_chunks).
  8. Repeat witness-diff on chunks=4 and chunks=8 fixtures (to catch off-by-one in formulas that worked for n=2).
  9. End-to-end recursion: port the chunks2.ml recursive-over-chunks pattern and verify a wrapped chunked proof.

  ---
  Why I'm comfortable this can be incremental

  - Every checkpoint has a hard, byte-level acceptance criterion, not "it builds + I think it's right".
  - Checkpoints 0-3 cannot regress existing tests: Type widenings at NumChunks=1 are structurally identity. The compiler enforces it.
  - OCaml fixtures are already authored: chunks{2,4,8}.ml exist; we just need to wrap each in a dump_*.ml analogue.
  - Witness-diff tooling is proven: we used it through 197 micro-iterations of multi-branch convergence. It scales.
  - The math kernels are pure: actual_evaluation, evals_of_split_evals, combine_split_evaluations, vanishes_on_zk_and_previous_rows are all field
  arithmetic. Test in isolation.

  Suggested start

  Just Checkpoint 0 and 1 in their own PRs. ~4 days total. After 1 lands, we have NumChunks plumbed and an OCaml fixture waiting; from there the rate is
  bounded by how fast we can move on per-divergence fixes, not by infrastructure friction.

