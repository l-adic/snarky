# Circuit-implemented verifiers, proved faithful to the wire protocol

**Status: TARGET ARCHITECTURE — agreed 2026-07-31; work is staged, not started** (the
gadget-law layer it consumes is landing with the snarky PS-alignment walk, plan D12).
The long-range goal past `formal/docs/snarky-ps-alignment.md`: prove that circuit
implementations of the kimchi verifier are faithful to the wire-protocol verifier
(`kimchiVerify`), the way pickles' in-circuit verifiers must be.

## The shape of the problem

The verifier is NOT one circuit. It splits by native field arithmetic, pickles
deferred-values style: over a proof from curve `C`, the group-side work (fq-sponge
absorption of commitments, challenge-bit squeezing, the `f_comm`/`ft_comm` MSMs, the IPA
fold) is native to the base field, while the scalar-side work (challenge reconstruction,
`ζⁿ` ladders, barycentric public evaluations, chunk combination, the fr-sponge `(v, u)`,
`ftEval0`, the permutation scalar, the combined inner product) is native to
`C.ScalarField`. The two fragments communicate through encoded boundary values —
128-bit challenge packs, endo-mapped scalars, shifted scalars, the fq-sponge digest.

Faithfulness is therefore a glue theorem over fragments, not a single-circuit statement:
given assignments satisfying each fragment's compiled constraints, with the fragments'
public inputs decoding to the same boundary values, the wire verifier accepts.

## Invariant core (no architecture removes these)

1. **Per-gadget soundness content** — "these constraints force this variable to that
   value" must be proved for every primitive. Full circuit-determinism is false
   (`equals`'s `zInv` is unconstrained when `z = 0` — don't-care auxiliaries exist), so
   the per-gadget relational statements are irreducible.
2. **A composition mechanism** — how gadget laws chain through a fragment.
3. **A wire anchor** — the object proved faithful must be PROVED to coincide with the
   deployed `kimchiVerify`, or the theorem is about a re-implementation.

## The architecture: lemma towers over the existing embedding

No new DSL, no combinator framework. Chosen over a free-monad
DSL-with-two-interpreters because the field split breaks that design's "write the
verifier once" premise (it would need a partitioning compiler — formalizing
deferred-values compilation itself), fragments are individually small enough for towers,
and the boundary work lives outside any DSL regardless. Precedent: the kimchi package's
own `ok_iff` → `sound_*` → `chain_*` → capstone towers. The free-monad design remains
the named fallback, per fragment, if a tower's proofs become painfully repetitive at the
sponge/MSM loops — it would consume the same per-op lemmas and bind laws unchanged.

The layers, bottom to top:

1. **Gadget laws** (plan D12; `Snarky.equals_sound`/`equals_complete` and the rest, each
   beside its gadget in `Circuit/DSL/{Field,Boolean}`): per-gadget soundness — every assignment satisfying the
   constraints `build` emits pins the result's evaluation — and completeness — the
   honest `prove` run succeeds from any fresh-enough assignment. Each law reads off a
   definitional shape lemma of the built circuit, so a drifted gadget cannot keep its
   law. Field-generic in `F` by requirement: both fragments instantiate the same lemmas.
   Composition lemmas (`build`/`prove` over bind, freshness preservation) let a
   composite def's law be proved from its children's.
2. **Tower mid-levels**: each named sub-circuit def gets its law, with the DEPLOYED run
   functions as specs — `Kimchi.Verifier.Reflect` already names every intermediate of
   `kimchiVerify`'s body as a closed-form run function (`runOracles`, `runPubEvals`,
   `runVU`, `runPScalar`, `runFtComm`, `runInput`), and `kimchiVerify_reflects` reads
   acceptance into them. A scalar-side example: the `ftEval0` sub-circuit's soundness
   concludes `… = .ok (Kimchi.Protocol.Linearization.ftEval0 …)` — no new spec object.
3. **Fragments**: `scalarFragment` over `C.ScalarField`, `groupFragment` over the base
   field, each a tower root packaged through `Backend/Compile`'s payoff statement
   (walk step 14) — "a successful solve yields a satisfying assignment agreeing with the
   declared public input/output encoding" is exactly the fragment-interface seam.
4. **The boundary library**: a `Boundary` record of what crosses the fields (challenge
   bit-packs, endo pre-images, the fq-digest, shifted `cip`/`b`), per-side decode
   functions from public inputs, and `BoundaryConsistent pubP pubQ` (decode equality).
   Engines: `DSL/Bits.pack`/`unpack` round-trip laws (walk step 12 — written knowing
   this consumer) and, later, shifted-scalar decode lemmas. Digest-compression binding
   stays out of the core statement: consistency is decode-equality, matching how the
   deployment structurally enforces public-input equality.
5. **The one wire-side refactor**: the run functions are field-pure except the challenge
   seam — `fqOracles` fuses the fq-sponge squeeze with the bits-to-scalar
   interpretation. Expose it as `runChallengeBits` (base-field side) plus an
   interpretation lemma `runOracles = interpretBits ∘ runChallengeBits`. Additive lemmas
   beside `Reflect.lean`'s run functions — do not restructure them (their let-mirror of
   the verifier body is deliberate and fragile).
6. **The glue theorem**: satisfying assignments for both fragments + boundary
   consistency imply `kimchiVerify … = true`, via fragment laws → boundary decode →
   the challenge-seam lemma → `kimchiVerify_reflects`. The completeness direction runs
   `prove` and is kept quasi-definitional by a standing discipline: fragment witness
   code calls the wire verifier's own functions (the sponge gadget's `AsProver` block
   calls `Poseidon` itself, never a re-implementation).

## Staging

- Now (walk steps 9–9b): gadget-law template + `build_bind`/`prove_bind`/freshness — the
  lemma library everything above consumes.
- During the walk: steps 10–12 write Boolean/Assert/Bits laws in the same form (Bits as
  the boundary engine); step 14 builds the fragment seam.
- After the walk: the challenge-bits lemma, the fragments, the boundary library, the
  glue — each a lemma-tower exercise, no new architecture anywhere.
- Backend transport (laws over `Basic F` today → a lawful-`BasicSystem` class with
  per-constructor `holds` equations) when the `Snarky.Kimchi.GateConstraint` consumer
  materializes.
