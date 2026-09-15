# Findings from implementing the rule-DSL simplification

Corrections and additions to `pickles-rule-dsl-simplification-plan.md`,
keyed to its sections. Written from the work on branch
`worktree-pickles-rule-dsl-phase1` (base `origin/main`), which is where
every claim below was checked.

This file exists separately only because the plan lives on another
branch; fold each item into the section it names.

## 1. The plan's Phase 1 and Phase 3 are not buildable as written

§5 says the three `CompilableSpec` methods become three functions over
`Array Slot`, and that Phase 3 then deletes the class. Their *inputs*
can be an array. Their *outputs* cannot: each returns a carrier indexed
per slot by that slot's own chunk count — the VK blueprint chain and the
per-proof witness carrier. A function over an array cannot build a
per-slot type-indexed chain, so the class survives, and Phase 3's
deletion sits behind it.

This is not a defect in the chunk axis. A slot verifies a proof from
another application, applications are compiled independently, and an
application importing one chunked tag and one unchunked one has slots
that genuinely differ in it. That every slot declaration in the
repository currently says `1` is a fact about the fixtures, not about
the axis. §3.3 and §8.4 are right to keep it type-level.

**What landed instead**: the deduplication half. Each of the three
methods had two instance bodies that were near-verbatim copies differing
only in what kind of slot the head is. Each now has one shared body, and
the instances supply only the differences.

| Method | Commit |
|---|---|
| compile shape | `c320838a` |
| prove data | `9ac3ea92` |
| advice | `bfe19d41` |

`Prove/Compile.purs` went 4193 → 3751 lines, 1254 deletions against 856
insertions.

Rewrite Phases 1 and 3 around this boundary, or scope the chunk axis as
its own project first. Reifying that axis is much harder than the slot
widths were: a width only sized containers, so an array plus a width
sufficed, whereas the chunk count also determines how many bases the
in-circuit verifier folds, through a chain of multiplications and
additions. Erasing it changes loop structure inside the circuit.

## 2. Two type-level residues, both of which should stay (§3.2)

**`outputSize`** cannot be erased here. `compile` takes the circuit's
public output as a `Proxy` and counts its field elements through
`CircuitType`, so the width must be in the type. Neither option §3.2
offers — an existential, or a runtime-length output — is available
without changing `snarky`, which the reified-`Typ` work deliberately did
not do. Open question 3 should be closed as "not a pickles decision".

**The consumer-side slot width** is a second residue §3.2 does not name:
the one in `verifyOne`, `finalizeOtherProofCircuit` and
`challengePolyEvals`. It is unconstrained in all three signatures — no
reflection, no arithmetic. Its only effect is to tie the mask, the
challenge stacks and the opening points to one length, which is what
keeps five zips total. Erasing it would trade those for silently
truncating array zips inside the sponge digest and the inner-product
helpers, where a truncated mask absorbs fewer challenges. No gate here
could catch that, because every fixture builds the three collections
from a single width, so they always agree. Leave it.

## 3. §3.3's rule has no room for `mpv`

The stated rule is that a length varying per application is runtime and
a length fixed by kimchi or pickles stays in the type. `mpv` is neither:
it varies per application *and* is named by the specification. The
sentence needs a third case, or a rewording that puts `mpv` on the
type-level side for a stated reason.

## 4. The wrap domain was computed three different ways, all wrong

Before this branch, the compiler derived it from the three-entry table
in three places: applied to the number of slots from that position to
the end of the list, and applied to the head slot's own bound. An
override then replaced the result, which is why nothing failed: every
rule is either single-slot, where the readings coincide, or overridden,
where none is consulted.

OCaml computes one value per compile: the override when given, otherwise
the table applied to `max_proofs_verified`. That is now what this does
(`31a467aa`).

**There is no estimator on either side.** `Wrap_domains.Make.f`, the
function `compile.ml:472` actually calls, is only the table lookup. The
same functor defines `f_debug`, which builds a dummy wrap circuit and
measures it, but nothing calls it, and the file carries a TODO asking
why the functor ignores its own arguments. So the table is a guess in
both languages, and the override is how a wrong guess is corrected.

OCaml also checks the guess against the wrap circuit it built and fails
with a message naming both sizes. That check had no port; it does now
(`4fdbd087`). Without it a wrong guess surfaced much later as a kimchi
permutation error naming neither the domain nor the override.

## 5. A two-slot rule with no override cannot work, in either language

Consequence of §4, worth recording because it looks like a test gap. The
table says 15 for two proofs; `SimpleChainN2`'s wrap circuit is really
14. Removing its override makes the guard fire with exactly those two
numbers. OCaml hits the same wall, which is why its own dumper passes
`override_wrap_domain`. So there is no such fixture to write, and the
positional reading corrected in §4 had never worked.

## 6. Process: the incremental check gives false greens

`check` returned clean in 0.2 s on a tree where the build had five real
errors, more than once. Only the gates are evidence for anything
crossing a module boundary, and they must be run sequentially — they
drive `spago` against the same build directory.

For the work in §1 the prove gate is the load-bearing one: those bodies
do cross-field coercions and oracle calls that only end-to-end proving
exercises, so a bad text move would pass a type-check and fail there.
