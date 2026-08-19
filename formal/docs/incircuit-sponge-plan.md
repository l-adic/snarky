# The random-oracle package port — implementation plan

## What and why

`packages/random-oracle` is the PS hashing layer between the Poseidon permutation and
its consumers: the duplex sponge (absorb/squeeze, the Fiat–Shamir transcript
primitive) and the block hash (`Random_oracle.hash`), each at two levels — over field
values and over circuit variables. The Lean side has the value duplex sponge
(`Poseidon.Basic`, fixture-validated against `mina_poseidon` traces) and the
permutation gadget (`Snarky.Kimchi.poseidon`, oracle-checked), and nothing in between:
no circuit sponge, no block hash at either level. Any in-circuit verifier that needs a
challenge must hand-roll raw permutation calls and re-prove its own absorb schedule.

This plan ports the package's remaining content. The circuit modules land in the
snarky package's Kimchi tree (they emit the `poseidon` gadget, which is
kimchi-specific); the value module lands in the poseidon package beside the value
sponge it belongs with. Each circuit op gets a sound/complete law pair pinning it to
its value counterpart, so any absorb/squeeze schedule composes with no per-transcript
lemmas.

| PS module | Contents | Lean status / target |
| --- | --- | --- |
| `RandomOracle/Sponge.purs` | value duplex sponge | **ported** — `Poseidon.Basic` |
| `Snarky/Circuit/RandomOracle/Sponge.purs` | circuit duplex sponge | S1–S2 → `Snarky/Kimchi/Circuit/Sponge.lean` |
| `RandomOracle.purs` | value block hash | S3 → `poseidon/Poseidon/RandomOracle.lean` |
| `Snarky/Circuit/RandomOracle.purs` | circuit block hash | S4 → `Snarky/Kimchi/Circuit/RandomOracle.lean` |
| `RandomOracle/Input.purs` | `Chunked` packing (`packToFields`) | deferred (see below) |
| `RandomOracle/DomainSeparator.purs` | domain-separated init states | deferred (see below) |

## Ground truth (verified on main)

- Value sponge, `poseidon/Poseidon/Basic.lean`: `Mode`, `absorb1`, `addSlot` are
  `private`; `slot`, `init`, `absorb` (= `foldl absorb1`), `squeeze` public. Branch
  tests are spelled `n.val = 2`; mode advance `.absorbed (n + 1)`; `addSlot` adds
  `slot + x`.
- Permutation gadget, `snarky/Snarky/Kimchi/Circuit/Poseidon.lean`: `poseidon (p :
  Poseidon.Params F) (s : FVar F × FVar F × FVar F) : CircuitM F c _`. Its laws are in
  the same file, stated at `c := KimchiConstraint F`, both threading `hsize :
  p.roundConstants.size = 5 * 11`; `poseidon_spec` payload: result cell-vals =
  `Poseidon.blockCipher p` of input cell-vals. Neither is `@[spec]`-registered.
- Seal, `snarky/Snarky/Circuit/DSL/Utils.lean`: `sealVar`, with `@[spec]`-registered
  `sealVar_spec` (payload `r.val V = x.val V`) and `sealVar_complete_spec`
  (pre `(x.eval env).isOk`, post `∀ xv, x.eval env = .ok xv → r.eval env' = .ok xv`).
- PS circuit sponge: exports exactly `initialState`, `spongeFromConstants`, `absorb`,
  `squeeze`; absorption is `seal (add_ x state[i])` (input-first operand order); the
  mode is plain PS data, not circuit variables. The PS circuit block hash does **not**
  seal — `addBlock` feeds bare `add_` sums straight into the permutation.
- Oracle corpus: no standalone sponge or hash circuit exists
  (`poseidon_step_circuit.json` covers the raw permutation gadget only).

## Stages

One commit per stage, review pause after each. Standing gates for every stage: the
packages build (`lake build Poseidon Snarky` from `formal/`), `scripts/check-style.sh`,
the touched packages' axiom gates, `scripts/deadcode.sh`; poseidon fixture scripts
(`check_sponge_vectors.sh`, `check_fq_sponge.sh`) whenever poseidon is touched; the
snarky oracle corpus as regression whenever the Kimchi tree is touched.

### S0 — poseidon exposure (~15 lines, `poseidon/Poseidon/Basic.lean` only)

The circuit sponge shares the value sponge's mode type and its laws target the value
single-element step, so:

- `private inductive Mode` → `inductive SpongeMode` (public; renamed because `Mode`
  is too generic a name to export from `Poseidon`). Internal references: the `State`
  field and docstring mentions. Nothing outside the file names it today.
- `private def absorb1` → public (the law target; `absorb` stays `foldl absorb1`).
- `private def addSlot` → public (the S2 proofs reduce `absorb1` applications by
  `simp only [Poseidon.absorb1, Poseidon.addSlot]` from the snarky package, which
  requires both nameable).

No semantic change. Reachability of the newly-public names is via existing roots
(`absorb`/`State`), so no `roots.txt` change.

### S1 — the circuit duplex sponge (`snarky/Snarky/Kimchi/Circuit/Sponge.lean`, new, ~100 lines)

Namespace `Snarky.Kimchi`, importing the permutation gadget module. Public surface =
the PS export list exactly; the slot helpers stay private.

```lean
structure SpongeVar (F : Type) where
  state : FVar F × FVar F × FVar F   -- the width-3 state, as circuit variables
  mode  : Poseidon.SpongeMode        -- absorbed n / squeezed n, shared with the value sponge

def SpongeVar.init : SpongeVar F                              -- initialState: const-0 cells, absorbed 0
def SpongeVar.ofConstants (s : Poseidon.State F) : SpongeVar F -- spongeFromConstants
private def slotVar    : (triple) → Fin 3 → FVar F             -- Poseidon.slot over FVar (pure read)
private def addSlotVar : (triple) → Fin 3 → FVar F → CircuitM F c (triple)
  -- per slot: sealVar (CVar.add_ x cell), PS operand order (add_assign: seal (state[i] + x))

def SpongeVar.absorb (p : Poseidon.Params F) (sv : SpongeVar F) (x : FVar F) :
    CircuitM F c (SpongeVar F)
def SpongeVar.squeeze (p : Poseidon.Params F) (sv : SpongeVar F) :
    CircuitM F c (FVar F × SpongeVar F)
```

`absorb`/`squeeze` mirror `Poseidon.absorb1`/`Poseidon.squeeze` branch for branch —
same `match sv.mode`, same `if n.val = 2` spelling, same `.absorbed (n + 1)` mode
arithmetic — with `addSlotVar`/`poseidon p`/`slotVar` in place of
`addSlot`/`blockCipher p`/`slot`. Argument order also mirrors `absorb1` (sponge, then
element). Constraint emission: one `poseidon` call per permutation, one seal per
absorb, squeeze reads are free.

Port-fidelity notes for the module docstring's deviation ledger:

- state is the concrete triple, not PS's `Vector 3` (matching the gadget and the value
  sponge's `Triple`);
- branch tests spelled `n.val = 2` as in the value sponge (PS: `n == rate`, rate = 2 —
  same thing, chosen so S2's `if_pos`/`if_neg` align);
- seal operand order kept as PS writes it (`add_ x cell`), so a future byte-parity
  check sees identical CVar trees;
- **no oracle circuit yet**: the corpus has no standalone sponge dump, so the port is
  byte-unverified until one is added; S2 pins value-semantics to the fixture-validated
  value sponge, which is the semantic half. (Decision point at review: default is to
  note and defer; the alternative is a new PS-side dump + transcription, which drags
  `packages/pickles-circuit-diffs` into scope.)

Wiring: the four public names go into `snarky/roots.txt` as port surface (they are
consumer-less until S2, and port surface is rooted by standing policy).

### S2 — the duplex sponge laws (same file, ~300 lines)

Two reads-as relations (naming to be aligned with the house `Reads` vocabulary at
write time — sound side is `val`-based, complete side `eval`-based):

```lean
def SpongeVar.Vals (V) (sv : SpongeVar F) (s : Poseidon.State F) : Prop :=
  sv.state.1.val V = s.state.1 ∧ sv.state.2.1.val V = s.state.2.1 ∧
  sv.state.2.2.val V = s.state.2.2 ∧ sv.mode = s.mode

def SpongeVar.Reads (env) (sv : SpongeVar F) (s : Poseidon.State F) : Prop :=
  -- same shape with `.eval env = .ok _` cells
```

with near-rfl entry points `vals_init : Vals V .init Poseidon.init`,
`vals_ofConstants : Vals V (.ofConstants s) s`, and their `reads_*` twins.

The four op laws, at `c := KimchiConstraint F` like `poseidon_spec`, each threading
`hsize` (consumers discharge it once per params instantiation):

```lean
@[spec] theorem SpongeVar.absorb_spec … :
  ⦃Sound (fun V r => ∀ s, Vals V sv s → Vals V r (Poseidon.absorb1 p s (x.val V))) Q⦄
  SpongeVar.absorb p sv x ⦃Q⦄

@[spec] theorem SpongeVar.squeeze_spec … :
  ⦃Sound (fun V r => ∀ s, Vals V sv s →
      r.1.val V = (Poseidon.squeeze p s).1 ∧ Vals V r.2 (Poseidon.squeeze p s).2) Q⦄
  SpongeVar.squeeze p sv ⦃Q⦄
```

plus `absorb_complete_spec` / `squeeze_complete_spec` in the same conditional shape
over `Reads` (pre: input cells and `x` evaluable; post: output `Reads` the value step).
All four `@[spec]`-registered so transcripts of any shape glide under mvcgen; the
unregistered `poseidon_spec`/`poseidon_complete_spec` get wrapped here once and
downstream never touches them again.

Proof route, each law: destructure `sv`, case on the (meta-level) mode, `by_cases hn :
n.val = 2` — the branch program is then concrete; walk it with
`poseidon_spec`/`poseidon_complete_spec` (manual refine) and the registered `sealVar`
laws; in the payload, `intro s hs`, destructure, substitute the mode equality so the
value-side `absorb1`/`squeeze` reduces by `simp only` with `[absorb1, addSlot, slot,
if_pos hn]`; cell goals close by the `CVar.add_` val/eval lemmas plus `add_comm` (PS
seals `x + cell`, the value `addSlot` adds `cell + x`); mode goals are `rfl`.

Wiring: the four laws + four entry points added to `snarky/roots.txt` and
`snarky/scripts/check_axioms.lean` (146 → 154).

### S3 — the value block hash (`poseidon/Poseidon/RandomOracle.lean`, new, ~80 lines + validation)

Port of `RandomOracle.purs`, namespace `Poseidon.RandomOracle`, over the value
sponge's `Triple`:

```lean
def toBlocks (xs : List F) : List (F × F)   -- rate-2 chunking, zero-padded; [] → one zero block
def addBlock (st : Triple) (b : F × F) : Triple
def update (p : Params F) (st : Triple) (xs : List F) : Triple
  -- foldl (blockCipher p ∘ addBlock) over toBlocks — permute after every block
def digest (st : Triple) : F              -- slot 0
def hash (p : Params F) (xs : List F) : F -- digest (update p init.state xs)
```

Validation is a theorem, not a fixture: block mode and the duplex automaton agree —

```lean
theorem hash_eq_sponge (p : Params F) (xs : List F) :
    hash p xs = (Poseidon.squeeze p (Poseidon.absorb p Poseidon.init xs)).1
```

The two differ only in permute scheduling (block mode permutes eagerly after each
block, the duplex lazily before the next absorb or at the squeeze) and in padding
(zero-padding adds `0` to a slot, which is the identity). The proof is an induction
over blocks with a two-case alignment invariant; if it turns out disproportionate,
fall back to trace validation through the existing poseidon fixture kit and demote the
theorem to a follow-up — flagged at review either way.

Wiring: poseidon `roots.txt` + its axiom-gate script gain the surface; both poseidon
fixture scripts rerun.

### S4 — the circuit block hash (`snarky/Snarky/Kimchi/Circuit/RandomOracle.lean`, new, ~120 + ~200 lines)

Port of `Snarky/Circuit/RandomOracle.purs`'s operational core:

```lean
def initState : FVar F × FVar F × FVar F                  -- const-0 cells
private def addBlockVar : (triple) → FVar F × FVar F → (triple)  -- bare add_, NO seal (as PS)
private def updateBlock (p) : (triple) → FVar F × FVar F → CircuitM F c (triple)
def update  (p) (st : triple) (xs : List (FVar F)) : CircuitM F c (triple)
  -- meta-level chunking mirroring PS: odd-pad with const 0, [] → one zero block, foldlM updateBlock
def hash2   (p) (a b : FVar F) : CircuitM F c (FVar F)
def hashVec (p) (xs : List (FVar F)) : CircuitM F c (FVar F)
```

Laws in the S2 style, pinning each op to the S3 value model: `update_spec` /
`update_complete_spec` (cell-wise conditional payload, result cells read as
`RandomOracle.update p (input cell-vals) (map val xs)`), with `hash2_spec` /
`hashVec_spec` and complete twins as corollaries reading as `RandomOracle.hash`. The
chunking is meta-level (list structure, not circuit data), so the walk is a `foldlM`
induction over blocks, each step discharged by the wrapped permutation law; the value
side steps by `List.foldl` unfolding of S3's `update`.

Not ported, recorded in the module docstring's deviation ledger:

- the `Digest` newtype and its `CircuitType`/`CheckedType`/`AssertEqual` instances,
  and the `Hashable`/`HashInput` classes with `hashOf` — PS generic-deriving and
  dispatch ergonomics; the Lean port models the operations, and Lean callers apply
  them directly;
- PS's `Vector 3`/`Vector 2` become the concrete pairs/triples, as everywhere else.

Wiring: roots + axiom-gate entries for the public surface and laws.

## Deferred, explicitly

- **`RandomOracle/Input.purs`** (`Chunked`, `packToFields` — the greedy bit-packer
  mirroring mina's `Random_oracle_input.Chunked.pack_to_fields`): self-contained and
  portable, but nothing on the Lean side consumes structured hash inputs yet. Port it
  when a consumer (account/merkle-style hashing) arrives.
- **`RandomOracle/DomainSeparator.purs`**: FFI-backed (`foreign import` per curve) —
  the semantics live in JS, not PS source, so a port means transcribing the
  mina-hasher domain-string algorithm and validating it against vectors. Defer until
  domain-separated hashing has a Lean consumer.
- **A sponge/hash oracle circuit** (byte-parity for S1/S4): see the S1 decision point.

## Payoff

The hashing layer stops at hand-written permutation calls today; after this, it is
`absorb`/`squeeze`/`hash` with laws that already know what they compute. Any
Fiat–Shamir transcript or in-circuit hash — whatever the schedule — composes from the
four registered op laws and lands on the fixture-validated value sponge, with no new
sponge reasoning per consumer.
