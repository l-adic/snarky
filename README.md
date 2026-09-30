# Snarky

[![CI](https://github.com/l-adic/snarky/actions/workflows/test.yml/badge.svg)](https://github.com/l-adic/snarky/actions/workflows/test.yml)
[![Lean](https://github.com/l-adic/snarky/actions/workflows/lean.yml/badge.svg)](https://github.com/l-adic/snarky/actions/workflows/lean.yml)

Snarky is a PureScript implementation of Mina's recursive proof stack: the snarky circuit
DSL, the kimchi proof system, and pickles recursion. The cryptography comes from o1-labs'
[proof-systems](https://github.com/o1-labs/proof-systems) through a Rust binding that builds
for Node and for the browser. Alongside it, a Lean 4 formalization specifies kimchi and
pickles and checks the PureScript circuits against that specification.

**Demo:** [l-adic.github.io/snarky](https://l-adic.github.io/snarky/) proves a block of
ledger transactions in the browser, merging them recursively into a single proof.

## Why

Pickles lets a chain of computations of any length be checked with one constant-size proof.
It is how Mina verifies its entire history in one step. Its reference implementation is OCaml
inside the Mina node, and o1js reaches it through a js_of_ocaml build of that same code.
Snarky is an independent implementation, written to be read. Circuits are typed PureScript
values, and the prover and verifier are ordinary library code. Every circuit is compared
against the deployed original, so no piece is assumed to match it.

## What's here

**A circuit DSL.** `snarky` builds constraint systems from typed programs over field
elements, booleans, bit decompositions, and curve points, and over user types that define how
they are allocated and checked. One program yields both the constraint system and, given
inputs, its witness. `snarky-kimchi` compiles to kimchi's gates, including its custom Poseidon
and scalar-multiplication gates. Built on top of it are Poseidon and the random-oracle sponge,
Schnorr signatures, and Merkle trees.

**Pickles.** `pickles` implements the recursion over the Pasta curve cycle. A step circuit
runs an application rule and verifies up to two previous proofs. A wrap circuit, over the
other field, verifies the step proof, so every proof in a chain ha
same verifier. Side-loaded verification keys and circuits larger than the SRS (chunking) are
supported. In CI, the constraint systems of 121 circuits, whole st
their gadgets, are compared gate by gate against those exported from Mina's OCaml. On a shared
recursive benchmark, native PureScript compiles 2.6× faster and pr
([bench/README.md](bench/README.md)).

**A formal specification.** [`formal/`](formal/README.md) is a Lea
development containing:

- kimchi's gates as predicates on witnesses, with the elliptic-cur
  Mathlib's group law and the Poseidon gate against the production
- the arithmetization that reduces a satisfied circuit to one poly
- the verifier, an executable transcription of `kimchi/src/verifie
  inner-product commitment it finishes on, validated against proofs and keys recorded from
  the Rust implementation;
- a deep embedding of the snarky DSL;
- a Lean port of the pickles circuits. CI checks that their constr
  PureScript ones, and theorems show that a valuation satisfying the step and wrap circuits
  carries proofs that `kimchiVerify` accepts, composed along a cha

The claims are relative. Satisfying the circuits implies that the specified verifier
accepts. The development makes no cryptographic soundness claim, and it excludes lookups and
kimchi's optional gates (range check, foreign-field, XOR, rotation).

## Layout

| Path | Contents |
| --- | --- |
| `packages/kimchi-napi` | Rust binding to proof-systems (napi-rs
| `packages/curves`, `pasta-runtime` | Pasta fields and curves |
| `packages/snarky`, `snarky-curves`, `sized-vector` | the DSL, in-circuit curve arithmetic, type-level vectors |
| `packages/snarky-kimchi` | the kimchi backend |
| `packages/poseidon`, `random-oracle`, `blake2` | hashing and sponges |
| `packages/schnorr`, `merkle-tree` | signatures and authenticated storage |
| `packages/pickles` | recursion: step, wrap, prove, verify |
| `packages/pickles-circuit-diffs` | the gate-level comparison against Mina's OCaml circuits |
| `packages/example` | a Merkle-ledger rollup: transfer circuits, a snark-worker pool, terminal and web apps |
| `formal/` | the Lean formalization (`Pasta`, `Poseidon`, `Bulletproof`, `Kimchi`, `Snarky`, `Pickles`) |
| `bench/` | the o1js comparison harness |
| `mina/` | the Mina submodule, used as the reference implementation |

## Building

You need Node.js 23 and a stable Rust toolchain. The Lean build also needs
[elan](https://github.com/leanprover/elan).

```bash
git clone --recursive https://github.com/l-adic/snarky
npm install                                  # dependencies + native binding
make fetch-srs && make gen-linearization     # SRS files, generated pickles code
npx spago build && make test
make lean-build                              # formal/ (run `lake exe cache get` there first)
```

Run `make help` to list the remaining targets.
