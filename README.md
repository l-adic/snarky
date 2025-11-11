# Snarky

Embedded DSL for constructing zero-knowledge circuits in PureScript.


## Summary
A port of the [ocaml snarky DSL](https://github.com/o1-labs/snarky) to PureScript,
backed by [arkworks](https://github.com/arkworks-rs/algebra) for the finite field
arithmetic and cryptography (using [napi-rs](https://napi.rs/)).

## Example
The closest thing to an example is currently the [factors test](https://github.com/l-adic/snarky/blob/main/packages/snarky/test/Snarky/Test/Circuit/Factors.purs).
This is like the hello-world of zk circuits: 

Given a public integer `n`, I know a private non-trivial factorization (neither factor being `1` or `n`) `a` and `b` such that `a * b == n`

## Build

```bash
make all
```

## Test

```bash
make test
```

## Structure

- `packages/curves/` - Elliptic curve field operations (Pallas, Vesta, BN254)
- `packages/snarky/` - Circuit DSL
