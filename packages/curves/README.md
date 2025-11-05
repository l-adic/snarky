# Curves Package

PureScript FFI bindings for elliptic curve field operations (Pallas, Vesta, BN254).

## Build & Test

```bash
make test
```

## Architecture

Unified Rust N-API module exports all three curves with namespaced functions to avoid napi-rs External type conflicts. Each PureScript module calls curve-specific functions from the shared native module.