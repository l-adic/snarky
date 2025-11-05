# curves-napi

Rust N-API module providing native elliptic curve field operations for Pallas, Vesta, and BN254.

## Build

```bash
npm run build
```

## Usage

This package is consumed as a local npm dependency. Functions are exported with curve prefixes:
- `pallasZero()`, `pallasAdd()`, etc.
- `vestaZero()`, `vestaAdd()`, etc. 
- `bn254Zero()`, `bn254Add()`, etc.

All curves are built into a single module to avoid napi-rs External type conflicts.