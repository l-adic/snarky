# Poseidon Circuit Implementation Notes

## Overview
We successfully implemented Poseidon cryptographic constraint evaluation for the snarky circuit construction framework, with specialized implementations for both Pallas and Vesta field types.

## Architecture

### Low-Level Permutation vs High-Level Hash Function
Our implementation focuses on the **low-level Poseidon permutation constraint** rather than the full sponge construction:

- **What we implemented**: 55-round Poseidon permutation that takes `Vector 3 f` and produces `Vector 3 f`
- **What we discovered we need**: Full sponge construction with absorption and squeeze phases for variable-length input hashing

### Key Components

#### 1. Type Class Design (`packages/poseidon/src/Poseidon/Class.purs`)
```purescript
class PoseidonField f where
  sbox :: f -> f                           -- x^7 operation
  applyMds :: Vector 3 f -> Vector 3 f    -- 3x3 MDS matrix application
  fullRound :: Vector 3 f -> Int -> Vector 3 f
  getRoundConstants :: Proxy f -> Int -> Vector 3 f
  getNumRounds :: Proxy f -> Int           -- Returns 55
  getMdsMatrix :: Proxy f -> Vector 3 (Vector 3 f)
  hash :: Array f -> f                     -- High-level sponge hash
```

#### 2. Constraint Validation (`packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/Poseidon.purs`)
- Validates 55 round transitions using mathematical constraint evaluation
- Each round: S-box → Add round constants → MDS matrix multiplication
- Uses FFI bindings to proof-systems Rust implementation
- Type: `PoseidonConstraint f = { state :: Vector 56 (Vector 3 (FVar f)) }`

#### 3. Circuit Implementation (`packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/Poseidon.purs`)
```purescript
poseidonConstraintCircuit :: Vector 3 (FVar f) -> Snarky t m (Vector 3 (FVar f))
```
- Creates witness table for all 56 states (initial + 55 round outputs)
- Uses `Vector.scanl` with `Vector.cons` to handle PureScript's scanl behavior
- Fires `KimchiPoseidon` constraint to bind the computation

## Key Technical Discoveries

### 1. Vector.scanl Behavior Difference
**PureScript vs Haskell**: PureScript's `scanl` doesn't include the initial state in output
- **Solution**: Use `Vector.cons` to prepend initial state: `initialState :<| Vector.scanl`
- **Result**: Correct 56-state witness table (initial + 55 rounds)

### 2. Field-Specific Implementation Required
Cannot use generic field type `f` with FFI functions:
- **Created**: Separate `Pallas.purs` and `Vesta.purs` FFI modules
- **Avoided**: "PallasBaseField" usage - use proper field modules instead

### 3. Constraint vs Hash Function Distinction
**Low-level constraint circuit** (what we implemented):
- Input: `Vector 3 (FVar f)` 
- Output: `Vector 3 (FVar f)`
- Validates: Single 55-round permutation

**High-level hash function** (future work needed):
- Input: Variable-length `Array f` or `Array (FVar f)`
- Output: Single `FVar f`
- Implements: Full sponge construction with absorption/squeeze

## Testing Strategy

### Current Tests
- `poseidonHash`: Extracts element 2 from constraint circuit output
- `poseidonConstraintCircuit`: Tests full 3-element state output
- **Reference implementation**: Manual `fullRound` application (not sponge hash)
- **Verification**: Against proof-systems FFI implementation

### Test Architecture
```purescript
circuitSpecPure' constraints eval solver (satisfied referenceImpl) genInputs
```
- Generates random `Vector 3 (F PallasBaseField)` inputs
- Compares circuit output with reference computation
- All 32/32 tests passing

## Future Work: In-Circuit Random Oracle

### Current Gap
Our circuit implements the Poseidon permutation but not the full hash function that OCaml code uses as a random oracle in pickles.

### Sponge Construction Requirements
For variable-length input hashing, we need:
1. **Absorption phase**: Break input into chunks, XOR with state, apply permutation
2. **Squeeze phase**: Extract output elements from final state
3. **Padding**: Handle inputs not divisible by rate (number of absorbed elements per round)

### Implementation Path
The high-level `hash` function in our type class should guide the circuit implementation:
```purescript
-- Current: low-level permutation
poseidonConstraintCircuit :: Vector 3 (FVar f) -> Snarky t m (Vector 3 (FVar f))

-- Needed: high-level hash function  
poseidonHashCircuit :: Array (FVar f) -> Snarky t m (FVar f)
```

## Key Files
- **Type class**: `packages/poseidon/src/Poseidon/Class.purs`
- **FFI bindings**: `packages/poseidon/src/Poseidon/FFI/{Pallas,Vesta}.purs`
- **Constraint evaluation**: `packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/Poseidon.purs`
- **Circuit implementation**: `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/Poseidon.purs`
- **Tests**: `packages/snarky-kimchi/test/Test/Snarky/Circuit/Kimchi/Poseidon.purs`

## Status
✅ Low-level permutation constraint: **Complete and tested**
🔄 High-level sponge hash function: **Type class defined, circuit implementation needed**