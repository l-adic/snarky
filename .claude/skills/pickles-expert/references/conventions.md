# Pickles Field Naming & Usage Conventions

## 1. The Curve Cycle (Pasta Curves)

Both Pallas and Vesta curves use the equation: $y^2 = x^3 + 5$

| Curve | Base Field | Scalar Field |
|-------|------------|--------------|
| **Pallas** | Fp (smaller) | Fq |
| **Vesta** | Fq (larger) | Fp |

The cycle: `Pallas.ScalarField = Vesta.BaseField = Fq` and vice versa.

### Implementation Mapping

| Mina Concept | Our Implementation | Field |
|--------------|-------------------|-------|
| `Fp` / `Tick.Field` | `Pallas.BaseField` | Fp |
| `Fq` / `Tock.Field` | `Vesta.BaseField` | Fq |
| `Tick.Inner_curve` | `Pallas.G` | Pallas (Base Fp) |
| `Tock.Inner_curve` | `Vesta.G` | Vesta (Base Fq) |

---

## 2. Master Backend Mapping

| Component | Backend | Circuit Field | IPA Curve | Inner Curve |
|-----------|---------|---------------|-----------|-------------|
| **Tick/Step** | Vesta-based | **Fp** | Vesta | Pallas |
| **Tock/Wrap** | Pallas-based | **Fq** | Pallas | Vesta |

- **Circuit field**: Where polynomial coefficients live.
- **Inner curve**: Curve whose points are native to the circuit (coordinates $\in$ circuit field).

---

## 3. Shifted Value Protocol (Type1 vs Type2)

**Source:** `mina/src/lib/crypto/plonkish_prelude/shifted_value.ml`

| Type | Scenario | Encoding | Circuit |
|------|----------|----------|---------|
| **Type1** | $F_{scalar} < F_{circuit}$ | $t = (s - 2^n - 1) / 2$ | **Wrap** (Fq native, Fp foreign) |
| **Type2** | $F_{scalar} > F_{circuit}$ | $(s \gg 1, s \ \& \ 1)$ | **Step** (Fp native, Fq foreign) |

### Type2 Absorption (Sponge)
When absorbing a Type2 scalar `{sDiv2, sOdd}` into a native sponge:
1. Absorb `sDiv2` as a native field element.
2. Absorb `sOdd` as a single bit.
**No foreign field arithmetic is required.**

---

## 4. Poseidon Parameters

| Field | Used By | Rust Ground Truth |
|-------|---------|-------------------|
| **Fp** | Tick/Step | `poseidon/src/pasta/fp_kimchi.rs` |
| **Fq** | Tock/Wrap | `poseidon/src/pasta/fq_kimchi.rs` |

---

## 5. Quick Reference: "What field am I in?"

| If you see... | Circuit field is... |
|---------------|---------------------|
| `Tick`, `Step`, `Vesta_based_plonk` | **Fp** |
| `Tock`, `Wrap`, `Pallas_based_plonk` | **Fq** |
| `Inner_curve = Pallas` | **Fp** |
| `Inner_curve = Vesta` | **Fq** |
| `Type2` shifted values | **Step (Fp)** verifying Fq |
| `Type1` shifted values | **Wrap (Fq)** verifying Fp |
