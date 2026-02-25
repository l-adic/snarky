# Type2 Shifted Value: OCaml vs PureScript Representation

## Summary

~~Previously we believed OCaml's `Shifted_value.Type2` wraps a single field element,
creating a mismatch with PureScript's two-value representation.~~

**This was incorrect.** OCaml's `Type2` is polymorphic (`Shifted_value of 'f`), and in the
actual circuit representation, `'f` is instantiated as `(Field.t * Boolean.var)` — the same
`(s_div_2, s_odd)` pair that PureScript uses. There is no structural mismatch.

## The polymorphism trick

Source: `mina/src/lib/crypto/plonkish_prelude/shifted_value.ml`

```ocaml
module Type2 = struct
  type 'f t = Shifted_value of 'f    (* 'f is polymorphic! *)
end
```

The type definition looks like a single-element wrapper, but `'f` gets instantiated differently
depending on context:

| Context | `'f` instantiation | Circuit vars |
|---------|-------------------|-------------|
| Constant/prover side | `Tock.Field.t` (single) | n/a |
| Step circuit (Fp) | `(Field.t * Boolean.var)` | 2 |

### Prover side: single field element

The `of_field`/`to_field` functions operate on single field constants (for serialization):
- `of_field s = Shifted_value (s - 2^n)`
- `to_field (Shifted_value t) = t + 2^n`

### Circuit side: pair (matches PureScript)

In the Step circuit, `Other_field.t` is defined as a pair (`mina/src/lib/crypto/pickles/impls.ml:50-56`):

```ocaml
module Other_field = struct
    (* Tick.Field.t = p < q = Tock.Field.t *)
    type t = (* Low bits, high bit *)
      Field.t * Boolean.var
```

So `Other_field.t Shifted_value.Type2.t` = `Shifted_value of (Field.t * Boolean.var)` = **2 circuit
variables**, exactly like PureScript's `Type2 { sDiv2 :: f, sOdd :: b }`.

The Step circuit's `input` function (`impls.ml:153`) uses:
```ocaml
Shifted_value.Type2.typ Other_field.typ_unchecked
```
where `typ_unchecked = Typ.tuple2 Field.typ Boolean.typ` — two variables per shifted value.

## PureScript representation (correct)

Source: `packages/snarky-kimchi/src/Snarky/Types/Shifted.purs`

```purescript
newtype Type1 f = Type1 f                              -- 1 circuit var
newtype Type2 f b = Type2 { sDiv2 :: f, sOdd :: b }    -- 2 circuit vars
newtype SplitField f b = SplitField { sDiv2 :: f, sOdd :: b }  -- raw split, no shift
```

`Type2` matches the OCaml circuit representation. `SplitField` is structurally identical but
semantically different (see below).

## Which shifted value type is used where

### Step circuit (Fp) — uses Type2

The Step circuit verifies Wrap proofs. The Wrap proof's deferred values contain scalars from
the Tock field (Fq), which is larger than Fp. Since Fq > Fp, these values need the
`(s_div_2, s_odd)` decomposition — hence Type2.

- `Other_field.t = (Field.t * Boolean.var)` (pair, because Fq doesn't fit in Fp)
- Public input uses `Shifted_value.Type2.typ Other_field.typ_unchecked` (2 vars each)

### Wrap circuit (Fq) — uses Type1

The Wrap circuit verifies Step proofs. The Step proof's deferred values contain scalars from
the Tick field (Fp), which fits inside Fq. No decomposition needed — hence Type1.

- `Other_field.t = Field.t` (single, because Fp fits in Fq)
- Public input uses `Shifted_value.Type1.wrap_typ fp` (1 var each)

The comment at `impls.ml:237-240` confirms:
```
(* Type1 shifted values are used because the Wrap circuit's scalar field
   (Tick/Vesta) fits within its native field (Tock/Pallas), so no
   high-bit separation is needed (unlike Type2 which splits into
   (high_bits, low_bit) for larger scalar fields). *)
```

## Why both fields are ~255 bits but one doesn't fit

Both Fp and Fq are 255-bit primes, but Fq > Fp by ~86 billion. A 255-bit value from Fq
may exceed Fp. The decomposition `(s >> 1, s & 1)` solves this:
- `s >> 1` has at most 254 bits, which always fits in Fp
- `s & 1` is a single bit

## Shift + split: two operations, married in both OCaml and PureScript

The Type2 representation combines **two** operations:

1. **Shift**: subtract `2^n` from the scalar (where `n = field_size_in_bits`)
2. **Split**: decompose the result into `(s_div_2, s_odd)`

### OCaml: separated across two types

In OCaml these happen in two stages:
1. `Shifted_value.Type2.of_field s` → `Shifted_value (s - 2^n)` — shift (prover side)
2. `Other_field.typ_unchecked` converts the shifted constant to circuit vars → `((s - 2^n) >> 1, (s - 2^n) & 1)` — split

### PureScript: combined in one type

PureScript's `toShifted` does both in one step:
```purescript
sBigInt = toBigInt (s - shift)   -- shift first
sOdd = BigInt.odd sBigInt        -- then split
sDiv2 = ...
```

Both approaches store the same values: `((s - 2^n) >> 1, (s - 2^n) & 1)`.

### Why the shift is necessary

The pre-shift by `-2^n` cancels the implicit `+2^n` in `scale_fast_unpack`'s accumulator
initialization (which starts at `2G`). Without the pre-shift, `scaleFast2` would compute
`[s + 2^n] * G` instead of `[s] * G`.

### SplitField: raw split without the shift

PureScript also provides `SplitField` for cases where a raw parity decomposition is needed
without the `2^n` shift:

```purescript
-- Type2:      fromShifted (Type2 {sDiv2, sOdd})      = 2*sDiv2 + sOdd + 2^n
-- SplitField: joinField   (SplitField {sDiv2, sOdd}) = 2*sDiv2 + sOdd
```

Used by `scaleFast2'` which takes a raw circuit-field scalar, witnesses the `(sDiv2, sOdd)`
decomposition, constrains `2 * sDiv2 + sOdd = s`, then delegates to `scaleFast2`.

## Impact on Circuit JSON Comparison

**No mismatch exists.** Both OCaml and PureScript use 2 circuit variables per Type2 shifted
value in the Step circuit, and 1 circuit variable per Type1 shifted value in the Wrap circuit.

## scale_fast2: where the decomposition is used

In both OCaml and PureScript, `scale_fast2` receives the already-decomposed `(s_div_2, s_odd)`
pair and computes:

```
h = [2 * s_div_2 + 1 + 2^(ceil(bits/5)*5)] * G    (via scale_fast_unpack)
result = if s_odd then h else h - G
```

This yields `[s' + 2^n] * G` where `s' = 2 * s_div_2 + s_odd` and `n` depends on chunk count.
When the input is a Type2 shifted value (where `s' = s - 2^n`), the result is `[s] * G`.

OCaml also provides `scale_fast2'` (`plonk_curve_ops.ml:254-278`) which takes a single
circuit-field scalar and witnesses the `(s_div_2, s_odd)` decomposition internally, constraining
`2 * s_div_2 + s_odd = s`.

## References

- OCaml shifted_value: `mina/src/lib/crypto/plonkish_prelude/shifted_value.ml`
- OCaml Other_field (Step): `mina/src/lib/crypto/pickles/impls.ml` (lines 50-107)
- OCaml Other_field (Wrap): `mina/src/lib/crypto/pickles/impls.ml` (lines 187-227)
- OCaml scale_fast2: `mina/src/lib/crypto/pickles/plonk_curve_ops.ml` (lines 236-278)
- PureScript shifted types: `packages/snarky-kimchi/src/Snarky/Types/Shifted.purs`
- PureScript scaleFast2: `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/VarBaseMul.purs`
