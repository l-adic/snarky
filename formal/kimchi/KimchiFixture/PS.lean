import CompElliptic.Fields.Pasta
import Kimchi.Index.Satisfies
import Kimchi.Verifier.Kimchi
import FixtureKit.Parse
import Pasta.Endo
import Lean.Data.Json

/-!
# Ingesting PureScript harness witness exports

Decoders for the JSON the PureScript circuit-diff harness writes to
`packages/pickles-circuit-diffs/circuits/results/` — the comparison's `purescript` side
carries the compiled gate list and, when the harness ran witness generation, a solved
witness (`witness`/`publicInputs`, 32-byte little-endian hex; gate coefficients are the
comparison format's signed decimals). This is the PureScript sibling of the proof-systems
decoders alongside it — the target model is shared, only
the element encodings differ, so the decoders here compose over the same combinators.

The dump carries no domain data, so ingestion synthesizes it and lets `Index.build?`
decide every law: rows pad to the smallest two-power holding the gates plus the
zero-knowledge rows (padding rows are constraint-free `zero` gates, identity-wired,
witnessed by zeros), `ω = g^((p−1)/n)` from the field's multiplicative generator, and
the coset shifts are small generator powers. A wrong synthesis cannot be trusted into
an index — `build?` returns `none` and the check fails loudly.

Executable costs are quadratic in the padded domain (the wiring-bijectivity decision and
the copy-constraint sweep are `7n × 7n`-ish), which is fine for the gate-gadget dumps
this ingests; whole-circuit dumps would need a smarter checker.
-/

namespace Kimchi.Fixture.PS

open FixtureKit

open Lean Kimchi Kimchi.Index CompElliptic.Fields.Pasta

/-! ## Element decoders (the PureScript encodings) -/

/-- A hex digit's value. -/
def hexVal? (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- A little-endian byte-hex string (byte 0 least significant) as a natural. -/
def hexLEtoNat (s : String) : Except String ℕ := do
  let cs := s.toList.toArray
  unless cs.size % 2 = 0 do throw s!"odd-length hex: {s.take 40}"
  let mut acc : ℕ := 0
  let mut place : ℕ := 1
  for j in [0 : cs.size / 2] do
    let some hi := hexVal? cs[2 * j]! | throw s!"not hex: {s.take 40}"
    let some lo := hexVal? cs[2 * j + 1]! | throw s!"not hex: {s.take 40}"
    acc := acc + (hi * 16 + lo) * place
    place := place * 256
  return acc

/-- A little-endian hex string as an element of `ZMod m` (the cast reduces). -/
def parseHexLE {m : ℕ} (j : Json) : Except String (ZMod m) := do
  return ((← hexLEtoNat (← j.getStr?)) : ZMod m)

/-- A signed decimal string (the comparison format shows values above `p/2` negated)
as an element of `ZMod m`. -/
def parseSignedDecimal {m : ℕ} (j : Json) : Except String (ZMod m) := do
  let s ← j.getStr?
  let (neg, digits) := if s.startsWith "-" then (true, s.drop 1) else (false, s)
  match digits.toNat? with
  | some v => return if neg then -(v : ZMod m) else (v : ZMod m)
  | none => throw s!"not a signed decimal: {s.take 40}"

/-- The harness's gate-kind tags (`gateKindToString`). -/
def parseGateKind : String → Except String GateType
  | "Zero" => .ok .zero
  | "Generic" => .ok .generic
  | "Poseidon" => .ok .poseidon
  | "CompleteAdd" => .ok .completeAdd
  | "VarBaseMul" => .ok .varBaseMul
  | "EndoMul" => .ok .endoMul
  | "EndoMulScalar" => .ok .endoScalar
  | t => .error s!"unknown gate kind: {t}"

/-! ## The comparison JSON's PureScript side -/

/-- A witness-carrying PureScript circuit: the gate table columns of the dump and the
solved witness. Wires are `(column, row)` targets in kimchi's cyclic-successor
encoding, one per column position. -/
structure Raw where
  publicInputSize : ℕ
  typs : Array GateType
  coeffs : Array (Array Fp)
  wires : Array (Array (ℕ × ℕ))
  witness : Array (Array Fp)
  pub : Array Fp

/-- A `{row, col}` wire object as a `(column, row)` target. -/
def parseWire (j : Json) : Except String (ℕ × ℕ) := do
  return (← (← j.getObjVal? "col").getNat?, ← (← j.getObjVal? "row").getNat?)

/-- The PureScript side of a comparison JSON; `none` when the JSON is not a comparison
or carries no witness. -/
def parseComparison? (j : Json) : Except String (Option Raw) := do
  let .ok ps := j.getObjVal? "purescript" | return none
  let .ok w := ps.getObjVal? "witness" | return none
  if w.isNull then return none
  let gatesJ ← (← ps.getObjVal? "gates").getArr?
  let typs ← gatesJ.mapM fun g => do parseGateKind (← (← g.getObjVal? "kind").getStr?)
  let coeffs ← gatesJ.mapM fun g => do
    parseArrOf parseSignedDecimal (← g.getObjVal? "coeffs")
  let wires ← gatesJ.mapM fun g => do parseArrOf parseWire (← g.getObjVal? "wires")
  return some
    { publicInputSize := ← (← ps.getObjVal? "publicInputSize").getNat?
      typs := typs
      coeffs := coeffs
      wires := wires
      witness := ← parseArrOf (parseArrOf parseHexLE) (← w.getObjVal? "witness")
      pub := ← parseArrOf parseHexLE (← w.getObjVal? "publicInputs") }

/-! ## Domain synthesis -/

/-- kimchi's zero-knowledge row count (one chunk). -/
def zkRows : ℕ := 3

/-- The Pasta base fields' multiplicative generator (proof-systems `fp.rs` GENERATOR). -/
def fpGenerator : ℕ := 5

/-- Fast modular exponentiation (`Monoid.npow` on `ZMod` is linear in the exponent —
unusable at 255-bit exponents). -/
def powMod (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | e + 1, m =>
    let h := powMod b ((e + 1) / 2) m
    if (e + 1) % 2 = 0 then h * h % m else h * h % m * (b % m) % m
decreasing_by omega

/-! ## Ingestion into the index model -/

/-- A solved witness at domain size `n`: the public input and the 15-column register
table — the decoded `WitnessExport`, and exactly the assignment arguments of
`Satisfies`. -/
structure Witness (n publicCount : ℕ) where
  pub : Fin publicCount → Fp
  tab : Fin n → Fin 15 → Fp

/-- A dumped circuit ingested into the index model: the index (constructed by decision)
and the dumped witness, at the padded two-power domain bundled as `n` (the domain size
is computed from the dump, so the existential is carried as a field, in the manner of
the index's own laws). Consumers state their own propositions about it
(`Satisfies inst.idx inst.wit.pub inst.wit.tab`), the way the fixture scripts do. -/
structure Instance where
  n : ℕ
  nz : NeZero n
  idx : Index Fp n
  wit : Witness n idx.publicCount

/-- The gate table at padded domain size `n`: the dump's rows, then constraint-free
`zero` gates, identity-wired and witnessed by zeros. -/
private def gateTable (raw : Raw) (n : ℕ) :
    Except String (Fin n → GateRow Fp n) := do
  let rows := raw.typs.size
  let gateRows ← (Array.range n).mapM fun i => do
    if hreal : i < rows then do
      let ws ← raw.wires[i]!.mapM fun (col, row) => do
        if h : col < 7 ∧ row < n then
          return ((⟨col, h.1⟩ : Fin 7), (⟨row, h.2⟩ : Fin n))
        else throw s!"wire out of range at row {i}"
      if h7 : ws.size = 7 then
        return { typ := raw.typs[i]!
                 coeffs := fun c => (raw.coeffs[i]!).getD (c : ℕ) 0
                 wires := fun c => ws[(c : ℕ)]'(by omega) : GateRow Fp n }
      else throw s!"expected 7 wires at row {i}, got {ws.size}"
    else if hi : i < n then
      return { typ := .zero, coeffs := fun _ => 0
               wires := fun c => (c, ⟨i, hi⟩) : GateRow Fp n }
    else throw "row index out of the padded domain"
  if hsz : gateRows.size = n then
    return fun i => gateRows[(i : ℕ)]'(by omega)
  else throw "padded gate table size mismatch"

/-- Ingest a parsed export: validate its shape, pad to the smallest two-power domain
holding the gates plus the zero-knowledge rows, synthesize `ω = g^((p−1)/n)` and
generator-power coset shifts, and construct the index with `Index.build?` — every
synthesized law is decided on the data, so a wrong synthesis is a loud failure here,
never a trusted fact downstream. -/
def build (raw : Raw) : Except String Instance := do
  let rows := raw.typs.size
  unless raw.coeffs.size = rows ∧ raw.wires.size = rows do throw "gate array sizes differ"
  unless raw.witness.size = 15 do throw s!"expected 15 witness columns, got {raw.witness.size}"
  unless raw.witness.all (·.size = rows) do throw "witness column length ≠ gate rows"
  unless raw.pub.size = raw.publicInputSize do throw "publicInputs size ≠ publicInputSize"
  unless raw.publicInputSize ≤ rows do throw "more public inputs than rows"
  let n := 2 ^ Nat.clog 2 (rows + zkRows)
  let omega : Fp := (powMod fpGenerator ((PALLAS_BASE_CARD - 1) / n) PALLAS_BASE_CARD : ℕ)
  let shifts : Fin 7 → Fp := fun i => (powMod fpGenerator (i : ℕ) PALLAS_BASE_CARD : ℕ)
  let gates ← gateTable raw n
  match Index.build? gates raw.publicInputSize zkRows omega
      Pasta.pallas_endo (Kimchi.Verifier.mdsOfParams Kimchi.Verifier.KimchiVesta.frParams)
      shifts with
  | none => throw "Index.build? rejected the padded dump (a synthesized law failed)"
  | some idx =>
    return { n := n
             nz := ⟨(Nat.two_pow_pos _).ne'⟩
             idx := idx
             wit :=
               { pub := fun i => raw.pub.getD (i : ℕ) 0
                 tab := fun i c =>
                   if (i : ℕ) < rows then (raw.witness[(c : ℕ)]!).getD (i : ℕ) 0
                   else 0 } }

end Kimchi.Fixture.PS
