import CompElliptic.Fields.Pasta
import Kimchi.Index.Satisfies
import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Wire
import FixtureKit.Parse
import Pasta.Endo
import Lean.Data.Json

/-!
# Ingesting PureScript circuit dumps

Decoders for the comparison JSON the PureScript circuit-diff harness writes. Its PureScript
side carries the compiled gate list and, when the harness ran witness generation, a solved
witness. Field elements are 32-byte little-endian hex; gate coefficients are signed decimals.

The dump carries no domain data, so `build` synthesizes it and lets `Index.build?` decide
every law: rows pad to the smallest two-power holding the gates plus `zkRows`, and `ω` and
the coset shifts are powers of the field's multiplicative generator. A wrong synthesis makes
`Index.build?` return `none`, and ingestion fails.
-/

namespace Kimchi.Fixture.PS

open FixtureKit

open Lean Kimchi Kimchi.Index CompElliptic.Fields.Pasta

/-! ## Element decoders -/

/-- A hex digit's value. -/
private def hexVal? (c : Char) : Option ℕ :=
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
private def parseSignedDecimal {m : ℕ} (j : Json) : Except String (ZMod m) := do
  let s ← j.getStr?
  let (neg, digits) := if s.startsWith "-" then (true, s.drop 1) else (false, s)
  match digits.toNat? with
  | some v => return if neg then -(v : ZMod m) else (v : ZMod m)
  | none => throw s!"not a signed decimal: {s.take 40}"

/-- The harness's gate-kind tags. -/
private def parseGateKind : String → Except String GateType
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
structure Raw (F : Type) where
  /-- The circuit's declared public-input size. -/
  publicInputSize : ℕ
  /-- The gate type of each dumped row. -/
  typs : Array GateType
  /-- The per-row coefficient cells. -/
  coeffs : Array (Array F)
  /-- The per-row wire targets, `(column, row)` per column position. -/
  wires : Array (Array (ℕ × ℕ))
  /-- The variable id in each register cell, `none` for an empty cell. Cell values and
  wire cycles do not depend on allocation order; only these ids pin it. -/
  vars : Array (Array (Option ℕ))
  /-- The solved witness, one array per register column. -/
  witness : Array (Array F)
  /-- The public-input values. -/
  pub : Array F

/-- A `{row, col}` wire object as a `(column, row)` target. -/
private def parseWire (j : Json) : Except String (ℕ × ℕ) := do
  return (← (← j.getObjVal? "col").getNat?, ← (← j.getObjVal? "row").getNat?)

/-- A cell's variable id: a natural, or `-1` for an empty cell. -/
private def parseVarId (j : Json) : Except String (Option ℕ) := do
  let i ← j.getInt?
  return if i < 0 then none else some i.toNat

/-- The gate table of a comparison JSON's PureScript side, with the witness fields empty. -/
private def parseGates {m : ℕ} (ps : Json) : Except String (Raw (ZMod m)) := do
  let gatesJ ← (← ps.getObjVal? "gates").getArr?
  let typs ← gatesJ.mapM fun g => do parseGateKind (← (← g.getObjVal? "kind").getStr?)
  let coeffs ← gatesJ.mapM fun g => do
    parseArrOf parseSignedDecimal (← g.getObjVal? "coeffs")
  let wires ← gatesJ.mapM fun g => do parseArrOf parseWire (← g.getObjVal? "wires")
  let vars ← gatesJ.mapM fun g => do parseArrOf parseVarId (← g.getObjVal? "variables")
  return {
    publicInputSize := ← (← ps.getObjVal? "publicInputSize").getNat?
    typs := typs
    coeffs := coeffs
    wires := wires
    vars := vars
    witness := #[]
    pub := #[] }

/-- The PureScript side of a comparison JSON; `none` when the JSON is not a comparison
or carries no witness. -/
def parseComparison? {m : ℕ} (j : Json) : Except String (Option (Raw (ZMod m))) := do
  let .ok ps := j.getObjVal? "purescript" | return none
  let .ok w := ps.getObjVal? "witness" | return none
  if w.isNull then return none
  let raw ← parseGates ps
  return some
    { raw with
      witness := ← parseArrOf (parseArrOf parseHexLE) (← w.getObjVal? "witness")
      pub := ← parseArrOf parseHexLE (← w.getObjVal? "publicInputs") }

/-- Like `parseComparison?`, but a comparison without a witness parses too, with empty
`witness` and `pub`: every dump carries the constraint-system fields. -/
def parseComparisonCs? {m : ℕ} (j : Json) : Except String (Option (Raw (ZMod m))) := do
  let .ok ps := j.getObjVal? "purescript" | return none
  let raw ← parseGates ps
  match ps.getObjVal? "witness" with
  | .error _ => return some raw
  | .ok w =>
    if w.isNull then return some raw
    return some
      { raw with
        witness := ← parseArrOf (parseArrOf parseHexLE) (← w.getObjVal? "witness")
        pub := ← parseArrOf parseHexLE (← w.getObjVal? "publicInputs") }

/-! ## Domain synthesis -/

/-- kimchi's zero-knowledge row count (one chunk). -/
def zkRows : ℕ := 3

/-- The field-specific data domain synthesis and the index need: the multiplicative
generator (`ω` and the coset shifts are its powers), the curve's endomorphism coefficient
and the Poseidon MDS matrix. -/
structure Side (p : ℕ) where
  /-- The field's multiplicative generator. -/
  generator : ℕ
  /-- The endomorphism coefficient of the curve whose base field this is. -/
  endo : ZMod p
  /-- The Poseidon MDS matrix over this field. -/
  mds : Gate.Poseidon.Mds (ZMod p)

/-- The step side: `Fp`, Pallas's base field. -/
def fpSide : Side PALLAS_BASE_CARD :=
  ⟨5, Pasta.pallasEndo, Kimchi.Verifier.mdsOfParams Bulletproof.IpaVesta.curve.frSponge.params⟩

/-- The wrap side: `Fq`, Vesta's base field. -/
def fqSide : Side PALLAS_SCALAR_CARD :=
  ⟨5, Pasta.vestaEndo, Kimchi.Verifier.mdsOfParams Bulletproof.IpaPallas.curve.frSponge.params⟩

/-- Fast modular exponentiation (`Monoid.npow` on `ZMod` is linear in the exponent —
unusable at 255-bit exponents). -/
private def powMod (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | e + 1, m =>
    let h := powMod b ((e + 1) / 2) m
    if (e + 1) % 2 = 0 then h * h % m else h * h % m * (b % m) % m
decreasing_by omega

/-- The generator of the domain of size `n`: `g^((p − 1)/n)` for `g` the side's `generator`.
At `n = 2^k` it is the field's `2^32`-th root of unity `g^((p − 1)/2^32)` raised to
`2^(32 − k)`, since both Pasta fields have two-adicity `32`. -/
def Side.omega {p : ℕ} (side : Side p) (n : ℕ) : ZMod p :=
  (powMod side.generator ((p - 1) / n) p : ℕ)

/-! ## Ingestion into the index model -/

/-- A solved witness at domain size `n`: the public input and the register table, the
assignment arguments of `Satisfies`. -/
structure Witness (F : Type) (n publicCount : ℕ) where
  /-- The public-input values. -/
  pub : Fin publicCount → F
  /-- The register table, one row per domain point. -/
  tab : Fin n → Fin wCols → F

/-- A dumped circuit ingested into the index model: the index and the dumped witness at
the padded domain size `n`, which is computed from the dump and so carried as a field.
Consumers state their own propositions, e.g. `Satisfies inst.idx inst.wit.pub inst.wit.tab`. -/
structure Instance (F : Type) [Field F] where
  /-- The padded two-power domain size. -/
  n : ℕ
  /-- The domain size is positive. -/
  nz : NeZero n
  /-- The index constructed from the dump by decision (`Index.build?`). -/
  idx : Index F n
  /-- The dumped witness, shaped to the index's public count. -/
  wit : Witness F n idx.publicCount

/-- The gate table at padded domain size `n`: the dump's rows, then constraint-free
`zero` gates, identity-wired and witnessed by zeros. -/
private def gateTable {F : Type} [Field F] (raw : Raw F) (n : ℕ) :
    Except String (Fin n → GateRow F n) := do
  let rows := raw.typs.size
  let gateRows ← (Array.range n).mapM fun i => do
    if hreal : i < rows then do
      let ws ← raw.wires[i]!.mapM fun (col, row) => do
        if h : col < 7 ∧ row < n then
          return ((⟨col, h.1⟩ : Fin permCols), (⟨row, h.2⟩ : Fin n))
        else throw s!"wire out of range at row {i}"
      if h7 : ws.size = 7 then
        return { typ := raw.typs[i]!
                 coeffs := fun c => (raw.coeffs[i]!).getD (c : ℕ) 0
                 wires := fun c => ws[(c : ℕ)]'(by omega) : GateRow F n }
      else throw s!"expected 7 wires at row {i}, got {ws.size}"
    else if hi : i < n then
      return { typ := .zero, coeffs := fun _ => 0
               wires := fun c => (c, ⟨i, hi⟩) : GateRow F n }
    else throw "row index out of the padded domain"
  if hsz : gateRows.size = n then
    return fun i => gateRows[(i : ℕ)]'(by omega)
  else throw "padded gate table size mismatch"

/-- Ingest a parsed dump: check its array sizes, pad and synthesize the domain (see the
module docstring), and construct the index with `Index.build?`. A wrong synthesis fails
here, never downstream. -/
def build {p : ℕ} [Fact p.Prime] (side : Side p) (raw : Raw (ZMod p)) :
    Except String (Instance (ZMod p)) := do
  let rows := raw.typs.size
  unless raw.coeffs.size = rows ∧ raw.wires.size = rows do throw "gate array sizes differ"
  unless raw.witness.size = 15 do throw s!"expected 15 witness columns, got {raw.witness.size}"
  unless raw.witness.all (·.size = rows) do throw "witness column length ≠ gate rows"
  unless raw.pub.size = raw.publicInputSize do throw "publicInputs size ≠ publicInputSize"
  unless raw.publicInputSize ≤ rows do throw "more public inputs than rows"
  let n := 2 ^ Nat.clog 2 (rows + zkRows)
  let omega := side.omega n
  -- Generator powers, not the deployed sampled shifts: `Index.build?` decides the coset law
  -- for any shift set.
  let shifts : Fin permCols → ZMod p := fun i => (powMod side.generator (i : ℕ) p : ℕ)
  let gates ← gateTable raw n
  match Index.build? gates raw.publicInputSize zkRows omega side.endo side.mds shifts with
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
