import Lean.Data.Json
import Kimchi.Circuit
import Kimchi.Field.Pasta

/-!
# Ingesting a dumped `{circuit, witness}` JSON into the Lean model

Reads the combined JSON the PureScript dumper emits and produces a concrete
`Circuit (ZMod pastaP)` / `Witness (ZMod pastaP)` / public-input vector, ready for the
executable `check`. Field elements are 32-byte little-endian hex (matching the on-disk
circuit fixtures); `parseField` decodes them and `Nat.cast` reduces mod `pastaP`.

Expected JSON shape (`publicInputSize`, `gates`, `witness` column-major 15×n, `publicInputs`):

```json
{ "publicInputSize": 6,
  "gates": [ { "typ": "Generic", "wires": [{"row":0,"col":0}, …], "coeffs": ["01…","00…", …] }, … ],
  "witness": [ ["…","…", …], … ],
  "publicInputs": ["…", …] }
```
-/

namespace Kimchi.Json

open Lean Kimchi.Circuit Kimchi.Field

/-! ## Little-endian hex → field element -/

/-- A single hex digit's value (`a`–`f` and `A`–`F` accepted; others → 0). -/
def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Decode a little-endian hex string (byte 0 = least significant) to a `Nat`. -/
def hexLEtoNat (s : String) : Nat := Id.run do
  let cs := s.toList.toArray
  let mut acc : Nat := 0
  let mut place : Nat := 1
  for j in [0 : cs.size / 2] do
    let byte := hexVal (cs.getD (2 * j) '0') * 16 + hexVal (cs.getD (2 * j + 1) '0')
    acc := acc + byte * place
    place := place * 256
  return acc

/-- Decode a little-endian hex field element into `Fp` (`ZMod pastaP`); the cast reduces. -/
def parseField (s : String) : Fp := (hexLEtoNat s : Fp)

/-! ## JSON record mirrors (derive `FromJson` structurally). -/

structure JWire where
  row : Nat
  col : Nat
deriving FromJson

structure JGate where
  typ : String
  wires : Array JWire
  coeffs : Array String
deriving FromJson

/-- The combined dump: gates, the column-major (15 × n) witness, and the public inputs. -/
structure JCircuit where
  publicInputSize : Nat
  gates : Array JGate
  witness : Array (Array String)
  publicInputs : Array String
deriving FromJson

/-! ## Conversion to the Lean model. -/

/-- Map the dump's `typ` string to a `GateKind`. -/
def kindOf : String → GateKind
  | "Generic"       => .generic
  | "Zero"          => .zero
  | "Poseidon"      => .poseidon
  | "CompleteAdd"   => .completeAdd
  | "VarBaseMul"    => .varBaseMul
  | "EndoMul"       => .endoMul
  | "EndoMulScalar" => .endoMulScalar
  | _               => .zero

def toGate (g : JGate) : Gate Fp :=
  { kind := kindOf g.typ
  , coeffs := g.coeffs.map parseField
  , wires := g.wires.map (fun wr => (wr.row, wr.col)) }

def toCircuit (jc : JCircuit) : Circuit Fp :=
  { publicInputSize := jc.publicInputSize, gates := jc.gates.map toGate }

/-- Transpose the column-major witness (`witness[col][row]`) into the row-major model. -/
def toWitness (jc : JCircuit) : Witness Fp :=
  let cols := jc.witness.map (fun col => col.map parseField)
  let nrows := (cols.getD 0 #[]).size
  { rows := (Array.range nrows).map (fun r => cols.map (fun col => col.getD r 0)) }

def toPub (jc : JCircuit) : Array Fp := jc.publicInputs.map parseField

/-- Parse, convert, and run the verified checker. -/
def loadAndCheck (path : System.FilePath) : IO Bool := do
  let s ← IO.FS.readFile path
  match Json.parse s >>= fromJson? (α := JCircuit) with
  | .error e => throw (IO.userError s!"failed to load {path}: {e}")
  | .ok jc => return check (toCircuit jc) (toWitness jc) (toPub jc)

end Kimchi.Json
