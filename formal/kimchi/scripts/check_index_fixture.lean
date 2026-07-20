import CompElliptic.Fields.Pasta
import Kimchi.Index.Satisfies
import FixtureKit.Parse
import Lean.Data.Json

/-!
# The index model against a mixed-gate kimchi fixture

Replays the index model on production data (`fixtures/index_vesta.json`, from
`tools/fixture-dump`'s `index_dump`: a circuit with a public row, wired generic rows, a
full Poseidon gadget, a CompleteAdd row, and an EndoMulScalar block — kimchi's own row
checker and the full production prove+verify asserted at dump time):

* **construction by decision**: `Index.build?` must accept the dumped table — deciding
  the primitive-root and coset certificates, the row bounds, and the wiring laws on the
  production data;
* **the derived columns**: the model's `selectorRow`/`coeffRow`/`sigmaAddrRow` must
  reproduce the production selector, coefficient, and sigma column evaluations row by
  row — pinning the table→columns derivation;
* **satisfiability**: `decide (Satisfies idx pub wTab)` on the production witness — the
  checker is the `Decidable` instance of the predicate itself, nothing else;
* **negatives**: a corrupted gate cell, a corrupted wired cell, and a corrupted public
  input must each be rejected.
-/

open Lean FixtureKit Kimchi Kimchi.Index CompElliptic.Fields.Pasta

def parseGateType : String → Except String GateType
  | "zero" => .ok .zero
  | "generic" => .ok .generic
  | "poseidon" => .ok .poseidon
  | "completeAdd" => .ok .completeAdd
  | "varBaseMul" => .ok .varBaseMul
  | "endoMul" => .ok .endoMul
  | "endoScalar" => .ok .endoScalar
  | t => .error s!"unknown gate type: {t}"

structure RawFixture where
  n : ℕ
  zkRows : ℕ
  publicCount : ℕ
  pub : Array Fp
  omega : Fp
  endoBase : Fp
  shifts : Array Fp
  typs : Array GateType
  coeffs : Array (Array Fp)
  wires : Array (Array (ℕ × ℕ))
  witness : Array (Array Fp)
  selectors : Array (GateType × Array Fp)
  coefficients : Array (Array Fp)
  sigma : Array (Array Fp)

def parseRaw (j : Json) : Except String RawFixture := do
  let fld (k : String) : Except String Json := j.getObjVal? k
  let pF : Json → Except String Fp := parseZMod
  let gatesJ ← (← fld "gates").getArr?
  let typs ← gatesJ.mapM fun g => do parseGateType (← (← g.getObjVal? "typ").getStr?)
  let coeffs ← gatesJ.mapM fun g => do parseArrOf pF (← g.getObjVal? "coeffs")
  let wires ← gatesJ.mapM fun g => do
    (← (← g.getObjVal? "wires").getArr?).mapM fun w => do
      let a ← w.getArr?
      return (← a[0]!.getNat?, ← a[1]!.getNat?)
  let selJ ← fld "selectors"
  let sel (name : String) (t : GateType) : Except String (GateType × Array Fp) := do
    return (t, ← parseArrOf pF (← selJ.getObjVal? name))
  return { n := ← parseNat (← fld "n")
           zkRows := ← parseNat (← fld "zk_rows")
           publicCount := ← parseNat (← fld "public_count")
           pub := ← parseArrOf pF (← fld "public")
           omega := ← pF (← fld "omega")
           endoBase := ← pF (← fld "endo_base")
           shifts := ← parseArrOf pF (← fld "shifts")
           typs := typs
           coeffs := coeffs
           wires := wires
           witness := ← parseArrOf (parseArrOf pF) (← fld "witness")
           selectors := #[← sel "generic" .generic, ← sel "poseidon" .poseidon,
             ← sel "completeAdd" .completeAdd, ← sel "varBaseMul" .varBaseMul,
             ← sel "endoMul" .endoMul, ← sel "endoScalar" .endoScalar]
           coefficients := ← parseArrOf (parseArrOf pF) (← fld "coefficients")
           sigma := ← parseArrOf (parseArrOf pF) (← fld "sigma") }

def buildGates (fx : RawFixture) {n : ℕ} (_hn : fx.n = n) :
    Except String (Fin n → GateRow Fp n) := do
  unless fx.typs.size = n && fx.wires.size = n && fx.coeffs.size = n do
    throw "gate table size mismatch"
  let rows ← (Array.range n).mapM fun i => do
    let ws ← (fx.wires[i]!).mapM fun (col, row) => do
      if h : col < 7 ∧ row < n then
        return ((⟨col, h.1⟩ : Fin 7), (⟨row, h.2⟩ : Fin n))
      else throw s!"wire out of range at row {i}"
    let t : GateType := fx.typs[i]!
    let cf : Array Fp := fx.coeffs[i]!
    if h7 : ws.size = 7 then
      return { typ := t
               coeffs := fun c => cf[(c : ℕ)]!
               wires := fun c => ws[(c : ℕ)]'(by omega) : GateRow Fp n }
    else throw "wire count"
  if hsz : rows.size = n then
    return fun i => rows[(i : ℕ)]'(by omega)
  else throw "row count"

def checks (fx : RawFixture) {n : ℕ} [NeZero n]
    (idx : Index Fp n) : List (String × Bool) :=
  let wTab : Fin n → Fin 15 → Fp := fun i c => (fx.witness[(c : ℕ)]!)[(i : ℕ)]!
  let pub : Fin idx.publicCount → Fp := fun i => fx.pub[(i : ℕ)]!
  let sat (w : Fin n → Fin 15 → Fp) (p : Fin idx.publicCount → Fp) : Bool :=
    decide (Satisfies idx p w)
  -- Corruption targets derived from the index, not from the dumper's layout: a
  -- constrained non-generic row (all modeled gates read column 0), and a nontrivially
  -- wired cell. Their absence is a fixture-quality failure, reported loudly.
  let gateRow? : Option (Fin n) := (List.finRange n).find? fun i =>
    (idx.gates i).typ != GateType.zero && (idx.gates i).typ != GateType.generic
  let wired? : Option (Fin 7 × Fin n) := (List.finRange n).findSome? fun r =>
    ((List.finRange 7).find? fun col => idx.wiringMap (col, r) != (col, r)).map
      fun col => (col, r)
  let bump (r : Fin n) (c : ℕ) : Fin n → Fin 15 → Fp :=
    fun i c' => if i = r ∧ (c' : ℕ) = c then wTab i c' + 1 else wTab i c'
  [ ("selector columns match production",
      fx.selectors.all fun (t, col) =>
        (List.finRange n).all fun i => idx.selectorRow t i == col[(i : ℕ)]!),
    ("coefficient columns match production",
      (List.finRange 15).all fun c =>
        (List.finRange n).all fun i =>
          idx.coeffRow c i == (fx.coefficients[(c : ℕ)]!)[(i : ℕ)]!),
    ("sigma columns match production",
      (List.finRange 7).all fun c =>
        (List.finRange n).all fun i =>
          idx.sigmaAddrRow c i == (fx.sigma[(c : ℕ)]!)[(i : ℕ)]!),
    ("Satisfies (decided from the predicate)", sat wTab pub),
    ("corrupted gate cell rejected (target derived from the table)",
      match gateRow? with
      | some r => !sat (bump r 0) pub
      | none => false),
    ("corrupted wired cell rejected (target derived from the wiring)",
      match wired? with
      | some (col, r) => !sat (bump r (col : ℕ)) pub
      | none => false),
    ("corrupted public input rejected", !sat wTab (fun i => pub i + 1)) ]

def run {n : ℕ} [NeZero n] (fx : RawFixture) (hn : fx.n = n) : IO Unit := do
  let gates ← IO.ofExcept (buildGates fx hn)
  let some idx := Index.build? gates fx.publicCount fx.zkRows fx.omega fx.endoBase
      (fun i => fx.shifts[(i : ℕ)]!)
    | throw (IO.userError "Index.build? rejected the production data")
  IO.println "  ✓ Index.build? accepts (all laws decided on production data)"
  let results := checks fx (n := n) idx
  for (name, ok) in results do
    IO.println s!"  {if ok then "✓" else "✗"} {name}"
  unless results.all (·.2) do
    throw (IO.userError "index fixture check FAILED")
  IO.println s!"✓ the index model matches kimchi on the mixed-gate fixture \
    (n={n}, gates incl. generic/poseidon/completeAdd/endoScalar)"

def main : IO Unit := do
  let dir := (← IO.getEnv "KIMCHI_FIXTURES_DIR").getD "fixtures"
  let raw ← IO.FS.readFile s!"{dir}/index_vesta.json"
  let fx ← match Json.parse raw >>= parseRaw with
    | .ok fx => pure fx
    | .error e => throw (IO.userError s!"index fixture parse error: {e}")
  if hpos : 0 < fx.n then
    haveI : NeZero fx.n := ⟨Nat.pos_iff_ne_zero.mp hpos⟩
    run fx rfl
  else
    throw (IO.userError "empty domain")

#eval main
