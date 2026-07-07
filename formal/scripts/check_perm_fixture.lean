import CompElliptic.Fields.Pasta
import Kimchi.Quotient.Wiring
import Kimchi.Fixture.Parse
import Lean.Data.Json

/-!
# Permutation-argument check against a kimchi fixture

Replays the permutation argument's row-level semantics on production data
(`fixtures/perm_vesta.json`, from `tools/fixture-dump`'s `perm_dump`: a wired circuit
whose accumulator comes from kimchi's `perm_aggreg`, with the full production
prove+verify asserted at dump time). Checked here by evaluating the
formalization's own definitions: the row forms `shiftSideRow`/`sigmaSideRow`
(`Kimchi/Quotient/Wiring.lean`, proved equal to the polynomial-level definitions by
`shiftSide_eval_row`/`sigmaSide_eval_row`) and the decidable certificates
`primitiveRootCertificate`/`cosetShiftsCertificate` (proved to imply the specification
`Prop`s by `isPrimitiveRoot_of_certificate`/`cosetShifts_of_certificate`):

* the primitive-root certificate for `ω` (with the power-of-two side condition checked,
  so `isPrimitiveRoot_of_certificate` yields the `hω` hypothesis at these parameters);
* the `CosetShifts` certificate for the dumped shift constants (plus kimchi's
  `shift₀ = 1` convention) — `cosetShifts_of_certificate` yields `Wiring.lean`'s
  specification hypothesis at these parameters;
* the two boundary pins `z(1) = 1`, `z(ω^(n-zk)) = 1`;
* the division-free accumulator recurrence at every unmasked row;
* the telescoped grand-product equality over the unmasked region;
* a negative check: corrupting one wired cell must break the recurrence.

Run (after `lake build Kimchi`): `scripts/check_perm_fixture.sh`.
-/

open Lean Kimchi.Fixture Kimchi.Quotient.Permutation CompElliptic.Fields.Pasta

structure PermFixture where
  n : ℕ
  zkRows : ℕ
  omega : Fp
  beta : Fp
  gamma : Fp
  shifts : Array Fp
  witness : Array (Array Fp)
  sigma : Array (Array Fp)
  z : Array Fp

def parseFixture (j : Json) : Except String PermFixture := do
  let fld (k : String) : Except String Json := j.getObjVal? k
  let pF : Json → Except String Fp := parseZMod
  return { n := ← parseNat (← fld "n")
           zkRows := ← parseNat (← fld "zk_rows")
           omega := ← pF (← fld "omega")
           beta := ← pF (← fld "beta")
           gamma := ← pF (← fld "gamma")
           shifts := ← parseArrOf pF (← fld "shifts")
           witness := ← parseArrOf (parseArrOf pF) (← fld "witness")
           sigma := ← parseArrOf (parseArrOf pF) (← fld "sigma")
           z := ← parseArrOf pF (← fld "z") }

/-- Row `j` of a table as a `Fin 7`-function. -/
def rowFn (tab : Array (Array Fp)) (j : ℕ) : Fin 7 → Fp :=
  fun i => (tab[(i : ℕ)]!)[j]!

/-- The library's shift-side row form at fixture row `j`. -/
def shiftRow (fx : PermFixture) (wit : Array (Array Fp)) (j : ℕ) : Fp :=
  shiftSideRow (rowFn wit j) (fun i => fx.shifts[(i : ℕ)]!) fx.beta fx.gamma (fx.omega ^ j)

/-- The library's σ-side row form at fixture row `j`. -/
def sigmaRow (fx : PermFixture) (wit : Array (Array Fp)) (j : ℕ) : Fp :=
  sigmaSideRow (rowFn wit j) (rowFn fx.sigma j) fx.beta fx.gamma

/-- The recurrence `z(ωʲ⁺¹)·sigmaRow(j) = z(ωʲ)·shiftRow(j)` at every unmasked row. -/
def recurrenceHolds (fx : PermFixture) (wit : Array (Array Fp)) : Bool :=
  (List.range (fx.n - fx.zkRows)).all fun j =>
    fx.z[j + 1]! * sigmaRow fx wit j == fx.z[j]! * shiftRow fx wit j

def check (fx : PermFixture) : List (String × Bool) :=
  let m := fx.n - fx.zkRows
  [ ("n is a power of two", decide (∃ k < fx.n + 1, fx.n = 2 ^ k)),
    ("omega primitive (isPrimitiveRoot_of_certificate)",
      primitiveRootCertificate fx.omega fx.n),
    ("CosetShifts (cosetShifts_of_certificate)",
      fx.shifts[0]! == 1
        && cosetShiftsCertificate (fun i => fx.shifts[(i : ℕ)]!) fx.n),
    ("boundary z(1) = 1", fx.z[0]! == 1),
    ("boundary z(ω^(n-zk)) = 1", fx.z[m]! == 1),
    ("accumulator recurrence on unmasked rows", recurrenceHolds fx fx.witness),
    ("grand-product equality",
      (List.range m).foldl (fun acc j => acc * shiftRow fx fx.witness j) 1
        == (List.range m).foldl (fun acc j => acc * sigmaRow fx fx.witness j) 1),
    ("corrupted wired cell breaks the recurrence",
      !recurrenceHolds fx (fx.witness.modify 1 (·.modify 0 (· + 1)))) ]

def main : IO Unit := do
  let raw ← IO.FS.readFile "fixtures/perm_vesta.json"
  let fx ← match Json.parse raw >>= parseFixture with
    | .ok fx => pure fx
    | .error e => throw (IO.userError s!"perm fixture parse error: {e}")
  let results := check fx
  for (name, ok) in results do
    IO.println s!"  {if ok then "✓" else "✗"} {name}"
  unless results.all (·.2) do
    throw (IO.userError "permutation fixture check FAILED")
  IO.println s!"✓ the permutation argument matches kimchi on the fixture \
    (n={fx.n}, zk_rows={fx.zkRows})"

#eval main
