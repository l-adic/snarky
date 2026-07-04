import Kimchi.CoreFn

/-!
# CheckCoreFn — evaluate compiled PureScript inside Lean and cross-validate

Runs the CoreFn interpreter (`Kimchi/CoreFn.lean`) on the *actual compiled artifact* of
`Snarky.Types.Shifted.forbiddenShiftedValues` — the shift-protocol wraparound guard: the n-bit
values whose Type1-shifted form collides mod the scalar order (the list the deployed
`shiftedEqualType1`/forbidden-value checks are built from).

The expected value is computed from an *independent* Lean statement of the spec: all
`0 ≤ x < 2ⁿ` with `x ≡ −2ⁿ (mod r)` or `x ≡ −2ⁿ−1 (mod r)`, sorted, deduplicated. Agreement
means the deployed computation — dictionaries, `unfoldr`, `sort`, `nub`, BigInt arithmetic and
all — reproduces the formal spec, with only the `purs` frontend and the interpreter trusted.

Run from `formal/` (needs the PS build's `output/` at the repo root):

    lake env lean --run CheckCoreFn.lean
-/

open Kimchi.CoreFn

/-- The spec, stated independently: n-bit representatives of `−2ⁿ` and `−2ⁿ−1` mod `r`. -/
def expectedForbidden (r : Int) (n : Nat) : List Int :=
  let twoN : Int := 2 ^ n
  let reps (x : Int) : List Int :=
    let base := x.emod r
    (List.range (((twoN - base) / r).toNat + 1)).map (fun k => base + r * Int.ofNat k)
      |>.filter (· < twoN)
  ((reps (-twoN)) ++ (reps (-twoN - 1))).eraseDups.mergeSort (· ≤ ·)

def main : IO Unit := do
  let ctx ← Ctx.new "../output"
  -- Vesta.ScalarField modulus (= the Pallas base field cardinality)
  let r : Int :=
    0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
  let n : Nat := 255
  let arg := Value.vObj [("modulus", .vBig r), ("sizeInBits", .vInt (Int.ofNat n))]
  let result ← run ctx "Snarky.Types.Shifted" "forbiddenShiftedValues" [arg]
  let got ← match result with
    | .vArr es => es.toList.mapM fun v => do
        match v with
        | .vBig b => pure b
        | v => throw (IO.userError s!"non-bigint in result: {v.describe}")
    | v => throw (IO.userError s!"expected array result, got {v.describe}")
  let expected := expectedForbidden r n
  IO.println s!"corefn-evaluated forbiddenShiftedValues: {got.length} values"
  IO.println s!"independent Lean spec:                   {expected.length} values"
  if got == expected then
    IO.println "MATCH: compiled PureScript ≡ Lean spec (via CoreFn evaluation) = true"
  else do
    IO.println s!"MISMATCH!\n  got:      {got.take 4}...\n  expected: {expected.take 4}..."
    throw (IO.userError "cross-validation failed")
