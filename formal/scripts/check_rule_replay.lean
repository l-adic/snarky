import PicklesFixture.ApplicationRun

/-!
Focused replay checks: every exported constraint variant, non-contiguous input cells,
allocations, expression-valued returns, scope rejection and missing witness advice.
-/

open Lean Snarky Snarky.Kimchi PicklesFixture CompElliptic.Fields.Pasta

private def obj (xs : List (String × Json)) := Json.mkObj xs
private def arr (xs : List Json) := Json.arr xs.toArray
private def varJson (n : Nat) := obj [("var", toJson n)]
private def literal (n : Nat) := obj [("const", toJson (toString n))]
private def expression (n : Nat) :=
  obj [("scale", obj [("k", toJson "3"),
    ("x", obj [("add", arr [varJson n, literal 5])])])]
private def point (n : Nat) := obj [("x", expression n), ("y", expression (n + 1))]
private def fields (xs : List (String × Nat)) := xs.map fun (k, n) => (k, expression n)
private def operands (n count : Nat) := arr ((List.range count).map fun i => expression (n + i))

private def pt (f : Nat → FVar Fp) (n : Nat) : AffinePoint (FVar Fp) := ⟨f n, f (n + 1)⟩

private def cases : List (Json × ((Nat → FVar Fp) → KimchiConstraint Fp)) := [
  (obj [("basic", obj [("r1cs", obj (fields [("left", 0), ("right", 1), ("output", 2)]))])],
    fun f => .basic (.r1cs (f 0) (f 1) (f 2))),
  (obj [("basic", obj [("equal", operands 0 2)])], fun f => .basic (.equal (f 0) (f 1))),
  (obj [("basic", obj [("square", operands 0 2)])], fun f => .basic (.square (f 0) (f 1))),
  (obj [("basic", obj [("boolean", expression 0)])], fun f => .basic (.boolean (f 0))),
  (obj [("pad", operands 0 7)], fun f => .pad (Vector.ofFn fun i => f i.val)),
  (obj [("addComplete", obj ([("p1", point 0), ("p2", point 2), ("p3", point 4)] ++
      fields [("inf", 6), ("sameX", 7), ("s", 8), ("infZ", 9), ("x21Inv", 10)]))],
    fun f => .addComplete ⟨pt f 0, pt f 2, pt f 4, f 6, f 7, f 8, f 9, f 10⟩),
  (obj [("poseidon", obj [("state", arr ((List.range 56).map fun i => operands (3 * i) 3))])],
    fun f => .poseidon ⟨Poseidon.fpParams.mds, Poseidon.fpParams.roundConstants.toList,
      (List.range 56).map fun i => (f (3 * i), f (3 * i + 1), f (3 * i + 2))⟩),
  (obj [("varBaseMul", arr [obj ([("accs", arr ((List.range 6).map fun i => point (2 * i))),
      ("bits", operands 12 5), ("slopes", operands 17 5), ("base", point 24)] ++
      fields [("nPrev", 22), ("nNext", 23)])])],
    fun f => .varBaseMul [⟨pt f 0, pt f 2, pt f 4, pt f 6, pt f 8, pt f 10,
      f 12, f 13, f 14, f 15, f 16, f 17, f 18, f 19, f 20, f 21, f 22, f 23, pt f 24⟩]),
  (obj [("endoScalar", arr [obj (fields [("n0", 0), ("n8", 1), ("a0", 2), ("a8", 3),
      ("b0", 4), ("b8", 5)] ++ [("xs", operands 6 8)])])],
    fun f => .endoScalar [⟨f 0, f 1, f 2, f 3, f 4, f 5, Vector.ofFn fun i => f (6 + i.val)⟩]),
  (obj [("endoMul", obj [("state", arr [obj ([("t", point 0), ("p", point 2),
      ("r", point 4), ("s", point 6), ("bits", operands 12 4)] ++
      fields [("s1", 8), ("s3", 9), ("nAcc", 10), ("nAccNext", 11), ("inv", 16)])]),
      ("s", point 17), ("nAcc", expression 19)])],
    fun f => .endoMul ⟨[⟨pt f 0, pt f 2, pt f 4, pt f 6, f 8, f 9, f 10, f 11,
      f 12, f 13, f 14, f 15, f 16⟩], pt f 17, f 19, Bulletproof.IpaPallas.curve.endo.coeff⟩)]

private def rule (c : Json) (n : Nat := 200) := obj [
  ("inputSize", toJson (3 : Nat)),
  ("ops", arr [obj [("alloc", toJson n)], obj [("constraint", c)]]),
  ("prevs", arr [obj [("statement", arr [expression 0]), ("mustVerify", varJson 3)]]),
  ("publicOutput", arr [expression 4])]

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def requireRejected {α : Type} (r : Except String α) (message : String) : IO Unit :=
  match r with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

def main : IO Unit := do
  let env : Vector (FVar Fp) 3 := #v[.var 70, .var 11, .var 45]
  let renumber := fun n => if n < 3 then env[n]?.getD (.const 0) else .var (100 + n - 3)
  let value := fun n => CVar.scale (3 : Fp) (.add (renumber n) (.const 5))
  for (c, expected) in cases do
    let d ← IO.ofExcept (RuleDump.ofJson (rule c))
    if hi : d.inputSize = 3 then
      if hp : 0 < d.prevs.size then
        let built := build (replayRule d none (env.cast hi.symm)) 100
        require (decide (built.constraints = [expected value]))
          "constraint replay changed an operand"
        require (built.nextVar == 300) "replay allocation count differs"
        require (built.result.2.toArray == #[value 4]) "public output expression differs"
        let prev := built.result.1 ⟨0, hp⟩
        require (prev.appState.toArray == #[value 0]) "predecessor expression differs"
        require (prev.mustVerify.toCVar.val (fun v => v) == 100) "dynamic mustVerify was lost"
      else throw (IO.userError "missing predecessor")
    else throw (IO.userError "input size changed")
    requireRejected (RuleDump.ofJson (obj [("inputSize", toJson (0 : Nat)),
      ("ops", arr [obj [("constraint", c)]]), ("prevs", arr []), ("publicOutput", arr [])]))
      "out-of-scope constraint operand was accepted"
  let ops : List RuleOp := [.alloc 2]
  match prove (replayOps (some #[1]) ops 0 #[]) 0 Assignments.empty with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "short rule witness was accepted")
  match prove (replayOps (some #[1, 2]) ops 0 #[]) 0
      Assignments.empty with
  | .error _ => throw (IO.userError "complete rule witness was rejected")
  | .ok r =>
    require (r.assignments 0 == some 1 && r.assignments 1 == some 2)
      "rule witness allocation values differ"
  requireRejected (parseOp (obj [("constraint", obj [("unknown", Json.null)])]))
    "unknown constraint was accepted"
  requireRejected (parseOp (obj [("constraint", obj [("pad", operands 0 6)])]))
    "malformed padding row was accepted"
  requireRejected (parseOp (obj [("constraint", obj [("endoMul", obj [
    ("state", arr []), ("s", point 0), ("nAcc", expression 2)])])]))
    "empty endomorphism multiplication was accepted"
  let forward := obj [("inputSize", toJson (0 : Nat)), ("prevs", arr []),
    ("publicOutput", arr []), ("ops", arr [obj [("alloc", toJson (1 : Nat))],
      obj [("constraint", obj [("basic", obj [("boolean", varJson 1)])])],
      obj [("alloc", toJson (1 : Nat))]])]
  requireRejected (RuleDump.ofJson forward) "use before allocation was accepted"
  IO.println "✓ rule replay: all constraint variants, remapping, returns, scope and witness bounds"
