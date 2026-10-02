import Pickles

/-!
# Why is X in (or out of) the closure?

`AUDIT_ROOTS` (comma-separated) and `AUDIT_TARGETS`: for each target, the shortest
dependency path from some root, or a report that it is unreachable.

Run from `formal/`:
`AUDIT_ROOTS=Pickles.stepWrap_kimchiVerify AUDIT_TARGETS=Pickles.chooseKey
lake env lean scripts/closure_path.lean`.
-/

open Lean

namespace ClosurePath

def declValue? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value | _ => none

def directDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci => match declValue? ci with
    | some v => ci.type.getUsedConstants ++ v.getUsedConstants
    | none => ci.type.getUsedConstants

def isOurs (n : Name) : Bool :=
  let n := (privateToUserName? n).getD n
  (`Kimchi).isPrefixOf n || (`Pasta).isPrefixOf n || (`Poseidon).isPrefixOf n
    || (`FixtureKit).isPrefixOf n || (`Bulletproof).isPrefixOf n || (`Snarky).isPrefixOf n
    || (`Schnorr).isPrefixOf n || (`Pickles).isPrefixOf n

/-- BFS from `roots`, recording each reached node's parent. -/
partial def bfs (env : Environment) (roots : Array Name) : Std.HashMap Name Name :=
  let rec go (par : Std.HashMap Name Name) : List Name → Std.HashMap Name Name
    | [] => par
    | n :: rest =>
      let fresh := (directDeps env n).filter fun d => isOurs d && !par.contains d
      let par := fresh.foldl (fun m d => m.insert d n) par
      go par (rest ++ fresh.toList)
  go (roots.foldl (fun m r => m.insert r r) ∅) roots.toList

def pathTo (par : Std.HashMap Name Name) (t : Name) : Option (List Name) :=
  if !par.contains t then none
  else
    let rec climb (n : Name) (acc : List Name) (fuel : ℕ) : List Name :=
      match fuel with
      | 0 => acc
      | fuel + 1 =>
        match par[n]? with
        | some p => if p == n then n :: acc else climb p (n :: acc) fuel
        | none => n :: acc
    some (climb t [] 200)

end ClosurePath

open ClosurePath in
run_cmd do
  let env ← getEnv
  let parse (s : String) : Array Name :=
    (s.splitOn ",").filterMap
      (fun t => let t := t.trimAscii.toString; if t.isEmpty then none else some t.toName)
      |>.toArray
  let roots := parse ((← IO.getEnv "AUDIT_ROOTS").getD "")
  let targets := parse ((← IO.getEnv "AUDIT_TARGETS").getD "")
  for r in roots do unless env.contains r do throwError "root {r} not in env"
  let par := bfs env roots
  let mut out := s!"roots ({roots.size}): {roots.toList}\n\n"
  for t in targets do
    if !env.contains t then out := out ++ s!"{t}: NOT A DECLARATION\n\n" else
    match pathTo par t with
    | none => out := out ++ s!"{t}: OUTSIDE the closure\n\n"
    | some p =>
      out := out ++ s!"{t}: in closure, depth {p.length - 1}\n"
      for (n, i) in p.zipIdx do out := out ++ s!"  {String.join (List.replicate i "  ")}{n}\n"
      out := out ++ "\n"
  IO.println out
