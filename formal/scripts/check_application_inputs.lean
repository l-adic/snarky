import PicklesFixture.ApplicationImport

/-!
Check rejection of malformed reconstruction inputs using the selected TwoPhaseChain sidecar.
No SRS computation or comparison circuit is needed for these reader and layout checks.
-/

open Lean PicklesFixture PicklesFixture.Application Pickles.Application

private def rejected {α : Type u} (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: malformed input was accepted")

private def replaceAt : Json → List String → Json → Except String Json
  | _, [], value => pure value
  | j, key :: rest, value => do
    let child ← replaceAt (← j.getObjVal? key) rest value
    return j.setObjVal! key child

def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let path := s!"{dir}/TwoPhaseChain/shapes/two_phase_chain.json"
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let parsed ← IO.ofExcept (ApplicationDump.ofJson raw)
  for (label, path, value) in [
      ("missing rules", ["rules"], Json.arr #[]),
      ("zero chunk count", ["resolved", "stepChunks"], toJson (0 : Nat)),
      ("missing step key", ["resolved", "stepKeys"], Json.arr #[]),
      ("wrong SRS curve", ["environment", "srs", "wrap", "curve"], toJson "vesta"),
      ("wrong SRS rounds", ["environment", "srs", "step", "rounds"], toJson (15 : Nat)),
      ("missing wrap evaluations", ["environment", "padding", "wrapEvals"], Json.arr #[]),
      ("missing padding", ["environment", "padding", "unfinalized"], Json.arr #[]),
      ("wrong challenge count", ["environment", "padding", "wrapChallenges", "raw"],
        Json.arr #[])] do
    rejected label (ApplicationDump.ofJson (← IO.ofExcept (replaceAt raw path value)))
  let E ← IO.ofExcept (raw.getObjVal? "environment")
  let padding ← IO.ofExcept (E.getObjVal? "padding")
  let challenges ← IO.ofExcept (padding.getObjVal? "wrapChallenges")
  let expanded ← IO.ofExcept (challenges.getObjVal? "expanded" >>= Json.getArr?)
  rejected "wrong challenge expansion" (ApplicationDump.ofJson (← IO.ofExcept (replaceAt raw
    ["environment", "padding", "wrapChallenges", "expanded"]
    (Json.arr (expanded.set! 0 (toJson "0"))))))
  let unfs ← IO.ofExcept (padding.getObjVal? "unfinalized" >>= Json.getArr?)
  let ufields ← IO.ofExcept (unfs[0]!.getObjVal? "fields" >>= Json.getArr?)
  let invalid := unfs[0]!.setObjVal! "fields"
    (Json.arr (ufields.set! 31 (toJson "2")))
  rejected "non-Boolean padding" (ApplicationDump.ofJson (← IO.ofExcept (replaceAt raw
    ["environment", "padding", "unfinalized"] (Json.arr (unfs.set! 0 invalid)))))
  rejected "missing branch" ({ parsed.shape with branches := #[] }.load #[])
  rejected "unknown import" ({ parsed.shape with branches := #[#[.external 0]] }.load #[])
  rejected "too many slots" ({ parsed.shape with branches := #[#[.self, .self, .self]] }.load #[])
  let changed := { parsed.shape with
    statement := { parsed.shape.statement with
      inputFields := parsed.shape.statement.inputFields + 1 } }
  match changed.load #[] with
  | .error e => throw (IO.userError e)
  | .ok loaded =>
    let b : loaded.shape.Branch := ⟨0, loaded.shape.branches_pos⟩
    let some rule := parsed.rules[0]? | throw (IO.userError "missing test rule")
    rejected "rule input layout" (CheckedRule.check loaded.shape b rule)
  IO.println "✓ application readers: malformed counts, SRS references, padding, layouts and imports"
