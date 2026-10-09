import BulletproofFixture.SRSLoader
import Kimchi.Verifier.Kimchi

/-!
# Regenerate committed Lagrange bases

Compute the manifest's table prefixes directly from the SRS files and the canonical domain
generator, without reading any cache, application dump or proof cache. The Python regeneration
driver supplies the manifest, an empty output directory and the SRS directory, then pins the
generated tables and SRS inputs together. Normal CI consumes the committed tables.
-/

open Lean Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier

private def natField (j : Json) (name : String) : Except String Nat := do
  (← j.getObjVal? name).getNat?

private def generate (C : Ipa.KimchiCurve) (name : String)
    (sqrt : C.BaseField → Option C.BaseField) (srsDir outDir : System.FilePath)
    (tables : Array Json) : IO Unit := do
  let loaded ← IO.mkRef ([] : List (Nat × SRS C.Point))
  for entry in tables do
    let curve ← IO.ofExcept ((← IO.ofExcept (entry.getObjVal? "curve")).getStr?)
    if curve == name then
      let file ← IO.ofExcept ((← IO.ofExcept (entry.getObjVal? "file")).getStr?)
      let k ← IO.ofExcept (natField entry "srsRounds")
      let log2 ← IO.ofExcept (natField entry "domainLog2")
      let chunks ← IO.ofExcept (natField entry "chunks")
      let count ← IO.ofExcept (natField entry "count")
      unless log2 ≤ C.twoAdicity && 0 < count && count ≤ 2 ^ log2 &&
          chunks == 2 ^ (log2 - k) do
        throw (IO.userError s!"{file}: invalid domain, prefix or chunk count")
      let σ ← match (← loaded.get).lookup k with
        | some σ => pure σ
        | none => do
          let σ ← Fixture.SRSLoader.loadSRS C sqrt k (srsDir / s!"{name}.srs")
          loaded.modify ((k, σ) :: ·)
          pure σ
      IO.println s!"{file}: computing {count} commitments of {chunks} chunks"
      (← IO.getStdout).flush
      let start ← IO.monoMsNow
      let pts := Ipa.lagrangeBasis C σ chunks (2 ^ log2) (domainGenerator C log2) count
      let json := Json.arr (pts.map fun row ↦ Json.arr (row.toArray.map fun p ↦
        Json.arr #[Json.str (toString p.x.val), Json.str (toString p.y.val)]))
      IO.FS.writeFile (outDir / file) json.compress
      IO.println s!"✓ {file}: {((← IO.monoMsNow) - start)} ms"
      (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let [manifest, outDir, srsDir] := args
    | throw (IO.userError "usage: regenerate-lagrange-cache MANIFEST OUT_DIR SRS_DIR")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile manifest))
  let tables ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "tables")).getArr?)
  IO.FS.createDirAll outDir
  generate IpaPallas.curve "pallas" pallasBase.sqrt? srsDir outDir tables
  generate IpaVesta.curve "vesta" vestaBase.sqrt? srsDir outDir tables
