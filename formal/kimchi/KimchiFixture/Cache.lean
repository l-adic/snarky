import KimchiFixture.Kimchi
import KimchiFixture.PS

/-!
# The PureScript proof cache, decoded

The pickles test suite memoises every kimchi proof it produces under
`packages/pickles/test/fixtures/proof-cache/`, in the format of
`packages/snarky-kimchi/src/Snarky/Backend/Kimchi/ProofCache.purs`:
`{ "<vkDigest>": { "<publicInput>": entry } }`. An entry holds the verification key's JSON,
the proof's serde JSON, and links to the proofs it is built on (`step` on a wrap proof,
`prevs` on a step proof). This module reads a file into `Entry` records.

Two encodings meet here:

* the verification key is camelCase, with points as uncompressed `[x, y]` little-endian hex
  pairs;
* the proof is arkworks serde: snake_case, with points compressed to 33 bytes of hex, the
  `x` coordinate then a flag byte (`0x80` the larger root, `0x00` the smaller, `0x40` the
  identity). The square root that decompresses is a parameter, supplied per curve.
-/

open Lean FixtureKit Bulletproof Bulletproof.Fixture Kimchi.Verifier Kimchi.Verifier.Wire
open CompElliptic.CurveForms.ShortWeierstrass (OnCurve)

namespace Kimchi.Fixture.Cache

/-- A hex string, little-endian, as a scalar. -/
private def scalar (C : Ipa.KimchiCurve) (j : Json) : Except String C.ScalarField :=
  Kimchi.Fixture.PS.parseHexLE (m := C.scalar) j

/-- A hex string, little-endian, as a base-field element. -/
private def base (C : Ipa.KimchiCurve) (j : Json) : Except String C.BaseField :=
  Kimchi.Fixture.PS.parseHexLE (m := C.base) j

/-- An uncompressed `[x, y]` hex pair (the verification key's encoding). -/
private def pointXY (C : Ipa.KimchiCurve) : Json → Except String C.Point :=
  parseSWPoint (base C) C.E

/-- A compressed point (the proof's encoding): 32 little-endian bytes of `x`, then the
arkworks flag byte, as hex. -/
private def pointCompressed (C : Ipa.KimchiCurve)
    (sqrt : C.BaseField → Option C.BaseField) (j : Json) : Except String C.Point := do
  let s ← j.getStr?
  unless s.length = 66 do throw s!"compressed point: expected 66 hex chars, got {s.length}"
  pointOfCompressed C sqrt (← Kimchi.Fixture.PS.hexLEtoNat (s.take 64).toString)
    (← Kimchi.Fixture.PS.hexLEtoNat (s.drop 64).toString)

/-- A serde commitment: `{ chunks: [compressed point, …] }`. -/
private def chunks (C : Ipa.KimchiCurve) (sqrt : C.BaseField → Option C.BaseField)
    (j : Json) : Except String (Array C.Point) := do
  parseArrOf (pointCompressed C sqrt) (← j.getObjVal? "chunks")

/-- A serde evaluation pair: `{ zeta: [scalar, …], zeta_omega: [scalar, …] }`. -/
private def evalPair (C : Ipa.KimchiCurve) (j : Json) :
    Except String (PointEvaluations (Array C.ScalarField)) := do
  return { zeta := ← parseArrOf (scalar C) (← j.getObjVal? "zeta")
           zetaOmega := ← parseArrOf (scalar C) (← j.getObjVal? "zeta_omega") }

/-- The proof's serde JSON as the kimchi proof wire record. -/
def parseProof (C : Ipa.KimchiCurve) (sqrt : C.BaseField → Option C.BaseField) (j : Json) :
    Except String (KimchiProof C) := do
  let comms ← j.getObjVal? "commitments"
  let ev ← j.getObjVal? "evals"
  let op ← j.getObjVal? "proof"
  let pe := evalPair C
  let evals : ProofEvaluations (Array C.ScalarField) :=
    { w := ← parseSized "w" wCols (← parseArrOf pe (← ev.getObjVal? "w"))
      z := ← pe (← ev.getObjVal? "z")
      s := ← parseSized "s" sigmaRows (← parseArrOf pe (← ev.getObjVal? "s"))
      coefficients := ← parseSized "coefficients" coeffCols
        (← parseArrOf pe (← ev.getObjVal? "coefficients"))
      genericSelector := ← pe (← ev.getObjVal? "generic_selector")
      poseidonSelector := ← pe (← ev.getObjVal? "poseidon_selector")
      completeAddSelector := ← pe (← ev.getObjVal? "complete_add_selector")
      mulSelector := ← pe (← ev.getObjVal? "mul_selector")
      emulSelector := ← pe (← ev.getObjVal? "emul_selector")
      endomulScalarSelector := ← pe (← ev.getObjVal? "endomul_scalar_selector") }
  -- The public evaluations are optional; serde writes an absent one as `null`.
  let pubEvals ← match (ev.getObjVal? "public").toOption with
    | some Json.null | none => pure none
    | some pj => some <$> pe pj
  let pt := pointCompressed C sqrt
  let tComm ← chunks C sqrt (← comms.getObjVal? "t_comm")
  return { wComm := ← parseSized "w_comm" wCols
             (← parseArrOf (chunks C sqrt) (← comms.getObjVal? "w_comm"))
           zComm := ← chunks C sqrt (← comms.getObjVal? "z_comm")
           tComm
           evals
           pubEvals
           ftEval1 := ← scalar C (← j.getObjVal? "ft_eval1")
           opening :=
             { lr := ← parseArrOf (parsePair pt) (← op.getObjVal? "lr")
               delta := ← pt (← op.getObjVal? "delta")
               z1 := ← scalar C (← op.getObjVal? "z1")
               z2 := ← scalar C (← op.getObjVal? "z2")
               sg := ← pt (← op.getObjVal? "sg") }
           prevChallenges := ← parseArrOf (fun r => do
               return { comm := ← chunks C sqrt (← r.getObjVal? "comm")
                        chals := ← parseArrOf (scalar C) (← r.getObjVal? "chals") })
             (← j.getObjVal? "prev_challenges") }

/-- A natural written as a JSON number or as a numeral string. -/
private def natJ (j : Json) : Except String ℕ :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => parseNat j

/-- The verification key's JSON as the kimchi key wire record. `endo` and `digest` are not
on the wire; `lagrangeBasis` is left empty for the caller to derive from the SRS. -/
def parseVK (C : Ipa.KimchiCurve) (endo : C.ScalarField) (digest : C.BaseField) (j : Json) :
    Except String (KimchiVK C) := do
  let dom ← j.getObjVal? "domain"
  let ev ← j.getObjVal? "evals"
  let comm (k : String) : Except String (Array C.Point) := do
    parseArrOf (pointXY C) (← ev.getObjVal? k)
  return { domainLog2 := ← natJ (← dom.getObjVal? "logSizeOfGroup")
           omega := ← scalar C (← dom.getObjVal? "groupGen")
           sigmaComm := ← parseSized "sigmaComm" permCols
             (← parseArrOf (parseArrOf (pointXY C)) (← ev.getObjVal? "sigmaComm"))
           coefficientsComm := ← parseSized "coefficientsComm" coeffCols
             (← parseArrOf (parseArrOf (pointXY C)) (← ev.getObjVal? "coefficientsComm"))
           genericComm := ← comm "genericComm"
           poseidonComm := ← comm "psmComm"
           completeAddComm := ← comm "completeAddComm"
           mulComm := ← comm "mulComm"
           emulComm := ← comm "emulComm"
           endomulScalarComm := ← comm "endomulScalarComm"
           shifts := ← parseSized "shifts" permCols
             (← parseArrOf (scalar C) (← j.getObjVal? "shifts"))
           zkRows := ← natJ (← j.getObjVal? "zkRows")
           prevChallenges := ← natJ (← j.getObjVal? "prevChallenges")
           endo
           digest
           lagrangeBasis := #[] }

/-- The comma-joined decimal public input. -/
private def parsePublicInput (C : Ipa.KimchiCurve) (s : String) :
    Except String (Array C.ScalarField) :=
  (s.splitOn ",").toArray.mapM fun t => match t.toNat? with
    | some v => pure (v : C.ScalarField)
    | none => throw s!"public input: not a numeral: {t.take 40}"

/-- One cached proof, decoded: its key, its records, and the proofs it is built on. -/
structure Entry (C : Ipa.KimchiCurve) where
  /-- The verification key's digest, as the cache keys it. -/
  vkDigest : String
  /-- The public input's key string, as the cache keys it — what a link names. -/
  publicInputKey : String
  /-- The public input. -/
  publicInput : Array C.ScalarField
  /-- The verification key. -/
  vk : KimchiVK C
  /-- The proof. -/
  proof : KimchiProof C
  /-- The cache key of the step proof this (wrap) proof wrapped. -/
  step : Option (String × String)
  /-- Per slot of this (step) proof, the cache key of the wrap proof it verified there —
  `none` on a base-case slot. -/
  prevs : Array (Option (String × String))

/-- A link: the cache key of another entry. -/
private def parseRef (j : Json) : Except String (String × String) := do
  return (← (← j.getObjVal? "vkDigest").getStr?, ← (← j.getObjVal? "publicInput").getStr?)

/-- One cache entry at a curve. -/
private def parseEntry (C : Ipa.KimchiCurve) (endo : C.ScalarField)
    (sqrt : C.BaseField → Option C.BaseField) (vkDigest pi : String) (e : Json) :
    Except String (Entry C) := do
  let some d := vkDigest.toNat? | throw s!"vk digest is not a numeral: {vkDigest.take 40}"
  let vkJ ← Json.parse (← (← e.getObjVal? "vk").getStr?)
  let proofJ ← Json.parse (← (← e.getObjVal? "proof").getStr?)
  let step ← match (e.getObjVal? "step").toOption with
    | some Json.null | none => pure none
    | some sj => pure (some (← parseRef sj))
  let prevs ← match (e.getObjVal? "prevs").toOption with
    | some Json.null | none => pure #[]
    | some pj => parseArrOf (fun r => match r with
        | Json.null => pure none
        | _ => some <$> parseRef r) pj
  return { vkDigest, publicInputKey := pi, publicInput := ← parsePublicInput C pi
           vk := ← parseVK C endo (d : C.BaseField) vkJ
           proof := ← parseProof C sqrt proofJ, step, prevs }

/-- Whether a cache entry's verification key lies on `C`: its first σ commitment's
coordinates satisfy `C`'s equation. -/
private def entryOnCurve (C : Ipa.KimchiCurve) (e : Json) : Except String Bool := do
  let vkJ ← Json.parse (← (← e.getObjVal? "vk").getStr?)
  let sigma ← (← vkJ.getObjVal? "evals").getObjVal? "sigmaComm"
  let comms ← parseArrOf (parseArrOf (parsePair (base C))) sigma
  let some p := comms[0]?.bind (·[0]?) | throw "sigmaComm: no commitment"
  return decide (OnCurve C.E.A C.E.B p)

/-- A cache file's entries at `C`, and the count of buckets skipped. Step and wrap proofs
are committed on different Pasta curves; a bucket whose first entry fails `entryOnCurve` is
the other curve's and is skipped. -/
def parseFile (C : Ipa.KimchiCurve) (endo : C.ScalarField)
    (sqrt : C.BaseField → Option C.BaseField) (raw : String) :
    Except String (Array (Entry C) × ℕ) := do
  let j ← Json.parse raw
  let buckets ← j.getObj?
  let mut out : Array (Entry C) := #[]
  let mut skipped := 0
  for ⟨vkDigest, inner⟩ in buckets.toArray do
    let entries := (← inner.getObj?).toArray
    let some (_, e0) := entries[0]? | continue
    unless ← entryOnCurve C e0 do
      skipped := skipped + 1
      continue
    match entries.mapM fun ⟨pi, e⟩ => parseEntry C endo sqrt vkDigest pi e with
    | .ok es => out := out ++ es
    | .error msg => throw s!"bucket {vkDigest.take 12}…: {msg}"
  return (out, skipped)

end Kimchi.Fixture.Cache
