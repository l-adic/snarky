import KimchiFixture.Kimchi
import KimchiFixture.PS

/-!
# The PureScript proof cache, decoded

`packages/pickles/test/fixtures/proof-cache/*.json` is the pickles test suite's memo of
every kimchi proof it produced: `{ "<vkDigest>": { "<publicInput>": Entry } }` with
`Entry = { vk, proof, step? }` — the verification key's JSON, the proof's serde JSON and,
on a wrap proof, the key of the step proof it wrapped. This module reads that file into
the wire records `kimchiVerify` and the circuit halves take.

Two encodings meet here, both PureScript's own:

* the verification key is `vkRawToJson`'s shape — camelCase, points as uncompressed
  `[x, y]` little-endian hex pairs, commitments as arrays of them;
* the proof is arkworks serde — snake_case, points **compressed**: 33 bytes of hex, the
  `x` coordinate then a flag byte (`0x80` the larger root, `0x00` the smaller, `0x40`
  the identity). Decompression is a Tonelli–Shanks root, supplied per curve.

Neither `endo` nor `lagrangeBasis` is on the wire. `endo` is a curve constant; the
Lagrange basis is SRS-derived and left empty here — the verifier driver fills it.
-/

open Lean FixtureKit Bulletproof Bulletproof.Fixture Kimchi.Verifier Kimchi.Verifier.Wire
open CompElliptic.CurveForms.ShortWeierstrass

namespace Kimchi.Fixture.Cache

/-- A hex string, little-endian, as a scalar. -/
private def scalar (C : Ipa.KimchiCurve) (j : Json) : Except String C.ScalarField :=
  Kimchi.Fixture.PS.parseHexLE (m := C.scalar) j

/-- A hex string, little-endian, as a base-field element. -/
private def base (C : Ipa.KimchiCurve) (j : Json) : Except String C.BaseField :=
  Kimchi.Fixture.PS.parseHexLE (m := C.base) j

/-- A point from its coordinates: on the curve, or the `(0, 0)` identity sentinel. -/
private def mkPoint (C : Ipa.KimchiCurve) (x y : C.BaseField) : Except String C.Point :=
  if h : OnCurve C.E.A C.E.B (x, y) then return ⟨x, y, Or.inl h⟩
  else if h0 : (x, y) = ((0 : C.BaseField), (0 : C.BaseField)) then return ⟨x, y, Or.inr h0⟩
  else throw "point not on the curve"

/-- An uncompressed `[x, y]` hex pair (the verification key's encoding). -/
private def pointXY (C : Ipa.KimchiCurve) (j : Json) : Except String C.Point := do
  let (x, y) ← parsePair (base C) j
  mkPoint C x y

/-- A compressed point (the proof's encoding): 32 little-endian bytes of `x`, then a flag
byte. `sqrt` is the base field's square root; the flag picks the root — `0x80` the one
above `(p-1)/2`, `0x00` the one below — and `0x40` is the identity. -/
private def pointCompressed (C : Ipa.KimchiCurve)
    (sqrt : C.BaseField → Option C.BaseField) (j : Json) : Except String C.Point := do
  let s ← j.getStr?
  unless s.length = 66 do throw s!"compressed point: expected 66 hex chars, got {s.length}"
  let x : C.BaseField := ((← Kimchi.Fixture.PS.hexLEtoNat (s.take 64).toString) : ℕ)
  let flag ← Kimchi.Fixture.PS.hexLEtoNat (s.drop 64).toString
  if flag = 0x40 then return ← mkPoint C 0 0
  let some y0 := sqrt (x * x * x + C.E.A * x + C.E.B)
    | throw "compressed point: x is not on the curve"
  let big : C.BaseField → Bool := fun y => decide ((C.base - 1) / 2 < y.val)
  let y := if (flag = 0x80) = big y0 then y0 else -y0
  mkPoint C x y

/-- A serde commitment: `{ chunks: [compressed point, …] }`. -/
private def chunks (C : Ipa.KimchiCurve) (sqrt : C.BaseField → Option C.BaseField)
    (j : Json) : Except String (Array C.Point) := do
  parseArrOf (pointCompressed C sqrt) (← j.getObjVal? "chunks")

/-- A serde evaluation pair: `{ zeta: [chunks], zeta_omega: [chunks] }`. -/
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
  -- Absent public evaluations (the one-chunk form) are `null` on the serde wire.
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

/-- A natural written as a JSON number (`vkRawToJson`'s counts) or as a numeral string. -/
private def natJ (j : Json) : Except String ℕ :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => parseNat j

/-- The verification key's JSON (`vkRawToJson`) as the kimchi key wire record, at a given
digest and endo. `lagrangeBasis` is left empty: it is SRS-derived, not wire data. -/
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

/-- A cache file at a curve. A file holds a chain's step proofs, committed on one Pasta
curve, and its wrap proofs, committed on the other; a bucket whose points are not on
`C` is the other curve's and is skipped. The result is the entries at `C` and the count
of buckets skipped, so a caller can check the split it expects. -/
def parseFile (C : Ipa.KimchiCurve) (endo : C.ScalarField)
    (sqrt : C.BaseField → Option C.BaseField) (raw : String) :
    Except String (Array (Entry C) × ℕ) := do
  let j ← Json.parse raw
  let buckets ← j.getObj?
  let mut out : Array (Entry C) := #[]
  let mut skipped := 0
  for ⟨vkDigest, inner⟩ in buckets.toArray do
    let entries := (← inner.getObj?).toArray
    match entries.mapM fun ⟨pi, e⟩ => parseEntry C endo sqrt vkDigest pi e with
    | .ok es => out := out ++ es
    | .error msg =>
      if msg = "point not on the curve" then skipped := skipped + 1
      else throw s!"bucket {vkDigest.take 12}…: {msg}"
  return (out, skipped)

end Kimchi.Fixture.Cache
