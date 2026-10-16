import Std.Data.HashMap
import BulletproofFixture
import BulletproofFixture.SRSLoader
import KimchiFixture.Cache
import Kimchi.Verifier.Accumulator

/-!
# Verdicts on cached proofs

What the drivers decide of a cached proof beyond its circuits, computed once: the curve's SRS cut
to the proof's round count, loaded once per count (`PicklesFixture.srsAt`); the key's Lagrange
points, memoised on disk (`PicklesFixture.basisFor`); the entry's records checked at the SRS
(`Kimchi.Fixture.Cache.Entry.checked`); and the `kimchiVerify` and `accOk` verdicts several links
ask of one proof or accumulator, memoised (`PicklesFixture.Memo`).
-/

namespace PicklesFixture

open Kimchi.Fixture Bulletproof

/-- The curve's SRS cut to `k` rounds, loaded from `srs-cache/<name>.srs` once per `k`
(decompressing the file's points dominates a load). -/
def srsAt (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (k : ℕ) : IO (SRS C.Point) := do
  if let some σ := (← loaded.get).lookup k then return σ
  let srsDir := (← IO.getEnv "SRS_CACHE_DIR").getD "../srs-cache"
  let σ ← Fixture.SRSLoader.loadSRS C sqrt k s!"{srsDir}/{name}.srs"
  loaded.modify ((k, σ) :: ·)
  return σ

/-- The Lagrange points an entry's key reads — as many as its public-input count — at its
domain and `nc` chunks, computed from `σ` and memoised per curve, SRS size, domain and chunk
count under `lagrange-cache/`: `KimchiVK.lagrangePoints` at the key's count, where
`kimchiVerifyWith` is `kimchiVerify` by definition. -/
def basisFor (C : Ipa.KimchiCurve) (name : String) (σ : SRS C.Point) (nc : ℕ)
    (e : Cache.Entry C) : IO (Array (Vector C.Point nc)) := do
  let memoDir := (← IO.getEnv "LAGRANGE_CACHE_DIR").getD "lagrange-cache"
  Fixture.lagrangeBasisCached C s!"{memoDir}/{name}-k{σ.k}-2^{e.vk.domainLog2}-{nc}c.json" σ nc
    (2 ^ e.vk.domainLog2) e.vk.omega e.vk.publicCount

/-- The verdicts several links share, computed once per run: `kimchiVerify` runs the
`2^k`-point `sg` MSM, and every link that consumes a cached proof verifies it; `accOk` runs one
per accumulator, and the dummies unlinked accumulators carry repeat across proofs. In memory for
the life of the process, so nothing outlives the proofs it was computed on. A `kimchiVerify`
verdict is keyed by everything it reads: the curve, the SRS round count, the entry, and the
public input by value — a link rebuilds the public input from its circuit's cells, and a rebuilt
input that differs from the entry's must miss rather than reuse another link's verdict. -/
structure Memo where
  /-- `kimchiVerify`, per proof and public input. -/
  verify : IO.Ref (Std.HashMap String Bool)
  /-- `accOk`, per accumulator. -/
  acc : IO.Ref (Std.HashMap String Bool)

/-- A fresh memo. -/
def Memo.new : IO Memo := do
  return { verify := ← IO.mkRef {}, acc := ← IO.mkRef {} }

/-- A verdict from `ref`, computed and stored on a miss. Two workers missing at once both
compute it, and agree. -/
def memoized (ref : IO.Ref (Std.HashMap String Bool)) (key : String) (compute : Unit → Bool) :
    IO Bool := do
  if let some b := (← ref.get)[key]? then return b
  let b := compute ()
  ref.modify (·.insert key b)
  return b

end PicklesFixture
