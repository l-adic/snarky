import Std.Data.HashMap
import BulletproofFixture
import BulletproofFixture.SRSLoader
import KimchiFixture.Cache
import Pickles.Env
import Pickles.TwoHalves

/-!
# Verdicts on cached proofs

What the drivers decide of a cached proof beyond its circuits, computed once: the curve's SRS cut
to the proof's round count, loaded once per count (`PicklesFixture.srsAt`); the key's Lagrange
points, memoised on disk (`PicklesFixture.basisFor`); the entry's records checked at the SRS
(`PicklesFixture.checkedAny`), and its SRS and key checked once per key
(`PicklesFixture.keyFor`); the `kimchiVerify` and `sgOk` verdicts several checks ask of one
proof, memoised per proof and public input (`PicklesFixture.Memo`, `PicklesFixture.verifies`);
and the carry of a proof's deferred obligation into the next proof's old accumulators
(`PicklesFixture.carriesInto`), an unlinked accumulator satisfying `accOk` on its own
(`PicklesFixture.padOk`).
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

/-- A cache entry's checked wire records at the SRS `σ`: the records checked at the run's chunk
count and `σ`'s round count. -/
def checkedAny (C : Ipa.KimchiCurve) (σ : SRS C.Point) (e : Cache.Entry C) :
    IO ((nc : ℕ) × Kimchi.Verifier.KimchiVK C nc × Kimchi.Verifier.KimchiProof C nc σ.k) := do
  let nc := Kimchi.Verifier.Wire.runNc C σ e.vk
  match e.vk.check nc, e.proof.check nc σ.k with
  | some cvk, some cp => return ⟨nc, cvk, cp⟩
  | _, _ => throw (IO.userError "the cache entry's records failed the wire check")

/-- `checkedAny` at one chunk, the chunk count of every wrap proof. -/
def checkedAt (C : Ipa.KimchiCurve) (σ : SRS C.Point) (e : Cache.Entry C) :
    IO (Kimchi.Verifier.KimchiVK C 1 × Kimchi.Verifier.KimchiProof C 1 σ.k) := do
  let ⟨nc, cvk, cp⟩ ← checkedAny C σ e
  if h : nc = 1 then return (h ▸ cvk, h ▸ cp)
  else throw (IO.userError s!"the entry runs at {nc} chunks; this lane is one-chunk")

/-- The verdicts several lanes share, computed once per run: `kimchiVerify` and `sgOk` each
run the `2^k`-point `sg` MSM, and the `verify`, `theorem` and `carry` lanes ask for the same
proof's. In memory for the life of the process, so nothing outlives the proofs it was computed
on. Keyed by everything the verdict reads: the curve, the SRS round count, the entry, and the
public input by value — the `theorem` lane rebuilds the public input, and a rebuilt input that
differs from the entry's must miss rather than reuse the `verify` lane's verdict. `accOk` is
not memoised: the `carry` lane checks it against `sgOk`, which only means something when the
two are computed apart. -/
structure Memo where
  /-- `kimchiVerify`, per proof and public input. -/
  verify : IO.Ref (Std.HashMap String Bool)
  /-- `sgOk`, per proof and public input. -/
  sg : IO.Ref (Std.HashMap String Bool)

/-- A fresh memo. -/
def Memo.new : IO Memo := do
  return { verify := ← IO.mkRef {}, sg := ← IO.mkRef {} }

/-- The memo key of an entry's verdict at a public input. -/
def memoKey (C : Ipa.KimchiCurve) (name : String) (k : ℕ) (e : Cache.Entry C)
    (pub : Array C.ScalarField) : String :=
  s!"{name}/{k}/{e.vkDigest}/{e.publicInputKey}/{pub.toList.map (·.val)}"

/-- A verdict from `ref`, computed and stored on a miss. Two workers missing at once both
compute it, and agree. -/
def memoized (ref : IO.Ref (Std.HashMap String Bool)) (key : String) (compute : Unit → Bool) :
    IO Bool := do
  if let some b := (← ref.get)[key]? then return b
  let b := compute ()
  ref.modify (·.insert key b)
  return b

/-- The wire verifier on a cache entry, against the curve's SRS cut to the proof's round
count. -/
def verifies (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (memo : Memo) (e : Cache.Entry C) : IO Bool := do
  let σ ← srsAt C name sqrt loaded e.proof.opening.lr.size
  let ⟨nc, cvk, cp⟩ ← checkedAny C σ e
  let L ← basisFor C name σ nc e
  memoized memo.verify (memoKey C name σ.k e e.publicInput) fun _ =>
    Kimchi.Verifier.kimchiVerifyWith C σ cvk L cp e.publicInput

/-- An entry's SRS and key, both checked, at the key's chunk count. -/
abbrev Checked (C : Ipa.KimchiCurve) := (nc : ℕ) × Pickles.Srs C × Pickles.Key C nc

/-- An entry's checked SRS and key (`Srs.check`, `Key.check`), built once per key and handed
back for every later entry under the same key. The key is parsed at the run's chunk count
(`Wire.runNc`), which is the SRS's on its domain (`chunkCount`) by definition. -/
def keyFor (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (keys : IO.Ref (List (String × Checked C)))
    (e : Cache.Entry C) : IO (Checked C) := do
  let key := s!"{e.vkDigest}/{e.proof.opening.lr.size}/{e.publicInput.size}"
  if let some E := (← keys.get).lookup key then return E
  let σ ← srsAt C name sqrt loaded e.proof.opening.lr.size
  let ⟨nc, cvk, _⟩ ← checkedAny C σ e
  let some S := Pickles.Srs.check σ
    | throw (IO.userError "the SRS breaks an SRS invariant: there is no round or too many for \
        the absorb bound, or the blinding base is the identity")
  let some K := Pickles.Key.check cvk
    | throw (IO.userError "the key breaks a key invariant: its endo or shifts are not the \
        curve's, zk_rows is not the chunk count's or is above the domain, the generator is not \
        primitive on the domain, or its digest is not its commitments' (a commitment outside \
        the model, such as a lookup or optional gate, was absorbed)")
  keys.modify ((key, ⟨nc, S, K⟩) :: ·)
  return ⟨nc, S, K⟩

/-- An entry's checked proof at the SRS `σ` and the chunk count `nc`. -/
def checkedFor (C : Ipa.KimchiCurve) (nc : ℕ) (σ : SRS C.Point)
    (e : Cache.Entry C) : IO (Kimchi.Verifier.KimchiProof C nc σ.k) := do
  let ⟨nc', _, cp⟩ ← checkedAny C σ e
  if h : nc' = nc then return h ▸ cp
  else throw (IO.userError s!"the entry runs at {nc'} chunks, its key at {nc}")

/-- `keyFor` for a lane whose key is one chunk. -/
def keyFor1 (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (keys : IO.Ref (List (String × Checked C)))
    (e : Cache.Entry C) : IO (Pickles.Srs C × Pickles.Key C 1) := do
  let ⟨nc, S, K⟩ ← keyFor C name sqrt loaded keys e
  if h : nc = 1 then return (S, h ▸ K)
  else throw (IO.userError s!"the entry runs at {nc} chunks; this lane is one-chunk")

/-- The carry of `pred`'s deferred obligation into `succ`'s old accumulator `slot`, both on
`C`: `carry` decided on the two checked proofs, `accOk` on the accumulator, `sgOk` on `pred`,
and the last two agreeing. `carry` and `sgOk` are decided at the memoized Lagrange points
(`carryWith_lagrangePoints`, `sgOkWith_lagrangePoints`). -/
def carriesInto (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point)))
    (keys : IO.Ref (List (String × Checked C))) (memo : Memo)
    (pred succ : Cache.Entry C) (slot : ℕ) : IO Bool := do
  let ⟨nc, S, K⟩ ← keyFor C name sqrt loaded keys pred
  unless succ.proof.opening.lr.size = S.σ.k do
    throw (IO.userError s!"round counts differ: {S.σ.k} and {succ.proof.opening.lr.size}")
  let cp ← checkedFor C nc S.σ pred
  let ⟨_, _, cp'⟩ ← checkedAny C S.σ succ
  if h : slot < cp'.olds.size then
    -- `sgOk` is the predecessor's shared verdict (`memo`); `accOk` is the successor's own
    -- accumulator and stays a computation of its own, since its agreeing with `sgOk` is what
    -- the carry says
    let L ← basisFor C name S.σ nc pred
    let c := Pickles.carryWith S.σ K.cvk L cp pred.publicInput cp' ⟨slot, h⟩
    let s ← memoized memo.sg (memoKey C name S.σ.k pred pred.publicInput) fun _ =>
      Pickles.sgOkWith S.σ K.cvk L cp pred.publicInput
    let a := Pickles.accOk S.σ cp'.olds[slot]
    IO.println s!"    carry={c} accOk={a} sgOk(pred)={s}"
    return c && a && s && (s == a)
  else throw (IO.userError s!"slot {slot} beyond the {cp'.olds.size} accumulators")

/-- An unlinked old accumulator — a front pad or a base-case slot — satisfies `accOk` on its
own. -/
def padOk (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (e : Cache.Entry C) (slot : ℕ) : IO Bool := do
  let σ ← srsAt C name sqrt loaded e.proof.opening.lr.size
  let ⟨_, _, cp⟩ ← checkedAny C σ e
  if h : slot < cp.olds.size then return Pickles.accOk σ cp.olds[slot]
  else throw (IO.userError s!"slot {slot} beyond the {cp.olds.size} accumulators")

end PicklesFixture
