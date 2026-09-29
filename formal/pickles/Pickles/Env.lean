import Pickles.Curve
import Pickles.Statement
import Pickles.VkComms
import Kimchi.Columns
import Kimchi.Verifier.Kimchi

/-!
# The SRS and the key

The SRS and a verifier key as the verifiers read them, each with its own facts, and the one fact
that joins them: the key's chunk count is the run's at the SRS (`chunkCount`). What
`kimchiVerify`, both circuit halves and both top-level theorems share.

## Main definitions

* `Srs`: the SRS, its round count positive and within the absorb bound, its blinding base
  finite;
* `Key`: a key at `nc` chunks, at least one, its endo coefficient, shifts and generator the
  curve's, its domain one of the field, its zero-knowledge rows the chunk count's and within the
  domain, its digest its commitments' (`KimchiVK.indexDigest`);
* `Srs.check`, `Key.check`: the decidable forms a driver checks once per SRS and per key;
* `KimchiVK.indexState`, `KimchiVK.indexDigest`: the fq-sponge after the key's commitments,
  and its squeeze, the verifier-index digest;
* `KimchiVK.lagrangeRelations`: the coefficient vectors of the chunks of the key's first `m`
  Lagrange polynomials, the relations a statement asks the SRS to avoid (`SRS.Avoids`).

## Main results

* `Key.omega_prim`, `three_le_zkRowsOf`: the generator is primitive on the domain, and there are
  at least three zero-knowledge rows at any positive chunk count;
* `Key.chunk_lt`, `Key.chunk_add_le`: at the run's chunk count, every chunk starts within the
  domain and holds `min (2^k) n` of its points;
* `Key.lagrange_ne`: where the SRS avoids the Lagrange relations, every chunk of the key's
  first `m` Lagrange points (`KimchiVK.lagrangePoints`) is a finite point;
* `Key.avoids_lagrangeRelations_iff`: whether it does is read off the Lagrange points.

## Implementation notes

The chunk count is a parameter of the key, pinned to the run's by a hypothesis where a statement
needs it (`chunkCount`): one chunk for a domain within the SRS, `n / 2^k` above it. One chunk is
production's invariant for a wrap proof; a step proof may be chunked. The zero-knowledge row
count is the chunk count's (`zkRows_eq`), never fixed at its one-chunk value.
-/

namespace Pickles

open Kimchi.Verifier Bulletproof Bulletproof.Ipa
open scoped Kimchi

/-! ## Primitivity -/

/-- A domain generator within the field's two-adicity is a primitive root of its domain's size:
the root of unity, of order `2 ^ twoAdicity`, squared `twoAdicity − log2` times. -/
private theorem isPrimitiveRoot_domainGenerator (C : KimchiCurve) {log2 : ℕ}
    (hl : log2 ≤ C.twoAdicity) : IsPrimitiveRoot (domainGenerator C log2) (2 ^ log2) := by
  have hr : IsPrimitiveRoot C.rootOfUnity (2 ^ C.twoAdicity) := by
    rw [← C.rootOfUnity_order]
    exact IsPrimitiveRoot.orderOf _
  have h := hr.pow_of_dvd (p := 2 ^ (C.twoAdicity - log2)) (by positivity)
    (Nat.pow_dvd_pow 2 (Nat.sub_le _ _))
  rw [Nat.pow_div (Nat.sub_le _ _) two_pos, Nat.sub_sub_self hl, ← powPow2_eq] at h
  exact h

/-! ## The key's digest -/

section Digest

variable {C : KimchiCurve} {nc : ℕ}

/-- A key's commitments as the record the circuit reads them in. -/
def _root_.Kimchi.Verifier.KimchiVK.comms (cvk : KimchiVK C nc) : VkComms nc C.Point :=
  ⟨cvk.sigmaComm, cvk.coefficientsComm, cvk.genericComm, cvk.poseidonComm, cvk.completeAddComm,
    cvk.mulComm, cvk.emulComm, cvk.endomulScalarComm⟩

/-- The fq-sponge after the key: its commitments' coordinates absorbed from the fresh sponge,
in `VkComms.indexPoints` order. -/
def _root_.Kimchi.Verifier.KimchiVK.indexState (cvk : KimchiVK C nc) :
    Poseidon.State C.BaseField :=
  Poseidon.absorb C.sponge.params Poseidon.init
    (cvk.comms.indexPoints.flatMap fun P => [P.x, P.y])

/-- The verifier-index digest recomputed from the key: `VerifierIndex::digest` on the
modeled fragment's commitments, the squeeze of `indexState`. -/
def _root_.Kimchi.Verifier.KimchiVK.indexDigest (cvk : KimchiVK C nc) : C.BaseField :=
  (Poseidon.squeeze C.sponge.params cvk.indexState).1

end Digest

/-! ## The key's Lagrange relations -/

section Relations

variable {C : KimchiCurve} {nc : ℕ}

/-- The Lagrange relations of a key at `m` points over an SRS of `2 ^ k` points: the coefficient
vectors of every chunk of its first `m` Lagrange polynomials, which its Lagrange points are the
commitments to. -/
def _root_.Kimchi.Verifier.KimchiVK.lagrangeRelations (cvk : KimchiVK C nc) (k m : ℕ) :
    List (Fin (2 ^ k) → C.ScalarField) :=
  (List.range m).flatMap fun i =>
    (List.finRange nc).map fun c : Fin nc => lagrangeCoeffs k cvk.n cvk.omega i c.val

/-- A key's Lagrange points are the commitments to its Lagrange relations, chunk by chunk. -/
theorem _root_.Kimchi.Verifier.KimchiVK.lagrangePoints_toList (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (m : ℕ) :
    (cvk.lagrangePoints σ m).toList = (List.range m).map fun i =>
      Vector.ofFn fun c : Fin nc => msm C σ.g (lagrangeCoeffs σ.k cvk.n cvk.omega i c) := by
  apply List.ext_getElem (by simp)
  intro i h₁ _
  have hs : i < (Ipa.lagrangeBasis C σ nc cvk.n cvk.omega m).size := by
    simpa [Ipa.lagrangeBasis] using h₁
  rw [Array.getElem_toList, List.getElem_map, List.getElem_range]
  ext c hc
  rw [Vector.getElem_ofFn]
  exact getElem_lagrangeBasis C σ nc cvk.n cvk.omega _ i hs ⟨c, hc⟩

end Relations

/-! ## The SRS -/

/-- The SRS as the verifiers read it: a round count with a round to absorb and within the absorb
bound across every slot, and a finite blinding base. -/
structure Srs (C : KimchiCurve) where
  /-- The SRS (`σ.h` the blinding base, `σ.k` the round count). -/
  σ : SRS C.Point
  /-- The round count is a round count: every slot's challenges together stay far below the
  128-bit absorb bound. -/
  rounds_small : MaxProofsVerified * σ.k < 2 ^ 128
  /-- There is a round: an opening has an `(L, R)` pair to absorb. -/
  rounds_pos : 0 < σ.k
  /-- The blinding base is a finite point. At the `(0, 0)` sentinel no cell reads as it
  (`onCurveAt_constPt`'s converse), so every statement over cells already assumed this. -/
  h_ne : σ.h ≠ 0

/-- The SRS's facts, decided: a driver checks them once per SRS it loads. -/
def Srs.check {C : KimchiCurve} (σ : SRS C.Point) : Option (Srs C) :=
  if h : MaxProofsVerified * σ.k < 2 ^ 128 ∧ 0 < σ.k ∧ σ.h ≠ 0 then
    some ⟨σ, h.1, h.2.1, h.2.2⟩
  else none

/-! ## The key -/

/-- The zero-knowledge row count at `nc` chunks: the least count strictly above the
zero-knowledge bound, three at one chunk. -/
def zkRowsOf (nc : ℕ) : ℕ := (2 * (permCols + 1) * nc - 2) / permCols + 1

/-- At least three zero-knowledge rows, at any positive chunk count. -/
theorem three_le_zkRowsOf {nc : ℕ} (h : 0 < nc) : 3 ≤ zkRowsOf nc := by
  rw [zkRowsOf]
  omega

/-- A verifier key at `nc` chunks as the verifiers read it: there is a chunk, the endomorphism
coefficient, permutation shifts and generator are the curve's, the domain is one of the field,
the digest is the key's commitments', and the zero-knowledge rows are the chunk count's and fit
in the domain. -/
structure Key (C : KimchiCurve) (nc : ℕ) where
  /-- The verifier key, at `nc` chunks. -/
  cvk : KimchiVK C nc
  /-- There is a chunk. -/
  nc_pos : 0 < nc
  /-- The key's endomorphism coefficient is the curve's: production derives it from the curve,
  never from the key's own data. -/
  endo_eq : cvk.endo = C.endoScalar
  /-- The zero-knowledge rows are the chunk count's: the least count strictly above the
  zero-knowledge bound at `nc` chunks, three at one chunk. -/
  zkRows_eq : cvk.zkRows = zkRowsOf nc
  /-- The key's domain holds its zero-knowledge rows. -/
  zkRows_le : cvk.zkRows ≤ cvk.n
  /-- The key's domain is one of the scalar field: its exponent is at most the two-adicity. -/
  domainLog2_le : cvk.domainLog2 ≤ C.twoAdicity
  /-- The key's digest is its commitments' (`KimchiVK.indexDigest`): the verifier takes the
  digest as an input, and production computes it from the key. -/
  digest_eq : cvk.digest = cvk.indexDigest
  /-- The key's generator is its domain's (`domainGenerator`): a constant of the scalar field,
  never chosen by the key. -/
  omega_eq : cvk.omega = domainGenerator C cvk.domainLog2
  /-- The key's permutation shifts are the curve's (`KimchiCurve.shifts`): no key chooses
  them. -/
  shifts_eq : cvk.shifts = C.shifts

/-- The key's facts, decided: a driver checks them once per key it loads. -/
def Key.check {C : KimchiCurve} {nc : ℕ} (cvk : KimchiVK C nc) : Option (Key C nc) :=
  if h : 0 < nc ∧ cvk.endo = C.endoScalar ∧
      cvk.zkRows = zkRowsOf nc ∧ cvk.zkRows ≤ cvk.n ∧
      cvk.domainLog2 ≤ C.twoAdicity ∧ cvk.digest = cvk.indexDigest ∧
      cvk.omega = domainGenerator C cvk.domainLog2 ∧ cvk.shifts = C.shifts then
    some ⟨cvk, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2⟩
  else none

namespace Key

variable {C : KimchiCurve} {nc : ℕ} (K : Key C nc)

/-- The key's generator generates its domain: it is its domain's generator within the field's
two-adicity (`isPrimitiveRoot_domainGenerator`). -/
theorem omega_prim : IsPrimitiveRoot K.cvk.omega K.cvk.n :=
  K.omega_eq ▸ isPrimitiveRoot_domainGenerator C K.domainLog2_le

theorem natCast_n_ne_zero (s : PastaShape C) : ((K.cvk.n : ℕ) : C.ScalarField) ≠ 0 := by
  rw [KimchiVK.n]
  push_cast
  exact pow_ne_zero _ s.scalar_two_ne

/-! ### The key's chunks over an SRS

The chunk count is the run's at an SRS of `2 ^ k` points (`chunkCount`): one chunk for a domain
within the SRS, `n / 2^k` above it. It is the one fact joining the key to the SRS. -/

section Chunks

variable {K} {k : ℕ} (hnc : nc = chunkCount k K.cvk.domainLog2)
include hnc

/-- The chunk count is at most the domain size. -/
theorem nc_le_n : nc ≤ K.cvk.n := by
  refine hnc.trans_le ?_
  rw [chunkCount, KimchiVK.n]
  split_ifs
  · exact Nat.one_le_two_pow
  · exact Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)

/-- Every chunk meets the domain: chunk `c` starts below `n`. -/
theorem chunk_lt (c : Fin nc) : c.val * 2 ^ k < K.cvk.n := by
  have hc : c.val < chunkCount k K.cvk.domainLog2 := hnc ▸ c.isLt
  rw [chunkCount] at hc
  rw [KimchiVK.n]
  split_ifs at hc with h
  · rw [Nat.lt_one_iff.1 hc, zero_mul]
    positivity
  · calc c.val * 2 ^ k < 2 ^ (K.cvk.domainLog2 - k) * 2 ^ k :=
          Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = 2 ^ K.cvk.domainLog2 := by rw [← pow_add, Nat.sub_add_cancel (not_lt.1 h)]

/-- Every chunk holds `min (2^k) n` domain points: the domain's points from chunk `c`'s start
on number at least the SRS size, or the whole domain at one chunk. -/
theorem chunk_add_le (c : Fin nc) : c.val * 2 ^ k + min (2 ^ k) K.cvk.n ≤ K.cvk.n := by
  have hc : c.val < chunkCount k K.cvk.domainLog2 := hnc ▸ c.isLt
  rw [chunkCount] at hc
  rw [KimchiVK.n]
  split_ifs at hc with h
  · rw [Nat.lt_one_iff.1 hc, zero_mul, Nat.zero_add]
    exact Nat.min_le_right _ _
  · calc c.val * 2 ^ k + min (2 ^ k) (2 ^ K.cvk.domainLog2)
        ≤ (c.val + 1) * 2 ^ k := by rw [Nat.succ_mul]; omega
      _ ≤ 2 ^ (K.cvk.domainLog2 - k) * 2 ^ k :=
          Nat.mul_le_mul_right _ hc
      _ = 2 ^ K.cvk.domainLog2 := by rw [← pow_add, Nat.sub_add_cancel (not_lt.1 h)]

end Chunks

/-! ### The relations the SRS avoids -/

variable {K}

/-- Every chunk of the key's first `m` Lagrange points is a finite point, where the SRS avoids
their relations. -/
theorem lagrange_ne (s : PastaShape C) (σ : SRS C.Point)
    (hnc : nc = chunkCount σ.k K.cvk.domainLog2) {m : ℕ}
    (h : σ.Avoids (K.cvk.lagrangeRelations σ.k m)) :
    ∀ Ps ∈ (K.cvk.lagrangePoints σ m).toList, ∀ c : Fin nc, Ps[c] ≠ 0 := by
  rw [K.cvk.lagrangePoints_toList]
  intro Ps hPs c
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hPs
  have ha : lagrangeCoeffs σ.k K.cvk.n K.cvk.omega i c ∈ K.cvk.lagrangeRelations σ.k m :=
    List.mem_flatMap.2 ⟨i, hi, List.mem_map.2 ⟨c, List.mem_finRange c, rfl⟩⟩
  simpa using h _ ha (lagrangeCoeffs_ne_zero _ _ _ _ _ (chunk_lt hnc c)
    (K.omega_prim.ne_zero (by rw [KimchiVK.n]; positivity)) (K.natCast_n_ne_zero s))

/-- Whether the SRS avoids the Lagrange relations, read off the Lagrange points: their
commitments are the points' chunks, so none is the identity iff no chunk is. A driver decides the
right side on points it computed once. -/
theorem avoids_lagrangeRelations_iff (s : PastaShape C) (σ : SRS C.Point)
    (hnc : nc = chunkCount σ.k K.cvk.domainLog2) (m : ℕ) :
    σ.Avoids (K.cvk.lagrangeRelations σ.k m)
      ↔ ∀ Ps ∈ (K.cvk.lagrangePoints σ m).toList, ∀ c : Fin nc, Ps[c] ≠ 0 := by
  refine ⟨lagrange_ne s σ hnc, fun h a ha _ => ?_⟩
  obtain ⟨i, hi, hai⟩ := List.mem_flatMap.1 ha
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hai
  have := h (Vector.ofFn fun c : Fin nc =>
      msm C σ.g (lagrangeCoeffs σ.k K.cvk.n K.cvk.omega i c))
    (by rw [K.cvk.lagrangePoints_toList]; exact List.mem_map.2 ⟨i, hi, rfl⟩) c
  simpa using this

end Key

end Pickles
