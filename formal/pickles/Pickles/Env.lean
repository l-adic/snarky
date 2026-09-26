import Pickles.Curve
import Pickles.Statement
import Pickles.VkComms
import Kimchi.Verifier.Kimchi

/-!
# The verification environment

The SRS and the verifier key of the proof under verification, with the invariants every
statement about them needs: what `kimchiVerify`, both circuit halves and both top-level
theorems share.

## Main definitions

* `Env`: the SRS, the key at `nc` chunks and their invariants — the key's endo coefficient is
  the curve's, the domain holds its zero-knowledge rows, the generator is primitive, the round
  count's bounds, the blinding base is a finite point, `nc` is the run's chunk count, the
  Lagrange basis is nonempty, within the domain, and the SRS's own (`Ipa.lagrangeBasis`), and
  the digest is the key's (`KimchiVK.indexDigest`);
* `KimchiVK.indexState`, `KimchiVK.indexDigest`: the fq-sponge after the key's commitments,
  and its squeeze, the verifier-index digest;
* `Env.Invariants`, `Env.ofInvariants`: the decidable form a driver checks once per key, and
  the environment it yields;
* `Env.lagrangeRelations`: the coefficient vectors of the key's Lagrange polynomials' chunks,
  the relations a statement asks the SRS to avoid (`SRS.Avoids`).

## Main results

* `Env.chunk_lt`, `Env.chunk_add_le`: every chunk starts within the domain and holds
  `min (2^k) n` of its points;
* `Env.lagrange_ne`: where the SRS avoids the Lagrange relations, every chunk of the key's
  Lagrange points is a finite point;
* `Env.avoids_lagrangeRelations_iff`, `Env.decidableAvoids`: whether it does is decided on
  the key's stored points, with no commitment recomputed.

## Implementation notes

The chunk count is a parameter, pinned to the run's (`nc_eq`, `Wire.runNc`): one chunk for a
domain within the SRS, `n / 2^k` above it. One chunk is production's invariant for a wrap
proof; a step proof may be chunked. The zero-knowledge row count is kept generic
(`zkRows_ge`), never fixed at its one-chunk value.
-/

namespace Pickles

open Kimchi.Verifier Bulletproof Bulletproof.Ipa

/-! ## Primitivity, runnable -/

/-- An element of order dividing `2 ^ d` and not `2 ^ (d - 1)` is a primitive `2 ^ d`-th root:
primitivity by two runs of squarings (`powPow2`). -/
private theorem isPrimitiveRoot_two_pow {F : Type*} [Field F] (g : F) (d : ℕ)
    (h1 : powPow2 g d = 1) (h2 : d = 0 ∨ powPow2 g (d - 1) ≠ 1) :
    IsPrimitiveRoot g (2 ^ d) := by
  rw [powPow2_eq] at h1
  cases d with
  | zero =>
      obtain rfl : g = 1 := by simpa using h1
      simp
  | succ d =>
      have h2' : ¬g ^ 2 ^ d = 1 := by simpa [powPow2_eq] using h2
      rw [← orderOf_eq_prime_pow h2' h1]
      exact IsPrimitiveRoot.orderOf g

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

/-! ## The environment -/

/-- The verification environment: the SRS and the verifier key of the proof under
verification, at `nc` chunks. Shared by the wire verifier and both circuit halves. -/
structure Env (C : KimchiCurve) (nc : ℕ) where
  /-- The SRS (`σ.h` the blinding base, `σ.k` the round count). -/
  σ : SRS C.Point
  /-- The verifier key, at `nc` chunks. -/
  cvk : KimchiVK C nc
  /-- The key's endomorphism coefficient is the curve's: production derives it from the curve,
  never from the key's own data. -/
  endo_eq : cvk.endo = C.endoScalar
  /-- At least three zero-knowledge rows (exactly three at one chunk; kept generic). -/
  zkRows_ge : 3 ≤ cvk.zkRows
  /-- The key's domain holds its zero-knowledge rows. -/
  zkRows_le : cvk.zkRows ≤ cvk.n
  /-- The key's generator generates its domain. -/
  omega_prim : IsPrimitiveRoot cvk.omega cvk.n
  /-- The round count is a round count: every slot's challenges together stay far below the
  128-bit absorb bound. -/
  rounds_small : MaxProofsVerified * σ.k < 2 ^ 128
  /-- There is a round: an opening has an `(L, R)` pair to absorb. -/
  rounds_pos : 0 < σ.k
  /-- The blinding base is a finite point. At the `(0, 0)` sentinel no cell reads as it
  (`onCurveAt_constPt`'s converse), so every statement over cells already assumed this. -/
  h_ne : σ.h ≠ 0
  /-- There is a Lagrange basis: a key with none commits to no public input. -/
  lagrange_pos : 0 < cvk.lagrangeBasis.size
  /-- The Lagrange basis is within the domain: a public input is a segment of a column. -/
  lagrange_le : cvk.lagrangeBasis.size ≤ cvk.n
  /-- The chunk count is the run's (`Wire.runNc`): one chunk for a domain below the SRS, the
  domain's multiple of the SRS otherwise. -/
  nc_eq : nc = if cvk.domainLog2 < σ.k then 1 else 2 ^ (cvk.domainLog2 - σ.k)
  /-- The key's Lagrange points are the SRS's: the chunked commitments to its domain's
  Lagrange polynomials (`Ipa.lagrangeBasis`). A key carries them, but they are no data of the
  circuit. -/
  lagrange_eq : cvk.lagrangeBasis = Ipa.lagrangeBasis C σ nc cvk.n cvk.omega cvk.lagrangeBasis.size
  /-- The key's digest is its commitments' (`KimchiVK.indexDigest`): the verifier takes the
  digest as an input, and production computes it from the key. -/
  digest_eq : cvk.digest = cvk.indexDigest
  /-- The key's generator is its domain's (`domainGenerator`): a constant of the scalar field,
  never chosen by the key. -/
  omega_eq : cvk.omega = domainGenerator C cvk.domainLog2

/-- The environment's invariants, of an SRS and a key as data: decidable, so a driver checks
them once on what it loaded. That the generator is primitive is checked by squaring
(`isPrimitiveRoot_two_pow`); the Lagrange points by computing them from the SRS, the one costly
check. -/
def Env.Invariants {C : KimchiCurve} {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) :
    Prop :=
  cvk.endo = C.endoScalar ∧ 3 ≤ cvk.zkRows ∧ cvk.zkRows ≤ cvk.n ∧
    (powPow2 cvk.omega cvk.domainLog2 = 1 ∧
      (cvk.domainLog2 = 0 ∨ powPow2 cvk.omega (cvk.domainLog2 - 1) ≠ 1)) ∧
    MaxProofsVerified * σ.k < 2 ^ 128 ∧ 0 < σ.k ∧ σ.h ≠ 0 ∧
    0 < cvk.lagrangeBasis.size ∧ cvk.lagrangeBasis.size ≤ cvk.n ∧
    nc = (if cvk.domainLog2 < σ.k then 1 else 2 ^ (cvk.domainLog2 - σ.k)) ∧
    cvk.lagrangeBasis = Ipa.lagrangeBasis C σ nc cvk.n cvk.omega cvk.lagrangeBasis.size ∧
    cvk.digest = cvk.indexDigest ∧ cvk.omega = domainGenerator C cvk.domainLog2

instance Env.decidableInvariants {C : KimchiCurve} {nc : ℕ} (σ : SRS C.Point)
    (cvk : KimchiVK C nc) :
    Decidable (Env.Invariants σ cvk) := by
  unfold Env.Invariants; infer_instance

/-- The environment of an SRS and a key whose invariants hold. -/
def Env.ofInvariants {C : KimchiCurve} {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (h : Env.Invariants σ cvk) : Env C nc :=
  ⟨σ, cvk, h.1, h.2.1, h.2.2.1, isPrimitiveRoot_two_pow _ _ h.2.2.2.1.1 h.2.2.2.1.2,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- There is a chunk. -/
theorem Env.nc_pos {C : KimchiCurve} {nc : ℕ} (E : Env C nc) : 0 < nc := by
  have h : 0 < (if E.cvk.domainLog2 < E.σ.k then 1 else 2 ^ (E.cvk.domainLog2 - E.σ.k)) := by
    split_ifs <;> positivity
  rwa [← E.nc_eq] at h

/-- The chunk count is at most the domain size. -/
theorem Env.nc_le_n {C : KimchiCurve} {nc : ℕ} (E : Env C nc) : nc ≤ E.cvk.n := by
  have h : (if E.cvk.domainLog2 < E.σ.k then 1 else 2 ^ (E.cvk.domainLog2 - E.σ.k))
      ≤ E.cvk.n := by
    rw [KimchiVK.n]
    split_ifs
    · exact Nat.one_le_two_pow
    · exact Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)
  rwa [← E.nc_eq] at h

/-- Every chunk meets the domain: chunk `c` starts below `n`. -/
theorem Env.chunk_lt {C : KimchiCurve} {nc : ℕ} (E : Env C nc) (c : Fin nc) :
    c.val * 2 ^ E.σ.k < E.cvk.n := by
  have hc : c.val < (if E.cvk.domainLog2 < E.σ.k then 1
      else 2 ^ (E.cvk.domainLog2 - E.σ.k)) := E.nc_eq ▸ c.isLt
  rw [KimchiVK.n]
  split_ifs at hc with h
  · rw [Nat.lt_one_iff.1 hc, zero_mul]
    positivity
  · calc c.val * 2 ^ E.σ.k < 2 ^ (E.cvk.domainLog2 - E.σ.k) * 2 ^ E.σ.k :=
          Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = 2 ^ E.cvk.domainLog2 := by rw [← pow_add, Nat.sub_add_cancel (not_lt.1 h)]

/-- Every chunk holds `min (2^k) n` domain points: the domain's points from chunk `c`'s start
on number at least the SRS size, or the whole domain at one chunk. -/
theorem Env.chunk_add_le {C : KimchiCurve} {nc : ℕ} (E : Env C nc) (c : Fin nc) :
    c.val * 2 ^ E.σ.k + min (2 ^ E.σ.k) E.cvk.n ≤ E.cvk.n := by
  have hc : c.val < (if E.cvk.domainLog2 < E.σ.k then 1
      else 2 ^ (E.cvk.domainLog2 - E.σ.k)) := E.nc_eq ▸ c.isLt
  rw [KimchiVK.n]
  split_ifs at hc with h
  · rw [Nat.lt_one_iff.1 hc, zero_mul, Nat.zero_add]
    exact Nat.min_le_right _ _
  · calc c.val * 2 ^ E.σ.k + min (2 ^ E.σ.k) (2 ^ E.cvk.domainLog2)
        ≤ (c.val + 1) * 2 ^ E.σ.k := by rw [Nat.succ_mul]; omega
      _ ≤ 2 ^ (E.cvk.domainLog2 - E.σ.k) * 2 ^ E.σ.k :=
          Nat.mul_le_mul_right _ hc
      _ = 2 ^ E.cvk.domainLog2 := by rw [← pow_add, Nat.sub_add_cancel (not_lt.1 h)]

/-! ### The relations the environment's SRS avoids -/

/-- The Lagrange relations of an environment: the coefficient vectors of every chunk of the
key's Lagrange polynomials, which its Lagrange points are the commitments to. -/
def Env.lagrangeRelations {C : KimchiCurve} {nc : ℕ} (E : Env C nc) :
    List (Fin (2 ^ E.σ.k) → C.ScalarField) :=
  (List.range E.cvk.lagrangeBasis.size).flatMap fun i =>
    (List.finRange nc).map fun c : Fin nc => lagrangeCoeffs E.σ.k E.cvk.n E.cvk.omega i c.val

/-- The key's Lagrange points are the commitments to the Lagrange relations, chunk by
chunk. -/
theorem Env.lagrangeBasis_toList {C : KimchiCurve} {nc : ℕ} (E : Env C nc) :
    E.cvk.lagrangeBasis.toList = (List.range E.cvk.lagrangeBasis.size).map fun i =>
      Vector.ofFn fun c : Fin nc => msm C E.σ.g (lagrangeCoeffs E.σ.k E.cvk.n E.cvk.omega i c) := by
  conv_lhs => rw [E.lagrange_eq]
  apply List.ext_getElem (by simp [Ipa.lagrangeBasis])
  intro i h₁ _
  have hs : i < (Ipa.lagrangeBasis C E.σ nc E.cvk.n E.cvk.omega
      E.cvk.lagrangeBasis.size).size := by simpa using h₁
  rw [Array.getElem_toList, List.getElem_map, List.getElem_range]
  ext c hc
  rw [Vector.getElem_ofFn]
  exact getElem_lagrangeBasis C E.σ nc E.cvk.n E.cvk.omega _ i hs ⟨c, hc⟩

theorem Env.natCast_n_ne_zero {C : KimchiCurve} {nc : ℕ} (s : PastaShape C) (E : Env C nc) :
    ((E.cvk.n : ℕ) : C.ScalarField) ≠ 0 := by
  rw [KimchiVK.n]
  push_cast
  exact pow_ne_zero _ s.scalar_two_ne

/-- Every chunk of the Lagrange points is a finite point, where the SRS avoids their
relations. -/
theorem Env.lagrange_ne {C : KimchiCurve} {nc : ℕ} (s : PastaShape C) (E : Env C nc)
    (h : E.σ.Avoids E.lagrangeRelations) :
    ∀ Ps ∈ E.cvk.lagrangeBasis.toList, ∀ c : Fin nc, Ps[c] ≠ 0 := by
  rw [E.lagrangeBasis_toList]
  intro Ps hPs c
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hPs
  have ha : lagrangeCoeffs E.σ.k E.cvk.n E.cvk.omega i c ∈ E.lagrangeRelations :=
    List.mem_flatMap.2 ⟨i, hi, List.mem_map.2 ⟨c, List.mem_finRange c, rfl⟩⟩
  simpa using h _ ha (lagrangeCoeffs_ne_zero _ _ _ _ _ (E.chunk_lt c)
    (E.omega_prim.ne_zero (by rw [KimchiVK.n]; positivity)) (E.natCast_n_ne_zero s))

/-- Whether the SRS avoids the Lagrange relations, read off the key: their commitments are the
key's Lagrange points' chunks (`lagrange_eq`), so none is the identity iff no chunk is. -/
theorem Env.avoids_lagrangeRelations_iff {C : KimchiCurve} {nc : ℕ} (s : PastaShape C)
    (E : Env C nc) :
    E.σ.Avoids E.lagrangeRelations
      ↔ ∀ Ps ∈ E.cvk.lagrangeBasis.toList, ∀ c : Fin nc, Ps[c] ≠ 0 := by
  refine ⟨E.lagrange_ne s, fun h a ha _ => ?_⟩
  obtain ⟨i, hi, hai⟩ := List.mem_flatMap.1 ha
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hai
  have := h (Vector.ofFn fun c : Fin nc =>
      msm C E.σ.g (lagrangeCoeffs E.σ.k E.cvk.n E.cvk.omega i c))
    (by rw [E.lagrangeBasis_toList]; exact List.mem_map.2 ⟨i, hi, rfl⟩) c
  simpa using this

/-- Decided on the key's points, with no commitment recomputed. The bounded `∀` is pinned to
the list walk: left to resolution it goes to `Vector`'s finite-type instance, which decides it
by enumerating the curve. -/
def Env.decidableAvoids {C : KimchiCurve} {nc : ℕ} (s : PastaShape C) (E : Env C nc) :
    Decidable (E.σ.Avoids E.lagrangeRelations) :=
  haveI : Decidable (∀ Ps ∈ E.cvk.lagrangeBasis.toList, ∀ c : Fin nc, Ps[c] ≠ 0) :=
    List.decidableBAll _ _
  decidable_of_iff _ (E.avoids_lagrangeRelations_iff s).symm

end Pickles
