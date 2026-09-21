import Pickles.Curve
import Pickles.Statement
import Kimchi.Verifier.Kimchi

/-!
# The verification environment

The SRS and the verifier key of the proof under verification, with the invariants every
statement about them needs: what `kimchiVerify`, both circuit halves and both top-level
theorems share.

## Main definitions

* `Env`: the SRS, the one-chunk key and their invariants — the key's endo coefficient is the
  curve's, the domain holds its zero-knowledge rows, the generator is primitive, the round
  count's bounds, the blinding base is a finite point, the Lagrange basis is nonempty, within
  the domain, and the SRS's own (`Ipa.lagrangeBasis`);
* `Env.Invariants`, `Env.ofInvariants`: the decidable form a driver checks once per key, and
  the environment it yields;
* `Env.lagrangeRelations`: the coefficient vectors of the key's Lagrange polynomials, the
  relations a statement asks the SRS to avoid (`SRS.Avoids`).

## Main results

* `Env.lagrange_ne`: where the SRS avoids the Lagrange relations, the key's Lagrange points
  are finite points;
* `Env.avoids_lagrangeRelations_iff`, `Env.decidableAvoids`: whether it does is decided on
  the key's stored points, with no commitment recomputed.

## Implementation notes

One chunk is production's invariant for a wrap proof (PS `WrapVkChunks = 1`) and a scope
restriction for a step proof: the scalar half's circuit holds one evaluation per column.
`zk_rows` is kept generic (`zkRows_ge`), never fixed at its one-chunk value.
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

/-! ## The environment -/

/-- The verification environment: the SRS and the verifier key of the proof under
verification, at one chunk. Shared by the wire verifier and both circuit halves. -/
structure Env (C : KimchiCurve) where
  /-- The SRS (`σ.h` the blinding base, `σ.k` the round count). -/
  σ : SRS C.Point
  /-- The verifier key, one chunk. -/
  cvk : KimchiVK C 1
  /-- The key's endomorphism coefficient is the curve's: production derives it from the curve
  (`endos::<G::OtherCurve>()`), never from the key's own data. -/
  endo_eq : cvk.endo = C.endoScalar
  /-- At least three zero-knowledge rows (`zk_rows = 3` at one chunk; kept generic). -/
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
  /-- The key's domain is within the SRS. -/
  domain_le : cvk.n ≤ 2 ^ σ.k
  /-- The key's Lagrange points are the SRS's: the commitments to its domain's Lagrange
  polynomials (`Ipa.lagrangeBasis`, production's `SRS::get_lagrange_basis`), one chunk each.
  A key carries them, but they are no data of the circuit. -/
  lagrange_eq : cvk.lagrangeBasis
    = (Ipa.lagrangeBasis C σ cvk.n domain_le cvk.omega cvk.lagrangeBasis.size).map (#v[·])

/-- The environment's invariants, of an SRS and a key as data: decidable, so a driver checks
them once on what it loaded. That the generator is primitive is checked by squaring
(`isPrimitiveRoot_two_pow`); the Lagrange points by computing them from the SRS, the one costly
check. -/
def Env.Invariants {C : KimchiCurve} (σ : SRS C.Point) (cvk : KimchiVK C 1) : Prop :=
  cvk.endo = C.endoScalar ∧ 3 ≤ cvk.zkRows ∧ cvk.zkRows ≤ cvk.n ∧
    (powPow2 cvk.omega cvk.domainLog2 = 1 ∧
      (cvk.domainLog2 = 0 ∨ powPow2 cvk.omega (cvk.domainLog2 - 1) ≠ 1)) ∧
    MaxProofsVerified * σ.k < 2 ^ 128 ∧ 0 < σ.k ∧ σ.h ≠ 0 ∧
    0 < cvk.lagrangeBasis.size ∧ cvk.lagrangeBasis.size ≤ cvk.n ∧
    ∃ h : cvk.n ≤ 2 ^ σ.k, cvk.lagrangeBasis
      = (Ipa.lagrangeBasis C σ cvk.n h cvk.omega cvk.lagrangeBasis.size).map (#v[·])

instance Env.decidableInvariants {C : KimchiCurve} (σ : SRS C.Point) (cvk : KimchiVK C 1) :
    Decidable (Env.Invariants σ cvk) := by
  unfold Env.Invariants; infer_instance

/-- The environment of an SRS and a key whose invariants hold. -/
def Env.ofInvariants {C : KimchiCurve} (σ : SRS C.Point) (cvk : KimchiVK C 1)
    (h : Env.Invariants σ cvk) : Env C :=
  ⟨σ, cvk, h.1, h.2.1, h.2.2.1, isPrimitiveRoot_two_pow _ _ h.2.2.2.1.1 h.2.2.2.1.2,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.choose, h.2.2.2.2.2.2.2.2.2.choose_spec⟩

/-! ### The relations the environment's SRS avoids -/

/-- The Lagrange relations of an environment: the coefficient vectors of the key's Lagrange
polynomials, which its Lagrange points are the commitments to. -/
def Env.lagrangeRelations {C : KimchiCurve} (E : Env C) :
    List (Fin (2 ^ E.σ.k) → C.ScalarField) :=
  (List.range E.cvk.lagrangeBasis.size).map (lagrangeCoeffs E.σ.k E.cvk.n E.cvk.omega)

theorem Env.lagrangeBasis_toList {C : KimchiCurve} (E : Env C) :
    E.cvk.lagrangeBasis.toList = E.lagrangeRelations.map fun a => #v[msm C E.σ.g a] := by
  apply List.ext_getElem?
  intro i
  rw [Array.getElem?_toList, E.lagrange_eq]
  by_cases hi : i < E.cvk.lagrangeBasis.size
  · have hs : i < (Ipa.lagrangeBasis C E.σ E.cvk.n E.domain_le E.cvk.omega
        E.cvk.lagrangeBasis.size).size := by simpa [Ipa.lagrangeBasis] using hi
    simp [Env.lagrangeRelations, hi, hs, getElem_lagrangeBasis]
  · simp [Env.lagrangeRelations, Ipa.lagrangeBasis, hi]

theorem Env.natCast_n_ne_zero {C : KimchiCurve} (s : PastaShape C) (E : Env C) :
    ((E.cvk.n : ℕ) : C.ScalarField) ≠ 0 := by
  rw [KimchiVK.n]
  push_cast
  exact pow_ne_zero _ s.scalar_two_ne

/-- The Lagrange points are finite points, where the SRS avoids their relations. -/
theorem Env.lagrange_ne {C : KimchiCurve} (s : PastaShape C) (E : Env C)
    (h : E.σ.Avoids E.lagrangeRelations) :
    ∀ Ps ∈ E.cvk.lagrangeBasis.toList, Ps[(0 : Fin 1)] ≠ 0 := by
  rw [E.lagrangeBasis_toList]
  intro Ps hPs
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hPs
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
  simpa using h _ ha (lagrangeCoeffs_ne_zero _ _ _ _ (by rw [KimchiVK.n]; positivity)
    (E.natCast_n_ne_zero s))

/-- Whether the SRS avoids the Lagrange relations, read off the key: their commitments are the
key's Lagrange points (`lagrange_eq`), so none is the identity iff no point is. -/
theorem Env.avoids_lagrangeRelations_iff {C : KimchiCurve} (s : PastaShape C) (E : Env C) :
    E.σ.Avoids E.lagrangeRelations
      ↔ ∀ Ps ∈ E.cvk.lagrangeBasis.toList, Ps[(0 : Fin 1)] ≠ 0 := by
  refine ⟨E.lagrange_ne s, fun h a ha _ => ?_⟩
  have := h #v[msm C E.σ.g a] (by rw [E.lagrangeBasis_toList]; exact List.mem_map.2 ⟨a, ha, rfl⟩)
  simpa using this

/-- Decided on the key's points, with no commitment recomputed. The bounded `∀` is pinned to
the list walk: left to resolution it goes to `Vector`'s finite-type instance, which decides it
by enumerating the curve. -/
def Env.decidableAvoids {C : KimchiCurve} (s : PastaShape C) (E : Env C) :
    Decidable (E.σ.Avoids E.lagrangeRelations) :=
  haveI : Decidable (∀ Ps ∈ E.cvk.lagrangeBasis.toList, Ps[(0 : Fin 1)] ≠ 0) :=
    List.decidableBAll _ _
  decidable_of_iff _ (E.avoids_lagrangeRelations_iff s).symm

end Pickles
