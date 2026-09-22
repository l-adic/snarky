import CompElliptic.Curves.Pasta
import CompElliptic.Curves.Pasta.Fast.MsmProj
import CompElliptic.Curves.Pasta.Fast.MsmProjPallas
import Pasta.Shifted
import Pasta.Endo
import Poseidon.GroupMap
import Bulletproof.Protocol

/-!
# The executable kimchi IPA verifier, over checked records

The batched IPA opening verifier of kimchi (`SRS::verify`, proof-systems
`poly-commitment/src/ipa.rs`), composed as one executable function over a *checked* claim:
the per-polynomial commitments, evaluation points and claimed evaluations, the combination
scalars, and the opening proof, against a separately supplied SRS (`Bulletproof.SRS`).
It strengthens production's acceptance test in two declared places: the round-count pin of
the checked records, and the final check as a conjunction (*What `verify` checks*).

Everything transcript-derived — the `U` base, the round challenges, the Schnorr challenge —
is recomputed here through the sponge layer of the `poseidon` package; nothing is taken as
input that the wire protocol does not carry. In particular the abstract SRS's randomisation
base `σ.U` is never read: the deployed protocol derives `U` from the transcript, and relating
the derived base to the abstract one is exactly the Fiat–Shamir assumption's junction.

## The checked records carry their shape in their types

`Proof C k` pins the round count (`lr` is a `Vector` of length `k`, the SRS's `σ.k`), and
`Input C k m p` pins the batch shape: `m` rows, `p` evaluation points, and the
claimed-evaluation matrix a `Vector` of `Vector`s. Every read of the verifier, and of every
statement over it, is total — a checked input cannot hold a ragged claim.

The raw serde records (`Wire.Proof`, `Wire.Input`, every payload a `Vec`) live in the `Wire`
namespace below with their `check` parses. Those parses state this verifier's totality
requirements — the round count, and `evals` square against the commitments and points — as a
total parse, so the parse *is* the proof. Clients compose check-then-verify.

Production's `SRS::verify` carries no such explicit guards; its `Vec` payloads feed the
transcript and the batched MSM equations as they are. An oversized `lr` panics, and an
undersized `lr` whose claim is committed over the SRS prefix is accepted. The round-count pin
here is therefore a declared modeling *strengthening* rather than the transcription of a
production check (external-audit W-F3). In the kimchi composition, exploiting that corner
against a `Corresponds`-satisfying key requires a discrete-log break, so the endpoint
exposure is priced.

## The curve bundle

Generic over a single `CommitmentCurve` bundle — the Lean analogue of the Rust
`G: CommitmentCurve` associated types: the base and scalar cardinalities with their primality
facts, the sponge spec, the curve `E`, and the map-to-curve. The bundle carries *facts*, not
structures: the field structures are the canonical `ZMod` instances synthesized from
primality, so the executable and abstract layers cannot disagree on any field operation.
Points are the library's `SWPoint E` (`Point`), so the group structure is inherited — `+`/`0`
and the binary-nsmul scalar action from CompElliptic's `AddCommGroup` instance, point
equality from its `DecidableEq`.

The scalar side reuses the `Bulletproof` definitions (`bPoly`, `bPolyCoefficients`,
`combinedB`, `combinedInnerProduct`) at the concrete scalar field. Scalars act on points as
`z.val • _`, the ℕ-action of the group; `Bulletproof.Reflection` relates this verifier to the
`Prop`-level `BatchAccepts`.

The absorbed-scalar encoding (`shift_scalar`) is selected by the modulus comparison from the
cardinalities — the `Shifted_value` Type1 register when the scalar modulus is below the base
modulus, the Type2 shift otherwise — at the scalar-modulus bit size `Nat.size scalar` (the
Rust `MODULUS_BIT_SIZE`).

## What `verify` checks

The two acceptance equations, at the derived challenges:

* Schnorr: `c • Q + δ = z1 • sg + (z1 · b0) • U + z2 • H`, with
  `Q = P + v • U + ∑ (uⱼ⁻¹ • Lⱼ + uⱼ • Rⱼ)`, `P` the polyscale combination of the
  commitments, `v` the combined inner product, and `b0` the evalscale combination of `bPoly`;
* `sg`-correctness: `sg = ⟨bPolyCoefficients chal, g⟩`.

`verifyWith` decides each equation and returns the conjunction. Production's `SRS::verify`
does not. Over a batch of proofs `i = 0, 1, …`, with `Aᵢ` the Schnorr residual
(`cᵢ • Qᵢ + δᵢ − z1ᵢ • sgᵢ − (z1ᵢ · b0ᵢ) • Uᵢ − z2ᵢ • H`) and `Bᵢ` the `sg` residual
(`⟨sᵢ, g⟩ − sgᵢ`), it settles every term through one multi-scalar multiplication against zero,

  `∑ᵢ (rⁱ • Aᵢ + sⁱ • Bᵢ) = 0`,

`r = rand_base` and `s = sg_rand_base` sampled by the verifier. This verifier is production's
at a one-proof batch, where both weights are `r⁰ = s⁰ = 1` and the deployed test is the single
equation `A + B = 0`. The conjunction `A = 0 ∧ B = 0` implies it and is not implied by it. Like
the round-count pin above, the conjunction is therefore a declared modeling *strengthening*,
not the transcription of production's check (external-audit V-4, statement-audit M2).
Acceptance here implies production's acceptance, and every statement over `verifyWith` —
`Kimchi.Verifier.kimchiVerify` and what is proved of it — is a statement about the conjunction.

`IpaVesta` and `IpaPallas` instantiate the two Pasta curves. Both are validated against
production prover/verifier fixtures by `scripts/check_ipa_fixture.lean`, which parses the
wire records and composes check-then-verify. The fixtures do not distinguish the conjunction
from production's test: an honest proof satisfies both equations, and the two predicates
differ only off the honest path.
-/

namespace Bulletproof.Ipa

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof

/-- The curve itself, with nothing a protocol layers on top of it: the two cardinalities with
their primality facts, the short-Weierstrass curve over the base field, its group order, and
the fast multi-scalar multiplication. Carrying facts rather than field structures makes every
field operation resolve to the canonical `ZMod` instances on both the executable and abstract
sides.

The sponges, the endomorphism and the map-to-curve are on `KimchiCurve`, which extends this.
Nothing supplies one of those in isolation: there are exactly two curves in the tree, and each
supplies all of it at once. -/
structure CommitmentCurve where
  /-- The base-field cardinality; the field itself is the canonical `ZMod base`. -/
  base : ℕ
  /-- The scalar-field cardinality; the field itself is the canonical `ZMod scalar`. -/
  scalar : ℕ
  [primeBase : Fact (Nat.Prime base)]
  [primeScalar : Fact (Nat.Prime scalar)]
  /-- The curve, in short-Weierstrass form over the base field. -/
  E : SWCurve (ZMod base)
  /-- The curve is short: `y² = x³ + B`. -/
  a_zero : E.A = 0
  /-- The scalar cardinality is the group order: `ScalarField` is the scalar ring of `Point`. -/
  card : Nat.card (SWPoint E) = scalar
  /-- A fast multi-scalar multiplication for this curve: the windowed-Pippenger accelerator
  run in projective coordinates, standing in for the naive `∑` so the executable verifier's
  large MSMs (the `2 ^ σ.k`-point `sg`-correctness check) pay one field inversion instead of
  one per addition. -/
  fastMsm : {n : ℕ} → (Fin n → SWPoint E) → (Fin n → ZMod scalar) → SWPoint E
  /-- `fastMsm` computes the multi-scalar multiplication `∑ i, (a i).val • g i`. -/
  fastMsm_spec : ∀ {n : ℕ} (g : Fin n → SWPoint E) (a : Fin n → ZMod scalar),
    fastMsm g a = ∑ i, (a i).val • g i

attribute [instance] CommitmentCurve.primeBase CommitmentCurve.primeScalar

/-- The base field — the canonical `ZMod` at the base cardinality. -/
abbrev CommitmentCurve.BaseField (C : CommitmentCurve) := ZMod C.base

/-- The scalar field — the canonical `ZMod` at the scalar cardinality. -/
abbrev CommitmentCurve.ScalarField (C : CommitmentCurve) := ZMod C.scalar

/-- The point type — the library's proof-carrying `SWPoint`, with its group structure. -/
abbrev CommitmentCurve.Point (C : CommitmentCurve) := SWPoint C.E

/-- The scalar order kills the point group (Lagrange): the integer → scalar reduction of a
scalar action is exact. -/
theorem CommitmentCurve.card_nsmul (C : CommitmentCurve) (X : C.Point) : C.scalar • X = 0 := by
  rw [← C.card]; exact card_nsmul_eq_zero'

instance CommitmentCurve.neZeroScalar (C : CommitmentCurve) : NeZero C.scalar :=
  ⟨C.primeScalar.out.ne_zero⟩

/-- The point group as a module over the scalar field. Derived from `card` rather than
supplied: the group is killed by the scalar order, which is exactly what makes it a
`ZMod scalar`-module. With this in scope a generic proof over an abstract curve has Mathlib's
`smul` API, instead of rebuilding the action from the killing fact by hand. -/
instance CommitmentCurve.pointModule (C : CommitmentCurve) : Module C.ScalarField C.Point :=
  AddCommGroup.zmodModule C.card_nsmul

/-- The curve as the kimchi verifier needs it: the curve itself, the two sponges, the
endomorphism and the SvdW map-to-curve, with the tie between the map's curve and this one.

One record rather than four, because there are exactly two of these in the tree and no half of
it is ever supplied on its own. The IPA opening verifier is indexed by this as well; it reads
everything here except `frSponge`. -/
structure KimchiCurve extends CommitmentCurve where
  /-- The Fq-sponge spec driving the verifier's Fiat–Shamir transcript. -/
  sponge : FqSponge.Spec base scalar
  /-- The scalar-side sponge, production's `G::sponge_params()`, that kimchi's `frOracles`
  runs. Not read by the IPA opening verifier itself. -/
  frSponge : FqSponge.Spec scalar scalar
  /-- The endomorphism the challenge expansion and the `endo_mul` ladders run on. -/
  endo : Pasta.EndoSpec E.toAffine
  /-- The dual curve's endomorphism coefficient, an element of this curve's scalar field:
  production's `VerifierIndex.endo` (`endos::<G::OtherCurve>().0`). A constant of the curve, so
  a verifier key carrying any other value is malformed. -/
  endoScalar : ZMod scalar
  /-- The SvdW map-to-curve deriving the transcript `U` base from a squeezed field element. -/
  groupMap : Poseidon.GroupMap.Spec base
  /-- The map-to-curve targets this curve. -/
  groupMap_E : groupMap.E = E

/-- The map-to-curve, as the transcript uses it: the SvdW map of `groupMap`, transported along
the tie to this curve's point type. -/
def KimchiCurve.toGroup (C : KimchiCurve) (t : ZMod C.base) : SWPoint C.E :=
  C.groupMap_E ▸ Poseidon.GroupMap.toGroup C.groupMap t

/-- A point with its ordinate in the lower half (`lower_half_ordinate`, `ipa.rs`): the point
itself when the ordinate's representative is at most `(p − 1)/2`, its negation otherwise. -/
def KimchiCurve.lowerHalf (C : KimchiCurve) (P : SWPoint C.E) : SWPoint C.E :=
  if (C.base - 1) / 2 < P.y.val then -P else P

/-- The transcript's `U` base (`u_base`, `ipa.rs`): the map-to-curve of `t` with its ordinate
in the lower half. -/
def KimchiCurve.uBase (C : KimchiCurve) (t : ZMod C.base) : SWPoint C.E :=
  C.lowerHalf (C.toGroup t)

/-- A point or its negation whose ordinate lies below `(p + 1)/2` is `lowerHalf` of the
point: the lower-half ordinate is unique, a zero ordinate being its own negation. -/
theorem KimchiCurve.lowerHalf_eq_of_lt (C : KimchiCurve) (hodd : 2 < C.base)
    {P Q : SWPoint C.E} (hQ : Q = P ∨ Q = -P) (hy : Q.y.val < (C.base + 1) / 2) :
    Q = C.lowerHalf P := by
  have hval := fun a : ZMod C.base => ZMod.val_lt a
  unfold lowerHalf
  rcases hQ with rfl | rfl
  · rw [if_neg (by omega)]
  · by_cases hz : P.y = 0
    · have hneg : -P = P := SWPoint.ext_pair (by simp [hz])
      rw [if_neg (by rw [hz, ZMod.val_zero]; omega), hneg]
    · rw [if_pos]
      haveI : NeZero P.y := ⟨hz⟩
      have hn := ZMod.val_neg_of_ne_zero P.y
      simp only [SWPoint.neg_y] at hy
      have := hval P.y
      omega


/-- The endomorphism eigenvalue in the scalar field: what the transcript's challenge
expansion (`endoExpand`) runs at. The eigenvalue itself is an integer on the endomorphism
spec; this is its image in the field the challenges live in. -/
def KimchiCurve.lam (C : KimchiCurve) : C.ScalarField := (C.endo.lam : C.ScalarField)

variable (C : KimchiCurve)

/-- Multi-scalar multiplication `∑ i, aᵢ • gᵢ` — dispatched to the curve's `fastMsm`
accelerator (the windowed Pippenger run in projective coordinates), which `fastMsm_spec`
proves equals the sum. This keeps the verifier's `2 ^ σ.k`-point `sg`-check from paying a
field inversion per addition. -/
def msm {n : ℕ} (g : Fin n → C.Point) (a : Fin n → C.ScalarField) : C.Point :=
  C.fastMsm g a

/-- The first `count` Lagrange-basis commitments over the domain of size `n` with generator
`ω`, in `nc` chunks (`SRS::get_lagrange_basis`): `L_i` has coefficients `ω^{-ij}/n`, and its
chunk `c` commits the coefficients `c · 2^k + t`, `t < 2^k`, against the SRS's generators.
Coefficients past `n` are zero, so a domain within the SRS is one chunk. -/
def lagrangeBasis (σ : SRS C.Point) (nc n : ℕ) (ω : C.ScalarField) (count : ℕ) :
    Array (Vector C.Point nc) :=
  let K := 2 ^ σ.k
  let ninv : C.ScalarField := (n : C.ScalarField)⁻¹
  (Array.range count).map fun i =>
    let r := ω⁻¹ ^ i
    Vector.ofFn fun c : Fin nc =>
      let len := min K (n - c * K)
      let g : Fin len → C.Point := fun t => σ.g ⟨t, by omega⟩
      let coeffs : Array C.ScalarField := Id.run do
        let mut acc := Array.mkEmpty len
        let mut c := ninv * r ^ (c.val * K)
        for _ in [0:len] do
          acc := acc.push c
          c := c * r
        return acc
      msm C g fun t => coeffs.getD t 0

/-! ### The SRS relations a statement names

A statement over an SRS cannot assume its generators independent: the point group has prime
order, so any two of its points are related. What it can assume is that the SRS avoids the
relations it names (`SRS.Avoids`): a list of coefficient vectors, none of which, if nonzero,
commits to the identity. The Lagrange points are such commitments (`getElem_lagrangeBasis`), at
the coefficients `lagrangeCoeffs`. -/

/-- The SRS avoids a list of relations: no nonzero coefficient vector of the list commits to
the identity. -/
def _root_.Bulletproof.SRS.Avoids {C : KimchiCurve} (σ : SRS C.Point)
    (R : List (Fin (2 ^ σ.k) → C.ScalarField)) : Prop :=
  ∀ a ∈ R, a ≠ 0 → msm C σ.g a ≠ 0

/-- The coefficients of chunk `c` of the `i`-th Lagrange polynomial of the domain of size `n`
with generator `ω`: `ω^{-im}/n` at `m = c · 2^k + j` for `m < n`, and zero past the domain. -/
def lagrangeCoeffs {F : Type*} [Field F] (k n : ℕ) (ω : F) (i c : ℕ) : Fin (2 ^ k) → F :=
  fun j => if c * 2 ^ k + j.val < n then (n : F)⁻¹ * (ω⁻¹ ^ i) ^ (c * 2 ^ k + j.val) else 0

/-- The wire's multi-scalar multiplication is the abstract scheme's generator commitment, as a
linear map: its linearity is `map_zero`, `map_add`, `map_smul`. -/
theorem msm_eq {n : ℕ} (g : Fin n → C.Point) (a : Fin n → C.ScalarField) :
    msm C g a = commitGenₗ g a := by
  rw [msm, C.fastMsm_spec, commitGenₗ_apply, commitGen]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Nat.cast_smul_eq_nsmul C.ScalarField, ZMod.natCast_zmod_val]

private theorem geom_foldl {F : Type*} [Field F] (r : F) :
    ∀ (l : List ℕ) (acc : Array F) (c : F),
      (l.foldl (fun (b : MProd (Array F) F) _ => ⟨b.1.push b.2, b.2 * r⟩) ⟨acc, c⟩).1
        = acc ++ ((List.range l.length).map fun j => c * r ^ j).toArray
  | [], acc, c => by simp
  | _ :: l, acc, c => by
      rw [List.foldl_cons, geom_foldl r l, List.length_cons, List.range_succ_eq_map]
      simp [pow_succ', mul_assoc, Function.comp_def]

/-- The array `lagrangeBasis`'s loop builds is the geometric progression `c, c·r, …`. -/
private theorem geom_loop {F : Type*} [Field F] (c r : F) (n : ℕ) (k : ℕ) :
    (Id.run do
      let mut acc := Array.mkEmpty n
      let mut c := c
      for _ in [0:n] do
        acc := acc.push c
        c := c * r
      return acc).getD k 0 = if k < n then c * r ^ k else 0 := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, bind_pure_comp,
    map_pure, List.forIn_pure_yield_eq_foldl]
  rw [geom_foldl]
  by_cases hk : k < n <;> simp [Array.getD, hk]

/-- A sum against the first `n` generators is the sum against all of them at the padded
coefficients. -/
private theorem msm_pad (σ : SRS C.Point) (n : ℕ) (hn : n ≤ 2 ^ σ.k) (a : ℕ → C.ScalarField) :
    msm C (fun j : Fin n => σ.g ⟨j, by omega⟩) (fun j => a j)
      = msm C σ.g fun j => if j.val < n then a j else 0 := by
  rw [msm_eq, msm_eq, commitGenₗ_apply, commitGenₗ_apply, commitGen, commitGen]
  let G : ℕ → C.Point := fun j => if h : j < 2 ^ σ.k then σ.g ⟨j, h⟩ else 0
  have hl : ∀ j : Fin n, a j • σ.g ⟨j, by omega⟩ = (fun j : ℕ => a j • G j) j := fun j => by
    have : (j : ℕ) < 2 ^ σ.k := by omega
    simp [G, this]
  have hr : ∀ j : Fin (2 ^ σ.k), (if j.val < n then a j else 0) • σ.g j
      = (fun j : ℕ => (if j < n then a j else 0) • G j) j := fun j => by simp [G]
  calc ∑ j : Fin n, a j • σ.g ⟨j, by omega⟩
      = ∑ j : Fin n, (fun j : ℕ => a j • G j) j := Finset.sum_congr rfl fun j _ => hl j
    _ = ∑ j ∈ Finset.range n, a j • G j := Fin.sum_univ_eq_sum_range (fun j => a j • G j) n
    _ = ∑ j ∈ Finset.range (2 ^ σ.k), (if j < n then a j else 0) • G j := by
        rw [← Finset.sum_subset (Finset.range_subset_range.2 hn)]
        · exact Finset.sum_congr rfl fun j hj => by simp [Finset.mem_range.1 hj]
        · intro j _ hj
          simp [Finset.mem_range.not.1 hj]
    _ = _ := (Fin.sum_univ_eq_sum_range
          (fun j => (if j < n then a j else 0) • G j) _).symm.trans
        (Finset.sum_congr rfl fun j _ => (hr j).symm)

/-- The Lagrange points are the commitments to the Lagrange coefficients, chunk by chunk. -/
theorem getElem_lagrangeBasis (σ : SRS C.Point) (nc n : ℕ) (ω : C.ScalarField) (count i : ℕ)
    (hi : i < (lagrangeBasis C σ nc n ω count).size) (c : Fin nc) :
    (lagrangeBasis C σ nc n ω count)[i][c] = msm C σ.g (lagrangeCoeffs σ.k n ω i c) := by
  simp only [lagrangeBasis, Array.getElem_map, Array.getElem_range, Fin.getElem_fin,
    Vector.getElem_ofFn, geom_loop]
  rw [msm_pad C σ (min (2 ^ σ.k) (n - c * 2 ^ σ.k)) (by omega) fun t =>
    if t < min (2 ^ σ.k) (n - c * 2 ^ σ.k) then
      (n : C.ScalarField)⁻¹ * (ω⁻¹ ^ i) ^ (c.val * 2 ^ σ.k) * (ω⁻¹ ^ i) ^ t else 0]
  congr 1
  funext j
  unfold lagrangeCoeffs
  have hj := j.isLt
  by_cases h : c * 2 ^ σ.k + j.val < n
  · have h' : j.val < min (2 ^ σ.k) (n - c * 2 ^ σ.k) := by omega
    simp only [h, h', if_true, pow_add, mul_assoc]
  · have h' : ¬ j.val < min (2 ^ σ.k) (n - c * 2 ^ σ.k) := by omega
    simp only [h, h', if_false]

/-- A chunk of a Lagrange polynomial that meets the domain is nonzero. -/
theorem lagrangeCoeffs_ne_zero {F : Type*} [Field F] (k n : ℕ) (ω : F) (i c : ℕ)
    (hc : c * 2 ^ k < n) (hω : ω ≠ 0) (hF : (n : F) ≠ 0) : lagrangeCoeffs k n ω i c ≠ 0 := by
  intro h
  have := congrFun h ⟨0, by positivity⟩
  simp [lagrangeCoeffs, hc, hF, hω] at this

/-- The `i`-th Lagrange polynomial of a domain within the SRS at `1`: its coefficients sum to
`δ_{i0}`. -/
theorem sum_lagrangeCoeffs {F : Type*} [Field F] (k n : ℕ) (ω : F)
    (hω : IsPrimitiveRoot ω n) (hle : n ≤ 2 ^ k) (hF : (n : F) ≠ 0) (i : ℕ) (hi : i < n) :
    ∑ j, lagrangeCoeffs k n ω i 0 j = if i = 0 then 1 else 0 := by
  have h1 : ∑ j, lagrangeCoeffs k n ω i 0 j
      = ∑ j ∈ Finset.range n, (n : F)⁻¹ * (ω⁻¹ ^ i) ^ j := by
    unfold lagrangeCoeffs
    simp only [zero_mul, _root_.zero_add]
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < n then (n : F)⁻¹ * (ω⁻¹ ^ i) ^ j else 0),
      ← Finset.sum_subset (Finset.range_subset_range.2 hle)]
    · exact Finset.sum_congr rfl fun j hj => by simp [Finset.mem_range.1 hj]
    · intro j _ hj
      simp [Finset.mem_range.not.1 hj]
  rw [h1, ← Finset.mul_sum]
  split_ifs with h0
  · subst h0
    simp [hF]
  · have hx : ω⁻¹ ^ i ≠ 1 := by
      rw [inv_pow, Ne, inv_eq_one]
      exact hω.pow_ne_one_of_pos_of_lt (Nat.pos_of_ne_zero h0).ne' hi
    have hxn : (ω⁻¹ ^ i) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, inv_pow, hω.pow_eq_one, inv_one, one_pow]
    have := geom_sum_mul (ω⁻¹ ^ i) n
    rw [hxn, sub_self] at this
    rw [(mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hx), mul_zero]

/-- An IPA opening proof at round count `k` — the checked form of the wire
`OpeningProof` (`ipa.rs`): the round count is the SRS's `σ.k`, pinned by the parse. -/
structure Proof (C : KimchiCurve) (k : ℕ) where
  /-- The per-round `(L, R)` commitment pairs — a `Vector` at the checked round count `k`. -/
  lr : Vector (C.Point × C.Point) k
  /-- The Schnorr commitment `δ`. -/
  delta : C.Point
  /-- The Schnorr response scalar acting on `sg` and the `U` base. -/
  z1 : C.ScalarField
  /-- The Schnorr response scalar acting on the blinding base `H`. -/
  z2 : C.ScalarField
  /-- The challenge-folded commitment base, checked against `⟨bPolyCoefficients chal, g⟩`. -/
  sg : C.Point

/-- A batched opening claim at its shape — round count `k`, `m` rows, `p` evaluation
points: the per-polynomial commitments (one segment each), the evaluation points, the
claimed evaluation matrix (`evals[i][j]` = polynomial `i` at point `j`), the
combination scalars, and the proof. Every read is total. -/
structure Input (C : KimchiCurve) (k m p : ℕ) where
  /-- The per-polynomial commitments, one segment each — the `m` rows of the claim. -/
  commitments : Vector C.Point m
  /-- The `p` evaluation points. -/
  xs : Vector C.ScalarField p
  /-- The claimed evaluation matrix: `evals[i][j]` = polynomial `i` at point `j`. -/
  evals : Vector (Vector C.ScalarField p) m
  /-- The polynomial-combination scalar `ξ`. -/
  polyscale : C.ScalarField
  /-- The evaluation-point-combination scalar `r`. -/
  evalscale : C.ScalarField
  /-- The opening proof, at the checked round count `k`. -/
  proof : Proof C k

variable {k m p : ℕ}

/-- The commitments as the `Fin`-indexed function of the abstract claim. -/
def Input.commitmentFn {C : KimchiCurve} (inp : Input C k m p) :
    Fin m → C.Point :=
  fun i => inp.commitments[i]

/-- The evaluation points as the `Fin`-indexed function of the abstract claim. -/
def Input.pointFn {C : KimchiCurve} (inp : Input C k m p) :
    Fin p → C.ScalarField :=
  fun j => inp.xs[j]

/-- The claimed evaluation matrix as the indexed function of the abstract claim. -/
def Input.evalFn {C : KimchiCurve} (inp : Input C k m p) :
    Fin m → Fin p → C.ScalarField :=
  fun i j => (inp.evals[i])[j]

/-- The combined inner product of the claimed evaluations
(`Bulletproof.combinedInnerProduct` at the checked matrix). -/
def cipOf {C : KimchiCurve} (inp : Input C k m p) : C.ScalarField :=
  combinedInnerProduct inp.polyscale inp.evalscale inp.evalFn

/-- The polyscale combination `∑ i, ξ^i • Cᵢ` of the commitments — the group-side mirror
of `Bulletproof.combinedCommitment`, by a running power. -/
def combineCommitments (ξ : C.ScalarField) (cs : Array C.Point) : C.Point :=
  (cs.foldl (fun (acc : C.Point × C.ScalarField) P => (acc.1 + acc.2.val • P, acc.2 * ξ))
    (0, 1)).1

/-- The transcript encoding of an absorbed scalar (`shift_scalar`,
`poly-commitment/src/commitment.rs`): the `Shifted_value` register form at the
scalar-modulus bit size `Nat.size scalar` (the Rust `MODULUS_BIT_SIZE`) — Type1
(`(x − 2ᵇ − 1)/2`) when the scalar modulus is below the base modulus, the Type2 shift
(`x − 2ᵇ`) otherwise. The branch is the Rust `n1 < n2`, decided from the cardinalities. -/
def shiftScalar (x : C.ScalarField) : C.ScalarField :=
  if C.scalar < C.base then Pasta.Shifted.shiftType1 (Nat.size C.scalar) x
  else Pasta.Shifted.shiftType2 (Nat.size C.scalar) x

/-- One round of the challenge fold: absorb `L` and `R`, squeeze one challenge, push it. -/
private def roundStep (acc : Array Prechallenge × FqSponge.S C.base)
    (LR : C.Point × C.Point) : Array Prechallenge × FqSponge.S C.base :=
  let us := challengeNat C.sponge (absorbG C.sponge (absorbG C.sponge acc.2 LR.1) LR.2)
  (acc.1.push us.1, us.2)

/-- The per-round prechallenge fold (the round loop of `SRS::verify`): absorb `L` and `R`,
squeeze one 128-bit prechallenge, threading the sponge state — one push per `(L, R)`
pair. The array-level engine of `roundChallenges`; the fold state is concrete data. -/
def roundChallengesAux (s : FqSponge.S C.base) (lr : Array (C.Point × C.Point)) :
    Array Prechallenge × FqSponge.S C.base :=
  lr.foldl (roundStep C) (#[], s)

/-- A left fold that pushes exactly one element per step grows the array by the list
length. -/
private theorem foldl_fst_size {S γ α : Type*} (step : (Array γ × S) → α → (Array γ × S))
    (hstep : ∀ acc a, (step acc a).1.size = acc.1.size + 1)
    (l : List α) (init : Array γ × S) :
    (l.foldl step init).1.size = init.1.size + l.length := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, hstep, List.length_cons]
    omega

/-- The fold squeezes exactly one round challenge per `(L, R)` pair. -/
theorem roundChallengesAux_size (s : FqSponge.S C.base) (lr : Array (C.Point × C.Point)) :
    (roundChallengesAux C s lr).1.size = lr.size := by
  unfold roundChallengesAux
  rw [← Array.foldl_toList, foldl_fst_size]
  · simp
  · intro acc a
    simp [roundStep, Array.size_push]

/-- The round prechallenges of a checked proof, from a given sponge state: the 128-bit
vector — sized by construction, one per round — and the post-fold sponge state. -/
def roundChallenges (s : FqSponge.S C.base) {k : ℕ} (lr : Vector (C.Point × C.Point) k) :
    Vector Prechallenge k × FqSponge.S C.base :=
  let r := roundChallengesAux C s lr.toArray
  (⟨r.1, (roundChallengesAux_size C s lr.toArray).trans lr.size_toArray⟩, r.2)

/-- What the verifier's Fiat–Shamir schedule produces from a given initial sponge state
`s₀` (`SRS::verify`, with the sponge supplied by the caller — kimchi hands the warm
post-`ζ` fq-sponge state here, `BatchEvaluationProof { sponge: fq_sponge, .. }`), before
any expansion: absorb the shifted combined inner product; squeeze the `U` base's preimage
`t`; per round absorb `L`, `R` and squeeze a 128-bit prechallenge; absorb `δ` and squeeze
the Schnorr prechallenge. This is exactly what a circuit's group half emits
(`Pickles.checkBulletproof`). The round prechallenges come back as a `Vector` at the
checked round count, so every downstream read is total. -/
def ipaRunAt (s₀ : FqSponge.S C.base) (cip : C.ScalarField) (pr : Proof C k) :
    C.BaseField × Vector Prechallenge k × Prechallenge :=
  let s := absorbFr C.sponge s₀ (shiftScalar C cip)
  let (t, s) := challengeFq C.sponge s
  let (chals, s) := roundChallenges C s pr.lr
  let s := absorbG C.sponge s pr.delta
  let (c, _) := challengeNat C.sponge s
  (t, chals, c)

/-- `ipaRunAt` at the verifier's own combined inner product `cipOf inp`. A circuit's group half
runs the same schedule at a *claimed* inner product, so the schedule is named with `cip` as a
parameter and this is its wire instance. -/
def ipaRun (s₀ : FqSponge.S C.base) (inp : Input C k m p) :
    C.BaseField × Vector Prechallenge k × Prechallenge :=
  ipaRunAt C s₀ (cipOf inp) inp.proof

/-- The verifier's Fiat–Shamir schedule from `s₀`: `ipaRun`, with the consumer's decodes
applied — `t` mapped to the `U` base, the round and Schnorr prechallenges endo-expanded at
the sponge's eigenvalue. -/
def transcriptFrom (s₀ : FqSponge.S C.base) (inp : Input C k m p) :
    C.Point × Vector C.ScalarField k × C.ScalarField :=
  let r := ipaRun C s₀ inp
  (C.uBase r.1, r.2.1.map (fun u => endoExpand C.lam u.val),
    endoExpand C.lam r.2.2.val)

/-- The standalone verifier's Fiat–Shamir schedule: `transcriptFrom` at the fresh
sponge `FqSponge.init` — the cold start. -/
def transcript (inp : Input C k m p) :
    C.Point × Vector C.ScalarField k × C.ScalarField :=
  transcriptFrom C FqSponge.init inp


/-- The acceptance decision from a given initial sponge state `s₀`, against a library
SRS: derive the transcript (from `s₀` — kimchi's warm start hands the post-`ζ`
fq-sponge state, verifier.rs:1184–1193), combine the claim, and check the Schnorr and
`sg`-correctness equations. The claim's shape is carried by its type (round count
`σ.k`), so there are no runtime guards — rejecting ragged input is the wire parse's
job. `σ.U` is never read — the deployed `U` is transcript-derived. -/
def verifyWith (σ : SRS C.Point) (uBase : C.Point) (chals : Vector C.ScalarField σ.k)
    (c : C.ScalarField) (inp : Input C σ.k m p) : Bool :=
  let chal : Fin σ.k → C.ScalarField := fun i => chals[i]
  let b0 := combinedB chal inp.evalscale inp.pointFn
  let v := cipOf inp
  let P := combineCommitments C inp.polyscale inp.commitments.toArray
  let Q := (inp.proof.lr.toArray.zip chals.toArray).foldl
    (fun acc (LRu : (C.Point × C.Point) × C.ScalarField) =>
      acc + (LRu.2⁻¹.val • LRu.1.1 + LRu.2.val • LRu.1.2))
    (P + v.val • uBase)
  let schnorr := decide (c.val • Q + inp.proof.delta
    = inp.proof.z1.val • inp.proof.sg + (inp.proof.z1 * b0).val • uBase
        + inp.proof.z2.val • σ.h)
  let sgOk := decide (inp.proof.sg = msm C σ.g (bPolyCoefficients chal))
  schnorr && sgOk

/-- The opening acceptance at the deployed Fiat–Shamir schedule: `verifyWith` fed the
transcript `transcriptFrom` derives by continuing the warm sponge. Definitionally the
former body, so every existing statement about `verifyFrom` is unchanged; the split only
names the boundary between the *derivation* (`transcriptFrom`) and the *algebra*
(`verifyWith`), so an alternative challenge source can be supplied without touching either. -/
def verifyFrom (σ : SRS C.Point) (s₀ : FqSponge.S C.base) (inp : Input C σ.k m p) :
    Bool :=
  let (uBase, chals, c) := transcriptFrom C s₀ inp
  verifyWith C σ uBase chals c inp

/-- The standalone acceptance decision: `verifyFrom` at the fresh sponge
`FqSponge.init` — the cold start, validated against the production opening fixtures. -/
def verify (σ : SRS C.Point) (inp : Input C σ.k m p) : Bool :=
  verifyFrom C σ FqSponge.init inp


/-! ## The prechallenge level

`transcriptFrom` factored to the raw squeezes of the automaton, the form a circuit
implementation of `check_bulletproof` is read against: `ipaSqueezes` is the schedule on
`Poseidon.State`, `ipaPrechallenges` its 128-bit packings, and
`transcriptFrom_eq_ipaPrechallenges` identifies `transcriptFrom`'s outputs with their
map-to-curve and endo-expansions. `schnorrAt` names the Schnorr equation at given advice,
`verifyWith_eq` splits `verifyWith` into it and the `sg`-correctness equation. -/

/-- The absorbed limbs of a scalar (`absorbFr`'s branch made explicit): one limb when the
scalar modulus is below the base modulus, the high bits then the low bit otherwise. -/
def scalarLimbs (x : C.ScalarField) : List C.BaseField :=
  if C.scalar < C.base then [((x.val : ℕ) : C.BaseField)]
  else [((x.val / 2 : ℕ) : C.BaseField), ((x.val % 2 : ℕ) : C.BaseField)]

/-- `absorbFr` absorbs `scalarLimbs`. -/
private theorem absorbFr_eq (s : FqSponge.S C.base) (x : C.ScalarField) :
    absorbFr C.sponge s x = absorbFq C.sponge s (scalarLimbs C x) := by
  unfold absorbFr scalarLimbs
  split <;> rfl

/-- One round of the raw schedule: absorb `L` then `R`, squeeze, append the raw element. -/
def ipaRound {F : Type*} [Field F] (p : Poseidon.Params F)
    (acc : List F × Poseidon.State F) (q : (F × F) × (F × F)) : List F × Poseidon.State F :=
  let sq := Poseidon.squeeze p
    (Poseidon.absorb p (Poseidon.absorb p acc.2 [q.1.1, q.1.2]) [q.2.1, q.2.2])
  (acc.1 ++ [sq.1], sq.2)

/-- The round fold's challenges accumulate onto the prefix; its state does not depend on
it. -/
theorem ipaRound_foldl {F : Type*} [Field F] (p : Poseidon.Params F) :
    ∀ (l : List ((F × F) × (F × F))) (acc : List F) (s : Poseidon.State F),
      l.foldl (ipaRound p) (acc, s)
        = (acc ++ (l.foldl (ipaRound p) ([], s)).1, (l.foldl (ipaRound p) ([], s)).2)
  | [], _, _ => by simp
  | q :: l, acc, s => by
    simp only [List.foldl_cons, ipaRound, List.nil_append]
    generalize Poseidon.squeeze p (Poseidon.absorb p (Poseidon.absorb p s [q.1.1, q.1.2])
      [q.2.1, q.2.2]) = sq
    rw [ipaRound_foldl p l (acc ++ [sq.1]) sq.2, ipaRound_foldl p l [sq.1] sq.2]
    simp [List.append_assoc]

/-- The raw squeezed elements of the opening transcript from a warm state (`transcriptFrom`
from `⟨s₀, []⟩`): the `U` base's preimage `t`, one element per `(L, R)` pair, and `c`'s.
Points enter as coordinate pairs, the scalar as its limbs. -/
def ipaSqueezes {F : Type*} [Field F] (p : Poseidon.Params F) (s₀ : Poseidon.State F)
    (cipLimbs : List F) (lr : List ((F × F) × (F × F))) (delta : F × F) : F × List F × F :=
  let sqT := Poseidon.squeeze p (Poseidon.absorb p s₀ cipLimbs)
  let r := lr.foldl (ipaRound p) ([], sqT.2)
  (sqT.1, r.1, (Poseidon.squeeze p (Poseidon.absorb p r.2 [delta.1, delta.2])).1)

/-- The 128-bit prechallenges of the opening transcript: `t` raw, each round's and `c`'s
squeeze mod `2^128` (`challengeNat`). `transcriptFrom` is their map-to-curve and
endo-expansions (`transcriptFrom_eq_ipaPrechallenges`). -/
def ipaPrechallenges {p : ℕ} [Field (ZMod p)] (params : Poseidon.Params (ZMod p))
    (s₀ : Poseidon.State (ZMod p)) (cipLimbs : List (ZMod p))
    (lr : List ((ZMod p × ZMod p) × (ZMod p × ZMod p))) (delta : ZMod p × ZMod p) :
    ZMod p × List ℕ × ℕ :=
  let r := ipaSqueezes params s₀ cipLimbs lr delta
  (r.1, r.2.1.map (·.val % 2 ^ 128), r.2.2.val % 2 ^ 128)

/-- A pair of points as coordinate pairs. -/
private def coordsPair (q : C.Point × C.Point) :
    (C.BaseField × C.BaseField) × (C.BaseField × C.BaseField) :=
  ((q.1.x, q.1.y), (q.2.x, q.2.y))

/-- The 128-bit packing of a raw squeeze. -/
private def packRaw (x : C.BaseField) : Prechallenge :=
  ⟨x.val % 2 ^ 128, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The round fold from an empty limb buffer is `ipaRound` on the automaton, its
prechallenges the packings of the raw elements. -/
private theorem foldl_rounds (l : List (C.Point × C.Point)) (acc : List C.BaseField)
    (st : Poseidon.State C.BaseField) :
    l.foldl (roundStep C) ((acc.map (packRaw C)).toArray, ⟨st, []⟩)
      = let r := (l.map (coordsPair C)).foldl (ipaRound C.sponge.params) (acc, st)
        ((r.1.map (packRaw C)).toArray, ⟨r.2, []⟩) := by
  induction l generalizing acc st with
  | nil => rfl
  | cons q l ih =>
    simp only [List.foldl_cons, List.map_cons, roundStep, absorbG, absorbFq,
      challengeNat_fresh, List.push_toArray, ipaRound, coordsPair]
    generalize Poseidon.squeeze C.sponge.params (Poseidon.absorb C.sponge.params
      (Poseidon.absorb C.sponge.params st [q.1.x, q.1.y]) [q.2.x, q.2.y]) = sq
    have h := ih (acc ++ [sq.1]) sq.2
    simp only [List.map_append, List.map_singleton, packRaw] at h
    exact h

/-- `ipaRunAt` from a warm state with an empty limb buffer is `ipaPrechallenges` on the
automaton: the same `t`, the same packed round and Schnorr prechallenges (as naturals). -/
theorem ipaRunAt_eq_ipaPrechallenges (st : Poseidon.State C.BaseField) (cip : C.ScalarField)
    (pr : Proof C k) :
    let r := ipaPrechallenges C.sponge.params st (scalarLimbs C (shiftScalar C cip))
      (pr.lr.toList.map fun q => ((q.1.x, q.1.y), (q.2.x, q.2.y))) (pr.delta.x, pr.delta.y)
    (ipaRunAt C ⟨st, []⟩ cip pr).1 = r.1 ∧
    (ipaRunAt C ⟨st, []⟩ cip pr).2.1.toList.map Subtype.val = r.2.1 ∧
    (ipaRunAt C ⟨st, []⟩ cip pr).2.2.val = r.2.2 := by
  dsimp only
  unfold ipaRunAt
  rw [absorbFr_eq]
  simp only [absorbFq, challengeFq]
  generalize hs : Poseidon.squeeze C.sponge.params
    (Poseidon.absorb C.sponge.params st (scalarLimbs C (shiftScalar C cip))) = sqT
  have h1 : (roundChallenges C ⟨sqT.2, []⟩ pr.lr).1.toArray
      = (roundChallengesAux C ⟨sqT.2, []⟩ pr.lr.toArray).1 := rfl
  have h2 : (roundChallenges C ⟨sqT.2, []⟩ pr.lr).2
      = (roundChallengesAux C ⟨sqT.2, []⟩ pr.lr.toArray).2 := rfl
  have hf := foldl_rounds C pr.lr.toArray.toList [] sqT.2
  simp only [List.map_nil] at hf
  delta coordsPair at hf
  rw [roundChallengesAux, ← Array.foldl_toList, hf] at h1 h2
  have hl : pr.lr.toArray.toList = pr.lr.toList := rfl
  rw [hl] at h1 h2
  rcases hrc : roundChallenges C ⟨sqT.2, []⟩ pr.lr with ⟨chals, s⟩
  rw [hrc] at h1 h2
  subst h2
  unfold ipaPrechallenges ipaSqueezes
  rw [hs]
  refine ⟨rfl, ?_, ?_⟩
  · show chals.toArray.toList.map Subtype.val = _
    rw [h1]
    simp only [List.map_map, Function.comp_def, packRaw]
  · simp only [absorbG, absorbFq, challengeNat_fresh]

/-- `ipaRun` from a warm state with an empty limb buffer is `ipaPrechallenges` on the
automaton: `ipaRunAt_eq_ipaPrechallenges` at the verifier's own inner product. -/
theorem ipaRun_eq_ipaPrechallenges (st : Poseidon.State C.BaseField) (inp : Input C k m p) :
    let r := ipaPrechallenges C.sponge.params st (scalarLimbs C (shiftScalar C (cipOf inp)))
      (inp.proof.lr.toList.map (coordsPair C)) (inp.proof.delta.x, inp.proof.delta.y)
    (ipaRun C ⟨st, []⟩ inp).1 = r.1 ∧
    (ipaRun C ⟨st, []⟩ inp).2.1.toList.map Subtype.val = r.2.1 ∧
    (ipaRun C ⟨st, []⟩ inp).2.2.val = r.2.2 :=
  ipaRunAt_eq_ipaPrechallenges C st (cipOf inp) inp.proof

/-- `transcriptFrom` from a warm state with an empty limb buffer, through
`ipaPrechallenges`: the `U` base is `uBase` of `t`, the round challenges and `c` the
endo-expansions of the packed squeezes. -/
theorem transcriptFrom_eq_ipaPrechallenges (st : Poseidon.State C.BaseField)
    (inp : Input C k m p) :
    let r := ipaPrechallenges C.sponge.params st (scalarLimbs C (shiftScalar C (cipOf inp)))
      (inp.proof.lr.toList.map (coordsPair C)) (inp.proof.delta.x, inp.proof.delta.y)
    (transcriptFrom C ⟨st, []⟩ inp).1 = C.uBase r.1 ∧
    (transcriptFrom C ⟨st, []⟩ inp).2.1.toList = r.2.1.map (endoExpand C.lam) ∧
    (transcriptFrom C ⟨st, []⟩ inp).2.2 = endoExpand C.lam r.2.2 := by
  obtain ⟨h1, h2, h3⟩ := ipaRun_eq_ipaPrechallenges C st inp
  simp only [transcriptFrom]
  refine ⟨by rw [h1], ?_, by rw [h3]⟩
  simp only [Vector.toList_map, ← h2, List.map_map, Function.comp_def]

/-- The Schnorr equation of the opening at given advice: `verifyWith`'s first conjunct
with the combined inner product `cip` and the challenge-polynomial evaluation `b` as
parameters, and `P` the combined commitment. -/
def schnorrAt (σ : SRS C.Point) (uBase : C.Point) (chals : Vector C.ScalarField k)
    (c cip b : C.ScalarField) (P : C.Point) (pr : Proof C k) : Prop :=
  let Q := (pr.lr.toArray.zip chals.toArray).foldl
    (fun acc (LRu : (C.Point × C.Point) × C.ScalarField) =>
      acc + (LRu.2⁻¹.val • LRu.1.1 + LRu.2.val • LRu.1.2))
    (P + cip.val • uBase)
  c.val • Q + pr.delta = pr.z1.val • pr.sg + (pr.z1 * b).val • uBase + pr.z2.val • σ.h

/-- `verifyWith` is `schnorrAt` at the verifier's own `cipOf`, `combinedB` and combined
commitment, together with the `sg`-correctness equation. -/
theorem verifyWith_eq (σ : SRS C.Point) (uBase : C.Point) (chals : Vector C.ScalarField σ.k)
    (c : C.ScalarField) (inp : Input C σ.k m p) :
    verifyWith C σ uBase chals c inp = true ↔
      schnorrAt C σ uBase chals c (cipOf inp)
          (combinedB (fun i => chals[i]) inp.evalscale inp.pointFn)
          (combineCommitments C inp.polyscale inp.commitments.toArray) inp.proof ∧
        inp.proof.sg = msm C σ.g (bPolyCoefficients fun i => chals[i]) := by
  simp [verifyWith, schnorrAt]

end Bulletproof.Ipa

/-! ## The wire boundary: serde records and the check parse -/

namespace Bulletproof.Ipa.Wire

variable {C : KimchiCurve}

/-- The wire opening proof (`OpeningProof`, ipa.rs): `lr` is a `Vec` — its length is
the SRS's round count, pinned by `check`. -/
structure Proof (C : KimchiCurve) where
  /-- The per-round `(L, R)` pairs — a `Vec`; its length is pinned to the round count
  by `check`. -/
  lr : Array (C.Point × C.Point)
  /-- The Schnorr commitment `δ`. -/
  delta : C.Point
  /-- The Schnorr response scalar acting on `sg` and the `U` base. -/
  z1 : C.ScalarField
  /-- The Schnorr response scalar acting on the blinding base `H`. -/
  z2 : C.ScalarField
  /-- The challenge-folded commitment base. -/
  sg : C.Point

/-- The wire batched claim (`BatchEvaluationProof`): every payload a `Vec`. -/
structure Input (C : KimchiCurve) where
  /-- The per-polynomial commitments. -/
  commitments : Array C.Point
  /-- The evaluation points. -/
  xs : Array C.ScalarField
  /-- The claimed evaluation matrix (`evals[i][j]` = polynomial `i` at point `j`);
  squareness against the commitments and points is `check`'s guard. -/
  evals : Array (Array C.ScalarField)
  /-- The polynomial-combination scalar `ξ`. -/
  polyscale : C.ScalarField
  /-- The evaluation-point-combination scalar `r`. -/
  evalscale : C.ScalarField
  /-- The wire opening proof. -/
  proof : Proof C

/-- Parse a wire proof at round count `k` — the checked verifier's `lr`-length
requirement as a total parse. -/
def Proof.check (k : ℕ) (w : Proof C) : Option (Ipa.Proof C k) :=
  if h : w.lr.size = k then
    some { lr := ⟨w.lr, h⟩, delta := w.delta, z1 := w.z1, z2 := w.z2, sg := w.sg }
  else none

/-- Parse a wire claim at its announced shape — the checked verifier's dimension
requirements (`evals` square against the commitments and points, the proof at round
count `k`) as a total parse into the checked input. -/
def Input.check (k : ℕ) (w : Input C) :
    Option (Ipa.Input C k w.commitments.size w.xs.size) := do
  let proof ← w.proof.check k
  let evals ← w.evals.mapM fun e =>
    if h : e.size = w.xs.size then some (⟨e, h⟩ : Vector C.ScalarField w.xs.size)
    else none
  if hm : evals.size = w.commitments.size then
    some { commitments := ⟨w.commitments, rfl⟩, xs := ⟨w.xs, rfl⟩
           evals := ⟨evals, hm⟩
           polyscale := w.polyscale, evalscale := w.evalscale, proof := proof }
  else none

end Bulletproof.Ipa.Wire

/-! ## The Pasta instantiations -/

namespace Bulletproof.IpaVesta

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Poseidon Bulletproof

/-- The Vesta bundle. The scalar modulus is below the base modulus, so scalars absorb in
Type1 form. The scalar field is `Fp`, so `G::sponge_params()` is the `fp_kimchi`
table. -/
abbrev curve : Ipa.KimchiCurve where
  base := PALLAS_SCALAR_CARD
  scalar := PALLAS_BASE_CARD
  sponge := FqVesta.spec
  frSponge :=
    { params := fpParams
      hsize := by
        show (Poseidon.FpKimchi.roundConstants.map _).size = Poseidon.fullRounds
        rw [Array.size_map]
        rfl }
  E := Vesta.curve
  a_zero := rfl
  card := Vesta.card_eq
  endo := Pasta.vestaEndoSpec
  endoScalar := Pasta.pallasEndo
  groupMap := GroupMapVesta.spec
  groupMap_E := rfl
  fastMsm := fun {_} g a =>
    CompElliptic.Curves.Pasta.Fast.MsmProj.pippengerProjScatterPar 8
      (List.ofFn fun i => ((a i).val, g i))
  fastMsm_spec := fun {_} g a => by
    rw [CompElliptic.Curves.Pasta.Fast.MsmProj.pippengerProjScatterPar_eq_msm 8 (by decide)
        (List.ofFn fun i => ((a i).val, g i))]
    simp [List.map_ofFn, List.sum_ofFn]

/-- The Vesta point type. -/
abbrev Point := curve.Point

end Bulletproof.IpaVesta

namespace Bulletproof.IpaPallas

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Poseidon Bulletproof

/-- The Pallas bundle. The scalar modulus is above the base modulus, so scalars absorb in
Type2 form (selected by the cardinalities). The scalar field is `Fq`, so
`G::sponge_params()` is the `fq_kimchi` table. -/
abbrev curve : Ipa.KimchiCurve where
  base := PALLAS_BASE_CARD
  scalar := PALLAS_SCALAR_CARD
  sponge := FqPallas.spec
  frSponge :=
    { params := fqParams
      hsize := by
        show (Poseidon.FqKimchi.roundConstants.map _).size = Poseidon.fullRounds
        rw [Array.size_map]
        rfl }
  E := Pallas.curve
  a_zero := rfl
  card := Pallas.card_eq
  endo := Pasta.pallasEndoSpec
  endoScalar := Pasta.vestaEndo
  groupMap := GroupMapPallas.spec
  groupMap_E := rfl
  fastMsm := fun {_} g a =>
    CompElliptic.Curves.Pasta.Fast.MsmProjPallas.pippengerProjScatterPar 8
      (List.ofFn fun i => ((a i).val, g i))
  fastMsm_spec := fun {_} g a => by
    rw [CompElliptic.Curves.Pasta.Fast.MsmProjPallas.pippengerProjScatterPar_eq_msm 8 (by decide)
        (List.ofFn fun i => ((a i).val, g i))]
    simp [List.map_ofFn, List.sum_ofFn]

/-- The Pallas point type. -/
abbrev Point := curve.Point

end Bulletproof.IpaPallas
