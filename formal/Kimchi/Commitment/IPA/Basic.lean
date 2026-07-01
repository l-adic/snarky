/-
Copyright (c) 2025 O(1) Labs. Released under Apache 2.0 license.
-/
import Mathlib
import ArkLib.Commitments.Functional.Basic

/-!
# The IPA Polynomial Commitment — foundational module

This file constructs kimchi's inner-product-argument (IPA) univariate polynomial
commitment as an instance of ArkLib's `Commitment.Scheme`. The scheme is generic
over an additive commitment group `G` with scalar field `F`: a degree-`(d-1)`
polynomial over `F` is committed by a Pedersen vector commitment to its
coefficient vector, and a claimed evaluation is proved through a logarithmic-round
folding argument wrapped in a zero-knowledge Schnorr step.

The mathematical statement follows Halo §3; the operational ground truth is the
kimchi Rust reference (`poly-commitment/src/ipa.rs`, `commitment.rs`). The
security theorems (correctness, binding) and the Pasta instantiation live in
sibling modules. The overall `Commitment.Scheme` shape mirrors the worked KZG
instance `references/arklib/KZG_Basic.lean` (`def kzg`).

## Layout

* `SRS` — the structured reference string (`ipa.rs::struct SRS`).
* `commit` — the Pedersen vector commitment (`ipa.rs::commit_non_hiding`/`mask`).
* `bPoly` — Halo's challenge polynomial (`commitment.rs::b_poly`).
* `openingRelation` — the Halo §3 opening relation `(P,x,v);(a,r)`.
* `OpeningProof` — the proof transcript (`ipa.rs::struct OpeningProof`).
* `pSpec` / `openingProof` — the interactive opening protocol (Halo §3.1).
* `ipa` — the `Commitment.Scheme` instance.

## References

* [Halo] Bowe, Grigg, Hopwood, *Recursive Proof Composition without a Trusted
  Setup*, Section 3.
* [kimchi] `poly-commitment/src/ipa.rs`, `poly-commitment/src/commitment.rs`.
-/

namespace Kimchi.Commitment.IPA

open Commitment OracleSpec OracleComp ProtocolSpec Polynomial

/-! ## The structured reference string -/

/-- The IPA structured reference string produced by `Setup(1^λ, d)`: a vector of
generators `g = (g₀, …, g_{d-1}) ∈ Gᵈ` used to commit to a polynomial in
coefficient form, together with a single blinding base `h ∈ G`. All elements are
sampled uniformly and independently; no trapdoor relates them.

These are exactly the fields `g` (commitment generators) and `h` (blinding base)
of `ipa.rs::struct SRS`. -/
structure SRS (G : Type) (d : ℕ) where
  /-- The generators used to commit to a polynomial in coefficient form. -/
  g : Fin d → G
  /-- The blinding base. -/
  h : G

section Defs

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] {d k : ℕ}

/-! ## The Pedersen commitment -/

/-- The IPA Pedersen vector commitment to a coefficient vector `a ∈ Fᵈ` under
blinding factor `r ∈ F`, relative to the SRS `σ = (g, h)`:
`Commit(σ, p(X); r) = ⟨a, g⟩ + [r]h = ∑ᵢ [aᵢ] gᵢ + [r]h`.

The non-hiding part `⟨a, g⟩` is `ipa.rs::commit_non_hiding`; adding `[r]h` for a
fresh `r` is `ipa.rs::mask`, which records `r` as the decommitment. -/
noncomputable def commit (srs : SRS G d) (a : Fin d → F) (r : F) : G :=
  (∑ i, a i • srs.g i) + r • srs.h

/-! ## The challenge polynomial -/

/-- Halo's symmetric challenge polynomial (eq. (3) of Halo §3.2): given `k` folding
challenges `u₁, …, u_k ∈ Fˣ`,
`bPoly(X) = ∏_{i=0}^{k-1} (u_{k-i}⁻¹ + u_{k-i} X^{2^i})`.

Its `i`-th factor `u_{k-1-i}⁻¹ + u_{k-1-i} · X^{2^i}` is the symmetric pairing of the
inverse challenge on the low window and the plain challenge on the high window — exactly
the recombination performed by the symmetric fold of `foldState`. Consequently
`eval x (bPoly u)` equals the folded residue `b₀` obtained by folding the powers-of-`x`
vector `(1, x, …, x^{d-1})` through all `k` rounds (the scalar half of the telescope
`innerSum_foldUpto`), which is what the verifier recomputes. This is the symmetric form of
Halo eq. (3); kimchi's `commitment.rs::b_poly` uses the un-normalized `∏(1 + u_{k-i} X^{2^i})`
variant tied to kimchi's asymmetric fold, differing only by the global factor `∏ᵢ uᵢ⁻¹`. -/
noncomputable def bPoly (chals : Fin k → F) : Polynomial F :=
  ∏ i : Fin k, (C (chals i.rev)⁻¹ + C (chals i.rev) * X ^ (2 ^ (i : ℕ)))

/-! ## The opening relation -/

/-- The IPA opening relation of Halo §3: the public statement `(P, x, v)` — a
commitment `P ∈ G`, an evaluation point `x ∈ F`, and a claimed value `v ∈ F` — is
paired with a witness `(a, r)` (coefficient vector `a ∈ Fᵈ`, blinding `r ∈ F`)
when `P = ⟨a, g⟩ + [r]h` and `v = ⟨a, (1, x, …, x^{d-1})⟩ = ∑ᵢ aᵢ xⁱ`. -/
def openingRelation (srs : SRS G d) (stmt : G × F × F)
    (wit : (Fin d → F) × F) : Prop :=
  stmt.1 = commit srs wit.1 wit.2 ∧ stmt.2.2 = ∑ i, wit.1 i * stmt.2.1 ^ (i : ℕ)

end Defs

/-! ## The opening proof transcript -/

/-- The IPA opening proof: the transcript emitted by the prover, mirroring
`ipa.rs::struct OpeningProof`. It records, for `k = log₂ d`:

* `lr` — the `k` rounds of cross-term commitments `(Lⱼ, Rⱼ) ∈ G × G`;
* `a` — the final folded scalar (the length-one residue of `a` after `k` folds);
* `sg` — the final folded commitment base `g₀ ∈ G` (Rust field `sg`);
* `delta` — the Schnorr blinding commitment (Halo's `R`, Rust field `delta`);
* `z1`, `z2` — the Schnorr responses `z₁ = ac + d` and `z₂ = cr' + s`. -/
structure OpeningProof (F G : Type) (k : ℕ) where
  /-- The `k` rounds of `(L, R)` cross-term commitments. -/
  lr : Fin k → G × G
  /-- The final folded scalar. -/
  a : F
  /-- The final folded commitment base `g₀`. -/
  sg : G
  /-- The Schnorr blinding commitment (Halo's `R`). -/
  delta : G
  /-- The first Schnorr response `z₁ = ac + d`. -/
  z1 : F
  /-- The second Schnorr response `z₂ = cr' + s`. -/
  z2 : F

section Scheme

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] {d k : ℕ}

/-- Local oracle interface evaluating a coefficient vector as a polynomial: the
query is a point `z ∈ F`, and the answer is `p(z) = ∑ᵢ aᵢ zⁱ`. Mirrors the KZG
local `OracleInterface` instance on coefficient vectors. -/
local instance evalOracle : OracleInterface (Fin d → F) where
  Query := F
  toOC.spec := F →ₒ F
  toOC.impl z := do
    let a ← read
    return ∑ i, a i * z ^ (i : ℕ)

/-! ## The interactive opening protocol -/

/-- The protocol specification for the IPA opening of Halo §3.1, with
`2k + 5` rounds:

* round `0`: `V_to_P G` — the verifier's random group element `U`;
* rounds `1, …, 2k`: alternating `P_to_V (G × G)` (the prover's `(Lⱼ, Rⱼ)`) and
  `V_to_P F` (the verifier's fold challenge `uⱼ`);
* round `2k+1`: `P_to_V (F × G)` — the final folded `(a, g₀)`;
* round `2k+2`: `P_to_V G` — the Schnorr blinding commitment `δ`;
* round `2k+3`: `V_to_P F` — the Schnorr challenge `c`;
* round `2k+4`: `P_to_V (F × F)` — the Schnorr responses `(z₁, z₂)`. -/
def pSpec (F G : Type) [Field F] (k : ℕ) : ProtocolSpec (2 * k + 5) where
  dir := fun i =>
    if i.val = 0 then .V_to_P
    else if i.val ≤ 2 * k then (if i.val % 2 = 1 then .P_to_V else .V_to_P)
    else if i.val = 2 * k + 3 then .V_to_P
    else .P_to_V
  «Type» := fun i =>
    if i.val = 0 then G
    else if i.val ≤ 2 * k then (if i.val % 2 = 1 then (G × G) else Fˣ)
    else if i.val = 2 * k + 1 then (F × G)
    else if i.val = 2 * k + 2 then G
    else if i.val = 2 * k + 3 then F
    else (F × F)

/-! ## The honest prover's running state and folding kernel

The honest prover of Halo §3.1 is realized below as an ArkLib `Prover`. To keep the
per-round state type uniform (the ArkLib `Prover` indexes its state by the round, but
all our rounds carry the same running data) we record the entire evolving computation in
a single `IPAProverState`. The folded vectors `a'`, `b'`, `g'` are stored as total
functions `ℕ → F` / `ℕ → G` (only the first `len` entries are meaningful), which avoids
the dependent length bookkeeping of genuinely halving vectors; folding simply halves
`len` and recombines the lower/upper windows.

The blinders `lⱼ, rⱼ, d, s` of the zero-knowledge layer are instantiated to `0`. This is
faithful for the verification equation (they cancel algebraically — see Halo eq. (2) and
the Schnorr check `[c]Q + δ = [z₁](G+[b]U) + [z₂]H`), and so suffices for the correctness
theorem; the perfect-hiding/ZK refinement (genuine sampling) is intentionally out of scope
here, since the headline security theorems are correctness and binding. -/

/-- The honest prover's running state: the received `U`, the current folded coefficient
vector `a`, evaluation vector `b`, and base vector `g` (each as a total function with only
the first `len` entries live), the accumulated synthetic blinder `rAcc`, and the Schnorr
challenge `c`. -/
structure IPAProverState (F G : Type) where
  /-- The verifier's random group element `U` (received in the setup move). -/
  U : G
  /-- The current folded coefficient vector `a'`. -/
  a : ℕ → F
  /-- The current folded evaluation vector `b'`. -/
  b : ℕ → F
  /-- The current folded base vector `g'`. -/
  g : ℕ → G
  /-- The number of live entries of `a`, `b`, `g`. -/
  len : ℕ
  /-- The synthetic blinder `r'` accumulated across the fold (here just the initial `r`,
  since all per-round blinders are `0`). -/
  rAcc : F
  /-- The Schnorr challenge `c` (received in the penultimate move). -/
  c : F

/-- The multiscalar product `⟨a, g⟩ = ∑_{i<m} aᵢ • gᵢ` over the first `m` entries. -/
noncomputable def innerFG (a : ℕ → F) (g : ℕ → G) (m : ℕ) : G :=
  ∑ i ∈ Finset.range m, a i • g i

/-- The scalar inner product `⟨a, b⟩ = ∑_{i<m} aᵢ bᵢ` over the first `m` entries. -/
noncomputable def innerFF (a b : ℕ → F) (m : ℕ) : F :=
  ∑ i ∈ Finset.range m, a i * b i

/-- The cross-term `Lⱼ = ⟨a'_lo, g'_hi⟩ + [lⱼ]H + [⟨a'_lo, b'_hi⟩]U` of Halo §3.1, with the
blinder `lⱼ = 0`. The lower window is `[0, half)`, the upper window `[half, len)`. -/
noncomputable def Lval (st : IPAProverState F G) : G :=
  let half := st.len / 2
  innerFG st.a (fun i => st.g (half + i)) half
    + innerFF st.a (fun i => st.b (half + i)) half • st.U

/-- The cross-term `Rⱼ = ⟨a'_hi, g'_lo⟩ + [rⱼ]H + [⟨a'_hi, b'_lo⟩]U` of Halo §3.1, with the
blinder `rⱼ = 0`. -/
noncomputable def Rval (st : IPAProverState F G) : G :=
  let half := st.len / 2
  innerFG (fun i => st.a (half + i)) st.g half
    + innerFF (fun i => st.a (half + i)) st.b half • st.U

/-- The fold of the prover state under challenge `uⱼ`: `a' ← a'_hi·uⱼ⁻¹ + a'_lo·uⱼ`,
`b' ← b'_lo·uⱼ⁻¹ + b'_hi·uⱼ`, `g' ← g'_lo·uⱼ⁻¹ + g'_hi·uⱼ`, halving `len`. -/
noncomputable def foldState (st : IPAProverState F G) (u : F) : IPAProverState F G :=
  let half := st.len / 2
  { st with
    a := fun i => st.a (half + i) * u⁻¹ + st.a i * u
    b := fun i => st.b i * u⁻¹ + st.b (half + i) * u
    g := fun i => u⁻¹ • st.g i + u • st.g (half + i)
    len := half }

/-! ## The dependent message-type computation

`pSpec`'s message/challenge type at round `j` is given by a nested `if` on `j.val`. The
following seven lemmas read off the concrete type in each of the seven cases. They are
stated on an opaque index `j` (with the case hypotheses supplied), which keeps `simp` from
prematurely reducing the literal comparisons; applying them to a literal index `⟨n, _⟩`
discharges the hypotheses by `omega` (after a defeq `show` exposing `(⟨n, _⟩).val = n`). -/

omit [AddCommGroup G] [Module F G] in
/-- Round `0` carries the verifier's group element `U ∈ G`. -/
lemma pType_zero (j : Fin (2 * k + 5)) (h0 : j.val = 0) :
    (pSpec F G k).«Type» j = G := by simp only [pSpec]; rw [if_pos h0]

omit [AddCommGroup G] [Module F G] in
/-- An odd round `≤ 2k` carries a cross-term pair `(Lⱼ, Rⱼ) ∈ G × G`. -/
lemma pType_LR (j : Fin (2 * k + 5)) (h0 : ¬ j.val = 0) (h1 : j.val ≤ 2 * k)
    (h2 : j.val % 2 = 1) : (pSpec F G k).«Type» j = (G × G) := by
  simp only [pSpec]; rw [if_neg h0, if_pos h1, if_pos h2]

omit [AddCommGroup G] [Module F G] in
/-- An even round `≤ 2k` carries a fold challenge `uⱼ ∈ Fˣ`. -/
lemma pType_u (j : Fin (2 * k + 5)) (h0 : ¬ j.val = 0) (h1 : j.val ≤ 2 * k)
    (h2 : ¬ j.val % 2 = 1) : (pSpec F G k).«Type» j = Fˣ := by
  simp only [pSpec]; rw [if_neg h0, if_pos h1, if_neg h2]

omit [AddCommGroup G] [Module F G] in
/-- Round `2k+1` carries the final folded `(a, g₀) ∈ F × G`. -/
lemma pType_final (j : Fin (2 * k + 5)) (h0 : ¬ j.val = 0) (h1 : ¬ j.val ≤ 2 * k)
    (h3 : j.val = 2 * k + 1) : (pSpec F G k).«Type» j = (F × G) := by
  simp only [pSpec]; rw [if_neg h0, if_neg h1, if_pos h3]

omit [AddCommGroup G] [Module F G] in
/-- Round `2k+2` carries the Schnorr blinding commitment `δ ∈ G`. -/
lemma pType_delta (j : Fin (2 * k + 5)) (h0 : ¬ j.val = 0) (h1 : ¬ j.val ≤ 2 * k)
    (h3 : ¬ j.val = 2 * k + 1) (h4 : j.val = 2 * k + 2) : (pSpec F G k).«Type» j = G := by
  simp only [pSpec]; rw [if_neg h0, if_neg h1, if_neg h3, if_pos h4]

omit [AddCommGroup G] [Module F G] in
/-- Round `2k+3` carries the Schnorr challenge `c ∈ F`. -/
lemma pType_c (j : Fin (2 * k + 5)) (h0 : ¬ j.val = 0) (h1 : ¬ j.val ≤ 2 * k)
    (h3 : ¬ j.val = 2 * k + 1) (h4 : ¬ j.val = 2 * k + 2) (h5 : j.val = 2 * k + 3) :
    (pSpec F G k).«Type» j = F := by
  simp only [pSpec]; rw [if_neg h0, if_neg h1, if_neg h3, if_neg h4, if_pos h5]

omit [AddCommGroup G] [Module F G] in
/-- Round `2k+4` carries the Schnorr responses `(z₁, z₂) ∈ F × F`. -/
lemma pType_z (j : Fin (2 * k + 5)) (h0 : ¬ j.val = 0) (h1 : ¬ j.val ≤ 2 * k)
    (h3 : ¬ j.val = 2 * k + 1) (h4 : ¬ j.val = 2 * k + 2) (h5 : ¬ j.val = 2 * k + 3) :
    (pSpec F G k).«Type» j = (F × F) := by
  simp only [pSpec]; rw [if_neg h0, if_neg h1, if_neg h3, if_neg h4, if_neg h5]

/-- The honest prover's message at round `j`, typed at the dependent message type
`(pSpec F G k).«Type» j`. Odd rounds `≤ 2k` send `(Lⱼ, Rⱼ)`; round `2k+1` sends the final
folded `(a, g₀)`; round `2k+2` sends `δ = 0` (the blinders `d = s = 0`); round `2k+4`
sends the Schnorr responses `(z₁, z₂) = (a·c, c·r')`. The remaining (challenge) rounds are
never queried for a message, so any well-typed value will do. -/
noncomputable def msgVal (st : IPAProverState F G) (j : Fin (2 * k + 5)) :
    (pSpec F G k).«Type» j := by
  by_cases h0 : j.val = 0
  · rw [pType_zero j h0]; exact 0
  · by_cases h1 : j.val ≤ 2 * k
    · by_cases h2 : j.val % 2 = 1
      · rw [pType_LR j h0 h1 h2]; exact (Lval st, Rval st)
      · rw [pType_u j h0 h1 h2]; exact 1
    · by_cases h3 : j.val = 2 * k + 1
      · rw [pType_final j h0 h1 h3]; exact (st.a 0, st.g 0)
      · by_cases h4 : j.val = 2 * k + 2
        · rw [pType_delta j h0 h1 h3 h4]; exact 0
        · by_cases h5 : j.val = 2 * k + 3
          · rw [pType_c j h0 h1 h3 h4 h5]; exact 0
          · rw [pType_z j h0 h1 h3 h4 h5]; exact (st.a 0 * st.c, st.c * st.rAcc)

/-- The verifier's accept/reject decision for the IPA opening of Halo §3.1. It reads `U`,
the cross-terms `(Lⱼ, Rⱼ)`, the fold challenges `uⱼ`, the final base `g₀`, the Schnorr
commitment `δ`, challenge `c`, and responses `(z₁, z₂)` from the transcript, forms
`P' = P + [v]U`, `b = bPoly(u)(x)`, the recombined
`Q = ∑ⱼ [uⱼ²]Lⱼ + P' + ∑ⱼ [uⱼ⁻²]Rⱼ`, and accepts iff
`[c]Q + δ = [z₁](g₀ + [b]U) + [z₂]H`. -/
noncomputable def verifyCheck (vk : SRS G d) (stmt : G × (_q : F) × F)
    (transcript : (pSpec F G k).FullTranscript) : Bool := by
  classical
  refine ?_
  -- transcript reads, each casting the dependent message type to the concrete type
  let U : G := cast (pType_zero (F := F) ⟨0, by omega⟩ (by show (0 : ℕ) = 0; omega))
    (transcript ⟨0, by omega⟩)
  let uvec : Fin k → F := fun t =>
    ↑(cast (pType_u (G := G) ⟨2 * t.val + 2, by have := t.isLt; omega⟩
      (by show ¬ (2 * t.val + 2 : ℕ) = 0; omega)
      (by show (2 * t.val + 2 : ℕ) ≤ 2 * k; have := t.isLt; omega)
      (by show ¬ (2 * t.val + 2 : ℕ) % 2 = 1; omega))
      (transcript ⟨2 * t.val + 2, by have := t.isLt; omega⟩))
  let Lof : Fin k → G := fun t =>
    (cast (pType_LR ⟨2 * t.val + 1, by have := t.isLt; omega⟩
      (by show ¬ (2 * t.val + 1 : ℕ) = 0; omega)
      (by show (2 * t.val + 1 : ℕ) ≤ 2 * k; have := t.isLt; omega)
      (by show (2 * t.val + 1 : ℕ) % 2 = 1; omega))
      (transcript ⟨2 * t.val + 1, by have := t.isLt; omega⟩)).1
  let Rof : Fin k → G := fun t =>
    (cast (pType_LR ⟨2 * t.val + 1, by have := t.isLt; omega⟩
      (by show ¬ (2 * t.val + 1 : ℕ) = 0; omega)
      (by show (2 * t.val + 1 : ℕ) ≤ 2 * k; have := t.isLt; omega)
      (by show (2 * t.val + 1 : ℕ) % 2 = 1; omega))
      (transcript ⟨2 * t.val + 1, by have := t.isLt; omega⟩)).2
  let final : F × G :=
    cast (pType_final ⟨2 * k + 1, by omega⟩ (by show ¬ (2 * k + 1 : ℕ) = 0; omega)
      (by show ¬ (2 * k + 1 : ℕ) ≤ 2 * k; omega) (by show (2 * k + 1 : ℕ) = 2 * k + 1; omega))
      (transcript ⟨2 * k + 1, by omega⟩)
  let delta : G :=
    cast (pType_delta ⟨2 * k + 2, by omega⟩ (by show ¬ (2 * k + 2 : ℕ) = 0; omega)
      (by show ¬ (2 * k + 2 : ℕ) ≤ 2 * k; omega) (by show ¬ (2 * k + 2 : ℕ) = 2 * k + 1; omega)
      (by show (2 * k + 2 : ℕ) = 2 * k + 2; omega))
      (transcript ⟨2 * k + 2, by omega⟩)
  let c : F :=
    cast (pType_c ⟨2 * k + 3, by omega⟩ (by show ¬ (2 * k + 3 : ℕ) = 0; omega)
      (by show ¬ (2 * k + 3 : ℕ) ≤ 2 * k; omega) (by show ¬ (2 * k + 3 : ℕ) = 2 * k + 1; omega)
      (by show ¬ (2 * k + 3 : ℕ) = 2 * k + 2; omega) (by show (2 * k + 3 : ℕ) = 2 * k + 3; omega))
      (transcript ⟨2 * k + 3, by omega⟩)
  let resp : F × F :=
    cast (pType_z ⟨2 * k + 4, by omega⟩ (by show ¬ (2 * k + 4 : ℕ) = 0; omega)
      (by show ¬ (2 * k + 4 : ℕ) ≤ 2 * k; omega) (by show ¬ (2 * k + 4 : ℕ) = 2 * k + 1; omega)
      (by show ¬ (2 * k + 4 : ℕ) = 2 * k + 2; omega) (by show ¬ (2 * k + 4 : ℕ) = 2 * k + 3; omega))
      (transcript ⟨2 * k + 4, by omega⟩)
  let P : G := stmt.1
  let x : F := stmt.2.1
  let v : F := stmt.2.2
  let g0 : G := final.2
  let z1 : F := resp.1
  let z2 : F := resp.2
  let P' : G := P + v • U
  let b : F := Polynomial.eval x (bPoly uvec)
  let Q : G := (∑ t : Fin k, (uvec t) ^ 2 • Lof t) + P' + (∑ t : Fin k, (uvec t)⁻¹ ^ 2 • Rof t)
  exact @decide (c • Q + delta = z1 • (g0 + b • U) + z2 • vk.h) (Classical.propDecidable _)

/-- The interactive opening protocol of Halo §3.1, packaged as ArkLib's `Proof`
for the relation of `openingRelation` (the opening interface of the commitment
scheme). The committer and verifier keys both hold the full SRS, since both
parties need the generator vector to run the fold.

The prover is the honest folding prover (`msgVal`/`foldState`); the verifier is the
recombination-and-Schnorr check (`verifyCheck`). The zero-knowledge blinders are taken to
be `0` (faithful for the verification equation; see the module note above). -/
noncomputable def openingProof (keys : SRS G d × SRS G d) :
    Proof unifSpec (G × (_q : F) × F) ((Fin d → F) × F) (pSpec F G k) where
  prover :=
    { PrvState := fun _ => IPAProverState F G
      input := fun ⟨⟨_, x, _⟩, a0, r0⟩ =>
        { U := 0
          a := fun n => if h : n < d then a0 ⟨n, h⟩ else 0
          b := fun n => x ^ n
          g := fun n => if h : n < d then keys.1.g ⟨n, h⟩ else 0
          len := d
          rAcc := r0
          c := 0 }
      sendMessage := fun ⟨j, _⟩ st => pure (msgVal st j, st)
      receiveChallenge := fun ⟨j, hdir⟩ st => pure (by
        by_cases h0 : j.val = 0
        · exact fun chal => { st with U := cast (pType_zero j h0) chal }
        · by_cases h1 : j.val ≤ 2 * k
          · -- a fold round: the challenge index is even, so the message type is `F`
            have h2 : j.val % 2 = 0 := by
              by_contra hc
              have hodd : j.val % 2 = 1 := by omega
              have hdir' : (pSpec F G k).dir j = Direction.P_to_V := by
                simp only [pSpec]; rw [if_neg h0, if_pos h1, if_pos hodd]
              rw [hdir'] at hdir; exact absurd hdir (by decide)
            exact fun chal => foldState st ↑(cast (pType_u j h0 h1 (by omega)) chal)
          · -- past the fold rounds: the only `V_to_P` index is the Schnorr challenge `c`
            have h3 : j.val = 2 * k + 3 := by
              by_contra hc
              have hdir' : (pSpec F G k).dir j = Direction.P_to_V := by
                simp only [pSpec]; rw [if_neg h0, if_neg h1, if_neg hc]
              rw [hdir'] at hdir; exact absurd hdir (by decide)
            exact fun chal =>
              { st with c := cast (pType_c j h0 h1 (by omega) (by omega) h3) chal })
      output := fun _ => pure (true, ()) }
  verifier :=
    { verify := fun stmt transcript => pure (verifyCheck keys.2 stmt transcript) }

/-! ## The commitment scheme instance -/

/-- The IPA scheme as ArkLib's `Commitment.Scheme`, mirroring `KZG_Basic.lean`'s
`def kzg`:

* `Data` is a coefficient vector in `Fᵈ` with the evaluation `OracleInterface`;
* `Commitment = G`, `Decommitment = F` (the blinding `r`; the scheme is
  randomized, unlike KZG where it is `Unit`);
* `ComKey = VerifKey = SRS G d`;
* `keygen` samples the SRS (random generators `g` and blinding base `h`);
* `commit` is the Pedersen commitment `(⟨a, g⟩ + [r]h, r)` with fresh `r`;
* `opening` is the interactive opening protocol `openingProof`.

The `opening` field is a stub at this stage (it depends on `openingProof`). -/
noncomputable def ipa [SampleableType F] [SampleableType G] :
    Commitment.Scheme unifSpec (Fin d → F) G F (SRS G d) (SRS G d)
      (pSpec F G k) where
  keygen := do
    let g ← ($ᵗ (Fin d → G))
    let h ← ($ᵗ G)
    let srs : SRS G d := ⟨g, h⟩
    return (srs, srs)
  commit := fun ck a => do
    let r ← ($ᵗ F)
    return (commit ck a r, r)
  opening := openingProof

end Scheme

end Kimchi.Commitment.IPA
