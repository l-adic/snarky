/-
Copyright (c) 2025 O(1) Labs. Released under Apache 2.0 license.
-/
import Kimchi.Commitment.IPA.Basic
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Perfect Completeness of the IPA Polynomial Commitment

This file states the first of the two headline security properties of the IPA
polynomial commitment of `Kimchi.Commitment.IPA.Basic`: **perfect completeness**.
Informally, an honest prover always convinces the verifier of a true evaluation:
committing to a polynomial `p` of degree `< d` and then running the honest opening
protocol on a point `x` with the true value `v = p(x)` makes the verifier accept
with probability `1`. This is the completeness half of Halo's Theorem 1; binding
and extractability are deferred to their own sibling module.

The Lean statement follows the two-layer shape used by ArkLib's worked KZG
development (`references/arklib/KZG_Correctness.lean`,
`KZG.CommitmentScheme.correctness`): the interface-level predicate
`Commitment.perfectCorrectness` is what the honest-transcript algebraic accept
equation reduces to after the oracle-computation plumbing of `keygen`, `commit`,
and the opening reduction is unfolded.

## References

* [Halo] Bowe, Grigg, Hopwood, *Recursive Proof Composition without a Trusted
  Setup*, Section 3, Theorem 1 (perfect completeness).
-/

namespace Kimchi.Commitment.IPA.Correctness

open Commitment OracleSpec OracleComp ProtocolSpec

/-! ## The telescoping algebra of the IPA fold

This section develops the field/group algebra underlying step (ii) of the
blueprint proof (the telescoping collapse of Halo's `Q` to `[a₀](g₀+[b]U)+[r']H`).
It is stated purely over `Basic`'s honest-prover kernel
(`IPAProverState`, `innerFG`, `innerFF`, `Lval`, `Rval`, `foldState`), so it is
reusable independently of the oracle-computation plumbing.

The central identity is `innerSum_foldState`: one honest fold of the prover state
changes the *telescoping invariant* `⟨a,g⟩ + [⟨a,b⟩]U + [r]H` by exactly the
verifier's per-round contribution `[u²]Lⱼ + [u⁻²]Rⱼ`. Summed over the `k` rounds
this is Halo eq. (2). -/

section Telescope

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- The IPA **telescoping invariant** attached to a prover state and a blinding
base `H`: `⟨a,g⟩ + [⟨a,b⟩]U + [rAcc]H`, taken over the live window `st.len`. The
honest verifier's `Q` is exactly this quantity evaluated at the *initial* state
(`P' = P + [v]U`), and the fold relation below shows each round preserves it up to
the verifier's `[u²]L + [u⁻²]R` correction. -/
noncomputable def innerSum (st : IPAProverState F G) (H : G) : G :=
  innerFG st.a st.g st.len + innerFF st.a st.b st.len • st.U + st.rAcc • H

/-- One honest fold of the multiscalar product `⟨a,g⟩`. The folded length-`m`
inner product equals the full length-`2m` inner product plus the `u²`/`u⁻²`
weighted cross terms `⟨a_lo,g_hi⟩` and `⟨a_hi,g_lo⟩` — the group-valued half of
the telescoping step. Requires `u ≠ 0` (the fold divides by `u`). -/
lemma innerFG_foldState (a : ℕ → F) (g : ℕ → G) (u : F) (hu : u ≠ 0) (m : ℕ) :
    innerFG (fun i => a (m + i) * u⁻¹ + a i * u) (fun i => u⁻¹ • g i + u • g (m + i)) m
      = innerFG a g (2 * m) + u ^ 2 • innerFG a (fun i => g (m + i)) m
        + (u⁻¹) ^ 2 • innerFG (fun i => a (m + i)) g m := by
  simp only [innerFG]
  rw [two_mul, Finset.sum_range_add, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  match_scalars <;> (field_simp; try ring)

/-- One honest fold of the scalar inner product `⟨a,b⟩`. The scalar analogue of
`innerFG_foldState`: the folded `⟨a',b'⟩` equals `⟨a,b⟩` plus the `u²`/`u⁻²`
weighted cross terms `⟨a_lo,b_hi⟩` and `⟨a_hi,b_lo⟩`. Requires `u ≠ 0`. -/
lemma innerFF_foldState (a b : ℕ → F) (u : F) (hu : u ≠ 0) (m : ℕ) :
    innerFF (fun i => a (m + i) * u⁻¹ + a i * u) (fun i => b i * u⁻¹ + b (m + i) * u) m
      = innerFF a b (2 * m) + u ^ 2 * innerFF a (fun i => b (m + i)) m
        + (u⁻¹) ^ 2 * innerFF (fun i => a (m + i)) b m := by
  simp only [innerFF]
  rw [two_mul, Finset.sum_range_add, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/-- **The telescoping fold step** (heart of Halo eq. (2)). One honest folding round
under challenge `u ≠ 0` shifts the telescoping invariant `innerSum` by exactly the
verifier's per-round contribution `[u²]Lⱼ + [u⁻²]Rⱼ`:
`innerSum (foldState st u) H = innerSum st H + [u²]·Lval st + [u⁻²]·Rval st`.
The hypothesis `st.len = 2 * m` records that the live window halves cleanly (it is
always a power of two in the honest run). -/
lemma innerSum_foldState (st : IPAProverState F G) (H : G) (u : F) (hu : u ≠ 0)
    (m : ℕ) (hlen : st.len = 2 * m) :
    innerSum (foldState st u) H = innerSum st H + u ^ 2 • Lval st + (u⁻¹) ^ 2 • Rval st := by
  have hm : st.len / 2 = m := by omega
  simp only [innerSum, foldState, Lval, Rval, hm]
  rw [hlen, innerFG_foldState st.a st.g u hu m, innerFF_foldState st.a st.b u hu m]
  rw [add_smul, add_smul, smul_add, smul_add]
  module

/-- Apply the honest fold to the first `j` challenges `uvec 0, …, uvec (j-1)` in
order. `foldUpto st uvec j` is the prover's running state after `j` folding
rounds; `foldUpto st uvec 0 = st`. -/
noncomputable def foldUpto (st : IPAProverState F G) (uvec : ℕ → F) : ℕ → IPAProverState F G
  | 0 => st
  | j + 1 => foldState (foldUpto st uvec j) (uvec j)

/-- After `j` honest folds the live window has shrunk by `2^j`. -/
lemma foldUpto_len (st : IPAProverState F G) (uvec : ℕ → F) (j : ℕ) :
    (foldUpto st uvec j).len = st.len / 2 ^ j := by
  induction j with
  | zero => simp [foldUpto]
  | succ n ih =>
    simp only [foldUpto, foldState]
    rw [ih, Nat.div_div_eq_div_mul, ← pow_succ]

/-- **Telescoping of Halo's `Q` (step (ii) of the blueprint proof).** Over `j ≤ k`
honest folds of a length-`2^k` state with nonzero challenges, the telescoping
invariant `innerSum` accumulates exactly the verifier's per-round corrections:
`innerSum (foldUptoₖ) H = innerSum st H + ∑ⱼ ([uⱼ²]Lⱼ + [uⱼ⁻²]Rⱼ)`, where
`Lⱼ = Lval (foldUpto j)` and `Rⱼ = Rval (foldUpto j)` are the honest cross terms of
round `j`. Specialized to `j = k` this is Halo eq. (2): the verifier's recombined
`Q` (which is `innerSum` of the initial state `P'` plus the same corrections)
equals `innerSum (foldUptoₖ) = [a₀]g₀ + [a₀·b₀]U + [r]H`. -/
lemma innerSum_foldUpto (st : IPAProverState F G) (H : G) (uvec : ℕ → F) (k : ℕ)
    (hk : st.len = 2 ^ k) (j : ℕ) (hj : j ≤ k) (hu : ∀ i < j, uvec i ≠ 0) :
    innerSum (foldUpto st uvec j) H
      = innerSum st H + ∑ i ∈ Finset.range j,
          ((uvec i) ^ 2 • Lval (foldUpto st uvec i)
            + ((uvec i)⁻¹) ^ 2 • Rval (foldUpto st uvec i)) := by
  induction j with
  | zero => simp [foldUpto]
  | succ n ih =>
    have hn : n ≤ k := by omega
    have hun : ∀ i < n, uvec i ≠ 0 := fun i hi => hu i (by omega)
    -- the state after `n < k` folds still has even (in fact `2^(k-n)`) live length
    have hlen_n : (foldUpto st uvec n).len = 2 * 2 ^ (k - n - 1) := by
      have hpow : st.len / 2 ^ n = 2 ^ (k - n) := by rw [hk, Nat.pow_div hn (by norm_num)]
      rw [foldUpto_len, hpow, ← pow_succ']
      congr 1
      omega
    rw [Finset.sum_range_succ, foldUpto,
      innerSum_foldState (foldUpto st uvec n) H (uvec n) (hu n (by omega)) _ hlen_n,
      ih hn hun]
    abel

/-! ### Preservation lemmas and the honest accept identity

The fold preserves the verifier element `U`, the synthetic blinder `rAcc`, and the Schnorr
challenge `c` (they are carried unchanged through `foldState`'s `{st with …}`). After `k`
folds of a length-`2^k` state the live window has length `1`, so the telescoping invariant
collapses to the single residue `[a₀]g₀ + [a₀b₀]U + [r]H`. Combining this with
`innerSum_foldUpto` (Halo eq. (2)) and the honest Schnorr responses yields the verifier's
accept equation — this is steps (ii)+(iii) of the blueprint proof, packaged as a single
field/group identity independent of the oracle plumbing. -/

/-- The fold preserves the received verifier element `U`. -/
lemma foldUpto_U (st : IPAProverState F G) (uvec : ℕ → F) (j : ℕ) :
    (foldUpto st uvec j).U = st.U := by
  induction j with
  | zero => rfl
  | succ n ih => simpa only [foldUpto, foldState] using ih

/-- The fold preserves the accumulated synthetic blinder `rAcc`. -/
lemma foldUpto_rAcc (st : IPAProverState F G) (uvec : ℕ → F) (j : ℕ) :
    (foldUpto st uvec j).rAcc = st.rAcc := by
  induction j with
  | zero => rfl
  | succ n ih => simpa only [foldUpto, foldState] using ih

/-- **The honest accept identity (steps (ii)+(iii) of the blueprint proof).** For a
length-`2^k` initial prover state with nonzero fold challenges, the honest Schnorr equation
`[c]Q + 0 = [a₀c](g₀ + [b₀]U) + [c·r]H` holds, where `Q = ∑ⱼ[uⱼ²]Lⱼ + innerSum st₀ H +
∑ⱼ[uⱼ⁻²]Rⱼ` is the verifier's recombination (with `innerSum st₀ H = P'` once the opening
relation is substituted) and `a₀, g₀, b₀, r` are the length-one residues of the fold. The
proof telescopes `Q` to `innerSum (foldUptoₖ) H` via `innerSum_foldUpto`, expands the
length-one invariant, and closes the scalar bilinearity by `module`. -/
lemma honest_accept (st0 : IPAProverState F G) (H : G) (uvec : ℕ → F) (c : F) (k : ℕ)
    (hlen : st0.len = 2 ^ k) (hu : ∀ i < k, uvec i ≠ 0) :
    c • ((∑ t ∈ Finset.range k, uvec t ^ 2 • Lval (foldUpto st0 uvec t))
          + innerSum st0 H
          + ∑ t ∈ Finset.range k, (uvec t)⁻¹ ^ 2 • Rval (foldUpto st0 uvec t))
      = ((foldUpto st0 uvec k).a 0 * c) •
            ((foldUpto st0 uvec k).g 0 + (foldUpto st0 uvec k).b 0 • st0.U)
          + (c * (foldUpto st0 uvec k).rAcc) • H := by
  -- the live window has collapsed to length one
  have hlen1 : (foldUpto st0 uvec k).len = 1 := by
    rw [foldUpto_len, hlen, Nat.div_self (pow_pos (by norm_num : (0:ℕ) < 2) k)]
  have hU : (foldUpto st0 uvec k).U = st0.U := foldUpto_U st0 uvec k
  -- Halo eq. (2): the recombined Q is the telescoped invariant at the final state
  have htel := innerSum_foldUpto st0 H uvec k hlen k (le_refl k) hu
  have hsum : (∑ t ∈ Finset.range k, uvec t ^ 2 • Lval (foldUpto st0 uvec t))
        + innerSum st0 H
        + ∑ t ∈ Finset.range k, (uvec t)⁻¹ ^ 2 • Rval (foldUpto st0 uvec t)
      = innerSum (foldUpto st0 uvec k) H := by
    rw [htel, Finset.sum_add_distrib]; abel
  -- expand the length-one invariant
  have hIS : innerSum (foldUpto st0 uvec k) H
      = (foldUpto st0 uvec k).a 0 • (foldUpto st0 uvec k).g 0
        + ((foldUpto st0 uvec k).a 0 * (foldUpto st0 uvec k).b 0) • st0.U
        + (foldUpto st0 uvec k).rAcc • H := by
    simp only [innerSum, innerFG, innerFF, hlen1, Finset.range_one, Finset.sum_singleton, hU]
  rw [hsum, hIS]
  module

/-- **Step (i): the fold of the powers-of-`x` vector telescopes.** If the initial evaluation
vector is `b i = xⁱ` over a length-`2^k` window, then after `j ≤ k` honest folds the entry
`i < 2^{k-j}` equals `xⁱ · ∏_{t<j} (uₜ⁻¹ + uₜ·x^{2^{k-1-t}})`. Induction on `j`; each round
contributes the symmetric factor of the fold. Specialized to `j = k, i = 0` this is the
folded residue `b₀ = ∏_{t<k} (uₜ⁻¹ + uₜ·x^{2^{k-1-t}})`, which `bPoly_eval_eq` identifies with
`eval x (bPoly u)`. -/
lemma foldUpto_b (st0 : IPAProverState F G) (uvec : ℕ → F) (x : F) (k : ℕ)
    (hlen : st0.len = 2 ^ k) (hb0 : ∀ n, st0.b n = x ^ n) :
    ∀ j ≤ k, ∀ i < 2 ^ (k - j),
      (foldUpto st0 uvec j).b i
        = x ^ i * ∏ t ∈ Finset.range j, ((uvec t)⁻¹ + uvec t * x ^ (2 ^ (k - 1 - t))) := by
  intro j
  induction j with
  | zero =>
    intro _ i _
    simp only [foldUpto, Finset.range_zero, Finset.prod_empty, mul_one, hb0]
  | succ n ih =>
    intro hsucc i hi
    have hn : n ≤ k := by omega
    -- the length of the state after `n` folds
    have hlenn : (foldUpto st0 uvec n).len = 2 ^ (k - n) := by
      rw [foldUpto_len, hlen, Nat.pow_div hn (by norm_num)]
    have hhalf : (foldUpto st0 uvec n).len / 2 = 2 ^ (k - 1 - n) := by
      rw [hlenn]
      have : k - n = (k - 1 - n) + 1 := by omega
      rw [this, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hi1 : i < 2 ^ (k - n) := by
      have : 2 ^ (k - (n + 1)) ≤ 2 ^ (k - n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hi2 : (foldUpto st0 uvec n).len / 2 + i < 2 ^ (k - n) := by
      rw [hhalf]
      have hkn : k - n = (k - 1 - n) + 1 := by omega
      have hlt : i < 2 ^ (k - 1 - n) := by
        have : k - (n + 1) = k - 1 - n := by omega
        rwa [this] at hi
      rw [hkn, pow_succ]; omega
    -- unfold one fold and apply the induction hypothesis to both windows
    simp only [foldUpto, foldState]
    rw [ih hn i hi1, ih hn _ hi2, hhalf, Finset.prod_range_succ]
    rw [pow_add]
    ring

/-- **Step (i), packaged.** The verifier's recomputed scalar `b = eval x (bPoly u)` equals the
prover's folded residue `b₀ = (foldUptoₖ).b 0`, when the fold uses the (ℕ-extended) challenge
vector `uvec i = chals ⟨i,·⟩`. This is the symmetric form of Halo eq. (3): unwinding the fold
of the powers-of-`x` vector gives `∏_{t<k}(uₜ⁻¹ + uₜ x^{2^{k-1-t}})`, which is exactly
`eval x (bPoly chals)` after reindexing the `bPoly` product by `Fin.rev`. -/
lemma bPoly_eval_eq (st0 : IPAProverState F G) (x : F) (chals : Fin k → F)
    (hlen : st0.len = 2 ^ k) (hb0 : ∀ n, st0.b n = x ^ n) :
    Polynomial.eval x (bPoly chals)
      = (foldUpto st0 (fun i => if h : i < k then chals ⟨i, h⟩ else 1) k).b 0 := by
  set uvecN : ℕ → F := fun i => if h : i < k then chals ⟨i, h⟩ else 1 with huv
  -- the folded residue, via the telescope at `j = k`, `i = 0`
  have hfold := foldUpto_b st0 uvecN x k hlen hb0 k (le_refl k) 0 (by simp)
  rw [hfold, pow_zero, one_mul]
  -- evaluate the `bPoly` product
  simp only [bPoly, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  -- rewrite the range-product over `Fin k`
  rw [← Fin.prod_univ_eq_prod_range
    (fun t => (uvecN t)⁻¹ + uvecN t * x ^ (2 ^ (k - 1 - t))) k]
  -- reindex the `bPoly` product by `Fin.rev`
  rw [← Equiv.prod_comp Fin.revPerm
    (fun i : Fin k => (uvecN i.val)⁻¹ + uvecN i.val * x ^ (2 ^ (k - 1 - i.val)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hrev : (Fin.revPerm i : Fin k).val = k - 1 - i.val := by
    simp [Fin.revPerm, Fin.val_rev]; omega
  have hval : uvecN (Fin.revPerm i : Fin k).val = chals i.rev := by
    rw [hrev, huv]
    have hlt : k - 1 - i.val < k := by omega
    simp only [hlt, dif_pos]
    congr 1
    simp [Fin.rev, Fin.ext_iff]; omega
  rw [hval, hrev]
  have hi := i.isLt
  rw [show k - 1 - (k - 1 - i.val) = i.val by omega]

end Telescope

section Correctness

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] {d k : ℕ}

/-- Local oracle interface evaluating a coefficient vector as a polynomial: the
query is a point `z ∈ F`, and the answer is `p(z) = ∑ᵢ aᵢ zⁱ`. Declared here so
`ipa` typechecks, exactly as in `Basic`/KZG. -/
local instance evalOracle : OracleInterface (Fin d → F) where
  Query := F
  toOC.spec := F →ₒ F
  toOC.impl z := do
    let a ← read
    return ∑ i, a i * z ^ (i : ℕ)

/-- **The honest input-state telescoping invariant equals `P' = P + [v]U`.** The honest prover's
input state (coefficient vector `data` padded to length `d`, evaluation vector the powers of
`x`, base vector `ck.g` padded, blinder `r0`) telescopes to the verifier's recombination base:
`innerSum (input) ck.h = commit ck data r0 + [⟨data, (xⁱ)⟩]U`. With `commit ck data r0 = P` and
`⟨data,(xⁱ)⟩ = v` this is `P + [v]U = P'`. -/
lemma innerSum_input (ck : SRS G d) (data : Fin d → F) (r0 x : F) (U : G) :
    innerSum
        { U := U
          a := fun n => if h : n < d then data ⟨n, h⟩ else 0
          b := fun n => x ^ n
          g := fun n => if h : n < d then ck.g ⟨n, h⟩ else 0
          len := d
          rAcc := r0
          c := 0 } ck.h
      = commit ck data r0 + (∑ i, data i * x ^ (i : ℕ)) • U := by
  simp only [innerSum, innerFG, innerFF, commit]
  -- the two `range d` sums become `Fin d` sums (the `if` guards are all `dif_pos`)
  have hFG : (∑ i ∈ Finset.range d,
      (if h : i < d then data ⟨i, h⟩ else 0) • (if h : i < d then ck.g ⟨i, h⟩ else 0))
      = ∑ i, data i • ck.g i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < d then data ⟨i, h⟩ else 0)
      • (if h : i < d then ck.g ⟨i, h⟩ else 0)) d]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [i.isLt, dif_pos, Fin.eta]
  have hFF : (∑ i ∈ Finset.range d,
      (if h : i < d then data ⟨i, h⟩ else 0) * x ^ i)
      = ∑ i, data i * x ^ (i : ℕ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < d then data ⟨i, h⟩ else 0) * x ^ i) d]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [i.isLt, dif_pos, Fin.eta]
  rw [hFG, hFF]
  abel

/-- **The honest verifier accept equation, in the exact shape produced by unfolding
`verifyCheck`.** This is `honest_accept` (steps (ii)+(iii)) combined with `bPoly_eval_eq`
(step (i)): once the verifier's transcript reads are replaced by their honest values
(`Lⱼ = Lval (foldUptoⱼ)`, `Rⱼ = Rval (foldUptoⱼ)`, `g₀ = (foldUptoₖ).g 0`, `z₁ = a₀c`,
`z₂ = c·rAcc`, `δ = 0`, `b = eval x (bPoly chals)`) the `decide`d equation is closed.
The `Fin k`-sums of the verifier match the `Finset.range k`-sums of `honest_accept` through the
ℕ-extended challenge vector `uvecN`. -/
lemma honest_eq (st0 : IPAProverState F G) (cc x : F) (chals : Fin k → F) (vkh : G)
    (hlen : st0.len = 2 ^ k) (hu : ∀ i : Fin k, chals i ≠ 0) (hb : ∀ n, st0.b n = x ^ n) :
    cc •
        ((∑ t : Fin k, (chals t) ^ 2 •
              Lval (foldUpto st0 (fun i => if h : i < k then chals ⟨i, h⟩ else 1) t))
            + innerSum st0 vkh
            + ∑ t : Fin k, (chals t)⁻¹ ^ 2 •
              Rval (foldUpto st0 (fun i => if h : i < k then chals ⟨i, h⟩ else 1) t))
          + (0 : G)
      = ((foldUpto st0 (fun i => if h : i < k then chals ⟨i, h⟩ else 1) k).a 0 * cc) •
            ((foldUpto st0 (fun i => if h : i < k then chals ⟨i, h⟩ else 1) k).g 0
              + Polynomial.eval x (bPoly chals) • st0.U)
          + (cc * st0.rAcc) • vkh := by
  -- step (i): the verifier's recomputed `b` is the folded residue `b₀`
  rw [bPoly_eval_eq st0 x chals hlen hb]
  set uvecN : ℕ → F := fun i => if h : i < k then chals ⟨i, h⟩ else 1 with huv
  -- the ℕ-extended challenge vector is nonzero on `[0, k)`
  have huN : ∀ i < k, uvecN i ≠ 0 := by
    intro i hi
    simp only [huv, hi, dif_pos]
    exact hu ⟨i, hi⟩
  -- the blinder accumulator is preserved by the fold
  rw [add_zero, ← foldUpto_rAcc st0 uvecN k]
  -- convert the `Fin k`-sums to `Finset.range k`-sums matching `honest_accept`
  have hL : (∑ t : Fin k, (chals t) ^ 2 • Lval (foldUpto st0 uvecN t))
      = ∑ t ∈ Finset.range k, uvecN t ^ 2 • Lval (foldUpto st0 uvecN t) := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => uvecN t ^ 2 • Lval (foldUpto st0 uvecN t)) k]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [huv, t.isLt, dif_pos, Fin.eta]
  have hR : (∑ t : Fin k, (chals t)⁻¹ ^ 2 • Rval (foldUpto st0 uvecN t))
      = ∑ t ∈ Finset.range k, (uvecN t)⁻¹ ^ 2 • Rval (foldUpto st0 uvecN t) := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => (uvecN t)⁻¹ ^ 2 • Rval (foldUpto st0 uvecN t)) k]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [huv, t.isLt, dif_pos, Fin.eta]
  rw [hL, hR]
  exact honest_accept st0 vkh uvecN cc k hlen huN

/-- **Cast-cancellation for the honest `(Lⱼ, Rⱼ)` message.** Reading the prover's odd-round message
back through the verifier's cast recovers the honest cross-term pair `(Lval st, Rval st)`. This is
one of the per-round cancellation lemmas the `runToRound` honest-execution characterization
(residue B) feeds into the verifier's reads. -/
lemma msgVal_LR_cast (st : IPAProverState F G) (j : Fin (2 * k + 5))
    (h0 : ¬ j.val = 0) (h1 : j.val ≤ 2 * k) (h2 : j.val % 2 = 1) :
    cast (pType_LR (F := F) (G := G) (k := k) j h0 h1 h2) (msgVal st j) = (Lval st, Rval st) := by
  simp only [msgVal, h0, h1, h2, dif_neg, dif_pos, not_false_eq_true, eq_mpr_eq_cast,
    cast_cast, cast_eq]

/-- **Cast-cancellation for the final folded `(a₀, g₀)` message** (round `2k+1`). -/
lemma msgVal_final_cast (st : IPAProverState F G) (j : Fin (2 * k + 5))
    (h0 : ¬ j.val = 0) (h1 : ¬ j.val ≤ 2 * k) (h3 : j.val = 2 * k + 1) :
    cast (pType_final (F := F) (G := G) (k := k) j h0 h1 h3) (msgVal st j) = (st.a 0, st.g 0) := by
  unfold msgVal
  rw [dif_neg h0, dif_neg h1, dif_pos h3]
  simp only [eq_mpr_eq_cast, cast_cast, cast_eq]

/-- **Cast-cancellation for the Schnorr blinding commitment `δ = 0`** (round `2k+2`). -/
lemma msgVal_delta_cast (st : IPAProverState F G) (j : Fin (2 * k + 5))
    (h0 : ¬ j.val = 0) (h1 : ¬ j.val ≤ 2 * k) (h3 : ¬ j.val = 2 * k + 1) (h4 : j.val = 2 * k + 2) :
    cast (pType_delta (F := F) (G := G) (k := k) j h0 h1 h3 h4) (msgVal st j) = (0 : G) := by
  unfold msgVal
  rw [dif_neg h0, dif_neg h1, dif_neg h3, dif_pos h4]
  simp only [eq_mpr_eq_cast, cast_cast, cast_eq]

/-- **Cast-cancellation for the Schnorr responses `(z₁, z₂) = (a₀·c, c·r')`** (round `2k+4`). -/
lemma msgVal_z_cast (st : IPAProverState F G) (j : Fin (2 * k + 5))
    (h0 : ¬ j.val = 0) (h1 : ¬ j.val ≤ 2 * k) (h3 : ¬ j.val = 2 * k + 1)
    (h4 : ¬ j.val = 2 * k + 2) (h5 : ¬ j.val = 2 * k + 3) :
    cast (pType_z (F := F) (G := G) (k := k) j h0 h1 h3 h4 h5) (msgVal st j)
      = (st.a 0 * st.c, st.c * st.rAcc) := by
  simp only [msgVal, h0, h1, h3, h4, h5, dif_neg, not_false_eq_true, eq_mpr_eq_cast,
    cast_cast, cast_eq]

/-! ### The honest-run support characterization (residue B)

The lemmas below characterize the support of `Prover.runToRound (Fin.last (2k+5))`. The strategy
is a `Fin.induction` over the round index carrying a *replay-state invariant*: on any support
element `(T, st)`, the running state `st` equals the honest replay state `stUpto T (round)`, and
each prover-to-verifier message read off `T` equals `msgVal` of the replay state at that round.
The replay state is the honest input state (with `U` installed from the round-0 read) folded by
the fold challenges read off `T`, with the Schnorr challenge `c` installed past round `2k+3`. -/

/-- Read the verifier's group element `U` off the partial transcript `T` (round-0 entry); the
default `0` is never used on the support (it agrees with the prover's initial `U = 0`). -/
private noncomputable def Uread (i : Fin (2 * k + 5 + 1))
    (T : (pSpec F G k).Transcript i) : G :=
  if h : 0 < i.val then
    cast (pType_zero (F := F) (G := G) (k := k) (Fin.castLE i.is_le ⟨0, h⟩) rfl) (T ⟨0, h⟩)
  else 0

/-- Read the `t`-th fold challenge `uₜ ∈ Fˣ` off the partial transcript `T` (entry `2t+2`), as a
field element; the default `1` is used outside the genuine fold window. -/
private noncomputable def uread (i : Fin (2 * k + 5 + 1))
    (T : (pSpec F G k).Transcript i) (t : ℕ) : F :=
  if h : t < k ∧ 2 * t + 2 < i.val then
    (cast (pType_u (F := F) (G := G) (k := k) (Fin.castLE i.is_le ⟨2 * t + 2, h.2⟩)
      (by have : (Fin.castLE i.is_le ⟨2 * t + 2, h.2⟩).val = 2 * t + 2 := rfl; omega)
      (by have : (Fin.castLE i.is_le ⟨2 * t + 2, h.2⟩).val = 2 * t + 2 := rfl; omega)
      (by have : (Fin.castLE i.is_le ⟨2 * t + 2, h.2⟩).val = 2 * t + 2 := rfl; omega))
      (T ⟨2 * t + 2, h.2⟩) : Fˣ).val
  else 1

/-- Read the Schnorr challenge `c ∈ F` off the partial transcript `T` (entry `2k+3`). -/
private noncomputable def cread (i : Fin (2 * k + 5 + 1))
    (T : (pSpec F G k).Transcript i) : F :=
  if h : 2 * k + 3 < i.val then
    cast (pType_c (F := F) (G := G) (k := k) (Fin.castLE i.is_le ⟨2 * k + 3, h⟩)
      (by have : (Fin.castLE i.is_le ⟨2 * k + 3, h⟩).val = 2 * k + 3 := rfl; omega)
      (by have : (Fin.castLE i.is_le ⟨2 * k + 3, h⟩).val = 2 * k + 3 := rfl; omega)
      (by have : (Fin.castLE i.is_le ⟨2 * k + 3, h⟩).val = 2 * k + 3 := rfl; omega)
      (by have : (Fin.castLE i.is_le ⟨2 * k + 3, h⟩).val = 2 * k + 3 := rfl; omega)
      (by have : (Fin.castLE i.is_le ⟨2 * k + 3, h⟩).val = 2 * k + 3 := rfl; omega))
      (T ⟨2 * k + 3, h⟩)
  else 0

/-- The honest input prover state with the round-0 group element `U0` installed. -/
private noncomputable def inputStU (ck : SRS G d) (data : Fin d → F) (decomm query : F)
    (U0 : G) : IPAProverState F G :=
  { U := U0
    a := fun n => if h : n < d then data ⟨n, h⟩ else 0
    b := fun n => query ^ n
    g := fun n => if h : n < d then ck.g ⟨n, h⟩ else 0
    len := d
    rAcc := decomm
    c := 0 }

/-- The honest replay state at round `m` derived from the partial transcript `T`: the input state
(with `U` installed) folded by the `min k ((m-1)/2)` fold challenges read off `T`, with the
Schnorr challenge installed once `m` is past round `2k+3`. -/
private noncomputable def stUpto (ck : SRS G d) (data : Fin d → F) (decomm query : F)
    (i : Fin (2 * k + 5 + 1)) (T : (pSpec F G k).Transcript i) (m : ℕ) : IPAProverState F G :=
  let s := foldUpto (inputStU ck data decomm query (Uread i T)) (uread i T) (min k ((m - 1) / 2))
  if 2 * k + 4 ≤ m then { s with c := cread i T } else s

/-- `foldUpto` only consults the challenge function on indices `[0, n)`. -/
private lemma foldUpto_congr (st : IPAProverState F G) (u v : ℕ → F) (n : ℕ)
    (h : ∀ s < n, u s = v s) : foldUpto st u n = foldUpto st v n := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [foldUpto]; rw [ih (fun s hs => h s (by omega)), h m (by omega)]

omit [Module F G] in
/-- `Uread` is stable under appending one entry: it only reads index `0`, which is unchanged
by `Fin.snoc` when `0 < i.val`. -/
private lemma Uread_snoc (i : Fin (2 * k + 5)) (T' : (pSpec F G k).Transcript i.castSucc)
    (x : (pSpec F G k).«Type» i) (hi : 1 ≤ i.val) :
    Uread i.succ (Fin.snoc T' x) = Uread i.castSucc T' := by
  simp only [Uread, Fin.val_succ, Fin.val_castSucc]
  rw [dif_pos (by omega), dif_pos (by omega)]
  congr 1
  rw [Fin.snoc]; rw [dif_pos (show (0 : ℕ) < i.val by omega)]; rfl

omit [AddCommGroup G] [Module F G] in
/-- `uread t` reads index `2t+2`; stable under appending one entry when `2t+2 < i.val`. -/
private lemma uread_snoc (i : Fin (2 * k + 5)) (T' : (pSpec F G k).Transcript i.castSucc)
    (x : (pSpec F G k).«Type» i) (t : ℕ) (ht : 2 * t + 2 < i.val) :
    uread i.succ (Fin.snoc T' x) t = uread i.castSucc T' t := by
  simp only [uread, Fin.val_succ, Fin.val_castSucc]
  by_cases htk : t < k
  · rw [dif_pos ⟨htk, by omega⟩, dif_pos ⟨htk, ht⟩]
    congr 2
    rw [Fin.snoc]; rw [dif_pos (show 2 * t + 2 < i.val by omega)]; rfl
  · rw [dif_neg (fun hc => htk hc.1), dif_neg (fun hc => htk hc.1)]

omit [AddCommGroup G] [Module F G] in
/-- `cread` reads index `2k+3`; stable under appending one entry when `2k+3 < i.val`. -/
private lemma cread_snoc (i : Fin (2 * k + 5)) (T' : (pSpec F G k).Transcript i.castSucc)
    (x : (pSpec F G k).«Type» i) (hc : 2 * k + 3 < i.val) :
    cread i.succ (Fin.snoc T' x) = cread i.castSucc T' := by
  simp only [cread, Fin.val_succ, Fin.val_castSucc]
  rw [dif_pos (by omega), dif_pos hc]
  congr 1
  rw [Fin.snoc]; rw [dif_pos (show 2 * k + 3 < i.val by omega)]; rfl

/-- **Transcript locality of the replay state.** On past rounds `m ≤ i.val` (with `i.val ≥ 1`),
the honest replay state computed from `Fin.snoc T' x` agrees with the one from `T'`: appending the
round-`i` entry does not change any read at an index `< i.val`. -/
private lemma stUpto_snoc (ck : SRS G d) (data : Fin d → F) (decomm query : F)
    (i : Fin (2 * k + 5)) (T' : (pSpec F G k).Transcript i.castSucc)
    (x : (pSpec F G k).«Type» i) (m : ℕ) (hi : 1 ≤ i.val) (hm : m ≤ i.val) :
    stUpto ck data decomm query i.succ (Fin.snoc T' x) m
      = stUpto ck data decomm query i.castSucc T' m := by
  simp only [stUpto]
  rw [Uread_snoc i T' x hi]
  rw [foldUpto_congr (inputStU ck data decomm query (Uread i.castSucc T'))
        (uread i.succ (Fin.snoc T' x)) (uread i.castSucc T') (min k ((m - 1) / 2))
        (fun s hs => uread_snoc i T' x s (by
          have : s < (m - 1) / 2 := lt_of_lt_of_le hs (min_le_right _ _)
          omega))]
  by_cases hcc : 2 * k + 4 ≤ m
  · rw [if_pos hcc, if_pos hcc, cread_snoc i T' x (by omega)]
  · rw [if_neg hcc, if_neg hcc]

/-- `stUpto` depends on the round number `m` only through the fold depth `min k ((m-1)/2)` and the
Schnorr-install threshold `2k+4 ≤ m`. -/
private lemma stUpto_m_congr (ck : SRS G d) (data : Fin d → F) (decomm query : F)
    (i : Fin (2 * k + 5 + 1)) (T : (pSpec F G k).Transcript i) (m m' : ℕ)
    (hd : min k ((m - 1) / 2) = min k ((m' - 1) / 2))
    (hc : (2 * k + 4 ≤ m) ↔ (2 * k + 4 ≤ m')) :
    stUpto ck data decomm query i T m = stUpto ck data decomm query i T m' := by
  simp only [stUpto, hd]
  by_cases h : 2 * k + 4 ≤ m
  · rw [if_pos h, if_pos (hc.mp h)]
  · rw [if_neg h, if_neg (fun hh => h (hc.mpr hh))]

omit [AddCommGroup G] [Module F G] in
/-- Arithmetic characterization of the prover-to-verifier rounds of `pSpec`. -/
private lemma dir_PtoV_cases (i : Fin (2 * k + 5)) (h : (pSpec F G k).dir i = Direction.P_to_V) :
    (i.val ≤ 2 * k ∧ i.val % 2 = 1) ∨ i.val = 2 * k + 1 ∨ i.val = 2 * k + 2
      ∨ i.val = 2 * k + 4 := by
  have hlt := i.isLt
  simp only [pSpec] at h
  split_ifs at h with h0 h1 h2 h3 <;> first | exact absurd h (by decide) | omega

omit [AddCommGroup G] [Module F G] in
/-- Arithmetic characterization of the verifier-to-prover rounds of `pSpec`. -/
private lemma dir_VtoP_cases (i : Fin (2 * k + 5)) (h : (pSpec F G k).dir i = Direction.V_to_P) :
    i.val = 0 ∨ (i.val ≤ 2 * k ∧ i.val % 2 = 0) ∨ i.val = 2 * k + 3 := by
  have hlt := i.isLt
  simp only [pSpec] at h
  split_ifs at h with h0 h1 h2 h3 <;> first | exact absurd h (by decide) | omega

/-- **The honest-run support characterization.** On any support element `(T, st)` of the prover's
run up to round `i`, the state `st` is the honest replay state `stUpto T i`, and every
prover-to-verifier message recorded in `T` equals `msgVal` of the replay state at that round.
Proved by `Fin.induction` on the round index, mirroring `Prover.processRound`. -/
private lemma support_runToRound (ck : SRS G d) (data : Fin d → F) (decomm query : F)
    (i : Fin (2 * k + 5 + 1)) :
    ∀ (T : (pSpec F G k).Transcript i) (st : IPAProverState F G),
    (T, st) ∈ support
        ((openingProof (F := F) (G := G) (d := d) (k := k) (ck, ck)).prover.runToRound i
          (commit ck data decomm, ⟨query, OracleInterface.answer data query⟩) (data, decomm)) →
    st = stUpto ck data decomm query i T i.val ∧
    ∀ (j : Fin i.val), (pSpec F G k).dir (Fin.castLE i.is_le j) = Direction.P_to_V →
        T j = msgVal (stUpto ck data decomm query i T j.val) (Fin.castLE i.is_le j) := by
  induction i using Fin.induction with
  | zero =>
    intro T st hp
    rw [Prover.runToRound_zero_of_prover_first] at hp
    simp only [support_pure] at hp
    obtain ⟨hT, hst⟩ := Prod.mk.inj hp
    refine ⟨?_, fun j => j.elim0⟩
    -- the initial replay state is the honest prover input (`U = 0`, no folds, no `c`)
    subst hst
    simp only [stUpto, Uread, Fin.val_zero, lt_irrefl, dif_neg, not_false_eq_true,
      Nat.zero_sub, Nat.zero_div, Nat.min_zero, foldUpto]
    rfl
  | succ i ih =>
    intro T st hp
    -- The run up to round `i+1` is one `processRound` applied to the run up to round `i`.
    have hstep :
        (openingProof (F := F) (G := G) (d := d) (k := k) (ck, ck)).prover.runToRound i.succ
            (commit ck data decomm, ⟨query, OracleInterface.answer data query⟩) (data, decomm)
          = (openingProof (F := F) (G := G) (d := d) (k := k) (ck, ck)).prover.processRound i
              ((openingProof (F := F) (G := G) (d := d) (k := k) (ck, ck)).prover.runToRound
                i.castSucc (commit ck data decomm, ⟨query, OracleInterface.answer data query⟩)
                (data, decomm)) := by
      rw [Prover.runToRound, Fin.induction_succ]; rfl
    rw [hstep] at hp
    -- RESIDUE (B), the per-round honest-execution step. `hp` is now membership in the support of
    -- `processRound i (runToRound i.castSucc …)`, a `bind` whose continuation cases on
    -- `(pSpec F G k).dir i`:
    --   * `V_to_P`: `Fin.snoc`s the sampled challenge (support `= Set.univ`, `getChallenge` is a
    --     query) and updates the state via `receiveChallenge` (round 0 installs `U`, the even
    --     rounds `2t+2` fold by `uₜ`, round `2k+3` installs `c`);
    --   * `P_to_V`: `Fin.snoc`s `msgVal state ⟨i⟩`, leaving the state unchanged.
    -- The remaining gap is to unwind this `bind` (`mem_support_bind_iff` does not fire directly
    -- through the dependent `match`-on-`dir` continuation — a `support_bind`/`Set.mem_iUnion`
    -- unfolding plus a `dir i` case split is needed), apply `ih` to the round-`i` element, and
    -- propagate the replay-state invariant through `Fin.snoc` (`Fin.snoc_castSucc`/`Fin.snoc_last`
    -- for transcript locality; `stUpto` is stable on indices `< i`).  All consuming infrastructure
    -- (`runToRound_verifyCheck` and the full algebra) is proven and axiom-clean.
    simp only [Prover.processRound, support_bind] at hp
    obtain ⟨⟨T', st'⟩, hx', hp⟩ := Set.mem_iUnion₂.mp hp
    split at hp
    · rename_i hdirVP
      simp only [openingProof, liftM_pure, pure_bind, support_bind, Set.mem_iUnion,
        support_pure, Set.mem_singleton_iff] at hp
      obtain ⟨chal, _, hp⟩ := hp
      obtain ⟨hT, hst⟩ := Prod.mk.inj hp
      obtain ⟨ihst, ihreads⟩ := ih T' st' hx'
      have hcase := dir_VtoP_cases i hdirVP
      simp only [Transcript.concat] at hT
      subst hT
      subst hst
      refine ⟨?_, ?_⟩
      · -- conjunct 1: the state is updated by `receiveChallenge`
        by_cases h0 : (↑i : ℕ) = 0
        · -- round `0`: install `U`
          rw [dif_pos h0]
          have hst0 : st' = inputStU ck data decomm query 0 := by
            rw [ihst]
            simp only [stUpto, Uread, Fin.val_castSucc, h0, lt_irrefl, dif_neg,
              not_false_eq_true, Nat.zero_sub, Nat.zero_div, Nat.min_zero, foldUpto]
            rw [if_neg (by omega)]
          have hRHS : stUpto ck data decomm query i.succ (Fin.snoc T' chal) ↑i.succ
              = inputStU ck data decomm query (Uread i.succ (Fin.snoc T' chal)) := by
            simp only [stUpto]
            rw [if_neg (by simp only [Fin.val_succ]; omega),
              show min k ((↑i.succ - 1) / 2) = 0 by simp only [Fin.val_succ, h0]; omega, foldUpto]
          have hU : Uread i.succ (Fin.snoc T' chal) = cast (pType_zero i h0) chal := by
            simp only [Uread]
            rw [dif_pos (by simp only [Fin.val_succ]; omega)]
            congr 1
            rw [Fin.snoc]; rw [dif_neg (show ¬ (0 : ℕ) < i.val by omega)]; rfl
          rw [hRHS, hU, hst0]
          simp only [inputStU]
        by_cases h1 : (↑i : ℕ) ≤ 2 * k
        · -- even round `2t+2`: fold by `uₜ`
          have hev : (↑i : ℕ) % 2 = 0 := by
            rcases hcase with h | ⟨_, he⟩ | h <;> omega
          rw [dif_neg h0, dif_pos h1]
          have hi : 1 ≤ (↑i : ℕ) := by omega
          have hRHS : stUpto ck data decomm query i.succ (Fin.snoc T' chal) ↑i.succ
              = foldUpto (inputStU ck data decomm query (Uread i.succ (Fin.snoc T' chal)))
                  (uread i.succ (Fin.snoc T' chal)) (↑i / 2) := by
            simp only [stUpto]
            rw [if_neg (by simp only [Fin.val_succ]; omega),
              show min k ((↑i.succ - 1) / 2) = ↑i / 2 by simp only [Fin.val_succ]; omega]
          rw [hRHS, show (↑i : ℕ) / 2 = (↑i / 2 - 1) + 1 by omega, foldUpto]
          have hbase : foldUpto (inputStU ck data decomm query (Uread i.succ (Fin.snoc T' chal)))
              (uread i.succ (Fin.snoc T' chal)) (↑i / 2 - 1) = st' := by
            have hms : stUpto ck data decomm query i.succ (Fin.snoc T' chal) (↑i : ℕ) = st' := by
              rw [stUpto_snoc ck data decomm query i T' chal (↑i : ℕ) hi (le_refl _), ihst]
              congr 1
            rw [← hms]; simp only [stUpto]
            rw [if_neg (by omega), show min k (((↑i : ℕ) - 1) / 2) = ↑i / 2 - 1 by omega]
          congr 1
          · exact hbase.symm
          · simp only [uread]
            rw [dif_pos ⟨show (↑i : ℕ) / 2 - 1 < k by omega,
              show 2 * (↑i / 2 - 1) + 2 < ↑i.succ.val by simp only [Fin.val_succ]; omega⟩]
            congr 1
            rw [Fin.snoc]; rw [dif_neg (show ¬ 2 * (↑i / 2 - 1) + 2 < i.val by omega)]
            exact (cast_cast _ _ chal).symm
        · -- round `2k+3`: install the Schnorr challenge `c`
          have h3 : (↑i : ℕ) = 2 * k + 3 := by
            rcases hcase with h | ⟨hle, _⟩ | h <;> omega
          rw [dif_neg h0, dif_neg h1]
          have hi : 1 ≤ i.val := by omega
          have hS : stUpto ck data decomm query i.succ (Fin.snoc T' chal) (2 * k + 3) = st' := by
            rw [stUpto_snoc ck data decomm query i T' chal (2 * k + 3) hi (by omega), ihst]
            congr 1
            simp only [Fin.val_castSucc]; omega
          have hfold : foldUpto (inputStU ck data decomm query (Uread i.succ (Fin.snoc T' chal)))
              (uread i.succ (Fin.snoc T' chal)) k = st' := by
            rw [← hS]; simp only [stUpto]
            rw [if_neg (by omega), show min k ((2 * k + 3 - 1) / 2) = k by omega]
          have e1 : stUpto ck data decomm query i.succ (Fin.snoc T' chal) ↑i.succ
              = { foldUpto (inputStU ck data decomm query (Uread i.succ (Fin.snoc T' chal)))
                    (uread i.succ (Fin.snoc T' chal)) k with
                    c := cread i.succ (Fin.snoc T' chal) } := by
            simp only [stUpto]
            rw [if_pos (by simp only [Fin.val_succ]; omega),
              show min k ((↑i.succ - 1) / 2) = k by simp only [Fin.val_succ, h3]; omega]
          rw [e1, hfold]
          congr 1
          simp only [cread]
          rw [dif_pos (by simp only [Fin.val_succ]; omega)]
          rw [Fin.snoc]; rw [dif_neg (show ¬ 2 * k + 3 < i.val by omega)]
          exact (cast_cast _ _ chal).symm
      · -- conjunct 2: the recorded messages (the new round is `V_to_P`, hence vacuous)
        intro j
        induction j using Fin.lastCases with
        | last =>
          intro hj
          exfalso
          rw [show (Fin.castLE i.succ.is_le (Fin.last ↑i)) = i from by ext; simp, hdirVP] at hj
          exact absurd hj (by decide)
        | cast j0 =>
          intro hj
          rw [Fin.snoc_castSucc]
          simp only [Fin.val_castSucc]
          have hi : 1 ≤ i.val := by have := j0.isLt; omega
          rw [stUpto_snoc ck data decomm query i T' chal j0.val hi (le_of_lt j0.isLt)]
          exact ihreads j0 hj
    · rename_i hdirPV
      simp only [openingProof, liftM_pure, pure_bind, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hp
      obtain ⟨hT, hst⟩ := hp
      obtain ⟨ihst, ihreads⟩ := ih T' st' hx'
      have hcase := dir_PtoV_cases i hdirPV
      have hi : 1 ≤ i.val := by omega
      subst st
      simp only [Transcript.concat] at hT
      subst hT
      refine ⟨?_, ?_⟩
      · -- conjunct 1: the state is unchanged on a `P_to_V` round
        rw [stUpto_m_congr ck data decomm query i.succ (Fin.snoc T' (msgVal st' i))
              (↑i.succ) i.val (by simp only [Fin.val_succ]; omega)
              (by simp only [Fin.val_succ]; omega),
            stUpto_snoc ck data decomm query i T' (msgVal st' i) i.val hi (le_refl _)]
        exact ihst
      · -- conjunct 2: the recorded messages
        intro j
        induction j using Fin.lastCases with
        | last =>
          intro _
          rw [Fin.snoc_last]
          have hst_eq :
              stUpto ck data decomm query i.succ (Fin.snoc T' (msgVal st' i)) i.val = st' :=
            (stUpto_snoc ck data decomm query i T' (msgVal st' i) i.val hi
              (le_refl _)).trans ihst.symm
          rw [show (Fin.last i.val).val = i.val from rfl, hst_eq]
          congr 1
        | cast j0 =>
          intro hj
          rw [Fin.snoc_castSucc]
          simp only [Fin.val_castSucc]
          rw [stUpto_snoc ck data decomm query i T' (msgVal st' i) j0.val hi
                (le_of_lt j0.isLt)]
          exact ihreads j0 hj

/-- **Residue (B): the honest prover-run transcript passes the verifier.** Any transcript `td`
in the support of the honest prover's full `2k+5`-round run satisfies the verifier's accept
equation. The proof characterizes the support of `Prover.runToRound (Fin.last (2k+5))` over the
genuine rounds (round 0 receives `U`; the `k` interleaved send-`(Lⱼ,Rⱼ)`/receive-`uⱼ` rounds; the
tail send-`(a₀,g₀)`/send-`δ`/receive-`c`/send-`(z₁,z₂)`), showing the run never fails and produces
the honest transcript, then closes `verifyCheck = true` via `honest_eq`, `innerSum_input`
(the `P' = P + [v]U` identity), and `bPoly_eval_eq`. The `hlen : st₀.len = 2^k` side-conditions
come from `hd`; the `uⱼ ≠ 0` side-conditions from the fold challenges being units (`Fˣ`). -/
lemma runToRound_verifyCheck (ck : SRS G d) (data : Fin d → F) (decomm query : F)
    (hd : d = 2 ^ k) (td : (pSpec F G k).FullTranscript) (runSt : IPAProverState F G)
    (hrun : (td, runSt) ∈ support
        ((openingProof (F := F) (G := G) (d := d) (k := k) (ck, ck)).prover.runToRound
          (Fin.last (2 * k + 5))
          (commit ck data decomm, ⟨query, OracleInterface.answer data query⟩) (data, decomm))) :
    verifyCheck ck (commit ck data decomm, ⟨query, OracleInterface.answer data query⟩) td
      = true := by
  -- Expose the verifier's `decide`d accept equation as a group/field identity in the transcript
  -- reads.  The verifier's `P' = P + [v]U` is already the literal `commit ck data decomm +
  -- [answer]·U` here, and (by `innerSum_input`) equals the telescoping invariant of the honest
  -- input state; the per-round reads `(Lⱼ, Rⱼ)`, the residue `(a₀, g₀)`, `δ`, and the Schnorr
  -- responses `(z₁, z₂)` are the honest `Lval`/`Rval`/fold values once the support of
  -- `Prover.runToRound (Fin.last (2k+5))` is characterized; then `honest_eq` closes the equation.
  -- RESIDUE (B): the `Prover.runToRound` / `Fin.induction` honest-execution characterization
  -- (the only remaining gap; the entire algebra and the `perfectCorrectness` plumbing are proven).
  -- The honest-run support characterization: every prover message read off `td` equals `msgVal`
  -- of the replay state at that round (the round-index `Fin.last` makes `castLE` the identity).
  have hcor : ∀ (j : Fin (2 * k + 5)), (pSpec F G k).dir j = Direction.P_to_V →
      td j = msgVal (stUpto ck data decomm query (Fin.last (2 * k + 5)) td j.val) j := by
    obtain ⟨_, hreads⟩ :=
      support_runToRound ck data decomm query (Fin.last (2 * k + 5)) td runSt hrun
    intro j hj
    exact hreads (Fin.cast (by rw [Fin.val_last]) j) hj
  -- direction facts for the message rounds
  have hdirP_odd : ∀ (m : ℕ) (hm : m < 2 * k + 5), m % 2 = 1 → m ≤ 2 * k →
      (pSpec F G k).dir ⟨m, hm⟩ = Direction.P_to_V := by
    intro m hm hodd hle
    simp only [pSpec]
    rw [if_neg (by omega), if_pos hle, if_pos hodd]
  have hdirP_tail : ∀ (m : ℕ) (hm : m < 2 * k + 5), m ≠ 0 → ¬ m ≤ 2 * k → m ≠ 2 * k + 3 →
      (pSpec F G k).dir ⟨m, hm⟩ = Direction.P_to_V := by
    intro m hm h0 h1 h3
    simp only [pSpec]
    rw [if_neg h0, if_neg h1, if_neg h3]
  simp only [verifyCheck, decide_eq_true_eq]
  -- Rewrite the three tail prover messages (final `(a₀,g₀)`, blinding `δ`, Schnorr `(z₁,z₂)`).
  rw [hcor ⟨2 * k + 1, by omega⟩ (hdirP_tail _ _ (by omega) (by omega) (by omega))]
  rw [hcor ⟨2 * k + 2, by omega⟩ (hdirP_tail _ _ (by omega) (by omega) (by omega))]
  rw [hcor ⟨2 * k + 4, by omega⟩ (hdirP_tail _ _ (by omega) (by omega) (by omega))]
  -- Cancel the verifier's outer casts to the honest tail values.  The `rfl` facts feed `omega`
  -- the reduced `Fin.val` of the literal indices.
  have hv1 : (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 5)).val = 2 * k + 1 := rfl
  have hv2 : (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 5)).val = 2 * k + 2 := rfl
  have hv4 : (⟨2 * k + 4, by omega⟩ : Fin (2 * k + 5)).val = 2 * k + 4 := rfl
  rw [msgVal_final_cast (stUpto ck data decomm query (Fin.last (2 * k + 5)) td (2 * k + 1))
        ⟨2 * k + 1, by omega⟩ (by omega) (by omega) (by omega)]
  rw [msgVal_delta_cast (stUpto ck data decomm query (Fin.last (2 * k + 5)) td (2 * k + 2))
        ⟨2 * k + 2, by omega⟩ (by omega) (by omega) (by omega) (by omega)]
  rw [msgVal_z_cast (stUpto ck data decomm query (Fin.last (2 * k + 5)) td (2 * k + 4))
        ⟨2 * k + 4, by omega⟩ (by omega) (by omega) (by omega) (by omega) (by omega)]
  -- Reduce the tail replay states to their `foldUpto` form (live window collapsed to length one).
  have e1 : stUpto ck data decomm query (Fin.last (2 * k + 5)) td (2 * k + 1)
      = foldUpto (inputStU ck data decomm query (Uread (Fin.last (2 * k + 5)) td))
          (uread (Fin.last (2 * k + 5)) td) k := by
    simp only [stUpto]; rw [if_neg (by omega)]; congr 1; omega
  have e4 : stUpto ck data decomm query (Fin.last (2 * k + 5)) td (2 * k + 4)
      = { foldUpto (inputStU ck data decomm query (Uread (Fin.last (2 * k + 5)) td))
            (uread (Fin.last (2 * k + 5)) td) k with c := cread (Fin.last (2 * k + 5)) td } := by
    have hmin : min k ((2 * k + 4 - 1) / 2) = k := by omega
    simp only [stUpto]; rw [if_pos (by omega), hmin]
  rw [e1, e4]
  dsimp only
  -- Match against the packaged honest accept equation `honest_eq`, with the replay state as `st0`,
  -- the Schnorr challenge `cread` as `cc`, and the fold-challenge vector `uread` as `chals`.
  have hu : ∀ i : Fin k, uread (Fin.last (2 * k + 5)) td i.val ≠ 0 := by
    intro i
    have hi := i.isLt
    simp only [uread]
    rw [dif_pos ⟨hi, by rw [Fin.val_last]; omega⟩]
    exact Units.ne_zero _
  -- the dite-guarded fold vector built from `chals = uread` collapses back to `uread`
  have huvN : (fun i => if h : i < k then uread (Fin.last (2 * k + 5)) td ↑(⟨i, h⟩ : Fin k) else 1)
      = uread (Fin.last (2 * k + 5)) td := by
    funext i
    by_cases h : i < k
    · rw [dif_pos h]
    · rw [dif_neg h]; simp only [uread]; rw [dif_neg (fun hc => h hc.1)]
  convert honest_eq (inputStU ck data decomm query (Uread (Fin.last (2 * k + 5)) td))
      (cread (Fin.last (2 * k + 5)) td) query
      (fun t : Fin k => uread (Fin.last (2 * k + 5)) td t.val) ck.h hd hu (fun n => rfl) using 2
  · -- (1) the verifier's recombination LHS equals the telescoped `Q`-form: the `(Lⱼ,Rⱼ)` reads
    -- become the honest cross terms, and `P' = P + [v]U` is the telescope's input value.
    rw [huvN]
    have hB : innerSum (inputStU ck data decomm query (Uread (Fin.last (2 * k + 5)) td)) ck.h
        = commit ck data decomm + (∑ i, data i * query ^ (i : ℕ)) •
            Uread (Fin.last (2 * k + 5)) td :=
      innerSum_input ck data decomm query (Uread (Fin.last (2 * k + 5)) td)
    congr 1
    · -- the Schnorr challenge read `c` equals `cread`
      simp only [cread]; rw [dif_pos (by rw [Fin.val_last]; omega)]
      rfl
    · congr 1
      · congr 1
        · -- the `Lⱼ` reads are the honest `Lval (foldUptoⱼ)`
          refine Finset.sum_congr rfl fun x _ => ?_
          have hx := x.isLt
          have hvx : (⟨2 * x.val + 1, by omega⟩ : Fin (2 * k + 5)).val = 2 * x.val + 1 := rfl
          have ex : stUpto ck data decomm query (Fin.last (2 * k + 5)) td (2 * x.val + 1)
              = foldUpto (inputStU ck data decomm query (Uread (Fin.last (2 * k + 5)) td))
                  (uread (Fin.last (2 * k + 5)) td) x.val := by
            simp only [stUpto]; rw [if_neg (by omega)]; congr 1; omega
          rw [hcor ⟨2 * x.val + 1, by omega⟩ (hdirP_odd _ _ (by omega) (by omega)),
              msgVal_LR_cast (stUpto ck data decomm query (Fin.last (2 * k + 5)) td (2 * x.val + 1))
                ⟨2 * x.val + 1, by omega⟩ (by omega) (by omega) (by omega), ex]
          congr 1
          simp only [uread]; rw [dif_pos ⟨hx, by rw [Fin.val_last]; omega⟩]
          rfl
        · -- `P' = commit + [v]U = innerSum (input)`
          rw [hB]; rfl
      · -- the `Rⱼ` reads are the honest `Rval (foldUptoⱼ)`
        refine Finset.sum_congr rfl fun x _ => ?_
        have hx := x.isLt
        have hvx : (⟨2 * x.val + 1, by omega⟩ : Fin (2 * k + 5)).val = 2 * x.val + 1 := rfl
        have ex : stUpto ck data decomm query (Fin.last (2 * k + 5)) td (2 * x.val + 1)
            = foldUpto (inputStU ck data decomm query (Uread (Fin.last (2 * k + 5)) td))
                (uread (Fin.last (2 * k + 5)) td) x.val := by
          simp only [stUpto]; rw [if_neg (by omega)]; congr 1; omega
        rw [hcor ⟨2 * x.val + 1, by omega⟩ (hdirP_odd _ _ (by omega) (by omega)),
            msgVal_LR_cast (stUpto ck data decomm query (Fin.last (2 * k + 5)) td (2 * x.val + 1))
              ⟨2 * x.val + 1, by omega⟩ (by omega) (by omega) (by omega), ex]
        congr 1
        simp only [uread]; rw [dif_pos ⟨hx, by rw [Fin.val_last]; omega⟩]
        rfl
  · -- (2) the residue `[a₀c](g₀ + [b]U)` matches; the `U` read is defeq, only the
    -- verifier's `b = eval x (bPoly u)` requires the pointwise fold-vector identity.
    rw [huvN]
    congr 2
    congr 1
    refine congrArg (Polynomial.eval query) ?_
    refine congrArg bPoly ?_
    funext t
    have ht := t.isLt
    simp only [uread]
    rw [dif_pos ⟨ht, by rw [Fin.val_last]; omega⟩]
    rfl
  · -- (3) the blinder term: `rAcc` is preserved by the fold
    rw [foldUpto_rAcc]

set_option linter.unusedSimpArgs false in
/-- **Perfect completeness of IPA** (Halo, Section 3, Theorem 1). The IPA
commitment scheme `ipa` satisfies perfect correctness in the sense of ArkLib's
`Commitment.perfectCorrectness`: for every coefficient vector and evaluation
point, the honest commit-then-open experiment makes the verifier accept with
probability `1` (correctness error `εc = 0`).

The proof reduces, after unfolding the `perfectCorrectness` plumbing, to the
algebraic accept-equation identity for the honest transcript of the opening
protocol. That algebra is fully developed above and axiom-clean: `honest_accept`
(steps (ii)+(iii) — Halo eq. (2) + the Schnorr check) and `bPoly_eval_eq`
(step (i) — `b₀ = eval x (bPoly u)`). The statement now carries the hypothesis
`(hd : d = 2 ^ k)` — residue (A) (the honest prover folds `k` times regardless of `d`,
and `honest_accept` only fires once the live window is length one, i.e. `d = 2 ^ k`) is
resolved by this hypothesis. One residue remains in the body (`sorry`): **(B)** the
`2k+5`-round prover-run support characterization (`Prover.runToRound` / `Fin.induction`)
that produces the honest transcript fed to `verifyCheck`. See `task_results/` for the
precise decomposition. -/
theorem ipa_correctness [SampleableType F] [SampleableType G]
    [[(pSpec F G k).Challenge]ₒ.Inhabited] [[(pSpec F G k).Challenge]ₒ.Fintype]
    [∀ i, VCVCompatible ((pSpec F G k).Challenge i)]
    [∀ i, SampleableType ((pSpec F G k).Challenge i)] (hd : d = 2 ^ k) :
    Commitment.perfectCorrectness (init := pure ∅) (impl := randomOracle)
      (ipa (F := F) (G := G) (d := d) (k := k)) := by
  -- Plumbing reduction (mirrors `KZG.CommitmentScheme.correctness`): unfold the
  -- error-`0` correctness predicate over the honest commit/open/verify experiment.
  -- `OptionT.probEvent_eq_one_of_simulateQ_support` reduces probability-one to: every
  -- element of the experiment's support is an accepting transcript.
  intro data query
  simp only [ENNReal.coe_zero, tsub_zero]
  rw [ge_iff_le, one_le_probEvent_iff]
  refine OptionT.probEvent_eq_one_of_simulateQ_support _ _ ∅ _ ?_
  intro x hx
  -- Unwind the keygen / commit binds of the honest experiment (mirrors KZG).
  simp only [ipa] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨⟨ck, vk⟩, hkeygen, hx⟩ := hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨⟨cm, decomm⟩, hcommit, hx⟩ := hx
  -- Extract `ck = vk` (keygen returns the SRS twice) and `cm = commit ck data decomm`.
  replace hkeygen := OracleComp.mem_support_of_mem_support_liftComp _ _ hkeygen
  replace hcommit := OracleComp.mem_support_of_mem_support_liftComp _ _ hcommit
  rw [mem_support_bind_iff] at hkeygen
  obtain ⟨gg, _hgg, hkeygen⟩ := hkeygen
  rw [mem_support_bind_iff] at hkeygen
  obtain ⟨hh, _hhh, hkeygen⟩ := hkeygen
  rw [mem_support_pure_iff] at hkeygen
  simp only [Prod.mk.injEq] at hkeygen
  obtain ⟨rfl, rfl⟩ := hkeygen
  rw [mem_support_bind_iff] at hcommit
  obtain ⟨rr, _hrr, hcommit⟩ := hcommit
  rw [mem_support_pure_iff] at hcommit
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcommit
  set ck : SRS G d := { g := gg, h := hh } with hck
  set stmt : G × (_q : F) × F :=
    (commit ck data decomm, ⟨query, OracleInterface.answer data query⟩) with hstmt
  -- The verifier verdict is the pure function `td ↦ verifyCheck ck stmt td`.
  have hf : ∀ (s : G × (_q : F) × F) (transcript : (pSpec F G k).FullTranscript),
      (openingProof (F := F) (G := G) (d := d) (k := k) (ck, ck)).verifier.verify s transcript
        = (pure (verifyCheck ck s transcript) : OptionT (OracleComp unifSpec) Bool) := by
    intro s transcript; rfl
  -- Unfold `Reduction.run` to expose the prover transcript and the pure-verifier verdict.
  unfold Reduction.run at hx
  simp only [OptionT.run_bind, Option.elimM] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨proverResultOpt, hprover, hx⟩ := hx
  -- The prover run is a lifted plain `OracleComp`, so its option is always `some` of a run result;
  -- and the run output statement/witness is `(true, ())`, while the transcript is honest.
  simp only [OptionT.run_monadLift, support_map, Set.mem_image] at hprover
  obtain ⟨pr, hpr, hpreq⟩ := hprover
  unfold Prover.run at hpr
  rw [OracleComp.monadLift_eq_self, mem_support_bind_iff] at hpr
  obtain ⟨⟨td, runSt⟩, hrun, hpr⟩ := hpr
  -- the prover output statement/witness is the constant `(true, ())`
  simp only [liftM_pure, pure_bind, mem_support_pure_iff] at hpr
  -- `pr = (td, (true, ()))`, hence `proverResultOpt = some (td, (true, ()))`
  subst hpr
  subst hpreq
  simp only [Option.elim_some] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨stmtOutOpt, hstmtOutOpt, hx⟩ := hx
  simp only [Verifier.run, hf, OptionT.run_pure] at hstmtOutOpt
  subst stmtOutOpt
  simp only [Option.elim_some, Option.getM_some, OptionT.run_pure] at hx
  -- `verifyCheck ck stmt td = true` by the honest-transcript characterization.
  have hverify : verifyCheck ck stmt td = true :=
    runToRound_verifyCheck ck data decomm query hd td runSt hrun
  subst hx
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [acceptRejectRel, Set.mem_singleton_iff, Prod.mk.injEq, and_true]
    exact hverify
  · exact hverify.symm

end Correctness

end Kimchi.Commitment.IPA.Correctness
