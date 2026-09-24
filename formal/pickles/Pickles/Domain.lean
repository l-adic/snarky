import Snarky.DSL.Field
import Snarky.DSL.Boolean
import Snarky.DSL.Utils
import Kimchi.Protocol.Linearization
import Pickles.Pseudo

set_option mvcgen.warning false

/-!
# Domain scalars

The domain arithmetic of `finalizeOtherProofCore` and its callers, transcribing
`plonk_checks.ml`, `step_verifier.ml`, `pseudo.ml` and `one_hot_vector.ml`: the negative powers
of the domain generator, the permutation vanishing polynomial, the step side's known-domain
selection and vanishing polynomial, the one-hot vector and the wrap side's domain selection, and
`ζ^(2^k)` by squaring and by multiplication.

## Main definitions

* `omegaPowers`: `ω⁻¹`, `ω^{−(zkRows−1)}`, `ω^{−zkRows}`, generic in `zkRows`.
* `zkPolynomial`: `(ζ − ω⁻¹)(ζ − ω^{−(zkRows−1)})(ζ − ω^{−zkRows})`.
* `knownDomainWhiches`, `knownDomainVanishingPolynomial`: the selector bits from the
  runtime domain log2, and `ζⁿ − 1` for the selected domain.
* `buildPow2PowsArray`, `pow2PowSquare`, `pow2PowMul`: `ζ^(2^i)` by squaring and by
  multiplication.
* `oneHotVector`: bit `j` is `[index = j]`, with some bit asserted set.
* `PlonkDomain`, `toDomain`: a domain selected in circuit, its generator and vanishing
  polynomial.
* `selectDomain`: the domain an index selects, through its one-hot bits.

## Main results

* `omegaPowers_spec`, `zkPolynomial_spec`, `zkPolynomial_eq_zkpmEval`: the powers read as
  stated, and the polynomial is `Kimchi.Protocol.Linearization.zkpmEval` once `ωⁿ = 1`.
* `knownDomainWhiches_spec`, `knownDomainVanishingPolynomial_spec`: the bits read as
  `[L = log2ᵢ]` and the polynomial as `∑ᵢ bᵢ · ζ^(2^log2ᵢ) − 1`.
* `buildPow2PowsArray_spec`, `pow2PowSquare_spec`, `pow2PowMul_spec`.
* `oneHotVector_spec`: the bits read as `[index = j]` and `index` names an entry.
* `toDomain_spec`: the generator reads as `∑ᵢ bᵢ · gen log2ᵢ`, the vanishing polynomial as
  `∑ᵢ bᵢ · ζ^(2^log2ᵢ) − 1`.
* `selectDomain_spec`: at an index reading as `j`, the domain is `log2s[j]`'s.
-/

namespace Pickles

open Std.Do Snarky

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- `ω⁻¹`, `ω^{−(zkRows−1)}` and `ω^{−zkRows}` for the domain generator `ω`. -/
structure OmegaPowers (F : Type) where
  /-- `ω⁻¹`. -/
  omegaToMinus1 : FVar F
  /-- `ω^{−(zkRows−1)}`. -/
  omegaToZkPlus1 : FVar F
  /-- `ω^{−zkRows}`. -/
  omegaToZk : FVar F

/-- `k` further multiplications by `ω⁻¹`. -/
private def omegaLoop (om1 : FVar F) : ℕ → FVar F → CircuitM F c (FVar F)
  | 0, term => pure term
  | k + 1, term => do
    let next ← mul term om1
    omegaLoop om1 k next

/-- The negative generator powers: `ω⁻¹` by one `inv`, `ω⁻²` by one `mul`, `zkRows − 3` further
multiplications by `ω⁻¹` reaching `ω^{−(zkRows−1)}`, and one more for `ω^{−zkRows}`. -/
def omegaPowers (generator : FVar F) (zkRows : ℕ) : CircuitM F c (OmegaPowers F) := do
  let om1 ← inv generator
  let om2 ← mul om1 om1
  let omZkP1 ← omegaLoop om1 (zkRows - 3) om2
  let omZk ← mul omZkP1 om1
  pure ⟨om1, omZkP1, omZk⟩

/-- The permutation vanishing polynomial at `ζ`,
`(ζ − ω⁻¹)(ζ − ω^{−(zkRows−1)})(ζ − ω^{−zkRows})`, in two `mul` rows. -/
def zkPolynomial (zeta : FVar F) (o : OmegaPowers F) : CircuitM F c (FVar F) := do
  let t1 ← mul (CVar.sub_ zeta o.omegaToMinus1) (CVar.sub_ zeta o.omegaToZkPlus1)
  mul t1 (CVar.sub_ zeta o.omegaToZk)

/-- One `equals` per candidate, emitted in list order. -/
private def whichesGo (domainLog2Var : FVar F) : List ℕ → CircuitM F c (List (BoolVar F))
  | [] => pure []
  | l :: rest => do
    let b ← equals (.const (l : F)) domainLog2Var
    let tail ← whichesGo domainLog2Var rest
    pure (b :: tail)

/-- Which known domain the previous proof uses: one `equals` of the runtime domain log2
against each candidate, emitted last-to-first, the bits returned in candidate order. -/
def knownDomainWhiches (domainLog2Var : FVar F) (log2s : List ℕ) :
    CircuitM F c (List (BoolVar F)) := do
  let rev ← whichesGo domainLog2Var log2s.reverse
  pure rev.reverse

/-- `[x, x², x⁴, …, x^(2^n)]` by `n` `square` rows. -/
def buildPow2PowsArray (x : FVar F) : ℕ → CircuitM F c (Array (FVar F))
  | 0 => pure #[x]
  | k + 1 => do
    let arr ← buildPow2PowsArray x k
    let sq ← square (arr.back?.getD x)
    pure (arr.push sq)

/-- `x^(2^n)` by `n` `mul` rows. -/
def pow2PowMul (x : FVar F) : ℕ → CircuitM F c (FVar F)
  | 0 => pure x
  | k + 1 => do
    let acc ← pow2PowMul x k
    mul acc acc

/-- `x^(2^n)` by `n` `square` rows. -/
def pow2PowSquare (x : FVar F) : ℕ → CircuitM F c (FVar F)
  | 0 => pure x
  | k + 1 => do
    let acc ← pow2PowSquare x k
    square acc

/-- `ζⁿ − 1` for the selected known domain: the table `ζ^(2^i)` for `i ≤ maxLog2`, the
domains' entries summed under their which bits, minus one, sealed. -/
def knownDomainVanishingPolynomial (whiches : List (BoolVar F)) (log2s : List ℕ)
    (maxLog2 : ℕ) (zeta : FVar F) : CircuitM F c (FVar F) := do
  let pow2Pows ← buildPow2PowsArray zeta maxLog2
  let pow2AtLog2 := log2s.map fun l => pow2Pows[l]?.getD (.const 0)
  let masked ← Pseudo.mask whiches pow2AtLog2
  sealVar (CVar.sub_ masked (.const 1))

/-- The one-hot vector of `index` over `n` entries: bit `j` is `[index = j]`, emitted
last-to-first, and `assertAny` over the bits, so `index` names an entry. -/
def oneHotVector (n : ℕ) (index : FVar F) : CircuitM F c (List (BoolVar F)) := do
  let bits ← knownDomainWhiches index (List.range n)
  assertAny bits
  pure bits

/-- A domain selected in circuit: its generator, and its vanishing polynomial `ζⁿ − 1` as a
gadget of `ζ`. -/
structure PlonkDomain (F c : Type) where
  /-- The selected domain's generator. -/
  generator : FVar F
  /-- `ζ ↦ ζⁿ − 1` at the selected size `n`. -/
  vanishingPolynomial : FVar F → CircuitM F c (FVar F)

/-- The domain the one-hot bits `which` select among `log2s`: the generator a mask over the
constants `gen log2ᵢ`, which emits no rows, and the vanishing polynomial
`knownDomainVanishingPolynomial` over a `ζ^(2^i)` table up to the largest `log2ᵢ`. -/
def toDomain (gen : ℕ → F) (which : List (BoolVar F)) (log2s : List ℕ) :
    CircuitM F c (PlonkDomain F c) := do
  let generator ← Pseudo.choose which log2s fun d => .const (gen d)
  pure ⟨generator, knownDomainVanishingPolynomial which log2s (log2s.foldr max 0)⟩

/-- The domain an index selects among `log2s`: its one-hot bits, then `toDomain`. -/
def selectDomain (gen : ℕ → F) (log2s : List ℕ) (index : FVar F) :
    CircuitM F c (PlonkDomain F c) := do
  let which ← oneHotVector log2s.length index
  toDomain gen which log2s

/-! ## Soundness -/

variable [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}

/-- The loop multiplies by `ω⁻¹` `k` times. -/
private theorem omegaLoop_spec (om1 : FVar F) :
    ∀ (k : ℕ) (term : FVar F),
      ⦃⌜True⌝⦄ omegaLoop (c := Builder V c) om1 k term
      ⦃⇓ r _ => ⌜r.val V = term.val V * om1.val V ^ k⌝⦄
  | 0, term => by
    simp only [omegaLoop]
    mvcgen
    simp
  | k + 1, term => by
    simp only [omegaLoop]
    have ih := fun next => omegaLoop_spec om1 k next
    mvcgen [ih]
    rename_i next _ hnext _ _
    intro h
    rw [h, hnext, pow_succ]
    ring

/-- Under any valuation satisfying the emitted constraints, with the generator reading as
`ω` and `3 ≤ zkRows`, the three outputs read as `ω⁻¹`, `(ω⁻¹)^(zkRows−1)` and
`(ω⁻¹)^zkRows`; the `inv` row forces `ω ≠ 0`. -/
theorem omegaPowers_spec (generator : FVar F) (zkRows : ℕ) (h3 : 3 ≤ zkRows) :
    ⦃⌜True⌝⦄ omegaPowers (c := Builder V c) generator zkRows
    ⦃⇓ o _ => ⌜generator.val V ≠ 0
      ∧ o.omegaToMinus1.val V = (generator.val V)⁻¹
      ∧ o.omegaToZkPlus1.val V = (generator.val V)⁻¹ ^ (zkRows - 1)
      ∧ o.omegaToZk.val V = (generator.val V)⁻¹ ^ zkRows⌝⦄ := by
  simp only [omegaPowers]
  mvcgen [omegaLoop_spec]
  rename_i om1 _ hinv om2 _ hom2 omZkP1 _ hloop omZk _ hzk
  have hne : generator.val V ≠ 0 := left_ne_zero_of_mul_eq_one hinv
  have hom1 : om1.val V = (generator.val V)⁻¹ := eq_inv_of_mul_eq_one_right hinv
  refine ⟨hne, hom1, ?_, ?_⟩
  · rw [hloop, hom2, hom1, ← pow_two, ← pow_add]
    congr 1
    omega
  · rw [hzk, hloop, hom2, hom1, ← pow_two, ← pow_add, ← pow_succ]
    congr 1
    omega

/-- Under any valuation the output reads as the product of `ζ` minus each of the three
powers. -/
theorem zkPolynomial_spec (zeta : FVar F) (o : OmegaPowers F) :
    ⦃⌜True⌝⦄ zkPolynomial (c := Builder V c) zeta o
    ⦃⇓ r _ => ⌜r.val V = (zeta.val V - o.omegaToMinus1.val V)
      * (zeta.val V - o.omegaToZkPlus1.val V) * (zeta.val V - o.omegaToZk.val V)⌝⦄ := by
  simp only [zkPolynomial]
  mvcgen
  rename_i t1 _ ht1 _ _
  intro h
  rw [h, ht1]
  simp only [CVar.val_sub_]

omit [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] in
/-- With `ω` of order dividing `n`, the negative powers are the complementary positive ones:
`(ω⁻¹)^k = ω^(n−k)` for `k ≤ n`. -/
theorem inv_pow_eq_pow_sub (n k : ℕ) (ω : F) (hω : ω ^ n = 1) (hk : k ≤ n) :
    ω⁻¹ ^ k = ω ^ (n - k) := by
  have : ω ^ (n - k) * ω ^ k = 1 := by rw [← pow_add, Nat.sub_add_cancel hk, hω]
  rw [inv_pow]
  exact (eq_inv_of_mul_eq_one_left this).symm

omit [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] in
/-- With `ω` of order dividing `n` and `zkRows ≤ n`, the polynomial of the negative powers is
`zkpmEval n zkRows ω ζ = (ζ − ω^(n−zkRows))(ζ − ω^(n−zkRows+1))(ζ − ω^(n−1))`. -/
theorem zkPolynomial_eq_zkpmEval (n zkRows : ℕ) (ω ζ : F) (hω : ω ^ n = 1)
    (hzk : zkRows ≤ n) (h1 : 1 ≤ zkRows) :
    (ζ - ω⁻¹) * (ζ - ω⁻¹ ^ (zkRows - 1)) * (ζ - ω⁻¹ ^ zkRows)
      = Kimchi.Protocol.Linearization.zkpmEval n zkRows ω ζ := by
  have h1' : ω⁻¹ = ω ^ (n - 1) := by simpa using inv_pow_eq_pow_sub n 1 ω hω (by omega)
  unfold Kimchi.Protocol.Linearization.zkpmEval
  rw [inv_pow_eq_pow_sub n zkRows ω hω hzk, inv_pow_eq_pow_sub n (zkRows - 1) ω hω (by omega),
    h1', show n - (zkRows - 1) = n - zkRows + 1 by omega]
  ring

/-- The bits read as the equalities, in order. -/
private theorem whichesGo_spec (domainLog2Var : FVar F) :
    ∀ log2s : List ℕ,
      ⦃⌜True⌝⦄ whichesGo (c := Builder V c) domainLog2Var log2s
      ⦃⇓ r _ => ⌜r.map (fun b : BoolVar F => (↑b : CVar F).val V)
        = log2s.map fun l : ℕ => if domainLog2Var.val V = (l : F) then 1 else 0⌝⦄
  | [] => by
    simp only [whichesGo]
    mvcgen
  | l :: rest => by
    simp only [whichesGo]
    have ih := whichesGo_spec domainLog2Var rest
    mvcgen [ih]
    rename_i b _ hb tail _ htail
    simp only [List.map_cons, hb, htail]
    congr 1
    have hc : (CVar.const (l : F) : CVar F).val V = (l : F) := rfl
    rw [hc]
    by_cases h : domainLog2Var.val V = (l : F)
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]

/-- Under any valuation, with the runtime domain log2 reading as `L`, the `i`-th bit reads as
`[L = log2ᵢ]`. -/
theorem knownDomainWhiches_spec (domainLog2Var : FVar F) (log2s : List ℕ) :
    ⦃⌜True⌝⦄ knownDomainWhiches (c := Builder V c) domainLog2Var log2s
    ⦃⇓ r _ => ⌜r.map (fun b : BoolVar F => (↑b : CVar F).val V)
      = log2s.map fun l : ℕ => if domainLog2Var.val V = (l : F) then 1 else 0⌝⦄ := by
  simp only [knownDomainWhiches]
  have h := whichesGo_spec (c := c) (V := V) domainLog2Var log2s.reverse
  mvcgen [h]
  rename_i rev _ hrev
  rw [List.map_reverse, hrev, ← List.map_reverse, List.reverse_reverse]

/-- Under any valuation the table has `maxLog2 + 1` entries and entry `i` reads as `x^(2^i)`. -/
theorem buildPow2PowsArray_spec (x : FVar F) :
    ∀ maxLog2 : ℕ,
      ⦃⌜True⌝⦄ buildPow2PowsArray (c := Builder V c) x maxLog2
      ⦃⇓ r _ => ⌜r.size = maxLog2 + 1
        ∧ ∀ i ≤ maxLog2, (r[i]?.getD (.const 0)).val V = x.val V ^ (2 ^ i)⌝⦄
  | 0 => by
    simp only [buildPow2PowsArray]
    mvcgen
    refine ⟨rfl, ?_⟩
    intro i hi
    interval_cases i
    simp
  | k + 1 => by
    simp only [buildPow2PowsArray]
    have ih := buildPow2PowsArray_spec x k
    mvcgen [ih]
    rename_i arr _ harr sq _ hsq
    obtain ⟨hsize, hent⟩ := harr
    have hback : arr.back?.getD x = arr[k]?.getD (.const 0) := by
      rw [Array.back?, hsize, Nat.add_sub_cancel]
      cases h : arr[k]? with
      | none => exact absurd h (by simp [hsize])
      | some v => rfl
    rw [hback, hent k le_rfl] at hsq
    refine ⟨by simp [hsize], ?_⟩
    intro i hi
    rw [Array.getElem?_push]
    split
    · rename_i hik
      rw [Option.getD_some, hsq, ← pow_add, ← two_mul, hik, hsize, pow_succ, mul_comm]
    · exact hent i (by omega)

/-- Under any valuation the output reads as `x^(2^n)`. -/
theorem pow2PowMul_spec (x : FVar F) :
    ∀ n : ℕ, ⦃⌜True⌝⦄ pow2PowMul (c := Builder V c) x n ⦃⇓ r _ => ⌜r.val V = x.val V ^ (2 ^ n)⌝⦄
  | 0 => by
    simp only [pow2PowMul]
    mvcgen
    simp
  | k + 1 => by
    simp only [pow2PowMul]
    have ih := pow2PowMul_spec x k
    mvcgen [ih]
    rename_i acc _ hacc _ _
    intro h
    rw [h, hacc, ← pow_add, ← two_mul, pow_succ, mul_comm]

/-- Under any valuation the output reads as `x^(2^n)`. -/
theorem pow2PowSquare_spec (x : FVar F) :
    ∀ n : ℕ, ⦃⌜True⌝⦄ pow2PowSquare (c := Builder V c) x n
      ⦃⇓ r _ => ⌜r.val V = x.val V ^ (2 ^ n)⌝⦄
  | 0 => by
    simp only [pow2PowSquare]
    mvcgen
    simp
  | k + 1 => by
    simp only [pow2PowSquare]
    have ih := pow2PowSquare_spec x k
    mvcgen [ih]
    rename_i acc _ hacc _ _
    intro h
    rw [h, hacc, ← pow_add, ← two_mul, pow_succ, mul_comm]

/-- Under any valuation satisfying the emitted constraints, with the `i`-th which bit reading
as `bᵢ` and every `log2ᵢ ≤ maxLog2`, the output reads as `∑ᵢ bᵢ · ζ^(2^log2ᵢ) − 1`. -/
theorem knownDomainVanishingPolynomial_spec (whiches : List (BoolVar F)) (log2s : List ℕ)
    (maxLog2 : ℕ) (zeta : FVar F) (hlog : ∀ l ∈ log2s, l ≤ maxLog2) :
    ⦃⌜True⌝⦄ knownDomainVanishingPolynomial (c := Builder V c) whiches log2s maxLog2 zeta
    ⦃⇓ r _ => ⌜r.val V = ((whiches.zip log2s).map fun e =>
        (↑e.1 : CVar F).val V * zeta.val V ^ (2 ^ e.2)).sum - 1⌝⦄ := by
  simp only [knownDomainVanishingPolynomial]
  have hp := buildPow2PowsArray_spec (c := c) (V := V) zeta maxLog2
  have hm := fun xs => Pseudo.mask_spec (c := c) (V := V) whiches xs
  mvcgen [hp, hm]
  rename_i _ pows _ hpows masked _ hmasked r _
  intro hr
  rw [hr, CVar.val_sub_, hmasked, List.zip_map_right, List.map_map]
  congr 2
  refine List.map_congr_left fun e he => ?_
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq,
    hpows.2 e.2 (hlog e.2 (List.of_mem_zip he).2)]

/-- Under any valuation satisfying the emitted constraints, bit `l` reads as `[index = l]`
for `l < n`, and `index` reads as one of `0, …, n − 1`. -/
theorem oneHotVector_spec (n : ℕ) (index : FVar F) :
    ⦃⌜True⌝⦄ oneHotVector (c := Builder V c) n index
    ⦃⇓ r _ => ⌜r.map (fun b : BoolVar F => (↑b : CVar F).val V)
        = (List.range n).map (fun l : ℕ => if index.val V = (l : F) then 1 else 0) ∧
      ∃ j < n, index.val V = (j : F)⌝⦄ := by
  simp only [oneHotVector]
  have hw := knownDomainWhiches_spec (c := c) (V := V) index (List.range n)
  mvcgen [hw, assertAny_spec]
  rename_i bits _ hbits _ _ hany
  refine ⟨hbits, ?_⟩
  have hread : ∀ b ∈ bits, ∃ l < n,
      (↑b : CVar F).val V = if index.val V = (l : F) then 1 else 0 := by
    intro b hb
    have hmem := List.mem_map_of_mem (f := fun b : BoolVar F => (↑b : CVar F).val V) hb
    rw [hbits] at hmem
    obtain ⟨l, hl, h⟩ := List.mem_map.mp hmem
    exact ⟨l, List.mem_range.mp hl, h.symm⟩
  obtain ⟨b, hb, h1⟩ := hany fun b hb => by
    obtain ⟨l, -, h⟩ := hread b hb
    rw [h]
    split <;> simp
  obtain ⟨l, hl, h⟩ := hread b hb
  rw [h1] at h
  split at h
  · exact ⟨l, hl, by assumption⟩
  · exact absurd h one_ne_zero

/-- Under any valuation satisfying the emitted constraints, the selected domain's generator
reads as `∑ᵢ bᵢ · gen log2ᵢ`, and its vanishing polynomial at any `ζ` as
`∑ᵢ bᵢ · ζ^(2^log2ᵢ) − 1`. -/
theorem toDomain_spec (gen : ℕ → F) (which : List (BoolVar F)) (log2s : List ℕ) :
    ⦃⌜True⌝⦄ toDomain (c := Builder V c) gen which log2s
    ⦃⇓ d _ => ⌜d.generator.val V
        = ((which.zip log2s).map fun e => (↑e.1 : CVar F).val V * gen e.2).sum ∧
      ∀ zeta : FVar F, ⦃⌜True⌝⦄ d.vanishingPolynomial zeta
        ⦃⇓ r _ => ⌜r.val V = ((which.zip log2s).map fun e =>
          (↑e.1 : CVar F).val V * zeta.val V ^ (2 ^ e.2)).sum - 1⌝⦄⌝⦄ := by
  simp only [toDomain]
  have h := Pseudo.choose_spec (c := c) (V := V) which log2s fun d => (.const (gen d) : FVar F)
  mvcgen [h]
  rename_i _ hgen
  exact ⟨hgen, fun zeta => knownDomainVanishingPolynomial_spec which log2s _ zeta
    fun _ hl => List.le_max_of_le' 0 hl le_rfl⟩

omit [DecidableEq F] in
/-- Weights reading as the indicator of `b` pick a list's `b`-th entry. -/
theorem sum_indicator {α : Type} (f : α → F) :
    ∀ (xs : List α) (ws : List F) (b : ℕ),
      ws = (List.range xs.length).map (fun l => if l = b then (1 : F) else 0) →
      (hb : b < xs.length) → ((ws.zip xs).map fun e => e.1 * f e.2).sum = f xs[b]
  | [], _, _, _, hb => absurd hb (Nat.not_lt_zero _)
  | x :: xs, ws, b, hws, hb => by
    rw [List.length_cons, List.range_succ_eq_map] at hws
    subst hws
    cases b with
    | zero =>
      simp only [List.map_cons, List.map_map, List.zip_cons_cons, List.sum_cons,
        List.getElem_cons_zero]
      rw [if_pos trivial, one_mul, add_eq_left]
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      obtain ⟨l, -, hl⟩ := List.mem_map.mp (List.of_mem_zip he).1
      rw [← hl]
      simp
    | succ b =>
      simp only [List.map_cons, List.map_map, List.zip_cons_cons, List.sum_cons,
        List.getElem_cons_succ]
      rw [if_neg (Nat.succ_ne_zero b).symm, zero_mul, zero_add]
      refine sum_indicator f xs _ b ?_ (by simpa using hb)
      simp [Function.comp_def]

omit [DecidableEq F] in
/-- A sum over bits zipped with values is the sum over the bits' readings zipped with them. -/
theorem sum_zip_bits {α : Type} (bits : List (BoolVar F)) (xs : List α) (g : α → F) :
    ((bits.zip xs).map fun e => (↑e.1 : CVar F).val V * g e.2).sum
      = (((bits.map fun x : BoolVar F => (↑x : CVar F).val V).zip xs).map
          fun e => e.1 * g e.2).sum := by
  rw [List.zip_map_left, List.map_map]
  rfl

/-- Under any valuation satisfying the emitted constraints, with the index reading as
`j < log2s.length` and the casts of the candidate indices distinct from `j`'s, the selected
domain's generator reads as `gen log2s[j]` and its vanishing polynomial as `ζ^(2^log2s[j]) − 1`. -/
theorem selectDomain_spec (gen : ℕ → F) (log2s : List ℕ) (index : FVar F) (j : ℕ)
    (hj : j < log2s.length) (hidx : index.val V = (j : F))
    (hinj : ∀ l < log2s.length, (j : F) = l → j = l) :
    ⦃⌜True⌝⦄ selectDomain (c := Builder V c) gen log2s index
    ⦃⇓ d _ => ⌜d.generator.val V = gen log2s[j] ∧ ∀ zeta : FVar F,
      ⦃⌜True⌝⦄ d.vanishingPolynomial zeta
      ⦃⇓ r _ => ⌜r.val V = zeta.val V ^ 2 ^ log2s[j] - 1⌝⦄⌝⦄ := by
  simp only [selectDomain]
  have hw := oneHotVector_spec (c := c) (V := V) log2s.length index
  have hd := fun which => toDomain_spec (c := c) (V := V) gen which log2s
  mvcgen [hw, hd]
  rename_i bits _ hbits d _
  intro hg hv
  have hind : bits.map (fun x : BoolVar F => (↑x : CVar F).val V)
      = (List.range log2s.length).map fun l => if l = j then (1 : F) else 0 := by
    rw [hbits.1]
    refine List.map_congr_left fun l hl => ?_
    rw [hidx]
    by_cases h : l = j
    · simp [h]
    · rw [if_neg h, if_neg fun h' => h (hinj l (List.mem_range.mp hl) h').symm]
  have hpick := fun f : ℕ → F =>
    (sum_zip_bits bits log2s f).trans (sum_indicator f log2s _ j hind hj)
  refine ⟨hg.trans (hpick gen), fun zeta => builder_spec_imp _ _ _ (hv zeta) ?_⟩
  intro r hr
  rw [hr, hpick fun l => zeta.val V ^ 2 ^ l]

/-! The gadgets are sealed after their specs: a consumer composes the specs, never the
bodies. -/
attribute [irreducible] omegaLoop omegaPowers zkPolynomial whichesGo knownDomainWhiches
  buildPow2PowsArray pow2PowMul pow2PowSquare knownDomainVanishingPolynomial
  oneHotVector toDomain

end Pickles
