import Snarky.DSL.Field
import Snarky.DSL.Boolean
import Snarky.DSL.Utils
import Kimchi.Protocol.Linearization
import Pickles.Pseudo

set_option mvcgen.warning false

/-!
# The domain scalars of `finalize_other_proof`

Port of the PureScript `Pickles.PlonkChecks.Domain`: the negative powers of the domain
generator and the permutation vanishing polynomial (OCaml `plonk_checks.ml`
`scalars_env`), the step side's known-domain selection and vanishing polynomial (OCaml
`step_verifier.ml`, `pseudo.ml`), and the wrap side's `ζ^(2^k)` by multiplication.

## Main definitions

* `omegaPowers`: `ω⁻¹`, `ω^{−(zkRows−1)}`, `ω^{−zkRows}`, generic in `zkRows`.
* `zkPolynomial`: `(ζ − ω⁻¹)(ζ − ω^{−(zkRows−1)})(ζ − ω^{−zkRows})`.
* `knownDomainWhiches`, `knownDomainVanishingPolynomial`: the selector bits from the
  runtime `domain_log2`, and `ζⁿ − 1` for the selected domain.
* `buildPow2PowsArray`, `pow2PowMul`: `ζ^(2^i)` tables by squaring and by multiplication.

## Main results

* `omegaPowers_spec`, `zkPolynomial_spec`, `zkPolynomial_eq_zkpmEval`: the powers read as
  stated, and the polynomial is `Kimchi.Protocol.Linearization.zkpmEval` once `ωⁿ = 1`.
* `knownDomainWhiches_spec`, `knownDomainVanishingPolynomial_spec`: the bits read as
  `[L = log2ᵢ]` and the polynomial as `∑ᵢ bᵢ · ζ^(2^log2ᵢ) − 1`.
* `buildPow2PowsArray_spec`, `pow2PowMul_spec`.
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

/-- The negative generator powers (plonk_checks.ml:248–264): `ω⁻¹ = 1/gen`, `ω⁻² = ω⁻¹ · ω⁻¹`
(OCaml's `square x = x * x`, an R1CS row), `zkRows − 3` further multiplications by `ω⁻¹`
reaching `ω^{−(zkRows−1)}`, and one more for `ω^{−zkRows}`. -/
def omegaPowers (generator : FVar F) (zkRows : ℕ) : CircuitM F c (OmegaPowers F) := do
  let om1 ← inv generator
  let om2 ← mul om1 om1
  let omZkP1 ← omegaLoop om1 (zkRows - 3) om2
  let omZk ← mul omZkP1 om1
  pure ⟨om1, omZkP1, omZk⟩

/-- The permutation vanishing polynomial at `ζ`,
`(ζ − ω⁻¹)(ζ − ω^{−(zkRows−1)})(ζ − ω^{−zkRows})` (plonk_checks.ml:273–279): two rows. -/
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

/-- Which known domain is the prev proof's: one `equals` of the runtime `domain_log2`
against each domain's, emitted last-to-first (OCaml's right-to-left `Vector.map`,
step_verifier.ml:880–893), the bits in domain order. -/
def knownDomainWhiches (domainLog2Var : FVar F) (log2s : List ℕ) :
    CircuitM F c (List (BoolVar F)) := do
  let rev ← whichesGo domainLog2Var log2s.reverse
  pure rev.reverse

/-- `[x, x², x⁴, …, x^(2^maxLog2)]` by `maxLog2` `square` rows (pseudo.ml:119–123). -/
def buildPow2PowsArray (x : FVar F) : ℕ → CircuitM F c (Array (FVar F))
  | 0 => pure #[x]
  | k + 1 => do
    let arr ← buildPow2PowsArray x k
    let sq ← square (arr.back?.getD x)
    pure (arr.push sq)

/-- `x^(2^n)` by `n` `mul` rows (OCaml `plonk_checks.ml` `pow2pow`, `acc * acc`). -/
def pow2PowMul (x : FVar F) : ℕ → CircuitM F c (FVar F)
  | 0 => pure x
  | k + 1 => do
    let acc ← pow2PowMul x k
    mul acc acc

/-- `ζⁿ − 1` for the selected known domain (`Pseudo.Domain.to_domain`'s
`vanishing_polynomial`, pseudo.ml:118–127): the table `ζ^(2^i)` for `i ≤ maxLog2` by
squaring, the entry at each domain's log2 selected by the which bits, minus one, sealed. -/
def knownDomainVanishingPolynomial (whiches : List (BoolVar F)) (log2s : List ℕ)
    (maxLog2 : ℕ) (zeta : FVar F) : CircuitM F c (FVar F) := do
  let pow2Pows ← buildPow2PowsArray zeta maxLog2
  let pow2AtLog2 := log2s.map fun l => pow2Pows[l]?.getD (.const 0)
  let masked ← Pseudo.mask whiches pow2AtLog2
  sealVar (CVar.sub_ masked (.const 1))

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

/-- Under any valuation the polynomial reads as `(ζ − o₁)(ζ − o₂)(ζ − o₃)` over the three
power readings. -/
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
/-- With `ω` of order dividing `n` and `zkRows ≤ n`, the polynomial of the negative powers is
`zkpmEval n zkRows ω ζ = (ζ − ω^(n−zkRows))(ζ − ω^(n−zkRows+1))(ζ − ω^(n−1))`. -/
theorem zkPolynomial_eq_zkpmEval (n zkRows : ℕ) (ω ζ : F) (hω : ω ^ n = 1)
    (hzk : zkRows ≤ n) (h1 : 1 ≤ zkRows) :
    (ζ - ω⁻¹) * (ζ - ω⁻¹ ^ (zkRows - 1)) * (ζ - ω⁻¹ ^ zkRows)
      = Kimchi.Protocol.Linearization.zkpmEval n zkRows ω ζ := by
  have key : ∀ k ≤ n, ω⁻¹ ^ k = ω ^ (n - k) := by
    intro k hk
    have : ω ^ (n - k) * ω ^ k = 1 := by rw [← pow_add, Nat.sub_add_cancel hk, hω]
    rw [inv_pow]
    exact (eq_inv_of_mul_eq_one_left this).symm
  have h1' : ω⁻¹ = ω ^ (n - 1) := by simpa using key 1 (by omega)
  unfold Kimchi.Protocol.Linearization.zkpmEval
  rw [key zkRows hzk, key (zkRows - 1) (by omega), h1',
    show n - (zkRows - 1) = n - zkRows + 1 by omega]
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

/-- Under any valuation, with the runtime `domain_log2` reading as `L`, the `i`-th bit reads
as `[L = log2ᵢ]`. -/
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

end Pickles
