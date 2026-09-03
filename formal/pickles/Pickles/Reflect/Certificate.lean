import Pickles.Linearization.Spec
import Pickles.Linearization.Map
import Pickles.Linearization.Fp
import Pickles.Linearization.Fq
import Pickles.Reflect.Poly
import Kimchi.Verifier.Kimchi
import Bulletproof.Wire
import Pasta.Endo

/-!
# The reflection certificate

The deployed token stream and the closed-form gate linearization are THE SAME POLYNOMIAL.

Both sides are run at `CMvPolynomial 56 Fp`, one distinct formal variable per input the
interpreter's environment reads, and the resulting polynomials are compared. This is not
agreement at production challenges — `pickles/scripts/check_polish.lean` already checks
that — but symbolic equality, from which the identity at every evaluation follows by
`Pickles.Linearization.evaluate_map` and
`Kimchi.Protocol.Linearization.gateLinearization_map`.

## Why this is cheap

The whole 4220-token program collapses to 486 monomials. The linearization is a SUM of
small per-gate constraints rather than a nested product, so normalising it does not blow
up — Poseidon's degree-7 S-boxes included. The proof therefore costs one compiled
polynomial comparison, and the two transport lemmas above are generic and cost nothing per
token.

## The trust surface

This module is the ONLY place in the tree that uses `native_decide` outside the upstream
CompElliptic certificates and pasta's two declared GLV anchors, and it is named in each
package's axiom gate for exactly that reason. Besides the two certificates it decides one
more fact about the closed streams — how far they read the α-table, at the end of the
module — which is bookkeeping of the same kind and lives here so the gate has one module
to trust. It trusts the compiler through
`Lean.trustCompiler`. The alternative, kernel `decide`, is not viable on a 486-monomial
comparison over a 255-bit field.

## From the certificate to the general statement

The certificate is an equality of POLYNOMIALS. `evaluate_fpTokens`, at the end of this
module, is what one actually wants: at every evaluation record and every choice of
challenges, the deployed stream agrees with the closed form. The transport is
`toEnv_compatible` (the environment is natural), then `evaluate_map` (a machine run crosses
the evaluation homomorphism) and `gateLinearization_map` (so does the closed form, resting
on each gate's `constraints_map`). Nothing in it inspects the token array, so its cost is
independent of the stream's length.

Everything between the certificate and that theorem is `private`: the symbolic apparatus
exists only to state and discharge the certificate, and nothing outside should depend on
the variable numbering.

## Scope

`endo` and `mds` are the DEPLOYED constants, not variables: they parameterise the gates'
`Argument`s, which are defined over the field, so they cannot be formal. The certificate is
therefore per-curve, and both sides of the cycle are certified here: `fp_reflects` over
`Fp`, Vesta's scalar field, where a Pallas proof is verified; and `fq_reflects` over `Fq`,
Pallas's scalar field, where a Vesta proof is verified. Each reads its own dump —
`fpTokens` and `fqTokens` — and its own endomorphism constant, `Pasta.pallasEndo` matching
the `endo` recorded in `kimchi/fixtures/linearization_vesta.json`.
-/

namespace Pickles.Reflect

open CPoly Bulletproof Kimchi.Protocol.Linearization Pickles.Linearization

variable {K : Type} [Field K] [BEq K] [LawfulBEq K]

/-- One formal variable per environment input: 15 witness cells at `ζ`, 15 at `ζω`, 15
coefficients, the six modelled gates' selectors, then `α`, `β`, `γ`, the joint combiner, the
zero-knowledge vanishing evaluation, and finally the permutation columns `z`, `z(ζω)` and
the six σ evaluations.

The permutation columns are given variables even though neither side reads them. They cost
nothing — an unread variable simply does not occur in either polynomial — and they let the
transported evaluations be literally `e` rather than `e` with those fields zeroed, which
is what spares the bridge a congruence lemma for each of `toEnv` and `gateLinearization`. -/
private abbrev NV : ℕ := 64

/-- The polynomial algebra the identity is decided in. -/
private abbrev MPoly (K : Type) [Field K] [BEq K] [LawfulBEq K] := CMvPolynomial NV K

/-- Variable `i`, or zero past the end. -/
private def xv (i : ℕ) : MPoly K := if h : i < NV then CMvPolynomial.X ⟨i, h⟩ else 0

/-- The evaluations, wholly formal. -/
private def symEvals : Evals (MPoly K) where
  w i := xv i
  wOmega i := xv (15 + i)
  z := xv 56
  zOmega := xv 57
  s i := xv (58 + i)
  coeffs i := xv (30 + i)
  genericSelector := xv 45
  poseidonSelector := xv 46
  completeAddSelector := xv 47
  mulSelector := xv 48
  emulSelector := xv 49
  endoScalarSelector := xv 50

/-- The interpreter environment at the formal evaluations. `β`, `γ`, the joint combiner and
the vanishing evaluation get their own variables even though the constant term reads none
of them: that way the identity holds for every value of each, rather than for one choice.
The Lagrange basis cannot be given a variable — it is a function — and the live stream
reaches it zero times, both occurrences lying inside disabled branches. -/
private abbrev symEnv (endo : K) (mds : Kimchi.Gate.Poseidon.Mds K) : Env Id (MPoly K) :=
  symEvals.toEnv endo mds (xv 51) (xv 52) (xv 53) (xv 54) (xv 55) (fun _ _ => 0)
    LookupEvals.zero (fun _ => false)

/-! ## The assignment, generically -/

/-- The six modelled gates' selectors, indexed. -/
private def selOf (e : Evals K) : Fin 6 → K
  | 0 => e.genericSelector | 1 => e.poseidonSelector | 2 => e.completeAddSelector
  | 3 => e.mulSelector     | 4 => e.emulSelector     | 5 => e.endoScalarSelector

/-- The five scalar inputs, indexed. -/
private def chalOf (α β γ jc van : K) : Fin 5 → K
  | 0 => α | 1 => β | 2 => γ | 3 => jc | 4 => van

/-- The permutation accumulator at both points, indexed. -/
private def accOf (e : Evals K) : Fin 2 → K
  | 0 => e.z | 1 => e.zOmega

/-- The assignment sending each formal variable to its intended value. Every branch is a
RANGE test, so each condition is one `omega` away — an `if k = 45 then …` chain would put
thirteen equality side conditions in front of the later blocks. -/
private def valsOf (α β γ jc van : K) (e : Evals K) (i : Fin NV) : K :=
  let k : ℕ := i
  if h : k < 15 then e.w ⟨k, h⟩
  else if h : k < 30 then e.wOmega ⟨k - 15, by omega⟩
  else if h : k < 45 then e.coeffs ⟨k - 30, by omega⟩
  else if h : k < 51 then selOf e ⟨k - 45, by omega⟩
  else if h : k < 56 then chalOf α β γ jc van ⟨k - 51, by omega⟩
  else if h : k < 58 then accOf e ⟨k - 56, by omega⟩
  else if h : k < 64 then e.s ⟨k - 58, by omega⟩
  else 0

/-- Evaluation at that assignment, as a `K`-algebra homomorphism. -/
private noncomputable def evalAt (α β γ jc van : K) (e : Evals K) : MPoly K →ₐ[K] K :=
  aevalAlgHom (valsOf α β γ jc van e)

@[simp] private theorem evalAt_xv (α β γ jc van : K) (e : Evals K) {i : ℕ} (h : i < NV) :
    evalAt α β γ jc van e (xv i) = valsOf α β γ jc van e ⟨i, h⟩ := by
  simp [evalAt, xv, h]

/-- The formal evaluations, transported along the assignment, are the intended ones. -/
private theorem symEvals_map (α β γ jc van : K) (e : Evals K) :
    symEvals.map (evalAt α β γ jc van e) = e := by
  have key : ∀ (k : ℕ) (h : k < NV),
      evalAt α β γ jc van e (xv k) = valsOf α β γ jc van e ⟨k, h⟩ :=
    fun k h => evalAt_xv α β γ jc van e h
  refine Evals.ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · funext i; obtain ⟨i, hi⟩ := i
    rw [show (Evals.map _ symEvals).w ⟨i, hi⟩ = evalAt α β γ jc van e (xv i) from rfl,
      key i (by simp only [NV]; omega)]
    simp [valsOf, hi]
  · funext i; obtain ⟨i, hi⟩ := i
    rw [show (Evals.map _ symEvals).wOmega ⟨i, hi⟩
      = evalAt α β γ jc van e (xv (15 + i)) from rfl, key _ (by simp only [NV]; omega)]
    simp [valsOf, Nat.add_sub_cancel_left, show ¬(15 + i < 15) from by omega,
      show 15 + i < 30 from by omega]
  · rw [show (Evals.map _ symEvals).z = evalAt α β γ jc van e (xv 56) from rfl,
      key 56 (by simp only [NV]; omega)]
    simp [valsOf, accOf]
  · rw [show (Evals.map _ symEvals).zOmega = evalAt α β γ jc van e (xv 57) from rfl,
      key 57 (by simp only [NV]; omega)]
    simp [valsOf, accOf]
  · funext i; obtain ⟨i, hi⟩ := i
    rw [show (Evals.map _ symEvals).s ⟨i, hi⟩
      = evalAt α β γ jc van e (xv (58 + i)) from rfl, key _ (by simp only [NV]; omega)]
    simp [valsOf, Nat.add_sub_cancel_left, show ¬(58 + i < 15) from by omega,
      show ¬(58 + i < 30) from by omega, show ¬(58 + i < 45) from by omega,
      show ¬(58 + i < 51) from by omega, show ¬(58 + i < 56) from by omega,
      show ¬(58 + i < 58) from by omega, show 58 + i < 64 from by omega]
  · funext i; obtain ⟨i, hi⟩ := i
    rw [show (Evals.map _ symEvals).coeffs ⟨i, hi⟩
      = evalAt α β γ jc van e (xv (30 + i)) from rfl, key _ (by simp only [NV]; omega)]
    simp [valsOf, Nat.add_sub_cancel_left, show ¬(30 + i < 15) from by omega,
      show ¬(30 + i < 30) from by omega, show 30 + i < 45 from by omega]
  all_goals
    first
      | (rw [show (Evals.map _ symEvals).genericSelector
              = evalAt α β γ jc van e (xv 45) from rfl, key 45 (by simp only [NV]; omega)]
         simp [valsOf, selOf])
      | (rw [show (Evals.map _ symEvals).poseidonSelector
              = evalAt α β γ jc van e (xv 46) from rfl, key 46 (by simp only [NV]; omega)]
         simp [valsOf, selOf])
      | (rw [show (Evals.map _ symEvals).completeAddSelector
              = evalAt α β γ jc van e (xv 47) from rfl, key 47 (by simp only [NV]; omega)]
         simp [valsOf, selOf])
      | (rw [show (Evals.map _ symEvals).mulSelector
              = evalAt α β γ jc van e (xv 48) from rfl, key 48 (by simp only [NV]; omega)]
         simp [valsOf, selOf])
      | (rw [show (Evals.map _ symEvals).emulSelector
              = evalAt α β γ jc van e (xv 49) from rfl, key 49 (by simp only [NV]; omega)]
         simp [valsOf, selOf])
      | (rw [show (Evals.map _ symEvals).endoScalarSelector
              = evalAt α β γ jc van e (xv 50) from rfl, key 50 (by simp only [NV]; omega)]
         simp [valsOf, selOf])

/-- The scalar inputs are transported to themselves. -/
private theorem evalAt_chal (α β γ jc van : K) (e : Evals K) :
    evalAt α β γ jc van e (xv 51) = α ∧ evalAt α β γ jc van e (xv 52) = β ∧
      evalAt α β γ jc van e (xv 53) = γ ∧ evalAt α β γ jc van e (xv 54) = jc ∧
      evalAt α β γ jc van e (xv 55) = van := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [evalAt_xv (h := by simp only [NV]; omega)]
      simp [valsOf, chalOf]

/-- **The bridge.** A certificate over the polynomial algebra yields the identity at every
evaluation record and every choice of challenges. Field-generic and token-generic: the two
deployed streams differ only in which certificate is supplied. -/
private theorem of_certificate (endo : K) (mds : Kimchi.Gate.Poseidon.Mds K)
    (toks : Array PolishToken)
    (hcert : (evaluate (symEnv endo mds) toks : MPoly K)
      = gateLinearization endo mds (xv 51) symEvals)
    (α β γ jc van : K) (e : Evals K) :
    (evaluate (e.toEnv endo mds α β γ jc van (fun _ _ => 0) LookupEvals.zero
      (fun _ => false)) toks : K)
      = gateLinearization endo mds α e := by
  obtain ⟨hα, hβ, hγ, hjc, hvan⟩ := evalAt_chal α β γ jc van e
  have hE := symEvals_map α β γ jc van e
  have hm := evaluate_map (evalAt α β γ jc van e) endo mds
    (xv 51) (xv 52) (xv 53) (xv 54) (xv 55) (fun _ _ => 0) LookupEvals.zero
    (fun _ => false) symEvals toks
  rw [hE, hα, hβ, hγ, hjc, hvan] at hm
  simp only [_root_.map_zero, LookupEvals.map_zero (_root_.map_zero _)] at hm
  rw [hm, hcert, gateLinearization_map, hα, hE]

/-! ## The two deployed streams -/

/-- Vesta's scalar field, where a Pallas proof is verified. -/
abbrev Fp := IpaVesta.curve.ScalarField

/-- The production Poseidon MDS matrix over `Fp`. -/
abbrev symMds : Kimchi.Gate.Poseidon.Mds Fp :=
  Kimchi.Verifier.mdsOfParams IpaVesta.curve.frParams

instance : DecidableEq (MPoly Fp) := CPoly.Lawful.instDecidableEq

/-- The stream's value over the polynomial algebra. Named rather than written inline:
`evaluate` lands in `Id _`, and instance search for `DecidableEq` is syntactic. -/
private def symValueP : MPoly Fp := evaluate (symEnv Pasta.pallasEndo symMds) fpTokens

/-- **The certificate, `Fp` side.** -/
private theorem fp_reflects :
    symValueP = gateLinearization Pasta.pallasEndo symMds (xv 51) symEvals := by
  native_decide

/-- **The deployed `Fp` stream computes the gate linearization.** -/
theorem evaluate_fpTokens (α β γ jc van : Fp) (e : Evals Fp) :
    (evaluate (e.toEnv Pasta.pallasEndo symMds α β γ jc van (fun _ _ => 0) LookupEvals.zero
      (fun _ => false)) fpTokens : Fp)
      = gateLinearization Pasta.pallasEndo symMds α e :=
  of_certificate _ _ _ fp_reflects α β γ jc van e

/-- Pallas's scalar field, where a Vesta proof is verified. -/
abbrev Fq := IpaPallas.curve.ScalarField

/-- The production Poseidon MDS matrix over `Fq`. -/
abbrev symMdsQ : Kimchi.Gate.Poseidon.Mds Fq :=
  Kimchi.Verifier.mdsOfParams IpaPallas.curve.frParams

instance : DecidableEq (MPoly Fq) := CPoly.Lawful.instDecidableEq

/-- The `Fq` stream's value over the polynomial algebra. -/
private def symValueQ : MPoly Fq := evaluate (symEnv Pasta.vestaEndo symMdsQ) fqTokens

/-- **The certificate, `Fq` side.** -/
private theorem fq_reflects :
    symValueQ = gateLinearization Pasta.vestaEndo symMdsQ (xv 51) symEvals := by
  native_decide

/-- **The deployed `Fq` stream computes the gate linearization.** -/
theorem evaluate_fqTokens (α β γ jc van : Fq) (e : Evals Fq) :
    (evaluate (e.toEnv Pasta.vestaEndo symMdsQ α β γ jc van (fun _ _ => 0) LookupEvals.zero
      (fun _ => false)) fqTokens : Fq)
      = gateLinearization Pasta.vestaEndo symMdsQ α e :=
  of_certificate _ _ _ fq_reflects α β γ jc van e

/-! ## How far the α-table is read

The streams read `alphaPow` only through the Alpha+Pow peephole, so the exponents reached
are `alphaExponents` of the array — a syntactic fact, decided here from the same closed
term the certificates are decided from. It is what a finite precomputed table needs: the
circuit's obligation on the table stops at this bound instead of ranging over every
natural. Both deployed streams stop at `31`; the PureScript table
(`Pickles.Linearization.Env.AlphaPowersLen`) holds `71`. -/

/-- The largest exponent at which either deployed stream reads the α-table. -/
def alphaBound : Nat := 31

/-- The `Fp` stream reads the α-table at exponents `≤ alphaBound` only. -/
theorem alphaExponents_fpTokens_le : ∀ n ∈ alphaExponents fpTokens, n ≤ alphaBound := by
  native_decide

/-- The `Fq` stream reads the α-table at exponents `≤ alphaBound` only. -/
theorem alphaExponents_fqTokens_le : ∀ n ∈ alphaExponents fqTokens, n ≤ alphaBound := by
  native_decide

end Pickles.Reflect
