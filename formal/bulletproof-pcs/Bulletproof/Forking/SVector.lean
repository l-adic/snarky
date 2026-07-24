import Bulletproof.Forking.Convention

/-!
# The s-vector bridge: `bPolyCoefficients` is the fold

The wire verifier's two evaluation-side quantities — the `sg`-correctness check
`sg = ⟨bPolyCoefficients u, g⟩` and the Schnorr slot `b0 = combinedB u r x` — are stated over the
*flattened* s-vector, while the fork machinery (`KimchiForkValid`, ironwood's deployed layer)
folds round by round. This module proves the two views equal.

The structural fact is that `bPolyCoefficients` satisfies exactly the doubling recursion of
ironwood's `sFun` (`Deployed/Fold.lean`), in kimchi's convention — the first round challenge
scales the **high** half:

```
bPolyCoefficients u = append (bPolyCoefficients (Fin.tail u)) (u 0 • bPolyCoefficients (Fin.tail u))
```

from which one commitment step is one `foldHalves` (`commitGen_bPolyCoefficients_step`, generic
over the module so it serves generators and eval vectors alike), and the `bPoly` evaluation
identity follows by folding `evalVector`, whose fold
`foldHalves (evalVector x) c = (1 + c·x^{2^k}) • evalVector x` is precisely `bPoly`'s
recurrence. The commitment algebra is ironwood's throughout
(`commitGen_append`, `commitGen_smul_left`, `commitGen_add_gen`, `commitGen_smul_gen`).
-/

namespace Bulletproof.Forking

open Bulletproof

variable {F : Type*} [Field F]

/-! ## The doubling recursion of the s-vector -/

/-- At depth `0` the s-vector is the constant `1` (the empty product). -/
theorem bPolyCoefficients_zero (u : Fin 0 → F) : bPolyCoefficients u = fun _ => 1 := by
  funext m
  simp [bPolyCoefficients]

/-- **The s-vector doubles by the head challenge, high half scaled** — `sFun`'s recursion in
kimchi's convention. The low half drops the head factor (top bit unset); the high half's top bit
contributes `u (Fin.rev (Fin.last k)) = u 0`. -/
theorem bPolyCoefficients_succ {k : ℕ} (u : Fin (k + 1) → F) :
    bPolyCoefficients u
      = append (bPolyCoefficients (Fin.tail u)) (u 0 • bPolyCoefficients (Fin.tail u)) := by
  funext m
  by_cases h : (m : ℕ) < 2 ^ k
  · rw [show append (bPolyCoefficients (Fin.tail u)) (u 0 • bPolyCoefficients (Fin.tail u)) m
        = bPolyCoefficients (Fin.tail u) ⟨m.val, h⟩ from dif_pos h]
    rw [bPolyCoefficients, bPolyCoefficients, Fin.prod_univ_castSucc]
    rw [show (Nat.testBit m.val (Fin.last k).val) = false from
      Nat.testBit_lt_two_pow (by simpa using h), if_neg (by simp), mul_one]
    exact Finset.prod_congr rfl fun j _ => by
      rw [Fin.val_castSucc, Fin.rev_castSucc]
      rfl
  · rw [show append (bPolyCoefficients (Fin.tail u)) (u 0 • bPolyCoefficients (Fin.tail u)) m
        = u 0 * bPolyCoefficients (Fin.tail u)
            ⟨m.val - 2 ^ k, by have := m.isLt; simp [pow_succ] at this; omega⟩ from dif_neg h]
    have hm : m.val = 2 ^ k + (m.val - 2 ^ k) := by omega
    have hm' : m.val - 2 ^ k < 2 ^ k := by have := m.isLt; simp [pow_succ] at this; omega
    rw [bPolyCoefficients, bPolyCoefficients, Fin.prod_univ_castSucc]
    rw [show (Nat.testBit m.val (Fin.last k).val) = true from by
      rw [Fin.val_last, hm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm']; rfl]
    rw [if_pos rfl, Fin.rev_last, mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by
      rw [Fin.val_castSucc, show Nat.testBit m.val j.val = Nat.testBit (m.val - 2 ^ k) j.val from by
        conv_lhs => rw [hm]
        exact Nat.testBit_two_pow_add_gt j.isLt _, Fin.rev_castSucc]
      rfl

/-! ## One commitment step is one fold -/

/-- **The s-vector commitment folds by the head challenge**: over any module (generators or eval
vectors), committing the depth-`k+1` s-vector equals committing the depth-`k` s-vector against
the generators folded by `foldHalves` at the head challenge. Ironwood's commitment algebra does
all the work. -/
theorem commitGen_bPolyCoefficients_step {M : Type*} [AddCommGroup M] [Module F M] {k : ℕ}
    (u : Fin (k + 1) → F) (g : Fin (2 ^ (k + 1)) → M) :
    commitGen g (bPolyCoefficients u)
      = commitGen (foldHalves g (u 0)) (bPolyCoefficients (Fin.tail u)) := by
  rw [bPolyCoefficients_succ]
  show Zcash.Snark.commitGen g (Zcash.Snark.append (bPolyCoefficients (Fin.tail u))
        (u 0 • bPolyCoefficients (Fin.tail u)))
      = Zcash.Snark.commitGen (Zcash.Snark.loHalf g + u 0 • Zcash.Snark.hiHalf g)
        (bPolyCoefficients (Fin.tail u))
  rw [Zcash.Snark.commitGen_append, Zcash.Snark.commitGen_smul_left,
    Zcash.Snark.commitGen_add_gen, Zcash.Snark.commitGen_smul_gen]

/-- The base of the fold: the depth-`0` s-vector commitment is the single generator. -/
theorem commitGen_bPolyCoefficients_zero {M : Type*} [AddCommGroup M] [Module F M]
    (u : Fin 0 → F) (g : Fin (2 ^ 0) → M) :
    commitGen g (bPolyCoefficients u) = g 0 := by
  rw [bPolyCoefficients_zero,
    show commitGen g (fun _ => (1 : F)) = (1 : F) • g 0 from Fin.sum_univ_one _, one_smul]

/-! ## The `bPoly` evaluation identity -/

/-- `bPoly`'s recurrence: split off the head factor. -/
theorem bPoly_succ {k : ℕ} (u : Fin (k + 1) → F) (x : F) :
    bPoly u x = (1 + u 0 * x ^ 2 ^ k) * bPoly (Fin.tail u) x := by
  rw [bPoly, bPoly, Fin.prod_univ_succ]
  have htail : ∀ j : Fin k,
      (1 + u (Fin.succ j) * x ^ 2 ^ (k + 1 - 1 - (Fin.succ j).val))
        = 1 + Fin.tail u j * x ^ 2 ^ (k - 1 - j.val) := fun j => by
    have he : k + 1 - 1 - (Fin.succ j).val = k - 1 - j.val := by
      rw [Fin.val_succ]; omega
    rw [he]; rfl
  rw [Finset.prod_congr rfl fun j _ => htail j]
  norm_num

/-- Folding the evaluation vector by `c` is scaling it by `bPoly`'s head factor: componentwise,
`x^i + c·x^{2^k + i} = (1 + c·x^{2^k})·x^i`. -/
theorem foldHalves_evalVector {k : ℕ} (x c : F) :
    foldHalves (evalVector (2 ^ (k + 1)) x) c
      = (1 + c * x ^ 2 ^ k) • evalVector (2 ^ k) x := by
  funext i
  show x ^ (i : ℕ) + c * x ^ (2 ^ k + (i : ℕ)) = (1 + c * x ^ 2 ^ k) * x ^ (i : ℕ)
  rw [pow_add]
  ring

/-- **`bPoly` is the inner product of the s-vector with the evaluation vector** — the closed
form of the wire's `b0` slot. By induction: one `commitGen_bPolyCoefficients_step` at the
module `M := F`, then `foldHalves_evalVector` produces exactly `bPoly`'s head factor. -/
theorem bPoly_eq_innerProduct : {k : ℕ} → (u : Fin k → F) → (x : F) →
    bPoly u x = innerProduct (bPolyCoefficients u) (evalVector (2 ^ k) x)
  | 0, u, x => by
      rw [show innerProduct (bPolyCoefficients u) (evalVector (2 ^ 0) x)
          = commitGen (evalVector (2 ^ 0) x) (bPolyCoefficients u) from rfl,
        commitGen_bPolyCoefficients_zero]
      simp [bPoly, evalVector]
  | k + 1, u, x => by
      rw [show innerProduct (bPolyCoefficients u) (evalVector (2 ^ (k + 1)) x)
          = commitGen (evalVector (2 ^ (k + 1)) x) (bPolyCoefficients u) from rfl,
        commitGen_bPolyCoefficients_step, foldHalves_evalVector,
        show commitGen ((1 + u 0 * x ^ 2 ^ k) • evalVector (2 ^ k) x)
              (bPolyCoefficients (Fin.tail u))
            = (1 + u 0 * x ^ 2 ^ k) • commitGen (evalVector (2 ^ k) x)
              (bPolyCoefficients (Fin.tail u)) from
          Zcash.Snark.commitGen_smul_gen _ _ _,
        bPoly_succ, smul_eq_mul]
      congr 1
      exact bPoly_eq_innerProduct (Fin.tail u) x

/-- **The batched `b0` slot is the inner product with the combined eval vector**: `combinedB` is
`bPoly` summed with `evalscale` weights, and the inner product distributes over the combination
(`innerProduct_combinedEvalVector`). This is the identity that carries the wire's Schnorr
equation onto the abstract capstone's `b`. -/
theorem combinedB_eq_innerProduct {k : ℕ} (u : Fin k → F) (r : F) {m : ℕ} (x : Fin m → F) :
    combinedB u r x
      = innerProduct (bPolyCoefficients u) (combinedEvalVector (2 ^ k) r x) := by
  rw [innerProduct_combinedEvalVector, combinedB]
  exact Finset.sum_congr rfl fun j _ => by rw [bPoly_eq_innerProduct]

end Bulletproof.Forking
