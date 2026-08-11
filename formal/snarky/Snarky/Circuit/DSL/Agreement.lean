import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Bits

/-!
# The agreement corollaries

Per-gadget instances of the alignment bridge (`Snarky.post_of_prove`): an honest
prover run's result satisfies the gadget's SOUNDNESS relation, read at the completion
of the final table (`Assignments.toValuation`). Each corollary is two lines — the
bridge applied to the gadget's `Sound` triple — so a drift between a gadget's
soundness and completeness specs would make its corollary unprovable: these are the
machine check that what the constraints force and what the prover computes is the
same arithmetic, stated once per gadget instead of trusted by inspection.

The runs are at the reference backend (`Basic F`), where `prove` checks each
constraint as it is added; operand facts held before the run transport to the
completed valuation through `CVar.val_toValuation` and `CVar.eval_le`.
-/

namespace Snarky

variable {F : Type} [Field F] [DecidableEq F]

/-- An honest `mul` result is the product, at the completed table. -/
theorem mul_agrees {x y : FVar F} {nv nv' : Nat} {env env' : Assignments F} {r : FVar F}
    (hrun : prove Basic.holds (mul (c := Basic F) x y) nv env = .ok ⟨r, nv', env'⟩) :
    r.val env'.toValuation = x.val env'.toValuation * y.val env'.toValuation :=
  post_of_prove (fun Q => mul_spec x y Q) hrun

/-- An honest `inv` result is the inverse, at the completed table. -/
theorem inv_agrees {x : FVar F} {nv nv' : Nat} {env env' : Assignments F} {r : FVar F}
    (hrun : prove Basic.holds (inv (c := Basic F) x) nv env = .ok ⟨r, nv', env'⟩) :
    r.val env'.toValuation = (x.val env'.toValuation)⁻¹ :=
  post_of_prove (fun Q => inv_spec x Q) hrun

/-- An honest `div` result is the quotient, at the completed table. -/
theorem div_agrees {x y : FVar F} {nv nv' : Nat} {env env' : Assignments F} {r : FVar F}
    (hrun : prove Basic.holds (div (c := Basic F) x y) nv env = .ok ⟨r, nv', env'⟩) :
    r.val env'.toValuation = x.val env'.toValuation / y.val env'.toValuation :=
  post_of_prove (fun Q => div_spec x y Q) hrun

/-- An honest `square` result is the square, at the completed table. -/
theorem square_agrees {x : FVar F} {nv nv' : Nat} {env env' : Assignments F} {r : FVar F}
    (hrun : prove Basic.holds (square (c := Basic F) x) nv env = .ok ⟨r, nv', env'⟩) :
    r.val env'.toValuation = x.val env'.toValuation * x.val env'.toValuation :=
  post_of_prove (fun Q => square_spec x Q) hrun

/-- An honest `pow` result is the power, at the completed table. -/
theorem pow_agrees {x : FVar F} {n : Nat} {nv nv' : Nat} {env env' : Assignments F}
    {r : FVar F}
    (hrun : prove Basic.holds (pow (c := Basic F) x n) nv env = .ok ⟨r, nv', env'⟩) :
    r.val env'.toValuation = x.val env'.toValuation ^ n :=
  post_of_prove (fun Q => pow_spec x n Q) hrun

/-- An honest `equals` result is the answer bit, at the completed table. -/
theorem equals_agrees {a b : FVar F} {nv nv' : Nat} {env env' : Assignments F}
    {r : BoolVar F}
    (hrun : prove Basic.holds (equals (c := Basic F) a b) nv env = .ok ⟨r, nv', env'⟩) :
    (↑r : CVar F).val env'.toValuation
      = equalsPure (a.val env'.toValuation) (b.val env'.toValuation) :=
  post_of_prove (fun Q => equals_spec a b Q) hrun

/-- An honest `neq` result is the negated answer bit, at the completed table. -/
theorem neq_agrees {a b : FVar F} {nv nv' : Nat} {env env' : Assignments F}
    {r : BoolVar F}
    (hrun : prove Basic.holds (neq (c := Basic F) a b) nv env = .ok ⟨r, nv', env'⟩) :
    (↑r : CVar F).val env'.toValuation
      = neqPure (a.val env'.toValuation) (b.val env'.toValuation) :=
  post_of_prove (fun Q => neq_spec a b Q) hrun

/-- An honest `xor` result is the xor bit on bit operands, at the completed table. -/
theorem xor_agrees {a b : BoolVar F} {nv nv' : Nat} {env env' : Assignments F}
    {r : BoolVar F}
    (hrun : prove Basic.holds (Snarky.xor (c := Basic F) a b) nv env
      = .ok ⟨r, nv', env'⟩) :
    ∀ ab bb : Bool, (↑a : CVar F).val env'.toValuation = bit ab →
      (↑b : CVar F).val env'.toValuation = bit bb →
      (↑r : CVar F).val env'.toValuation = bit (ab ^^ bb) :=
  post_of_prove (fun Q => xor_spec a b Q) hrun

/-- An honest `select` result is the chosen branch on a bit selector, at the completed
table. -/
theorem select_agrees {b : BoolVar F} {t e : FVar F} {nv nv' : Nat}
    {env env' : Assignments F} {r : FVar F}
    (hrun : prove Basic.holds (select (c := Basic F) b t e) nv env
      = .ok ⟨r, nv', env'⟩) :
    ∀ bb : Bool, (↑b : CVar F).val env'.toValuation = bit bb →
      r.val env'.toValuation
        = selectPure bb (t.val env'.toValuation) (e.val env'.toValuation) :=
  post_of_prove (fun Q => select_spec b t e Q) hrun

/-- An honest `unpack` result is a bit vector summing to the operand, at the completed
table. -/
theorem unpack_agrees [ToNat F] {v : FVar F} {n : Nat} {nv nv' : Nat}
    {env env' : Assignments F} {r : Vector (BoolVar F) n}
    (hrun : prove Basic.holds (unpack (c := Basic F) v n) nv env = .ok ⟨r, nv', env'⟩) :
    ∃ bs : Vector Bool n,
      (∀ i (hi : i < n), (r[i].toCVar).val env'.toValuation = bit bs[i]) ∧
        packPure bs = v.val env'.toValuation :=
  post_of_prove (fun Q => unpack_spec v n Q) hrun

/-- An honest `assertEqual` run leaves the operands reading equal, at the completed
table. -/
theorem assertEqual_agrees {x y : FVar F} {nv nv' : Nat} {env env' : Assignments F}
    {u : PUnit.{1}}
    (hrun : prove Basic.holds (assertEqual (c := Basic F) x y) nv env
      = .ok ⟨u, nv', env'⟩) :
    x.val env'.toValuation = y.val env'.toValuation :=
  post_of_prove (fun Q => assertEqual_spec x y Q) hrun

/-- An honest `assertNonZero` run leaves the operand reading nonzero, at the completed
table. -/
theorem assertNonZero_agrees {v : FVar F} {nv nv' : Nat} {env env' : Assignments F}
    {u : PUnit.{1}}
    (hrun : prove Basic.holds (assertNonZero (c := Basic F) v) nv env
      = .ok ⟨u, nv', env'⟩) :
    v.val env'.toValuation ≠ 0 :=
  post_of_prove (fun Q => assertNonZero_spec v Q) hrun

end Snarky
