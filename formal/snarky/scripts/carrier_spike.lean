import Snarky.Circuit.DSL.Field

/-! # SPIKE: making the prover reading's `mvcgen` work

A working demonstration, deliberately parked outside the `Snarky` lib (no CI gate
builds it; run with `lake env lean scripts/carrier_spike.lean` from `formal/snarky`).

Two defects keep `mvcgen` from walking a prover-side `do`-block, and this file fixes
both, at a cost the walk doc records:

1. **The bind carries the wrong instance.** A gadget's body elaborates at `CircuitM`
   (its definition site), so its binds hold `CircuitM.instMonad`; the prover reading's
   `wp_bind` matches `instMonadProverM`. `mvcgen` resolves `WPMonad` from the bind's
   instance, finds the SOUNDNESS interpretation, and abandons the goal. `retag` below
   is the repair: `rfl`, since the instances differ only by name, and a `simp` lemma
   that rewrites a program into the carrier's binds.
2. **Value-parameterized specs are unusable.** A completeness spec whose value
   arguments (`xv`, `yv`) appear only in its precondition cannot be instantiated by
   unification at a call site: `mvcgen` matches it and leaves bare `⊢ F` metavariable
   goals. The repair is to state completeness specs the way the soundness ones are
   already stated — no value parameters, the result characterized CONDITIONALLY on the
   operand readings (`PComputes` below).

With both in place the prover side behaves exactly like the soundness side: `mvcgen`
walks the binds, applies leaf specs from the registry, and leaves one entailment VC
per composition (it does not descend under a schematic spec's result binder, the same
limitation both readings share). The `myInv`/`myMul`/`myDiv` wrappers exist because
`[spec]` cannot be erased, so the repo's current value-parameterized specs would keep
matching: fresh head symbols simulate a clean registry. -/

open Std.Do

set_option mvcgen.warning false

namespace Snarky

-- `[spec]` cannot be erased, so the repo's value-parameterized specs keep matching.
-- Test on fresh head symbols: a faithful simulation of a clean registry.

variable {F : Type} [Field F] [DecidableEq F]

/-- The retag: gadget bodies elaborate their binds at `CircuitM` (their definition
site), so the prover reading's `wp_bind` never matches. `rfl` — the instances differ
only by name. -/
@[simp] theorem retag {α β : Type} (x : CircuitM F (Basic F) α)
    (f : α → CircuitM F (Basic F) β) :
    (x >>= f : CircuitM F (Basic F) β) = ((x : ProverM F α) >>= f : ProverM F β) := rfl

/-- Candidate replacement shape: no value parameters. `facts` are what the run needs;
`post` characterizes the result CONDITIONALLY on the operand readings, exactly as the
soundness shapes do — so every parameter is determined by unification at a call site. -/
abbrev PComputes (facts : Assignments F → Prop)
    (post : Assignments F → FVar F → Assignments F → Prop)
    (Q : PostCond (FVar F) (.arg Nat (.arg (Assignments F) (.except EvalError .pure)))) :
    Assertion (.arg Nat (.arg (Assignments F) (.except EvalError .pure))) :=
  fun nv env => ⌜env.FreshFrom nv ∧ facts env ∧
    ∀ (r : FVar F) (nv' : Nat) (env' : Assignments F),
      post env r env' → env'.FreshFrom nv' → env.Le env' → (Q.1 r nv' env').down⌝

/-- Fresh head symbols (clean-registry simulation). -/
def myInv {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (x : FVar F) :
    CircuitM F c (FVar F) := inv x

/-- Fresh head symbol for multiplication. -/
def myMul {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c (FVar F) := mul x y

/-- The composed gadget under test. -/
def myDiv {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c (FVar F) := do
  let yInv ← myInv y
  myMul x yInv

/-- `inv`, restated in the candidate shape. -/
@[spec] theorem inv_spec' (x : FVar F) (Q) :
    Triple (m := ProverM F) (myInv (c := Basic F) x)
      (PComputes (fun env => (x.eval env).isOk ∧
          ∀ xv, x.eval env = .ok xv → xv ≠ 0)
        (fun env r env' => ∀ xv, x.eval env = .ok xv → r.eval env' = .ok xv⁻¹) Q) Q := by
  intro nv env hpre
  obtain ⟨hfresh, ⟨hok, hne⟩, hk⟩ := hpre
  obtain ⟨xv, hx⟩ : ∃ xv, x.eval env = .ok xv := by
    cases h : x.eval env with
    | error e => rw [h] at hok; cases hok
    | ok v => exact ⟨v, rfl⟩
  have hxv := hne xv hx
  obtain ⟨⟨r, nv', env'⟩, hrun, heval, hfresh'⟩ := inv_complete hfresh hx hxv
  simp only [myInv, wp, PredTrans.apply, hrun]
  refine hk r nv' env' (fun xv' hx' => ?_) hfresh' (prove_assignments_le hrun)
  rw [hx] at hx'
  injection hx' with hx'
  exact hx' ▸ heval

/-- `mul`, restated in the candidate shape. -/
@[spec] theorem mul_spec' (x y : FVar F) (Q) :
    Triple (m := ProverM F) (myMul (c := Basic F) x y)
      (PComputes (fun env => (x.eval env).isOk ∧ (y.eval env).isOk)
        (fun env r env' => ∀ xv yv, x.eval env = .ok xv → y.eval env = .ok yv →
          r.eval env' = .ok (xv * yv)) Q) Q := by
  intro nv env hpre
  obtain ⟨hfresh, ⟨hokx, hoky⟩, hk⟩ := hpre
  obtain ⟨xv, hx⟩ : ∃ xv, x.eval env = .ok xv := by
    cases h : x.eval env with
    | error e => rw [h] at hokx; cases hokx
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨yv, hy⟩ : ∃ yv, y.eval env = .ok yv := by
    cases h : y.eval env with
    | error e => rw [h] at hoky; cases hoky
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨⟨r, nv', env'⟩, hrun, heval, hfresh'⟩ := mul_complete hfresh hx hy
  simp only [myMul, wp, PredTrans.apply, hrun]
  refine hk r nv' env' (fun xv' yv' hx' hy' => ?_) hfresh' (prove_assignments_le hrun)
  rw [hx] at hx'; rw [hy] at hy'
  injection hx' with hx'; injection hy' with hy'
  exact hx' ▸ hy' ▸ heval

/-- THE TEST: does `div`'s completeness triple now compose by `mvcgen` alone? -/
example (x y : FVar F) (Q) :
    Triple (m := ProverM F) (myDiv (c := Basic F) x y)
      (PComputes (fun env => (x.eval env).isOk ∧ (y.eval env).isOk ∧
          ∀ yv, y.eval env = .ok yv → yv ≠ 0)
        (fun env r env' => ∀ xv yv, x.eval env = .ok xv → y.eval env = .ok yv →
          r.eval env' = .ok (xv / yv)) Q) Q := by
  simp only [myDiv, retag]
  mvcgen
  rename_i nv env hpre
  obtain ⟨hfresh, ⟨hokx, hoky, hyne⟩, hk⟩ := hpre
  refine ⟨hfresh, ⟨hoky, hyne⟩, fun r nv' env' hr hfresh' hle => ?_⟩
  obtain ⟨yv, hy⟩ : ∃ yv, y.eval env = .ok yv := by
    cases h : y.eval env with
    | error e => rw [h] at hoky; cases hoky
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨xv, hx⟩ : ∃ xv, x.eval env = .ok xv := by
    cases h : x.eval env with
    | error e => rw [h] at hokx; cases hokx
    | ok v => exact ⟨v, rfl⟩
  have hx' : x.eval env' = .ok xv := CVar.eval_le hle hx
  have hr' : r.eval env' = .ok yv⁻¹ := hr yv hy
  refine mul_spec' x r Q nv' env' ⟨hfresh', ⟨by rw [hx']; rfl, by rw [hr']; rfl⟩,
    fun res nv'' env'' hres hfresh'' hle' => ?_⟩
  refine hk res nv'' env'' (fun a b ha hb => ?_) hfresh'' (hle.trans hle')
  rw [hx] at ha; rw [hy] at hb
  injection ha with ha; injection hb with hb
  subst ha; subst hb
  rw [div_eq_mul_inv]
  exact hres xv yv⁻¹ hx' hr'

end Snarky
