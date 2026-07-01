import ArkLib.OracleReduction.Execution

/-!
# Vendored ArkLib lemma (upstream `sorry` shim)

`ArkLib.OracleReduction.Execution.Reduction.runWithLog_discard_logs_eq_run` is currently a `sorry`
upstream (ArkLib `Execution.lean:415`) and is marked `@[simp]`, so citing it would leak `sorryAx`
into the IPA binding development's axiom closure. This file vendors a sorry-free copy under a local
name, proved by the argument from ArkLib PR #491 (Verified-zkEVM/ArkLib#491, "feat(OracleReduction):
prove identity verifier soundness and knowledge soundness"). When #491 merges upstream this file is
deleted and consumers cite the ArkLib theorem directly.

The proof is transcribed verbatim from PR #491; only the declaration name is local.
-/

namespace Kimchi.Commitment.IPA.ArkLibShim

open OracleComp OracleSpec SubSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {WitIn : Type} {StmtOut : Type} {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- In `OptionT`, lifting a pair-valued computation and projecting the first component in the
continuation equals lifting the map and binding directly. (ArkLib PR #491 private helper.) -/
private lemma OptionT_liftM_bind_fst {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β γ : Type} (x : m (α × β)) (f : α → OptionT m γ) :
    ((liftM x : OptionT m _) >>= fun p => f p.1) =
    (liftM (Prod.fst <$> x) : OptionT m _) >>= f := by
  rw [← bind_map_left]
  show (Prod.fst <$> monadLift x) >>= f = monadLift (Prod.fst <$> x) >>= f
  congr 1

/-- **Vendored (ArkLib PR #491).** Logging the queries made by both parties does not change the
output of the reduction: running with logging and discarding the logs equals running without.
Local sorry-free copy of `ArkLib.…Reduction.runWithLog_discard_logs_eq_run`. -/
theorem runWithLog_discard_logs_eq_run
    {stmt : StmtIn} {wit : WitIn}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} :
      Prod.fst <$>
        reduction.runWithLog stmt wit = reduction.run stmt wit := by
  simp only [Reduction.runWithLog, Reduction.run, map_bind, map_pure, Functor.map_map,
    Function.comp]
  have h1 := OptionT_liftM_bind_fst (m := OracleComp (oSpec + [pSpec.Challenge]ₒ))
    (Prover.runWithLog stmt wit reduction.prover)
    (fun proverResult =>
      liftM (simulateQ loggingOracle (Verifier.run stmt proverResult.1 reduction.verifier)).run
        >>= fun a_1 => (fun a_2 => (proverResult, a_2)) <$> a_1.1.getM)
  exact h1 ▸ by
    rw [Prover.runWithLog_discard_log_eq_run]
    congr 1; ext proverResult
    generalize Verifier.run stmt proverResult.1 reduction.verifier = vc
    induction vc using OracleComp.induction with
    | pure a => simp [simulateQ_pure, WriterT.run_pure]; rfl
    | query_bind t oa ih =>
      simp only [run_simulateQ_loggingOracle_query_bind]
      simp [bind_map_left, ih, OptionT.run_bind, Option.elimM, bind_assoc, OptionT.run_map]
      rfl

end Kimchi.Commitment.IPA.ArkLibShim
