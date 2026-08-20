import Schnorr.Circuit

/-!
# The circuit laws — the transcript

The transcript's law pair, in the wire's vocabulary: any satisfying valuation reads
`squeezeTranscript`'s result as `Poseidon.RandomOracle.hash` of the six absorbed
coordinates (`squeezeTranscript_spec`), and the honest prover run accepts on readable
points and reads it back (`squeezeTranscript_complete_spec`). That hash is
`transcriptHash` at the read points, definitionally, so the transcript needs no
further alignment. Both laws are the hash gadget's own (`hashVec_spec` /
`hashVec_complete_spec`) at the transcript's coordinate list — nothing here reasons
about the sponge.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta
open Std.Do

/-- The Vesta-side parameter tables have the full 55-round length — the hash laws'
size hypothesis, discharged once on the generated table. -/
private theorem fqParams_size :
    (_root_.Poseidon.fqParams).roundConstants.size = _root_.Poseidon.fullRounds := by
  show (_root_.Poseidon.FqKimchi.roundConstants.map _).size = _root_.Poseidon.fullRounds
  rw [Array.size_map]
  decide

/-- The transcript is sound: any satisfying valuation reads the squeezed variable as
the block-mode hash of the six absorbed coordinate readings — `transcriptHash` at the
point readings, definitionally. -/
theorem squeezeTranscript_spec (pk u : AffinePoint (FVar Fq))
    (Q : PostCond (FVar Fq) (.arg (BuilderState Fq) .pure)) :
    ⦃Sound (fun V (r : FVar Fq) =>
        r.val V = _root_.Poseidon.RandomOracle.hash _root_.Poseidon.fqParams
          [gen.x, gen.y, pk.x.val V, pk.y.val V, u.x.val V, u.y.val V]) Q⦄
    (squeezeTranscript (c := KimchiConstraint Fq) pk u)
    ⦃Q⦄ := by
  simp only [squeezeTranscript]
  exact RandomOracle.hashVec_spec _ fqParams_size _ Q

/-- The transcript is complete: the honest run accepts on readable point coordinates,
and the squeezed variable reads back as the block-mode hash of their values. -/
theorem squeezeTranscript_complete_spec (pk u : AffinePoint (FVar Fq))
    (Q : PostCond (FVar Fq) (.arg (ProverState Fq) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (pk.x.eval env).isOk ∧ (pk.y.eval env).isOk ∧
          (u.x.eval env).isOk ∧ (u.y.eval env).isOk)
        (fun env (r : FVar Fq) env' => ∀ px py ux uy,
          pk.x.eval env = .ok px → pk.y.eval env = .ok py →
          u.x.eval env = .ok ux → u.y.eval env = .ok uy →
          r.eval env' = .ok (_root_.Poseidon.RandomOracle.hash
            _root_.Poseidon.fqParams [gen.x, gen.y, px, py, ux, uy]))
        Q⦄
    (squeezeTranscript (c := KimchiProverC Fq) pk u)
    ⦃Q⦄ := by
  simp only [squeezeTranscript]
  have h := RandomOracle.hashVec_complete_spec (F := Fq)
    _root_.Poseidon.fqParams fqParams_size
  mvcgen [h]
  rename_i s hpre
  obtain ⟨⟨hpx, hpy, hux, huy⟩, hk⟩ := hpre
  obtain ⟨px, hpx⟩ := CVar.evalOk hpx
  obtain ⟨py, hpy⟩ := CVar.evalOk hpy
  obtain ⟨ux, hux⟩ := CVar.evalOk hux
  obtain ⟨uy, huy⟩ := CVar.evalOk huy
  refine ⟨fun x hx => ?_, fun r st' hout hle => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isOk_of_eq rfl
    · exact isOk_of_eq rfl
    · exact isOk_of_eq hpx
    · exact isOk_of_eq hpy
    · exact isOk_of_eq hux
    · exact isOk_of_eq huy
  · refine hk _ _ (fun px' py' ux' uy' hpx' hpy' hux' huy' => ?_) hle
    rw [hpx] at hpx'; rw [hpy] at hpy'; rw [hux] at hux'; rw [huy] at huy'
    injection hpx' with hpx'; injection hpy' with hpy'
    injection hux' with hux'; injection huy' with huy'
    subst hpx' hpy' hux' huy'
    exact hout _ (.cons (reads_fvar_iff.mpr rfl) (.cons (reads_fvar_iff.mpr rfl)
      (.cons (reads_fvar_iff.mpr hpx) (.cons (reads_fvar_iff.mpr hpy)
        (.cons (reads_fvar_iff.mpr hux) (.cons (reads_fvar_iff.mpr huy) .nil))))))
  intros
  exact fqParams_size

end Schnorr
