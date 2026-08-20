import Schnorr.Circuit

/-!
# The circuit laws

The transcript's law pair, in the wire's vocabulary: any satisfying valuation reads
`squeezeTranscript`'s result as `Poseidon.RandomOracle.hash` of the six absorbed
coordinates (`squeezeTranscript_spec`), and the honest prover run accepts on readable
points and reads it back (`squeezeTranscript_complete_spec`). That hash is
`transcriptHash` at the read points, definitionally, so the transcript needs no
further alignment. Both laws are the hash gadget's own (`hashVec_spec` /
`hashVec_complete_spec`) at the transcript's coordinate list — nothing here reasons
about the sponge.

## The sound endpoint and its two relaxations

`verifyCircuit_spec` composes the gadget laws into the relaxed wire verifier, at the
deployed Vesta dictionaries. Both cross-field quantities are certified as
reconstruction classes, not values, because that is all the constraints pin:

- **the challenge** — the range check fixes the 128-bit split only up to the
  transcript hash's integer preimages, so `verifyRelaxed` ∃-quantifies the split.
- **the response** — the `Fq` reading pins the ladder's integer scalar `s` only mod
  `q`, and the window `(2^255, 3·2^255)` spans several multiples of `q`: the wire
  genuinely cannot distinguish `z` from `z + q` (`scaleFast1_spec`'s wrap analysis).
  The statement ∃-quantifies `s`; the group action pins `s` mod `p`, and `(s : Fp)`
  is the response the certified statement carries. The ladder's forbidden band
  (`s ∉ forbiddenValues p`) survives as a hypothesis on the action clause.

The challenge leg is one integer read in two fields: the crumbs are determined by the
no-wrap bound `4^64 = 2^128 < q` (`nReconstruct_inj`), the decomposition is the
gate's integer scalar exactly (`decomposition_eq_toIntZ`), and the wire's recoding is
the gate's (`endoExpand_eq_toField`). The `SWPoint` statement points transport to the
Mathlib group the gate laws speak through pasta's `SWPoint.equivPoint`.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta
open Std.Do

/-- The Vesta-side parameter tables have the full 55-round length — the hash laws'
size hypothesis, discharged once on the generated table. -/
private theorem fqParams_size :
    Poseidon.fqParams.roundConstants.size = Poseidon.fullRounds := by
  show (Poseidon.FqKimchi.roundConstants.map _).size = Poseidon.fullRounds
  rw [Array.size_map]
  decide

/-- The transcript is sound: any satisfying valuation reads the squeezed variable as
the block-mode hash of the six absorbed coordinate readings — `transcriptHash` at the
point readings, definitionally. -/
theorem squeezeTranscript_spec (pk u : AffinePoint (FVar Fq))
    (Q : PostCond (FVar Fq) (.arg (BuilderState Fq) .pure)) :
    ⦃Sound (fun V (r : FVar Fq) =>
        r.val V = Poseidon.RandomOracle.hash Poseidon.fqParams
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
          r.eval env' = .ok (Poseidon.RandomOracle.hash
            Poseidon.fqParams [gen.x, gen.y, px, py, ux, uy]))
        Q⦄
    (squeezeTranscript (c := KimchiProverC Fq) pk u)
    ⦃Q⦄ := by
  simp only [squeezeTranscript]
  have h := RandomOracle.hashVec_complete_spec (F := Fq)
    Poseidon.fqParams fqParams_size
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

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The sound endpoint.** Any satisfying valuation certifies `verifyRelaxed` at the
read statement: when the statement bundle reads as nonzero wire points and a response
representative, there is one integer response `s` — ladder-bounded, pinned in `Fq` to
the `Type1` decode of the `z` reading — with `verifyRelaxed ⟨pkP, uP, (s : Fp)⟩` off
the ladder's forbidden band. Both relaxations (the challenge split, the ∃-quantified
response) are stated in the module docstring; the walk composes the transcript,
`lowest128Bits'`, `endoMul`, `scaleFast1`, and `addFast` laws at the deployed Vesta
dictionaries. -/
theorem verifyCircuit_spec (stv : Statement.Raw (FVar Fq))
    (Q : PostCond PUnit (.arg (BuilderState Fq) .pure)) :
    ⦃Sound (fun V (_ : PUnit) =>
        ∀ (pkP uP : SWPoint Vesta.curve) (zv : Fq), pkP ≠ 0 → uP ≠ 0 →
          readVal (val := Statement.Raw Fq) V stv = ⟨⟨pkP.x, pkP.y⟩, ⟨uP.x, uP.y⟩, zv⟩ →
          ∃ s : ℤ, 2 ^ 255 < s ∧ s < 3 * 2 ^ 255 ∧
            (s : Fq) = Type1.fromShifted 255 ⟨zv⟩ ∧
            (s ∉ forbiddenValues PALLAS_BASE_CARD →
              verifyRelaxed ⟨pkP, uP, (s : Fp)⟩)) Q⦄
    (verifyCircuit (c := KimchiConstraint Fq) stv)
    ⦃Q⦄ := by
  simp only [verifyCircuit, lowest128Bits]
  have hsq := squeezeTranscript_spec stv.pk stv.u
  have hlow := lowest128Bits'_spec (F := Fq) (by decide) (by decide) true
    (.const Pasta.vestaEndo)
  have hendo := EndoMul.endoMul_spec (F := Fq) HasEndo.vesta 32 (by norm_num) stv.pk
  simp only [show HasEndo.vesta.endo = Pasta.vestaEndo from rfl] at hendo
  have hscale := scaleFast1_spec (F := Fq) HasCurve.vesta 255 51 (by norm_num)
    ⟨.const gen.x, .const gen.y⟩ ⟨stv.z⟩
  have hadd := AddFast.addFast_checkFinite_spec (F := Fq) Vesta.curve.toAffine
    ⟨rfl, rfl, rfl, rfl⟩ (by decide) stv.u
  mvcgen [hsq, hlow, hendo, hscale, hadd]
  rename_i st hpre
  intro squeezed _ hsqv
  mvcgen [hlow, hendo, hscale, hadd]
  intro c _ hcv
  mvcgen [hendo, hscale, hadd]
  intro cpk _ hcpk
  mvcgen [hscale, hadd]
  intro zg _ hzgv
  mvcgen [hadd]
  intro rhs _ hrhsv
  mvcgen
  intro _ _ hax
  mvcgen
  intro _ _ hay
  refine hpre ⟨⟩ _ ?_
  intro pkP uP zv hpk0 hu0 hread
  -- one reading equation decomposes into the per-cell facts
  simp only [readVal_statementRaw, Statement.Raw.mk.injEq, AffinePoint.mk.injEq]
    at hread
  obtain ⟨⟨hpkx, hpky⟩, ⟨hux, huy⟩, hzv⟩ := hread
  subst hzv
  replace hpkx := hpkx.symm
  replace hpky := hpky.symm
  replace hux := hux.symm
  replace huy := huy.symm
  -- the wire points and the generator read on-curve
  have hpkC := SWPoint.onCurve_of_ne_zero hpk0
  have huC := SWPoint.onCurve_of_ne_zero hu0
  have hpkNS : Vesta.curve.toAffine.Nonsingular (stv.pk.x.val st.V) (stv.pk.y.val st.V) := by
    rw [← hpkx, ← hpky]; exact nonsingular_toW hpkC
  have huNS : Vesta.curve.toAffine.Nonsingular (stv.u.x.val st.V) (stv.u.y.val st.V) := by
    rw [← hux, ← huy]; exact nonsingular_toW huC
  have hgenC : OnCurve Vesta.curve.A Vesta.curve.B (gen.x, gen.y) := by
    rcases gen.onCurve with h | h
    · exact h
    · exact absurd h (by decide)
  have hgenNS : Vesta.curve.toAffine.Nonsingular gen.x gen.y := nonsingular_toW hgenC
  -- destructure the gadget payloads
  simp only [CVar.val] at hzgv
  obtain ⟨hi, hsplit, ⟨nH, hnH, rfl⟩, nL, hnL, hcL⟩ := hcv
  obtain ⟨crumbs, hcrv, hclen, hcrec, hfinC, sc, A, B, hseq, hsab, hAle, hBle,
    hAval, hBval, -⟩ := hcpk hpkNS
  obtain ⟨s, hslo, hshi, hspin, hsact⟩ := hzgv hgenNS
  refine ⟨s, by simpa using hslo, by simpa using hshi, by simpa using hspin, ?_⟩
  intro hband
  -- the ladder regime at Vesta: the one-wrap band, with the band hypothesis
  have hOv : HasCurve.vesta.W.order = PALLAS_BASE_CARD := Pasta.vesta_card
  have hreg : HasCurve.vesta.LadderRegime (5 * 51) s := by
    refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;> rw [hOv]
    · decide
    · decide
    · decide
    · exact hband
  obtain ⟨hzgNS, hzact⟩ := hsact hreg
  -- u is finite: odd prime order has no 2-torsion
  have huy0 : stv.u.y.val st.V ≠ 0 :=
    Kimchi.Gate.VarBaseMul.y_ne_zero_of_odd_order Vesta.curve.toAffine
      (by rw [Pasta.vesta_card]; decide) huNS
  obtain ⟨hrhsNS, hsum⟩ := hrhsv huNS hfinC huy0
  -- the asserts glue the two computed points; the master identity at the readings
  have hglue := Kimchi.Gate.EndoMul.some_congr Vesta.curve.toAffine hzgNS hrhsNS hax hay
  have hfinC' : Vesta.curve.toAffine.Nonsingular (cpk.x.val st.V) (cpk.y.val st.V) := hfinC
  have hseq' : WeierstrassCurve.Affine.Point.some _ _ hfinC'
      = sc • WeierstrassCurve.Affine.Point.some _ _ hpkNS := hseq
  have hmaster : s • WeierstrassCurve.Affine.Point.some gen.x gen.y hgenNS
      = WeierstrassCurve.Affine.Point.some _ _ huNS
        + sc • WeierstrassCurve.Affine.Point.some _ _ hpkNS :=
    (hzact.symm.trans (hglue.trans hsum.symm)).trans
      (congrArg (WeierstrassCurve.Affine.Point.some _ _ huNS + ·) hseq')
  -- the endoMul crumbs are the canonical decomposition of the low half
  have hcrums : crumbs = Kimchi.Gate.EndoScalar.crumbsOf 64 nL := by
    refine Kimchi.Gate.EndoScalar.nReconstruct_inj (p := PALLAS_SCALAR_CARD) crumbs _
      (by decide) (by decide) hcrv (Kimchi.Gate.EndoScalar.crumbsOf_valid 64 nL) ?_ ?_ ?_
    · rw [hclen, Kimchi.Gate.EndoScalar.crumbsOf_length]
    · rw [hclen]; decide
    · rw [← hcrec, hcL, Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf]
      congr 1
      exact (Nat.mod_eq_of_lt (lt_of_lt_of_le hnL (by decide))).symm
  -- the endoMul scalar is one integer; read it in Fp as the wire challenge
  have hsInt : sc = Kimchi.Gate.EndoScalar.toIntZ (Kimchi.Gate.EndoScalar.digitsOf 64 nL)
      HasEndo.vesta.lam :=
    HasEndo.vesta.decomposition_eq_toIntZ nL hsab
      (by norm_num at hAle ⊢; exact hAle) (by norm_num at hBle ⊢; exact hBle)
      (hcrums ▸ hAval) (hcrums ▸ hBval)
  have hchal : ((sc : ℤ) : Fp)
      = Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam nL := by
    rw [hsInt, Kimchi.Gate.EndoScalar.endoExpand_eq_toField (by decide) (by decide),
      show Poseidon.FqVesta.spec.lam = ((HasEndo.vesta.lam : ℤ) : Fp) from rfl,
      Kimchi.Gate.EndoScalar.crumbsOf_eq_map,
      Kimchi.Gate.EndoScalar.toField_digits (by decide) (by decide) _
        (Kimchi.Gate.EndoScalar.digitsOf_lt 64 _) HasEndo.vesta.lam]
  -- the relaxed wire verifier's witness
  refine ⟨nL, nH, hnL, hnH, ?_, ?_⟩
  · simp only [transcriptHash]
    rw [hpkx, hpky, hux, huy, ← hsqv, hsplit, hcL]
  · show ((s : Fp)).val • gen
      = uP + (Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam nL).val • pkP
    have hsmul : ∀ a b : ℤ, ((a : ZMod PALLAS_BASE_CARD) = (b : ZMod PALLAS_BASE_CARD)) →
        ∀ P : Vesta.curve.toAffine.Point, a • P = b • P := fun a b hab P =>
      Kimchi.Gate.VarBaseMul.smul_eq_smul_of_zmod_eq _ (by
        rw [ZMod.intCast_eq_intCast_iff] at hab ⊢
        rwa [Pasta.vesta_card])
    have hz1 : ((((s : Fp)).val : ℤ) : ZMod PALLAS_BASE_CARD)
        = ((s : ℤ) : ZMod PALLAS_BASE_CARD) := by
      push_cast
      simp [ZMod.natCast_val]
    have hz2 : (((Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam nL).val : ℤ)
        : ZMod PALLAS_BASE_CARD) = ((sc : ℤ) : ZMod PALLAS_BASE_CARD) := by
      push_cast
      rw [← hchal]
      simp [ZMod.natCast_val]
    apply (SWPoint.equivPoint Vesta.curve).injective
    rw [map_add, map_nsmul, map_nsmul,
      SWPoint.equivPoint_eq_some gen hgenC,
      SWPoint.equivPoint_eq_some pkP hpkC,
      SWPoint.equivPoint_eq_some uP huC,
      Kimchi.Gate.EndoMul.some_congr _ (nonsingular_toW hpkC) hpkNS hpkx hpky,
      Kimchi.Gate.EndoMul.some_congr _ (nonsingular_toW huC) huNS hux huy,
      ← natCast_zsmul, ← natCast_zsmul, hsmul _ _ hz1, hsmul _ _ hz2]
    exact hmaster

end Schnorr
