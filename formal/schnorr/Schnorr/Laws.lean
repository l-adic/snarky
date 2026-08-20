import Schnorr.Circuit

/-!
# The circuit laws

The endpoint pair: the circuit is faithful to the wire verifier, sound and
complete. The transcript needs no laws of its own — `verifyCircuit` calls the hash
gadget directly, and `hashVec`'s laws read the squeeze as `transcriptHash` at the
read points, definitionally.

Soundness certifies both cross-field quantities as reconstruction classes — all the
constraints pin. The challenge: the range check fixes the 128-bit split only up to
the hash's integer preimages, so `verifyRelaxed` ∃-quantifies it. The response: the
`Fq` reading pins the ladder's integer scalar only mod `q` over a window spanning
several multiples of `q`; the statement ∃-quantifies it, the group action pins it
mod `p`, and the ladder's forbidden band survives as a hypothesis. The challenge leg
is one integer read in two fields (`nReconstruct_inj`, `decomposition_eq_toIntZ`,
`endoExpand_eq_toField`); statement points transport through `SWPoint.equivPoint`.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta
open Std.Do

/-- The parameter tables have the full 55-round length — the hash laws' size
hypothesis. -/
private theorem fqParams_size :
    Poseidon.fqParams.roundConstants.size = Poseidon.fullRounds := by
  show (Poseidon.FqKimchi.roundConstants.map _).size = Poseidon.fullRounds
  rw [Array.size_map]
  decide

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The sound endpoint.** Any satisfying valuation certifies `verifyRelaxed`: when
the bundle reads as nonzero wire points and a response representative, some
ladder-bounded integer `s`, pinned in `Fq` to the reading's `Type1` decode, gives
`verifyRelaxed ⟨pkP, uP, (s : Fp)⟩` off the forbidden band. -/
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
  have hlow := lowest128Bits'_spec (F := Fq) (by decide) (by decide) true
    (.const Pasta.vestaEndo)
  have hendo := EndoMul.endoMul_spec (F := Fq) HasEndo.vesta 32 (by norm_num) stv.pk
  simp only [show HasEndo.vesta.endo = Pasta.vestaEndo from rfl] at hendo
  have hscale := scaleFast1_spec (F := Fq) HasCurve.vesta 255 51 (by norm_num)
    ⟨.const gen.x, .const gen.y⟩ ⟨stv.z⟩
  have hadd := AddFast.addFast_checkFinite_spec (F := Fq) Vesta.curve.toAffine
    ⟨rfl, rfl, rfl, rfl⟩ (by decide) stv.u
  mvcgen [hlow, hendo, hscale, hadd]
  case vc1.hsize => exact fqParams_size
  rename_i st hpre
  intro squeezed _ hsqv
  simp only [List.map_cons, List.map_nil, CVar.val] at hsqv
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

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The complete endpoint.** The honest checking-prover run accepts a statement
`verify` accepts, honestly encoded and nondegenerate, only extending the table.
Exported in plain run form — a concrete-field prover triple's type cannot be
referenced without evaluating the run it matches on; the triple is internal,
equivalent by `complete_spec_iff`. -/
theorem verifyCircuit_complete_spec (stv : Statement.Raw (FVar Fq))
    (stP : Statement) (zv : Fq)
    (hpk0 : stP.pk ≠ 0) (hu0 : stP.u ≠ 0) (hz0 : stP.z ≠ 0)
    (hfit : ToNat.toNat zv < 2 ^ 255)
    (hfaith : ((ToNat.toNat zv : ℕ) : Fq) = zv)
    (hreg : HasCurve.vesta.LadderRegime 255
      (Type1.fromShifted 255 ⟨(ToNat.toNat zv : ℤ)⟩))
    (henc : ((Type1.fromShifted 255 ⟨(ToNat.toNat zv : ℤ)⟩ : ℤ) : Fp) = stP.z)
    (hacc : verify stP = true) :
    ∀ st : ProverState Fq,
      Reads st.env stv (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zv⟩
        : Statement.Raw Fq) →
      ∃ out : Proved Fq PUnit,
        prove (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
            (verifyCircuit (c := KimchiConstraint Fq) stv) st.nv st.env = .ok out
          ∧ st.env.Le out.assignments := by
  have htriple : ∀ Q : PostCond PUnit (.arg (ProverState Fq)
      (.except EvalError .pure)),
      ⦃Complete
          (fun env => Reads env stv
            (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zv⟩ : Statement.Raw Fq))
          (fun _ _ _ => True) Q⦄
      (verifyCircuit (c := KimchiProverC Fq) stv)
      ⦃Q⦄ := ?_
  · intro st hpre
    revert htriple
    rw [show verifyCircuit (c := KimchiConstraint Fq) stv
        = verifyCircuit (c := KimchiProverC Fq) stv from rfl]
    generalize verifyCircuit (c := KimchiProverC Fq) stv = g
    intro htriple
    obtain ⟨out, hrun, -, hle⟩ := (complete_spec_iff g _ _).mp htriple st hpre
    exact ⟨out, hrun, hle⟩
  intro Q
  simp only [verifyCircuit, lowest128Bits]
  have hsq := RandomOracle.hashVec_complete_spec (F := Fq) Poseidon.fqParams
    fqParams_size
  have hlow := lowest128Bits'_complete_spec (F := Fq) true (.const Pasta.vestaEndo)
  have hendo := EndoMul.endoMul_complete_spec (F := Fq) HasEndo.vesta 32 (by norm_num)
    stv.pk
  simp only [show HasEndo.vesta.endo = Pasta.vestaEndo from rfl] at hendo
  have hscale := scaleFast1_complete_spec (F := Fq) HasCurve.vesta 255 51 (by norm_num)
    ⟨.const gen.x, .const gen.y⟩ ⟨stv.z⟩
  have hadd := AddFast.addFast_complete_spec (F := Fq) .checkFinite Vesta.curve.toAffine
    ⟨rfl, rfl, rfl, rfl⟩ (by decide) stv.u
  mvcgen -trivial [hsq, hlow, hendo, hscale, hadd]
  · exact fqParams_size
  rename_i st₀ hpre
  obtain ⟨hrd, hk⟩ := hpre
  rw [reads_statementRaw_iff] at hrd
  obtain ⟨hpkx, hpky, hux, huy, hzz⟩ := hrd
  -- the wire points and the generator are on-curve
  have hpkC := SWPoint.onCurve_of_ne_zero hpk0
  have huC := SWPoint.onCurve_of_ne_zero hu0
  have hgenC : OnCurve Vesta.curve.A Vesta.curve.B (gen.x, gen.y) := by
    rcases gen.onCurve with h | h
    · exact h
    · exact absurd h (by decide)
  have hpkNS : Vesta.curve.toAffine.Nonsingular stP.pk.x stP.pk.y := nonsingular_toW hpkC
  have huNS : Vesta.curve.toAffine.Nonsingular stP.u.x stP.u.y := nonsingular_toW huC
  have hgenNS : Vesta.curve.toAffine.Nonsingular gen.x gen.y := nonsingular_toW hgenC
  -- the transcript leg
  refine ⟨fun x hx => ?_, fun squeezed st₁ hout₁ hle₁ => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isOk_of_eq rfl
    · exact isOk_of_eq rfl
    · exact isOk_of_eq hpkx
    · exact isOk_of_eq hpky
    · exact isOk_of_eq hux
    · exact isOk_of_eq huy
  have hsqv : squeezed.eval st₁.env = .ok (transcriptHash stP.pk stP.u) :=
    hout₁ [gen.x, gen.y, stP.pk.x, stP.pk.y, stP.u.x, stP.u.y]
      (.cons (reads_fvar_iff.mpr rfl) (.cons (reads_fvar_iff.mpr rfl)
        (.cons (reads_fvar_iff.mpr hpkx) (.cons (reads_fvar_iff.mpr hpky)
          (.cons (reads_fvar_iff.mpr hux) (.cons (reads_fvar_iff.mpr huy) .nil))))))
  -- the split leg: the hash value's honest split representatives are faithful
  mvcgen -trivial [hlow, hendo, hscale, hadd]
  refine ⟨⟨isOk_of_eq hsqv, isOk_of_eq rfl, fun vv hvv => ?_⟩,
    fun c st₂ hout₂ hle₂ => ?_⟩
  · rw [hsqv] at hvv
    injection hvv with hvv
    subst hvv
    have hHbound : (transcriptHash stP.pk stP.u).val < 2 ^ 128 * 2 ^ 128 :=
      lt_of_lt_of_le (ZMod.val_lt _) (by decide)
    have hHdiv : (transcriptHash stP.pk stP.u).val / 2 ^ 128 < 2 ^ 128 :=
      (Nat.div_lt_iff_lt_mul (by positivity)).mpr hHbound
    refine ⟨ZMod.natCast_rightInverse _, hHdiv, ?_, ?_⟩
    · show (((ToNat.toNat (transcriptHash stP.pk stP.u) % 2 ^ 128 : ℕ) : Fq)).val
          = ToNat.toNat (transcriptHash stP.pk stP.u) % 2 ^ 128
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by decide))
    · show (((ToNat.toNat (transcriptHash stP.pk stP.u) / 2 ^ 128 : ℕ) : Fq)).val
          = ToNat.toNat (transcriptHash stP.pk stP.u) / 2 ^ 128
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le hHdiv (by decide))
  have hcv : c.val.eval st₂.env = .ok ((preChallenge stP.pk stP.u : ℕ) : Fq) :=
    hout₂ _ hsqv
  -- the challenge leg: endoMul at the canonical prechallenge
  mvcgen -trivial [hendo, hscale, hadd]
  have hpkx₂ := CVar.eval_le hle₂ (CVar.eval_le hle₁ hpkx)
  have hpky₂ := CVar.eval_le hle₂ (CVar.eval_le hle₁ hpky)
  refine ⟨⟨isOk_of_eq hcv, isOk_of_eq hpkx₂, isOk_of_eq hpky₂, fun v hv => ?_,
    fun x y hx hy => ?_⟩, fun cpk st₃ hout₃ hle₃ => ?_⟩
  · rw [hcv] at hv
    injection hv with hv
    subst hv
    have hpc : preChallenge stP.pk stP.u < 2 ^ 128 :=
      Nat.mod_lt _ (by positivity)
    constructor
    · show (((preChallenge stP.pk stP.u : ℕ) : Fq)).val < 2 ^ 128
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le hpc (by decide))]
      exact hpc
    · exact ZMod.natCast_rightInverse _
  · rw [hpkx₂] at hx
    rw [hpky₂] at hy
    injection hx with hx
    injection hy with hy
    subst hx
    subst hy
    exact hpkNS
  obtain ⟨xC, yC, hcpkx, hcpky, hfinC, sc, A, B, hseq, hsab, hAle, hBle,
    hAval, hBval, -⟩ := hout₃ _ _ _ hcv hpkx₂ hpky₂ hpkNS
  have hpcval : ToNat.toNat ((preChallenge stP.pk stP.u : ℕ) : Fq)
      = preChallenge stP.pk stP.u := by
    show (((preChallenge stP.pk stP.u : ℕ) : Fq)).val = _
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by decide))
  rw [hpcval, show (2 * 32 : ℕ) = 64 from by norm_num] at hAval hBval
  have hsInt : sc = Kimchi.Gate.EndoScalar.toIntZ
      (Kimchi.Gate.EndoScalar.digitsOf 64 (preChallenge stP.pk stP.u))
      HasEndo.vesta.lam :=
    HasEndo.vesta.decomposition_eq_toIntZ (preChallenge stP.pk stP.u) hsab
      (by norm_num at hAle ⊢; exact hAle) (by norm_num at hBle ⊢; exact hBle)
      hAval hBval
  have hchal : ((sc : ℤ) : Fp) = Poseidon.FqSponge.endoExpand
      Poseidon.FqVesta.spec.lam (preChallenge stP.pk stP.u) := by
    rw [hsInt, Kimchi.Gate.EndoScalar.endoExpand_eq_toField (by decide) (by decide),
      show Poseidon.FqVesta.spec.lam = ((HasEndo.vesta.lam : ℤ) : Fp) from rfl,
      Kimchi.Gate.EndoScalar.crumbsOf_eq_map,
      Kimchi.Gate.EndoScalar.toField_digits (by decide) (by decide) _
        (Kimchi.Gate.EndoScalar.digitsOf_lt 64 _) HasEndo.vesta.lam]
  -- the response leg: the ladder at the honest encoding
  mvcgen -trivial [hscale, hadd]
  have hzz₃ := CVar.eval_le hle₃ (CVar.eval_le hle₂ (CVar.eval_le hle₁ hzz))
  refine ⟨⟨isOk_of_eq hzz₃, isOk_of_eq rfl, isOk_of_eq rfl, fun v hv => ?_,
    fun x y hx hy => ?_⟩, fun zg st₄ hout₄ hle₄ => ?_⟩
  · rw [hzz₃] at hv
    injection hv with hv
    subst hv
    exact ⟨by simpa using hfit, hfaith, by simpa using hreg⟩
  · injection hx with hx
    injection hy with hy
    subst hx
    subst hy
    exact hgenNS
  obtain ⟨xZ, yZ, hzgx, hzgy, hzgNS, hzact⟩ := hout₄ _ _ _ hzz₃ rfl rfl hgenNS
  -- the wire equation, transported into the Mathlib group at the statement's points
  simp only [verify, decide_eq_true_eq] at hacc
  have haccM : (stP.z.val : ℤ)
      • WeierstrassCurve.Affine.Point.some gen.x gen.y hgenNS
      = WeierstrassCurve.Affine.Point.some _ _ huNS
        + (((Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam
            (preChallenge stP.pk stP.u)).val : ℤ)
          • WeierstrassCurve.Affine.Point.some _ _ hpkNS) := by
    have h := congrArg (SWPoint.equivPoint Vesta.curve) hacc
    rw [map_nsmul, map_add, map_nsmul,
      SWPoint.equivPoint_eq_some gen hgenC,
      SWPoint.equivPoint_eq_some stP.pk hpkC,
      SWPoint.equivPoint_eq_some stP.u huC] at h
    rw [← natCast_zsmul, ← natCast_zsmul] at h
    exact h
  -- scalars act through their residues mod the order
  have hsmul : ∀ a b : ℤ, ((a : ZMod PALLAS_BASE_CARD) = (b : ZMod PALLAS_BASE_CARD)) →
      ∀ P : Vesta.curve.toAffine.Point, a • P = b • P := fun a b hab P =>
    Kimchi.Gate.VarBaseMul.smul_eq_smul_of_zmod_eq _ (by
      rw [ZMod.intCast_eq_intCast_iff] at hab ⊢
      rwa [Pasta.vesta_card])
  have hchalV : ((((Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam
      (preChallenge stP.pk stP.u)).val : ℕ) : ℤ) : ZMod PALLAS_BASE_CARD)
      = ((sc : ℤ) : ZMod PALLAS_BASE_CARD) := by
    push_cast
    rw [← hchal]
    simp [ZMod.natCast_val]
  have hmaster : (stP.z.val : ℤ)
      • WeierstrassCurve.Affine.Point.some gen.x gen.y hgenNS
      = WeierstrassCurve.Affine.Point.some _ _ huNS
        + sc • WeierstrassCurve.Affine.Point.some _ _ hpkNS := by
    rw [haccM, hsmul _ _ hchalV]
  -- the sum is the nonzero [z]·G
  have hzpos : (0 : ℤ) < (stP.z.val : ℤ) := by
    rcases Nat.eq_zero_or_pos stP.z.val with h | h
    · exact absurd ((ZMod.val_eq_zero _).mp h) hz0
    · exact_mod_cast h
  have hgz : (stP.z.val : ℤ)
      • WeierstrassCurve.Affine.Point.some gen.x gen.y hgenNS ≠ 0 :=
    Kimchi.Gate.VarBaseMul.smul_ne_zero_of_lt Vesta.curve.toAffine
      (WeierstrassCurve.Affine.Point.some_ne_zero hgenNS) hzpos
      (by rw [Pasta.vesta_card]; exact_mod_cast ZMod.val_lt _)
  -- the complete addition of u and [c]·pk
  mvcgen -trivial [hadd]
  have hux₄ := CVar.eval_le hle₄ (CVar.eval_le hle₃ (CVar.eval_le hle₂
    (CVar.eval_le hle₁ hux)))
  have huy₄ := CVar.eval_le hle₄ (CVar.eval_le hle₃ (CVar.eval_le hle₂
    (CVar.eval_le hle₁ huy)))
  have hcpkx₄ := CVar.eval_le hle₄ hcpkx
  have hcpky₄ := CVar.eval_le hle₄ hcpky
  refine ⟨⟨isOk_of_eq hux₄, isOk_of_eq huy₄, isOk_of_eq hcpkx₄, isOk_of_eq hcpky₄,
    fun x1 y1 x2 y2 h1e h2e h3e h4e => ?_⟩, fun rhs st₅ hout₅ hle₅ => ?_⟩
  · rw [hux₄] at h1e
    rw [huy₄] at h2e
    rw [hcpkx₄] at h3e
    rw [hcpky₄] at h4e
    injection h1e with h1e
    injection h2e with h2e
    injection h3e with h3e
    injection h4e with h4e
    subst h1e
    subst h2e
    subst h3e
    subst h4e
    exact ⟨huNS, hfinC,
      Kimchi.Gate.VarBaseMul.y_ne_zero_of_odd_order Vesta.curve.toAffine
        (by rw [Pasta.vesta_card]; decide) huNS,
      fun h0 => hgz (hmaster.trans ((congrArg
        (WeierstrassCurve.Affine.Point.some _ _ huNS + ·) hseq).symm.trans h0))⟩
  obtain hpost := hout₅ _ _ _ _ hux₄ huy₄ hcpkx₄ hcpky₄ huNS hfinC
  rcases hpost with ⟨-, habs⟩ | ⟨x3, y3, hrx, hry, -, h3, hsum⟩
  · exact absurd (hmaster.trans ((congrArg
      (WeierstrassCurve.Affine.Point.some _ _ huNS + ·) hseq).symm.trans habs)) hgz
  -- the two computed points agree: the asserts hold
  have henc' : ((Type1.fromShifted (5 * 51) ⟨(ToNat.toNat zv : ℤ)⟩ : ℤ) : Fp)
      = stP.z := by simpa using henc
  have hzV : ((Type1.fromShifted (5 * 51) ⟨(ToNat.toNat zv : ℤ)⟩ : ℤ)
      : ZMod PALLAS_BASE_CARD) = ((stP.z.val : ℤ) : ZMod PALLAS_BASE_CARD) := by
    rw [henc']
    push_cast
    simp [ZMod.natCast_val]
  have hfinal : WeierstrassCurve.Affine.Point.some xZ yZ hzgNS
      = WeierstrassCurve.Affine.Point.some x3 y3 h3 :=
    hzact.trans ((hsmul _ _ hzV _).trans (hmaster.trans ((congrArg
      (WeierstrassCurve.Affine.Point.some _ _ huNS + ·) hseq).symm.trans hsum)))
  injection hfinal with hfx hfy
  -- the coordinate asserts and the closing continuation
  mvcgen -trivial
  refine ⟨⟨isOk_of_eq (CVar.eval_le hle₅ hzgx), isOk_of_eq hrx,
    fun a b ha hb => ?_⟩, fun _ st₆ hle₆ => ?_⟩
  · rw [CVar.eval_le hle₅ hzgx] at ha
    rw [hrx] at hb
    injection ha with ha
    injection hb with hb
    subst ha
    subst hb
    exact hfx
  mvcgen -trivial
  refine ⟨⟨isOk_of_eq (CVar.eval_le (hle₅.trans hle₆) hzgy),
    isOk_of_eq (CVar.eval_le hle₆ hry), fun a b ha hb => ?_⟩,
    fun _ st₇ hle₇ => ?_⟩
  · rw [CVar.eval_le (hle₅.trans hle₆) hzgy] at ha
    rw [CVar.eval_le hle₆ hry] at hb
    injection ha with ha
    injection hb with hb
    subst ha
    subst hb
    exact hfy
  exact hk ⟨⟩ st₇ (hle₁.trans (hle₂.trans (hle₃.trans (hle₄.trans
    (hle₅.trans (hle₆.trans hle₇))))))

end Schnorr
