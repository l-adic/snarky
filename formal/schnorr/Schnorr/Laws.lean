import Schnorr.Circuit

/-!
# The circuit laws

The endpoint pair: the circuit is faithful to the wire verifier, sound and
complete. The transcript needs no laws of its own — `verifyCircuit` calls the hash
gadget directly, and `hashVec`'s laws read the squeeze as `transcriptHash` at the
read points, definitionally.

Both cross-field quantities are pinned to canonical representatives by the circuit's
two canonicity locks (`unpackFull` on the transcript hash, `ltBitstringValue` on the
ladder's bits), so soundness lands on the wire `verify` at the statement's named
decode `Type1.fromShifted` — no reconstruction classes remain. The ladder's
forbidden band survives as a decidable hypothesis on the decode. The challenge leg
is one integer read in two fields (`nReconstruct_inj`, `decomposition_eq_toIntZ`,
`endoExpand_eq_toField`); the wire equation is read in Mathlib's group through
`verify_iff`, scalars acting through the point group's `Fp`-module structure.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta
open Pasta.Shifted (unshiftType1)
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
/-- **The sound endpoint.** Any satisfying valuation certifies the wire verifier at
the bundle's reading: when the read points are on-curve — the statement check's
contribution at the seam — the response decode is nonzero, and off the ladder's
forbidden band `verify` accepts the reading. The circuit's two canonicity locks pin
both cross-field readings exactly, so no reconstruction class survives into the
statement; the zero-response exclusion (`assertNotEqual` at `Type1.zeroCarrier`) holds
unconditionally, before the band hypothesis. -/
theorem verifyCircuit_spec (stv : Statement (FVar Fq))
    (Q : PostCond PUnit (.arg (BuilderState Fq) .pure)) :
    ⦃Sound (fun V (_ : PUnit) =>
        ∀ raw : Statement Fq, readVal (val := Statement Fq) V stv = raw →
          OnCurve Vesta.curve.A Vesta.curve.B (raw.pk.point.x, raw.pk.point.y) →
          OnCurve Vesta.curve.A Vesta.curve.B (raw.u.point.x, raw.u.point.y) →
          raw.z.fromShifted ≠ (0 : Fp) ∧
          (raw.z.fromShiftedZ ∉ forbiddenValues PALLAS_BASE_CARD → verify raw = true)) Q⦄
    (verifyCircuit (c := KimchiConstraint Fq) stv)
    ⦃Q⦄ := by
  simp only [verifyCircuit]
  mvcgen
  case vc1.hsize => exact fqParams_size
  rename_i st hpre
  intro squeezed _ hsqv
  simp only [List.map_cons, List.map_nil, CVar.val] at hsqv
  mvcgen
  intro hbits _ hunpv
  mvcgen
  intro cpk _ hcpk
  mvcgen
  intro zr _ hzrv
  mvcgen
  case vc2.hlen => simp
  intro _ _ hlockv
  mvcgen [AddFast.addFast_checkFinite_spec]
  intro rhs _ hrhsv
  mvcgen
  intro _ _ hax
  mvcgen
  intro _ _ hay
  mvcgen
  intro _ _ hzne
  refine hpre ⟨⟩ _ ?_
  intro raw hread hpkC huC
  -- the reading is the cells, projectionwise
  simp only [circuitVal] at hread
  subst hread
  dsimp only at hpkC huC ⊢
  have hpkNS : Vesta.curve.toAffine.Nonsingular
      (stv.pk.point.x.val st.V) (stv.pk.point.y.val st.V) := nonsingular_toW hpkC
  have huNS : Vesta.curve.toAffine.Nonsingular
      (stv.u.point.x.val st.V) (stv.u.point.y.val st.V) := nonsingular_toW huC
  -- the zero-response exclusion, then the band-conditional wire certificate
  refine ⟨fun h0 => hzne ((Type1.fromShifted_eq_zero_iff _).mp h0), fun hband => ?_⟩
  set pkR : VestaPoint Fq := ⟨⟨stv.pk.point.x.val st.V, stv.pk.point.y.val st.V⟩⟩ with hpkR
  set uR : VestaPoint Fq := ⟨⟨stv.u.point.x.val st.V, stv.u.point.y.val st.V⟩⟩ with huR
  -- the canonical unpack: the bits' value is the hash's representative
  obtain ⟨hbs, hbread, hbsum, hbslt⟩ := hunpv
  have hNfull : natLsbVal hbs.toList = (transcriptHash pkR uR).val :=
    (toNat_eq_of_natCast_eq (hbsum.trans hsqv) hbslt).symm
  -- the low 128 bits are the wire challenge
  set nL := natLsbVal (hbs.toList.take 128) with hnLdef
  have hnLpre : nL = preChallenge pkR uR := by
    rw [hnLdef, natLsbVal_take_eq_mod, hNfull]; rfl
  have hnL : nL < 2 ^ 128 := by
    rw [hnLpre]; exact Nat.mod_lt _ (by positivity)
  have hcval : (packLow 128 (by omega) hbits).val st.V = ((nL : ℕ) : Fq) :=
    packLow_val (by omega) hbread
  -- the endoMul crumbs are the challenge's; its scalar reads in Fp as the wire challenge
  obtain ⟨crumbs, hcrv, hclen, hcrec, hfinC, sc, A, B, hseq, hsab, hAle, hBle,
    hAval, hBval, -⟩ := hcpk hpkNS
  have hcrums := HasEndo.vesta_crumbs_eq hnL hcrv hclen (hcval.symm.trans hcrec)
  have hchal : ((sc : ℤ) : Fp)
      = Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam nL :=
    HasEndo.vesta_endoExpand hsab hAle hBle (hcrums ▸ hAval) (hcrums ▸ hBval)
  -- the ladder payload
  simp only [CVar.val] at hzrv
  obtain ⟨bs, hread, hpin, hpt⟩ := hzrv gen_nonsingular
  -- the canonicity lock: the ladder's bits are below the modulus, so its integer is
  -- the reading's representative
  have hlt : natLsbVal bs.toList < PALLAS_SCALAR_CARD :=
    hlockv bs.toList (forall₂_bit_of_reads hread)
  have hvalId : (stv.z.val.val st.V).val = natLsbVal bs.toList :=
    toNat_eq_of_natCast_eq hpin.symm hlt
  set s : ℤ := unshiftType1 (5 * 51) (natLsbVal bs.toList : ℤ) with hsdef
  clear_value s
  have hsdecode : s = Type1.fromShiftedZ ⟨stv.z.val.val st.V⟩ := by
    simp only [hsdef, Type1.fromShiftedZ, hvalId]
  -- the ladder regime at the canonical scalar
  have hregime : HasCurve.vesta.LadderRegime (5 * 51) s := by
    rw [hsdecode]; exact vesta_ladderRegime _ hband
  obtain ⟨hzgNS, hzact⟩ := hpt hregime
  -- u is finite: odd prime order has no 2-torsion
  have huy0 : stv.u.point.y.val st.V ≠ 0 :=
    Kimchi.Gate.VarBaseMul.y_ne_zero_of_odd_order Vesta.curve.toAffine
      (by rw [Pasta.vesta_card]; decide) huNS
  obtain ⟨hrhsNS, hsum⟩ := hrhsv huNS hfinC huy0
  -- the asserts glue the two computed points; the master identity at the readings
  have hglue := Kimchi.Gate.EndoMul.some_congr Vesta.curve.toAffine hzgNS hrhsNS hax hay
  have hfinC' : Vesta.curve.toAffine.Nonsingular (cpk.x.val st.V) (cpk.y.val st.V) := hfinC
  have hseq' : WeierstrassCurve.Affine.Point.some _ _ hfinC'
      = sc • WeierstrassCurve.Affine.Point.some _ _ hpkNS := hseq
  have hmaster : s • WeierstrassCurve.Affine.Point.some gen.x gen.y gen_nonsingular
      = WeierstrassCurve.Affine.Point.some _ _ huNS
        + sc • WeierstrassCurve.Affine.Point.some _ _ hpkNS :=
    (hzact.symm.trans (hglue.trans hsum.symm)).trans
      (congrArg (WeierstrassCurve.Affine.Point.some _ _ huNS + ·) hseq')
  -- the wire equation, in Mathlib's group at the reading
  have hz1 : ((s : ℤ) : Fp) = Type1.fromShifted ⟨stv.z.val.val st.V⟩ := by
    rw [hsdecode]; rfl
  have hc : ((sc : ℤ) : Fp) = challenge pkR uR := by
    rw [challenge, ← hnLpre]; exact hchal
  rw [verify_iff]
  refine ⟨hpkC, huC, fun h0 => hzne ((Type1.fromShifted_eq_zero_iff _).mp h0), ?_⟩
  dsimp only
  rw [← hz1, ← hc, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact hmaster

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The complete endpoint.** The honest checking-prover run accepts a statement
`verify` accepts, in the ladder regime, only extending the table — the guard's
on-curve and nonzero facts are what the honest runs need. Exported in plain run
form — a concrete-field prover triple's type cannot be referenced without evaluating
the run it matches on; the triple is internal, equivalent by `complete_spec_iff`. -/
theorem verifyCircuit_complete_spec (stv : Statement (FVar Fq)) (raw : Statement Fq)
    (hreg : HasCurve.vesta.LadderRegime 255 raw.z.fromShiftedZ)
    (hacc : verify raw = true) :
    ∀ st : ProverState Fq,
      Reads st.env stv raw →
      ∃ out : Proved Fq PUnit,
        prove (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
            (verifyCircuit (c := KimchiConstraint Fq) stv) st.nv st.env = .ok out
          ∧ st.env.Le out.assignments := by
  have htriple : ∀ Q : PostCond PUnit (.arg (ProverState Fq)
      (.except EvalError .pure)),
      ⦃Complete
          (fun env => Reads env stv raw)
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
  simp only [verifyCircuit]
  have hsq := RandomOracle.hashVec_complete_spec (F := Fq) Poseidon.fqParams
    fqParams_size
  mvcgen -trivial [hsq]
  · exact fqParams_size
  rename_i st₀ hpre
  obtain ⟨hrd, hk⟩ := hpre
  simp only [reads_ofEquiv_iff, reads_prod_iff, reads_fvar_iff, circuitVal] at hrd
  obtain ⟨⟨hpkx, hpky⟩, ⟨hux, huy⟩, hzz⟩ := hrd
  -- the wire's guard: both points on-curve, the response nonzero, and the equation
  obtain ⟨hpkC, huC, hz0, heq⟩ := (verify_iff raw).mp hacc
  have hpkNS : Vesta.curve.toAffine.Nonsingular raw.pk.point.x raw.pk.point.y :=
    nonsingular_toW hpkC
  have huNS : Vesta.curve.toAffine.Nonsingular raw.u.point.x raw.u.point.y :=
    nonsingular_toW huC
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
  have hsqv : squeezed.eval st₁.env = .ok (transcriptHash raw.pk raw.u) :=
    hout₁ [gen.x, gen.y, raw.pk.point.x, raw.pk.point.y, raw.u.point.x, raw.u.point.y]
      (.cons (reads_fvar_iff.mpr rfl) (.cons (reads_fvar_iff.mpr rfl)
        (.cons (reads_fvar_iff.mpr hpkx) (.cons (reads_fvar_iff.mpr hpky)
          (.cons (reads_fvar_iff.mpr hux) (.cons (reads_fvar_iff.mpr huy) .nil))))))
  -- the canonical unpack at the honest hash value
  mvcgen -trivial
  case hm => decide
  refine ⟨⟨isOk_of_eq hsqv, fun vv hvv => ?_⟩, fun hbits st₂ hout₂ hle₂ => ?_⟩
  · rw [hsqv] at hvv
    injection hvv with hvv
    subst hvv
    exact ⟨lt_of_lt_of_le (LawfulToNat.toNat_lt _) (by decide), LawfulToNat.toNat_lt _⟩
  have hdig := hout₂ _ hsqv
  -- the packed low bits read as the wire challenge
  have hcev : (packLow 128 (by omega) hbits).eval st₂.env
      = .ok ((preChallenge raw.pk raw.u : ℕ) : Fq) := by
    have hpre : preChallenge raw.pk raw.u
        = ToNat.toNat (transcriptHash raw.pk raw.u) % 2 ^ 128 := rfl
    rw [packLow_eval (by omega) (bs := unpackPure (transcriptHash raw.pk raw.u) 255)
      (fun i hi => by simp only [unpackPure, Vector.getElem_ofFn]; exact hdig i hi),
      natLsbVal_take_unpackPure (by omega), hpre]
  -- the challenge leg: endoMul at the canonical prechallenge
  mvcgen -trivial
  case hbits => norm_num
  case he => rfl
  have hpkx₂ := CVar.eval_le hle₂ (CVar.eval_le hle₁ hpkx)
  have hpky₂ := CVar.eval_le hle₂ (CVar.eval_le hle₁ hpky)
  refine ⟨⟨isOk_of_eq hcev, isOk_of_eq hpkx₂, isOk_of_eq hpky₂, fun v hv => ?_,
    fun x y hx hy => ?_⟩, fun cpk st₃ hout₃ hle₃ => ?_⟩
  · have hveq := hcev.symm.trans hv
    injection hveq with hveq
    subst hveq
    have hpc : preChallenge raw.pk raw.u < 2 ^ 128 :=
      Nat.mod_lt _ (by positivity)
    show (((preChallenge raw.pk raw.u : ℕ) : Fq)).val < 2 ^ 128
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le hpc (by decide))]
    exact hpc
  · rw [hpkx₂] at hx
    rw [hpky₂] at hy
    injection hx with hx
    injection hy with hy
    subst hx
    subst hy
    exact hpkNS
  obtain ⟨xC, yC, hcpkx, hcpky, hfinC, sc, A, B, hseq, hsab, hAle, hBle,
    hAval, hBval, -⟩ := hout₃ _ _ _ hcev hpkx₂ hpky₂ hpkNS
  have hpcval : ToNat.toNat ((preChallenge raw.pk raw.u : ℕ) : Fq)
      = preChallenge raw.pk raw.u := by
    show (((preChallenge raw.pk raw.u : ℕ) : Fq)).val = _
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by decide))
  rw [hpcval, show (2 * 32 : ℕ) = 64 from by norm_num] at hAval hBval
  have hchal : ((sc : ℤ) : Fp) = Poseidon.FqSponge.endoExpand
      Poseidon.FqVesta.spec.lam (preChallenge raw.pk raw.u) :=
    HasEndo.vesta_endoExpand hsab hAle hBle hAval hBval
  -- the response leg: the ladder at the honest encoding
  mvcgen -trivial
  case hn => norm_num
  have hzz₃ := CVar.eval_le hle₃ (CVar.eval_le hle₂ (CVar.eval_le hle₁ hzz))
  refine ⟨⟨isOk_of_eq hzz₃, isOk_of_eq rfl, isOk_of_eq rfl, fun v hv => ?_,
    fun x y hx hy => ?_⟩, fun zr st₄ hbitread hact hle₄ => ?_⟩
  · rw [hzz₃] at hv
    injection hv with hv
    subst hv
    refine ⟨lt_of_lt_of_le (LawfulToNat.toNat_lt _) (by decide),
      by simpa [Type1.fromShiftedZ] using hreg⟩
  · injection hx with hx
    injection hy with hy
    subst hx
    subst hy
    exact gen_nonsingular
  obtain ⟨xZ, yZ, hzgx, hzgy, hzgNS, hzact⟩ := hact _ _ _ hzz₃ rfl rfl gen_nonsingular
  have hdigz := hbitread _ hzz₃
  -- the canonicity lock at the honest bits
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  refine assertBitsBelow_complete_spec PALLAS_SCALAR_CARD 255 (by decide) _
    (by rw [List.length_map, Vector.length_toList])
    ((List.range 255).map (ToNat.toNat raw.z.val).testBit)
    (by
      rw [natLsbVal_testBit_range (m := ToNat.toNat raw.z.val)
        (lt_of_lt_of_le (ZMod.val_lt _) (by decide))]
      exact ZMod.val_lt _)
    _ st₄ ⟨forall₂_bit_of_evals hdigz, fun _ st₅ _ hle₅ => ?_⟩
  -- the wire equation at the ladder's integer: scalars act through the module
  have hzF : ((unshiftType1 (5 * 51) (ToNat.toNat raw.z.val : ℤ) : ℤ) : Fp)
      = raw.z.fromShifted := rfl
  have hc : ((sc : ℤ) : Fp) = challenge raw.pk raw.u := hchal
  have hmaster : (unshiftType1 (5 * 51) (ToNat.toNat raw.z.val : ℤ) : ℤ)
      • WeierstrassCurve.Affine.Point.some gen.x gen.y gen_nonsingular
      = WeierstrassCurve.Affine.Point.some _ _ huNS
        + sc • WeierstrassCurve.Affine.Point.some _ _ hpkNS := by
    rw [← Int.cast_smul_eq_zsmul (R := Fp), ← Int.cast_smul_eq_zsmul (R := Fp), hzF, hc]
    exact heq
  -- the sum is the nonzero [z]·G
  have hgz : (unshiftType1 (5 * 51) (ToNat.toNat raw.z.val : ℤ) : ℤ)
      • WeierstrassCurve.Affine.Point.some gen.x gen.y gen_nonsingular ≠ 0 := by
    rw [← Int.cast_smul_eq_zsmul (R := Fp), hzF]
    exact fun h => (smul_eq_zero.mp h).elim hz0
      (WeierstrassCurve.Affine.Point.some_ne_zero gen_nonsingular)
  -- the complete addition of u and [c]·pk
  mvcgen -trivial [AddFast.addFast_complete_spec]
  have hux₄ := CVar.eval_le hle₅ (CVar.eval_le hle₄
    (CVar.eval_le hle₃ (CVar.eval_le hle₂ (CVar.eval_le hle₁ hux))))
  have huy₄ := CVar.eval_le hle₅ (CVar.eval_le hle₄
    (CVar.eval_le hle₃ (CVar.eval_le hle₂ (CVar.eval_le hle₁ huy))))
  have hcpkx₄ := CVar.eval_le hle₅ (CVar.eval_le hle₄ hcpkx)
  have hcpky₄ := CVar.eval_le hle₅ (CVar.eval_le hle₄ hcpky)
  refine ⟨⟨isOk_of_eq hux₄, isOk_of_eq huy₄, isOk_of_eq hcpkx₄, isOk_of_eq hcpky₄,
    fun x1 y1 x2 y2 h1e h2e h3e h4e => ?_⟩, fun rhs st₆ hout₆ hle₆ => ?_⟩
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
  obtain hpost := hout₆ _ _ _ _ hux₄ huy₄ hcpkx₄ hcpky₄ huNS hfinC
  rcases hpost with ⟨-, habs⟩ | ⟨x3, y3, hrx, hry, -, h3, hsum⟩
  · exact absurd (hmaster.trans ((congrArg
      (WeierstrassCurve.Affine.Point.some _ _ huNS + ·) hseq).symm.trans habs)) hgz
  -- the two computed points agree: the asserts hold
  have hfinal : WeierstrassCurve.Affine.Point.some xZ yZ hzgNS
      = WeierstrassCurve.Affine.Point.some x3 y3 h3 :=
    hzact.trans (hmaster.trans ((congrArg
      (WeierstrassCurve.Affine.Point.some _ _ huNS + ·) hseq).symm.trans hsum))
  injection hfinal with hfx hfy
  -- the coordinate asserts and the closing continuation
  mvcgen -trivial
  have hzgx₆ := CVar.eval_le hle₆ (CVar.eval_le hle₅ hzgx)
  refine ⟨⟨isOk_of_eq hzgx₆, isOk_of_eq hrx,
    fun a b ha hb => ?_⟩, fun _ st₇ hle₇ => ?_⟩
  · exact ((Except.ok.inj (hzgx₆.symm.trans ha)).symm.trans
      (hfx.trans (Except.ok.inj (hrx.symm.trans hb))))
  mvcgen -trivial
  have hzgy₇ := CVar.eval_le hle₇ (CVar.eval_le hle₆
    (CVar.eval_le hle₅ hzgy))
  refine ⟨⟨isOk_of_eq hzgy₇,
    isOk_of_eq (CVar.eval_le hle₇ hry), fun a b ha hb => ?_⟩,
    fun _ st₈ hle₈ => ?_⟩
  · exact ((Except.ok.inj (hzgy₇.symm.trans ha)).symm.trans
      (hfy.trans (Except.ok.inj ((CVar.eval_le hle₇ hry).symm.trans hb))))
  -- the zero-response exclusion at the honest carrier
  mvcgen -trivial
  have hzz₈ := CVar.eval_le hle₈ (CVar.eval_le hle₇ (CVar.eval_le hle₆
    (CVar.eval_le hle₅ (CVar.eval_le hle₄ (CVar.eval_le hle₃ (CVar.eval_le hle₂
      (CVar.eval_le hle₁ hzz)))))))
  refine ⟨⟨isOk_of_eq hzz₈, isOk_of_eq rfl, fun a b ha hb => ?_⟩,
    fun _ st₉ hle₉ => ?_⟩
  · rw [hzz₈] at ha
    injection ha with ha
    injection hb with hb
    subst ha
    subst hb
    exact fun hEq => hz0 ((Type1.fromShifted_eq_zero_iff raw.z).mpr hEq)
  exact hk ⟨⟩ st₉ (hle₁.trans (hle₂.trans (hle₃.trans (hle₄.trans
    (hle₅.trans (hle₆.trans (hle₇.trans (hle₈.trans hle₉))))))))

end Schnorr
