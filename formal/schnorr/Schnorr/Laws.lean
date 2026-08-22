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
`endoExpand_eq_toField`); statement points transport through `SWPoint.equivPoint`.
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

/-- The low slice of a vector, `ofFn`-spelled, is `toList.take`. -/
private theorem toList_ofFn_slice {α : Type} (v : Vector α 255) :
    (Vector.ofFn fun i : Fin 128 => v[i.val]'(by omega)).toList
      = v.toList.take 128 := by
  rw [Vector.toList_ofFn]
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_take, Vector.length_toList]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_take, Vector.getElem_toList]

/-- The Horner value of the low 128 test-bits is the value mod `2^128`. -/
private theorem natLsbVal_ofFn_testBit_low (m : ℕ) :
    natLsbVal (List.ofFn fun i : Fin 128 => m.testBit i.val) = m % 2 ^ 128 := by
  rw [show (List.ofFn fun i : Fin 128 => m.testBit i.val)
      = (List.range 128).map (m % 2 ^ 128).testBit from ?_]
  · exact natLsbVal_testBit_range (Nat.mod_lt _ (by positivity))
  · apply List.ext_getElem
    · rw [List.length_ofFn, List.length_map, List.length_range]
    · intro i h1 h2
      rw [List.length_ofFn] at h1
      rw [List.getElem_ofFn, List.getElem_map, List.getElem_range,
        Nat.testBit_mod_two_pow, decide_eq_true h1, Bool.true_and]

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The sound endpoint.** Any satisfying valuation certifies the wire verifier at
the statement's canonical decode: when the bundle reads as nonzero wire points and a
`Type1` representative whose decode is off the ladder's forbidden band, `verify`
accepts `⟨pkP, uP, fromShifted zt⟩`. The circuit's two canonicity locks pin both
cross-field readings exactly, so no reconstruction class survives into the
statement; the zero-response exclusion (`assertNotEqual` at `Type1.zeroCarrier`) holds
unconditionally, before the band hypothesis. -/
theorem verifyCircuit_spec (stv : Statement.Raw (FVar Fq))
    (Q : PostCond PUnit (.arg (BuilderState Fq) .pure)) :
    ⦃Sound (fun V (_ : PUnit) =>
        ∀ (pkP uP : SWPoint Vesta.curve) (zt : Type1 Fq), pkP ≠ 0 → uP ≠ 0 →
          readVal (val := Statement.Raw Fq) V stv = ⟨⟨pkP.x, pkP.y⟩, ⟨uP.x, uP.y⟩, zt⟩ →
          zt.fromShifted ≠ (0 : Fp) ∧
          (zt.fromShiftedZ ∉ forbiddenValues PALLAS_BASE_CARD →
            verify ⟨pkP, uP, zt.fromShifted⟩ = true)) Q⦄
    (verifyCircuit (c := KimchiConstraint Fq) stv)
    ⦃Q⦄ := by
  simp only [verifyCircuit]
  have hendo := EndoMul.endoMul_spec (F := Fq) HasEndo.vesta 32 (by norm_num) stv.pk
  simp only [show HasEndo.vesta.endo = Pasta.vestaEndo from rfl] at hendo
  have hvbm := varBaseMul_spec (F := Fq) HasCurve.vesta 255 51 (by norm_num)
    ⟨.const gen.x, .const gen.y⟩ stv.z
  have hadd := AddFast.addFast_checkFinite_spec (F := Fq) Vesta.curve.toAffine
    ⟨rfl, rfl, rfl, rfl⟩ (by decide) stv.u
  mvcgen [hendo, hvbm, hadd]
  case vc1.hsize => exact fqParams_size
  rename_i st hpre
  intro squeezed _ hsqv
  simp only [List.map_cons, List.map_nil, CVar.val] at hsqv
  mvcgen [hendo, hvbm, hadd]
  intro hbits _ hunpv
  mvcgen [hendo, hvbm, hadd]
  intro cpk _ hcpk
  mvcgen [hvbm, hadd]
  intro zr _ hzrv
  mvcgen [hadd]
  case vc2.hlen => simp
  intro _ _ hlockv
  mvcgen [hadd]
  intro rhs _ hrhsv
  mvcgen
  intro _ _ hax
  mvcgen
  intro _ _ hay
  mvcgen
  intro _ _ hzne
  refine hpre ⟨⟩ _ ?_
  intro pkP uP zt hpk0 hu0 hread
  -- one reading equation decomposes into the per-cell facts
  simp only [readVal_statementRaw, Statement.Raw.mk.injEq, AffinePoint.mk.injEq]
    at hread
  obtain ⟨⟨hpkx, hpky⟩, ⟨hux, huy⟩, hzt⟩ := hread
  subst hzt
  -- the zero-response exclusion, then the band-conditional wire certificate
  refine ⟨fun h0 => hzne ((Type1.fromShifted_eq_zero_iff _).mp h0), fun hband => ?_⟩
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
  -- the canonical unpack: the full value is the hash's canonical representative
  obtain ⟨hbs, hbread, hbsum, hbslt⟩ := hunpv
  have hH : squeezed.val st.V = transcriptHash pkP uP := by
    rw [hsqv]
    simp only [transcriptHash]
    rw [hpkx, hpky, hux, huy]
  have hNfull : natLsbVal hbs.toList = (transcriptHash pkP uP).val := by
    have hcast : ((natLsbVal hbs.toList : ℕ) : Fq) = transcriptHash pkP uP := by
      rw [← packPure_natCast, hbsum, hH]
    have hval := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hbslt] at hval
  -- the low 128 bits are the wire challenge
  set nL := natLsbVal (hbs.toList.take 128) with hnLdef
  have hnL : nL < 2 ^ 128 := by
    have hlt := natLsbVal_lt (hbs.toList.take 128)
    have hlen : (hbs.toList.take 128).length = 128 := by simp
    rwa [hlen] at hlt
  have hcval : (challengeOf hbits).val st.V = ((nL : ℕ) : Fq) := by
    unfold challengeOf
    refine Eq.trans (pack_val
      (bs := Vector.ofFn fun i : Fin 128 => hbs[i.val]'(by omega)) ?_) ?_
    · intro i hi
      simp only [Vector.getElem_ofFn]
      exact hbread _ (by omega)
    · rw [packPure_natCast, toList_ofFn_slice]
  have hnLpre : nL = preChallenge pkP uP := by
    have hsplit := natLsbVal_take_drop 128 hbs.toList
    have hmod : (transcriptHash pkP uP).val % 2 ^ 128 = nL := by
      rw [← hNfull, hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hnL]
    rw [preChallenge, ← hmod]
  -- the endoMul crumbs are the canonical decomposition of the challenge
  obtain ⟨crumbs, hcrv, hclen, hcrec, hfinC, sc, A, B, hseq, hsab, hAle, hBle,
    hAval, hBval, -⟩ := hcpk hpkNS
  have hcrums : crumbs = Kimchi.Gate.EndoScalar.crumbsOf 64 nL := by
    refine Kimchi.Gate.EndoScalar.nReconstruct_inj (p := PALLAS_SCALAR_CARD) crumbs _
      (by decide) (by decide) hcrv (Kimchi.Gate.EndoScalar.crumbsOf_valid 64 nL) ?_ ?_ ?_
    · rw [hclen, Kimchi.Gate.EndoScalar.crumbsOf_length]
    · rw [hclen]; decide
    · rw [← hcrec, hcval, Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf]
      exact congrArg (Nat.cast (R := Fq))
        (Nat.mod_eq_of_lt (lt_of_lt_of_le hnL (by decide))).symm
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
  -- the ladder payload
  simp only [CVar.val] at hzrv
  obtain ⟨bs, hread, hpin, hpt⟩ := hzrv hgenNS
  -- the canonicity lock: the ladder's bits are below the modulus
  have hfa : List.Forall₂ (fun (x : BoolVar Fq) (b : Bool) =>
      (↑x : CVar Fq).val st.V = bit b)
      ((zr.lsbBits.toList.take (5 * 51)).map .unchecked) bs.toList := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp, fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_take,
      Vector.getElem_toList, BoolVar.toCVar_unchecked]
    exact hread i (by simpa using h2)
  have hlt : natLsbVal bs.toList < PALLAS_SCALAR_CARD := hlockv bs.toList hfa
  -- the ladder's integer is the reading's canonical representative
  have hvalId : (stv.z.val.val st.V).val = natLsbVal bs.toList := by
    have h := congrArg ZMod.val hpin
    rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at h
  set s : ℤ := unshiftType1 (5 * 51) (natLsbVal bs.toList : ℤ) with hsdef
  clear_value s
  have hsdecode : s = Type1.fromShiftedZ ⟨stv.z.val.val st.V⟩ := by
    simp only [hsdef, Type1.fromShiftedZ, hvalId]
  -- the ladder regime at the canonical scalar: the one-wrap band off the forbidden set
  have hOv : HasCurve.vesta.W.order = PALLAS_BASE_CARD := Pasta.vesta_card
  have hregime : HasCurve.vesta.LadderRegime (5 * 51) s := by
    refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;> rw [hOv]
    · decide
    · decide
    · decide
    · rw [hsdecode]
      exact hband
  obtain ⟨hzgNS, hzact⟩ := hpt hregime
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
  -- the wire equation, transported into the Mathlib group at the statement's points
  simp only [verify, decide_eq_true_eq]
  show ((Type1.fromShifted ⟨stv.z.val.val st.V⟩ : Fp)).val • gen
      = uP + (Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam
          (preChallenge pkP uP)).val • pkP
  have hsmul : ∀ a b : ℤ, ((a : ZMod PALLAS_BASE_CARD) = (b : ZMod PALLAS_BASE_CARD)) →
      ∀ P : Vesta.curve.toAffine.Point, a • P = b • P := fun a b hab P =>
    Kimchi.Gate.VarBaseMul.smul_eq_smul_of_zmod_eq _ (by
      rw [ZMod.intCast_eq_intCast_iff] at hab ⊢
      rwa [Pasta.vesta_card])
  have hz1 : ((((Type1.fromShifted ⟨stv.z.val.val st.V⟩ : Fp)).val : ℤ)
      : ZMod PALLAS_BASE_CARD) = ((s : ℤ) : ZMod PALLAS_BASE_CARD) := by
    rw [show (Type1.fromShifted ⟨stv.z.val.val st.V⟩ : Fp)
        = ((s : ℤ) : Fp) from by rw [hsdecode]; rfl]
    push_cast
    simp [ZMod.natCast_val]
  have hz2 : (((Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam
      (preChallenge pkP uP)).val : ℤ)
      : ZMod PALLAS_BASE_CARD) = ((sc : ℤ) : ZMod PALLAS_BASE_CARD) := by
    push_cast
    rw [← hnLpre, ← hchal]
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
    (stP : Statement) (zt : Type1 Fq)
    (hpk0 : stP.pk ≠ 0) (hu0 : stP.u ≠ 0) (hz0 : stP.z ≠ 0)
    (hreg : HasCurve.vesta.LadderRegime 255 (zt.fromShiftedZ))
    (henc : zt.fromShifted = stP.z)
    (hacc : verify stP = true) :
    ∀ st : ProverState Fq,
      Reads st.env stv (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zt⟩
        : Statement.Raw Fq) →
      ∃ out : Proved Fq PUnit,
        prove (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
            (verifyCircuit (c := KimchiConstraint Fq) stv) st.nv st.env = .ok out
          ∧ st.env.Le out.assignments := by
  have htriple : ∀ Q : PostCond PUnit (.arg (ProverState Fq)
      (.except EvalError .pure)),
      ⦃Complete
          (fun env => Reads env stv
            (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zt⟩ : Statement.Raw Fq))
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
  have hendo := EndoMul.endoMul_complete_spec (F := Fq) HasEndo.vesta 32 (by norm_num)
    stv.pk
  simp only [show HasEndo.vesta.endo = Pasta.vestaEndo from rfl] at hendo
  have hvbmc := varBaseMul_complete_spec (F := Fq) HasCurve.vesta 255 51 (by norm_num)
    ⟨.const gen.x, .const gen.y⟩ stv.z
  have hadd := AddFast.addFast_complete_spec (F := Fq) .checkFinite Vesta.curve.toAffine
    ⟨rfl, rfl, rfl, rfl⟩ (by decide) stv.u
  mvcgen -trivial [hsq, hendo, hvbmc, hadd]
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
  -- the canonical unpack at the honest hash value
  mvcgen -trivial [hendo, hvbmc, hadd]
  case hm => decide
  refine ⟨⟨isOk_of_eq hsqv, fun vv hvv => ?_⟩, fun hbits st₂ hout₂ hle₂ => ?_⟩
  · rw [hsqv] at hvv
    injection hvv with hvv
    subst hvv
    exact ⟨ZMod.natCast_rightInverse _,
      lt_of_lt_of_le (ZMod.val_lt _) (by decide), ZMod.val_lt _⟩
  have hdig := hout₂ _ hsqv
  -- the packed low bits read as the wire challenge
  have hcev : (challengeOf hbits).eval st₂.env
      = .ok ((preChallenge stP.pk stP.u : ℕ) : Fq) := by
    unfold challengeOf
    refine Eq.trans (pack_eval
      (bs := Vector.ofFn fun i : Fin 128 =>
        (ToNat.toNat (transcriptHash stP.pk stP.u)).testBit i.val) ?_) ?_
    · intro i hi
      simp only [Vector.getElem_ofFn]
      exact hdig _ (by omega)
    · rw [packPure_natCast, Vector.toList_ofFn, natLsbVal_ofFn_testBit_low]
      rfl
  -- the challenge leg: endoMul at the canonical prechallenge
  mvcgen -trivial [hendo, hvbmc, hadd]
  have hpkx₂ := CVar.eval_le hle₂ (CVar.eval_le hle₁ hpkx)
  have hpky₂ := CVar.eval_le hle₂ (CVar.eval_le hle₁ hpky)
  refine ⟨⟨isOk_of_eq hcev, isOk_of_eq hpkx₂, isOk_of_eq hpky₂, fun v hv => ?_,
    fun x y hx hy => ?_⟩, fun cpk st₃ hout₃ hle₃ => ?_⟩
  · have hveq := hcev.symm.trans hv
    injection hveq with hveq
    subst hveq
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
    hAval, hBval, -⟩ := hout₃ _ _ _ hcev hpkx₂ hpky₂ hpkNS
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
  mvcgen -trivial [hvbmc, hadd]
  have hzz₃ := CVar.eval_le hle₃ (CVar.eval_le hle₂ (CVar.eval_le hle₁ hzz))
  refine ⟨⟨isOk_of_eq hzz₃, isOk_of_eq rfl, isOk_of_eq rfl, fun v hv => ?_,
    fun x y hx hy => ?_⟩, fun zr st₄ hbitread hact hle₄ => ?_⟩
  · rw [hzz₃] at hv
    injection hv with hv
    subst hv
    refine ⟨lt_of_lt_of_le (ZMod.val_lt _) (by decide),
      ZMod.natCast_rightInverse _, by simpa [Type1.fromShiftedZ] using hreg⟩
  · injection hx with hx
    injection hy with hy
    subst hx
    subst hy
    exact hgenNS
  obtain ⟨xZ, yZ, hzgx, hzgy, hzgNS, hzact⟩ := hact _ _ _ hzz₃ rfl rfl hgenNS
  have hdigz := hbitread _ hzz₃
  -- the canonicity lock at the honest bits
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  have hfa : List.Forall₂ (fun (x : BoolVar Fq) (b : Bool) =>
      (↑x : CVar Fq).eval st₄.env = .ok (bit b))
      ((zr.lsbBits.toList.take (5 * 51)).map .unchecked)
      ((List.range 255).map (ToNat.toNat zt.val).testBit) := by
    rw [List.forall₂_iff_get]
    constructor
    · rw [List.length_map, List.length_take, Vector.length_toList,
        List.length_map, List.length_range]
      decide
    · intro i h1 h2
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_take,
        List.getElem_range, BoolVar.toCVar_unchecked, Vector.getElem_toList]
      exact hdigz i (by simpa using h2)
  refine assertBitsBelow_complete_spec PALLAS_SCALAR_CARD 255 (by decide) _
    (by rw [List.length_map, List.length_take, Vector.length_toList]; decide)
    ((List.range 255).map (ToNat.toNat zt.val).testBit)
    (by
      rw [natLsbVal_testBit_range (m := ToNat.toNat zt.val)
        (lt_of_lt_of_le (ZMod.val_lt _) (by decide))]
      exact ZMod.val_lt _)
    _ st₄ ⟨hfa, fun _ st₅ _ hle₅ => ?_⟩
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
  -- the honest encoding: the ladder's scalar is the wire response mod the order
  have henc' : ((unshiftType1 (5 * 51) (ToNat.toNat zt.val : ℤ) : ℤ) : Fp)
      = stP.z := by simpa [Type1.fromShifted, Type1.fromShiftedZ] using henc
  have hzV : ((unshiftType1 (5 * 51) (ToNat.toNat zt.val : ℤ) : ℤ)
      : ZMod PALLAS_BASE_CARD) = ((stP.z.val : ℤ) : ZMod PALLAS_BASE_CARD) := by
    rw [henc']
    push_cast
    simp [ZMod.natCast_val]
  -- the complete addition of u and [c]·pk
  mvcgen -trivial [hadd]
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
    hzact.trans ((hsmul _ _ hzV _).trans (hmaster.trans ((congrArg
      (WeierstrassCurve.Affine.Point.some _ _ huNS + ·) hseq).symm.trans hsum)))
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
    exact fun hEq => hz0 (henc.symm.trans ((Type1.fromShifted_eq_zero_iff zt).mpr hEq))
  exact hk ⟨⟩ st₉ (hle₁.trans (hle₂.trans (hle₃.trans (hle₄.trans
    (hle₅.trans (hle₆.trans (hle₇.trans (hle₈.trans hle₉))))))))

end Schnorr
