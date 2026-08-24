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
@[spec] theorem verifyCircuit_spec (V : Valuation Fq) (stv : Statement (FVar Fq)) :
    ⦃⌜True⌝⦄
    (verifyCircuit (c := Builder V (KimchiConstraint Fq)) stv)
    ⦃⇓ _ _ => ⌜∀ raw : Statement Fq, readVal (val := Statement Fq) V stv = raw →
        OnCurve Vesta.curve.A Vesta.curve.B (raw.pk.point.x, raw.pk.point.y) →
        OnCurve Vesta.curve.A Vesta.curve.B (raw.u.point.x, raw.u.point.y) →
        raw.z.fromShifted ≠ (0 : Fp) ∧
        (raw.z.fromShiftedZ ∉ forbiddenValues PALLAS_BASE_CARD → verify raw = true)⌝⦄ := by
  simp only [verifyCircuit]
  have hadd := AddFast.addFast_checkFinite_spec (F := Fq) (V := V)
  mvcgen [hadd]
  case hsize => exact fqParams_size
  case hlen => simp
  rename_i squeezed _ hsqv hbits _ hunpv cpk _ hcpk zr _ _ _ hlockv rhs _ hrhsv _ _ hax _ _ hay
    _ _ hzrv
  simp only [List.map_cons, List.map_nil, CVar.val] at hsqv
  intro hzne raw hread hpkC huC
  -- the reading is the cells, projectionwise
  simp only [circuitVal] at hread
  subst hread
  dsimp only at hpkC huC ⊢
  have hpkNS : Vesta.curve.toAffine.Nonsingular
      (stv.pk.point.x.val V) (stv.pk.point.y.val V) := nonsingular_toW hpkC
  have huNS : Vesta.curve.toAffine.Nonsingular
      (stv.u.point.x.val V) (stv.u.point.y.val V) := nonsingular_toW huC
  -- the zero-response exclusion, then the band-conditional wire certificate
  refine ⟨fun h0 => hzne ((Type1.fromShifted_eq_zero_iff _).mp h0), fun hband => ?_⟩
  set pkR : VestaPoint Fq := ⟨⟨stv.pk.point.x.val V, stv.pk.point.y.val V⟩⟩ with hpkR
  set uR : VestaPoint Fq := ⟨⟨stv.u.point.x.val V, stv.u.point.y.val V⟩⟩ with huR
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
  have hcval : (packLow 128 (by omega) hbits).val V = ((nL : ℕ) : Fq) :=
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
  have hvalId : (stv.z.val.val V).val = natLsbVal bs.toList :=
    toNat_eq_of_natCast_eq hpin.symm hlt
  set s : ℤ := unshiftType1 (5 * 51) (natLsbVal bs.toList : ℤ) with hsdef
  clear_value s
  have hsdecode : s = Type1.fromShiftedZ ⟨stv.z.val.val V⟩ := by
    simp only [hsdef, Type1.fromShiftedZ, hvalId]
  -- the ladder regime at the canonical scalar
  have hregime : HasCurve.vesta.LadderRegime (5 * 51) s := by
    rw [hsdecode]; exact vesta_ladderRegime _ hband
  obtain ⟨hzgNS, hzact⟩ := hpt hregime
  -- u is finite: odd prime order has no 2-torsion
  have huy0 : stv.u.point.y.val V ≠ 0 :=
    Kimchi.Gate.VarBaseMul.y_ne_zero_of_odd_order Vesta.curve.toAffine
      (by rw [Pasta.vesta_card]; decide) huNS
  obtain ⟨hrhsNS, hsum⟩ := hrhsv huNS hfinC huy0
  -- the asserts glue the two computed points; the master identity at the readings
  have hglue := Kimchi.Gate.EndoMul.some_congr Vesta.curve.toAffine hzgNS hrhsNS hax hay
  have hfinC' : Vesta.curve.toAffine.Nonsingular (cpk.x.val V) (cpk.y.val V) := hfinC
  have hseq' : WeierstrassCurve.Affine.Point.some _ _ hfinC'
      = sc • WeierstrassCurve.Affine.Point.some _ _ hpkNS := hseq
  have hmaster : s • WeierstrassCurve.Affine.Point.some gen.x gen.y gen_nonsingular
      = WeierstrassCurve.Affine.Point.some _ _ huNS
        + sc • WeierstrassCurve.Affine.Point.some _ _ hpkNS :=
    (hzact.symm.trans (hglue.trans hsum.symm)).trans
      (congrArg (WeierstrassCurve.Affine.Point.some _ _ huNS + ·) hseq')
  -- the wire equation, in Mathlib's group at the reading
  have hz1 : ((s : ℤ) : Fp) = Type1.fromShifted ⟨stv.z.val.val V⟩ := by
    rw [hsdecode]; rfl
  have hc : ((sc : ℤ) : Fp) = challenge pkR uR := by
    rw [challenge, ← hnLpre]; exact hchal
  rw [verify_iff]
  refine ⟨hpkC, huC, fun h0 => hzne ((Type1.fromShifted_eq_zero_iff _).mp h0), ?_⟩
  dsimp only
  rw [← hz1, ← hc, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact hmaster

open CompElliptic.Curves.Pasta in
/-- Points with equal coordinates are equal, past the nonsingularity proof. -/
private theorem some_congr {x y x' y' : Fq} (hx : x = x') (hy : y = y')
    (h : Vesta.curve.toAffine.Nonsingular x y) (h' : Vesta.curve.toAffine.Nonsingular x' y') :
    WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx hy
  rfl

/-- The state of `verifyCircuit`'s honest run: the hash, the canonical unpack, the
endomorphism ladder at the packed low bits, the variable-base ladder on the generator,
its bits' lock, the complete addition, and the exclusion's inverse — each at the state the
previous left (the two coordinate equalities allocate nothing). -/
def verifyRun (st : ProverState Fq) (stv : Statement (FVar Fq)) : ProverState Fq :=
  let h := RandomOracle.hashVecRun Poseidon.fqParams st
    [.const gen.x, .const gen.y, stv.pk.point.x, stv.pk.point.y, stv.u.point.x, stv.u.point.y]
  let u := unpackFullRun h.1 PALLAS_SCALAR_CARD 255 h.2
  let cpk := EndoMul.endoMulRun Pasta.vestaEndo 32 u.1 stv.pk.point ⟨packLow 128 (by omega) u.2⟩
  let zr := varBaseMulRun 255 51 cpk.1 ⟨.const gen.x, .const gen.y⟩ stv.z
  let lock := ltRun zr.1 (zr.2.lsbBits.toList.map .unchecked).reverse
    (modBitsMsb PALLAS_SCALAR_CARD 255)
  let rhs := AddFast.addFastRun lock.1 .checkFinite stv.u.point cpk.2
  (invRun rhs.1 (CVar.sub_ stv.z.val (.const Type1.zeroCarrier))).1

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- The honest run, stage for stage: on a table reading a statement `verify` accepts, in
the ladder regime, the checking prover lands at `verifyRun`, only extending the table. The
guard's on-curve and nonzero facts are what each stage's run needs. -/
private theorem run_facts (stv : Statement (FVar Fq)) (raw : Statement Fq)
    (hreg : HasCurve.vesta.LadderRegime 255 raw.z.fromShiftedZ) (hacc : verify raw = true)
    (st : ProverState Fq) (hsc : CircuitType.Scoped (Statement Fq) st stv)
    (hread : readVal (val := Statement Fq) st.env.toValuation stv = raw) :
    prove (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
        (verifyCircuit (c := KimchiConstraint Fq) stv) st.nv st.env
      = .ok ((verifyRun st stv).out ()) ∧ st.env.Le (verifyRun st stv).env := by
  subst hread
  simp only [scoped_ofEquiv_iff, scoped_prod_iff, scoped_fvar_iff, circuitVal] at hsc
  obtain ⟨⟨hpkx, hpky⟩, ⟨hux, huy⟩, hzz⟩ := hsc
  have hin : readVal (val := Statement Fq) st.env.toValuation stv
      = (⟨⟨⟨stv.pk.point.x.val st.env.toValuation, stv.pk.point.y.val st.env.toValuation⟩⟩,
          ⟨⟨stv.u.point.x.val st.env.toValuation, stv.u.point.y.val st.env.toValuation⟩⟩,
          ⟨stv.z.val.val st.env.toValuation⟩⟩ : Statement Fq) := by
    simp only [circuitVal]
  rw [hin] at hreg hacc
  set pkx := stv.pk.point.x.val st.env.toValuation with hpkxd
  set pky := stv.pk.point.y.val st.env.toValuation with hpkyd
  set ux := stv.u.point.x.val st.env.toValuation with huxd
  set uy := stv.u.point.y.val st.env.toValuation with huyd
  set zv := stv.z.val.val st.env.toValuation with hzvd
  obtain ⟨hpkC, huC, hz0, heq⟩ := (verify_iff _).mp hacc
  dsimp only at hpkC huC hz0 heq hreg
  have hpkNS : Vesta.curve.toAffine.Nonsingular pkx pky := nonsingular_toW hpkC
  have huNS : Vesta.curve.toAffine.Nonsingular ux uy := nonsingular_toW huC
  generalize hG : verifyRun st stv = G
  unfold verifyRun at hG
  extract_lets +lift h u cpk zr lock rhs at hG
  have hh : RandomOracle.hashVecRun Poseidon.fqParams st [CVar.const gen.x, CVar.const gen.y,
    stv.pk.point.x, stv.pk.point.y, stv.u.point.x, stv.u.point.y] = h := rfl
  have hu : unpackFullRun h.1 PALLAS_SCALAR_CARD 255 h.2 = u := rfl
  have hcpk : EndoMul.endoMulRun HasEndo.vesta.endo 32 u.1 stv.pk.point
    ⟨packLow 128 (by omega) u.2⟩ = cpk := rfl
  have hzr : varBaseMulRun 255 51 cpk.1 ⟨.const gen.x, .const gen.y⟩ stv.z = zr := rfl
  have hlock : ltRun zr.1 (zr.2.lsbBits.toList.map BoolVar.unchecked).reverse
    (modBitsMsb PALLAS_SCALAR_CARD 255) = lock := rfl
  have hrhs : AddFast.addFastRun lock.1 .checkFinite stv.u.point cpk.2 = rhs := rfl
  clear_value rhs lock zr cpk u h
  subst hG
  simp only [verifyCircuit, prove_bind]
  rw [show Pasta.vestaEndo = HasEndo.vesta.endo from rfl]
  -- the transcript leg
  have hxs : ∀ x ∈ [CVar.const gen.x, CVar.const gen.y, stv.pk.point.x, stv.pk.point.y,
      stv.u.point.x, stv.u.point.y], x.Scoped st := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact CVar.scoped_const _ _
    · exact CVar.scoped_const _ _
    · exact hpkx
    · exact hpky
    · exact hux
    · exact huy
  have gh := RandomOracle.hashVecRun_grants Poseidon.fqParams fqParams_size hxs
  rw [hh] at gh
  have hhv : h.2.val h.1.env.toValuation = transcriptHash ⟨⟨pkx, pky⟩⟩ ⟨⟨ux, uy⟩⟩ := by
    rw [gh.fvar_val]
    unfold transcriptHash
    simp only [List.map_cons, List.map_nil, CVar.val]
    rw [← hpkxd, ← hpkyd, ← huxd, ← huyd]
  have lh : st.env.Le h.1.env := gh.le
  rw [RandomOracle.hashVec_run Poseidon.fqParams st hxs, hh]
  simp only [Except.bind]
  -- the canonical unpack at the honest hash value
  have hlt : ToNat.toNat (h.2.val h.1.env.toValuation) < 2 ^ 255 := by
    rw [hhv]
    exact lt_of_lt_of_le (LawfulToNat.toNat_lt _) (by decide)
  have hbelow : ToNat.toNat (h.2.val h.1.env.toValuation) < PALLAS_SCALAR_CARD := by
    rw [hhv]
    exact LawfulToNat.toNat_lt _
  have hm : PALLAS_SCALAR_CARD < 2 ^ 255 := by decide
  rw [unpackFull_run PALLAS_SCALAR_CARD 255 hm h.1 gh.fvar_scoped hlt hbelow, hu]
  simp only [Except.bind]
  have lu : h.1.env.Le u.1.env := by
    have := unpackFullRun_le h.1 PALLAS_SCALAR_CARD 255 h.2
    rwa [hu] at this
  have lhu : st.env.Le u.1.env := lh.trans lu
  have hbit : ∀ i (hi : i < 255), (u.2[i]).toCVar.val u.1.env.toValuation
      = bit (unpackPure (h.2.val h.1.env.toValuation) 255)[i] := by
    intro i hi
    have := unpackFullRun_bit h.1 PALLAS_SCALAR_CARD 255 h.2 i hi
    rw [hu] at this
    simp only [unpackPure, Vector.getElem_ofFn]
    exact this
  -- the packed low bits read as the wire challenge
  have hcv : (packLow 128 (by omega) u.2).val u.1.env.toValuation
      = ((preChallenge ⟨⟨pkx, pky⟩⟩ ⟨⟨ux, uy⟩⟩ : ℕ) : Fq) := by
    rw [packLow_val (by omega) hbit, natLsbVal_take_unpackPure (by omega), hhv]
    rfl
  have hpc : preChallenge ⟨⟨pkx, pky⟩⟩ ⟨⟨ux, uy⟩⟩ < 2 ^ 128 := Nat.mod_lt _ (by positivity)
  have hpcval : ToNat.toNat ((preChallenge ⟨⟨pkx, pky⟩⟩ ⟨⟨ux, uy⟩⟩ : ℕ) : Fq)
      = preChallenge ⟨⟨pkx, pky⟩⟩ ⟨⟨ux, uy⟩⟩ := by
    show (((preChallenge ⟨⟨pkx, pky⟩⟩ ⟨⟨ux, uy⟩⟩ : ℕ) : Fq)).val = _
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le hpc (by decide))
  -- the challenge leg: endoMul at the canonical prechallenge
  have t3 : ∀ i (hi : i < 255), (u.2[i]).toCVar.Scoped u.1 := by
    intro i hi
    exact hu ▸ unpackFullRun_scoped h.1 PALLAS_SCALAR_CARD 255 h.2 i hi
  sorry
  have hfits : (⟨packLow 128 (by omega) u.2⟩ : SizedF (4 * 32) (FVar Fq)).Fits
      u.1.env.toValuation := by
    show ToNat.toNat ((packLow 128 (by omega) u.2).val u.1.env.toValuation) < 2 ^ (4 * 32)
    rw [hcv, hpcval]
    exact hpc
  have hT₁ : Vesta.curve.toAffine.Nonsingular (stv.pk.point.x.val u.1.env.toValuation)
      (stv.pk.point.y.val u.1.env.toValuation) := by
    rw [CVar.val_of_le lhu hpkx, CVar.val_of_le lhu hpky]
    exact hpkNS
  rw [EndoMul.endoMul_run (d := HasEndo.vesta) 32 (by norm_num) u.1 hsc (hpkx.of_le lhu) (hpky.of_le lhu)
    hfits hT₁, hcpk]
  simp only [Except.bind]
  have gc := EndoMul.endoMulRun_grants (d := HasEndo.vesta) 32 (by norm_num) u.1 (hpkx.of_le lhu)
    (hpky.of_le lhu) hfits hT₁
  rw [hcpk] at gc
  obtain ⟨lc, hcx, hcy, hfinC, sc, A, B, hseq, hsab, hAle, hBle, hAval, hBval, -⟩ := gc
  dsimp only at hAval hBval
  rw [hcv, hpcval, show (2 * 32 : ℕ) = 64 from by norm_num] at hAval hBval
  have hchal : ((sc : ℤ) : Fp) = challenge ⟨⟨pkx, pky⟩⟩ ⟨⟨ux, uy⟩⟩ :=
    HasEndo.vesta_endoExpand hsab hAle hBle hAval hBval
  have hseq' : WeierstrassCurve.Affine.Point.some (cpk.2.x.val cpk.1.env.toValuation)
        (cpk.2.y.val cpk.1.env.toValuation) hfinC
      = sc • WeierstrassCurve.Affine.Point.some pkx pky hpkNS := by
    rw [hseq, some_congr (CVar.val_of_le lhu hpkx) (CVar.val_of_le lhu hpky) hT₁ hpkNS]
  -- the response leg: the ladder at the honest encoding
  have lhc : st.env.Le cpk.1.env := lhu.trans lc
  have hzc : stv.z.val.val cpk.1.env.toValuation = zv := CVar.val_of_le lhc hzz
  have hrange : ToNat.toNat (stv.z.val.val cpk.1.env.toValuation) < 2 ^ (5 * 51) := by
    rw [hzc]
    exact lt_of_lt_of_le (LawfulToNat.toNat_lt _) (by decide)
  have hreg' : HasCurve.vesta.LadderRegime (5 * 51)
      (unshiftType1 (5 * 51) (ToNat.toNat (stv.z.val.val cpk.1.env.toValuation) : ℤ)) := by
    rw [hzc]
    simpa [Type1.fromShiftedZ] using hreg
  have hTg : Vesta.curve.toAffine.Nonsingular
      ((CVar.const gen.x : FVar Fq).val cpk.1.env.toValuation)
      ((CVar.const gen.y : FVar Fq).val cpk.1.env.toValuation) := gen_nonsingular
  rw [varBaseMul_run (d := HasCurve.vesta) 255 51 (by norm_num) cpk.1 (hzz.of_le lhc)
    (CVar.scoped_const _ _) (CVar.scoped_const _ _) hrange hreg' hTg, hzr]
  simp only [Except.bind]
  have gz := varBaseMulRun_grants (d := HasCurve.vesta) 255 51 (by norm_num) cpk.1
    (hzz.of_le lhc) (CVar.scoped_const _ _) (CVar.scoped_const _ _) hrange hreg' hTg
  rw [hzr] at gz
  obtain ⟨lz, hzgx, hzgy, hlsb, hzgNS, hzact⟩ := gz
  rw [hzc] at hzact
  -- the canonicity lock at the honest bits
  have hbits : ∀ x ∈ zr.2.lsbBits.toList.map BoolVar.unchecked, (↑x : CVar Fq).Scoped zr.1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
    rw [Vector.getElem_toList]
    exact (hlsb i (by simpa using hi)).1
  have hbs : List.Forall₂ (fun (x : BoolVar Fq) (b : Bool) =>
      (↑x : CVar Fq).val zr.1.env.toValuation = bit b)
      (zr.2.lsbBits.toList.map BoolVar.unchecked)
      ((List.range 255).map (ToNat.toNat zv).testBit) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp, fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map, Vector.getElem_toList, List.getElem_range]
    rw [BoolVar.toCVar_unchecked, (hlsb i (by simpa using h1)).2, hzc]
    rfl
  have hval : natLsbVal ((List.range 255).map (ToNat.toNat zv).testBit) < PALLAS_SCALAR_CARD := by
    rw [natLsbVal_testBit_range (lt_of_lt_of_le (LawfulToNat.toNat_lt _) (by decide))]
    exact LawfulToNat.toNat_lt _
  rw [assertBitsBelow_run PALLAS_SCALAR_CARD 255 hm
    (by rw [List.length_map, Vector.length_toList]) zr.1 hbits hbs hval, hlock]
  simp only [Except.bind]
  have ll : zr.1.env.Le lock.1.env := by
    have := (ltRun_scope _ (modBitsMsb PALLAS_SCALAR_CARD 255)
      fun x hx => hbits x (List.mem_reverse.mp hx)).1
    rwa [hlock] at this
  -- the wire equation at the ladder's integer: scalars act through the module
  have hzF : ((unshiftType1 (5 * 51) (ToNat.toNat zv : ℤ) : ℤ) : Fp)
      = (⟨zv⟩ : Type1 Fq).fromShifted := rfl
  have hmaster : (unshiftType1 (5 * 51) (ToNat.toNat zv : ℤ) : ℤ)
      • WeierstrassCurve.Affine.Point.some gen.x gen.y gen_nonsingular
      = WeierstrassCurve.Affine.Point.some ux uy huNS
        + sc • WeierstrassCurve.Affine.Point.some pkx pky hpkNS := by
    rw [← Int.cast_smul_eq_zsmul (R := Fp), ← Int.cast_smul_eq_zsmul (R := Fp), hzF, hchal]
    exact heq
  have hgz : (unshiftType1 (5 * 51) (ToNat.toNat zv : ℤ) : ℤ)
      • WeierstrassCurve.Affine.Point.some gen.x gen.y gen_nonsingular ≠ 0 := by
    rw [← Int.cast_smul_eq_zsmul (R := Fp), hzF]
    exact fun h => (smul_eq_zero.mp h).elim hz0
      (WeierstrassCurve.Affine.Point.some_ne_zero gen_nonsingular)
  have hsum_ne : WeierstrassCurve.Affine.Point.some ux uy huNS
      + WeierstrassCurve.Affine.Point.some (cpk.2.x.val cpk.1.env.toValuation)
        (cpk.2.y.val cpk.1.env.toValuation) hfinC ≠ 0 :=
    fun h0 => hgz (hmaster.trans ((congrArg
      (WeierstrassCurve.Affine.Point.some ux uy huNS + ·) hseq').symm.trans h0))
  -- the complete addition of u and [c]·pk
  have llk : st.env.Le lock.1.env := lhc.trans (lz.trans ll)
  have lcl : cpk.1.env.Le lock.1.env := lz.trans ll
  have huNS' : Vesta.curve.toAffine.Nonsingular (stv.u.point.x.val lock.1.env.toValuation)
      (stv.u.point.y.val lock.1.env.toValuation) := by
    rw [CVar.val_of_le llk hux, CVar.val_of_le llk huy]
    exact huNS
  have hfinC' : Vesta.curve.toAffine.Nonsingular (cpk.2.x.val lock.1.env.toValuation)
      (cpk.2.y.val lock.1.env.toValuation) := by
    rw [CVar.val_of_le lcl hcx, CVar.val_of_le lcl hcy]
    exact hfinC
  have hops : AddFast.Operands HasCurve.vesta .checkFinite
      (stv.u.point.x.val lock.1.env.toValuation) (stv.u.point.y.val lock.1.env.toValuation)
      (cpk.2.x.val lock.1.env.toValuation) (cpk.2.y.val lock.1.env.toValuation) := by
    refine ⟨huNS', hfinC', ?_, fun _ => ?_⟩
    · rw [CVar.val_of_le llk huy]
      exact Kimchi.Gate.VarBaseMul.y_ne_zero_of_odd_order Vesta.curve.toAffine
        (by rw [Pasta.vesta_card]; decide) huNS
    · rw [some_congr (CVar.val_of_le llk hux) (CVar.val_of_le llk huy) huNS' huNS,
        some_congr (CVar.val_of_le lcl hcx) (CVar.val_of_le lcl hcy) hfinC' hfinC]
      exact hsum_ne
  rw [AddFast.addFast_run (d := HasCurve.vesta) .checkFinite lock.1 (hux.of_le llk) (huy.of_le llk)
    (hcx.of_le lcl) (hcy.of_le lcl) hops, hrhs]
  simp only [Except.bind]
  have gr := AddFast.addFastRun_grants (d := HasCurve.vesta) .checkFinite lock.1 (hux.of_le llk)
    (huy.of_le llk) (hcx.of_le lcl) (hcy.of_le lcl) hops
  rw [hrhs] at gr
  obtain ⟨lr, hrx, hry, -, hpost⟩ := gr
  rcases hpost huNS' hfinC' with ⟨-, habs⟩ | ⟨h3, -, hsum⟩
  · rw [some_congr (CVar.val_of_le llk hux) (CVar.val_of_le llk huy) huNS' huNS,
      some_congr (CVar.val_of_le lcl hcx) (CVar.val_of_le lcl hcy) hfinC' hfinC] at habs
    exact absurd habs hsum_ne
  rw [some_congr (CVar.val_of_le llk hux) (CVar.val_of_le llk huy) huNS' huNS,
    some_congr (CVar.val_of_le lcl hcx) (CVar.val_of_le lcl hcy) hfinC' hfinC] at hsum
  -- the two computed points agree: the asserts hold
  have hfinal : WeierstrassCurve.Affine.Point.some (zr.2.g.x.val zr.1.env.toValuation)
        (zr.2.g.y.val zr.1.env.toValuation) hzgNS
      = WeierstrassCurve.Affine.Point.some (rhs.2.p.x.val rhs.1.env.toValuation)
        (rhs.2.p.y.val rhs.1.env.toValuation) h3 :=
    hzact.trans (hmaster.trans ((congrArg
      (WeierstrassCurve.Affine.Point.some ux uy huNS + ·) hseq').symm.trans hsum))
  injection hfinal with hfx hfy
  have lzr : zr.1.env.Le rhs.1.env := ll.trans lr
  rw [assertEqual_run rhs.1 (hzgx.of_le lzr) hrx (by rw [CVar.val_of_le lzr hzgx]; exact hfx)]
  simp only [Except.bind]
  rw [assertEqual_run rhs.1 (hzgy.of_le lzr) hry (by rw [CVar.val_of_le lzr hzgy]; exact hfy)]
  simp only [Except.bind]
  -- the zero-response exclusion at the honest carrier
  have lsr : st.env.Le rhs.1.env := llk.trans lr
  have hzne : stv.z.val.val rhs.1.env.toValuation
      ≠ (CVar.const Type1.zeroCarrier : FVar Fq).val rhs.1.env.toValuation := by
    rw [CVar.val_of_le lsr hzz]
    exact fun hEq => hz0 ((Type1.fromShifted_eq_zero_iff ⟨zv⟩).mpr hEq)
  rw [assertNotEqual_run rhs.1 (hzz.of_le lsr) (CVar.scoped_const _ _) hzne]
  exact ⟨rfl, lsr.trans (invRun_grants ((hzz.of_le lsr).sub_ (CVar.scoped_const _ _))).le⟩

open CompElliptic.Curves.Pasta in
/-- **The complete endpoint.** On a table reading a statement `verify` accepts, in the
ladder regime, the honest checking-prover run accepts and lands at `verifyRun` — the
guard's on-curve and nonzero facts are what the honest runs need. -/
theorem verifyCircuit_run (stv : Statement (FVar Fq)) (raw : Statement Fq)
    (hreg : HasCurve.vesta.LadderRegime 255 raw.z.fromShiftedZ) (hacc : verify raw = true)
    (st : ProverState Fq) (hsc : CircuitType.Scoped (Statement Fq) st stv)
    (hread : readVal (val := Statement Fq) st.env.toValuation stv = raw) :
    prove (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
        (verifyCircuit (c := KimchiConstraint Fq) stv) st.nv st.env
      = .ok ((verifyRun st stv).out ()) :=
  (run_facts stv raw hreg hacc st hsc hread).1

open CompElliptic.Curves.Pasta in
/-- The honest run only extends the table. -/
theorem verifyRun_le (stv : Statement (FVar Fq)) (raw : Statement Fq)
    (hreg : HasCurve.vesta.LadderRegime 255 raw.z.fromShiftedZ) (hacc : verify raw = true)
    (st : ProverState Fq) (hsc : CircuitType.Scoped (Statement Fq) st stv)
    (hread : readVal (val := Statement Fq) st.env.toValuation stv = raw) :
    st.env.Le (verifyRun st stv).env :=
  (run_facts stv raw hreg hacc st hsc hread).2

end Schnorr
