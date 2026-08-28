import Schnorr.Circuit

/-!
# The circuit laws

The endpoint pair. Soundness: any satisfying valuation certifies the wire verifier at the
bundle's reading. The two on-curve facts are the statement `CheckedType`'s contribution at
the compile seam, not something `verifyCircuit`'s own rows force; the band exclusion is the
ladder's non-degeneracy pricing. The zero-response exclusion holds unconditionally.

Both cross-field readings are pinned to canonical representatives by the circuit's two
canonicity locks (`unpackFull` on the transcript hash, `assertBitsBelow` on the ladder's
bits), so no reconstruction class survives into the statement and soundness lands on the
wire `verify` at the statement's own decode.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open Std.Do

/-- The parameter tables have the full round length — the hash laws' size hypothesis. -/
private theorem fqParams_size :
    Poseidon.fqParams.roundConstants.size = Poseidon.fullRounds := by
  show (Poseidon.FqKimchi.roundConstants.map _).size = Poseidon.fullRounds
  rw [Array.size_map]
  decide

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open WeierstrassCurve.Affine in
/-- **The sound endpoint.** -/
theorem verifyCircuit_spec {V : Valuation Fq} (stv : Statement (FVar Fq)) :
    ⦃⌜True⌝⦄
    verifyCircuit (c := Builder V (KimchiConstraint Fq)) stv
    ⦃⇓ _ _ => ⌜∀ raw : Statement Fq, CircuitType.Reads V stv raw →
        OnCurve Vesta.curve.A Vesta.curve.B (raw.pk.point.x, raw.pk.point.y) →
        OnCurve Vesta.curve.A Vesta.curve.B (raw.u.point.x, raw.u.point.y) →
        raw.z.toScalar ≠ (0 : Fp) ∧
        (raw.z.toScalarZ ∉ forbiddenValues PALLAS_BASE_CARD → verify raw = true)⌝⦄ := by
  simp only [verifyCircuit]
  have hendo := fun (sc : SizedF 128 (FVar Fq)) =>
    EndoMul.endoMul_spec (V := V) HasEndo.vesta stv.pk.point sc
  have hvbm := fun (b : AffinePoint (FVar Fq)) (sc : Type1 (FVar Fq)) =>
    varBaseMul_spec (V := V) HasCurve.vesta 255 51 (by norm_num) b sc
  mvcgen [hendo, hvbm]
  case vc1.hsize => exact fqParams_size
  case vc4.W => exact Vesta.curve.toAffine
  case vc5.ha => exact ⟨rfl, rfl, rfl, rfl⟩
  intro hzne raw hread hpkC huC
  obtain ⟨bs, hbread, hbsum, hbslt⟩ :=
    ‹∃ bs : Vector Bool 255, _ ∧ _ ∧ _›
  -- the reading is the cells, projectionwise
  rw [reads_statement] at hread
  obtain ⟨hpkR, huR, hzR⟩ := hread
  -- the response's decode is nonzero: the circuit's `assertNotEqual` row, at the carrier
  have hz0 : raw.z.toScalar ≠ (0 : Fp) := fun h0 => hzne (by
    rw [show (CVar.const Type1.zeroCarrier).val V = Type1.zeroCarrier from rfl,
      ← (Type1.toScalar_eq_zero_iff _).mp h0]
    exact hzR)
  refine ⟨hz0, fun hband => ?_⟩
  · -- the read points, in the curve vocabulary the gadget laws speak
    set pkR : VestaPoint Fq := ⟨⟨raw.pk.point.x, raw.pk.point.y⟩⟩ with hpkRdef
    set uR : VestaPoint Fq := ⟨⟨raw.u.point.x, raw.u.point.y⟩⟩ with huRdef
    have hpkAt : OnCurveAt Vesta.curve.toAffine V stv.pk.point
        (Point.some raw.pk.point.x raw.pk.point.y (nonsingular_toW hpkC)) :=
      OnCurveAt.of_reads hpkR.1 hpkR.2 _
    have huAt : OnCurveAt Vesta.curve.toAffine V stv.u.point
        (Point.some raw.u.point.x raw.u.point.y (nonsingular_toW huC)) :=
      OnCurveAt.of_reads huR.1 huR.2 _
    have hgenAt : OnCurveAt Vesta.curve.toAffine V
        (⟨CVar.const gen.x, CVar.const gen.y⟩ : AffinePoint (FVar Fq))
        (Point.some gen.x gen.y gen_nonsingular) :=
      ⟨gen_nonsingular, rfl⟩
    -- the low 128 bits are the wire challenge
    have hNfull : Kimchi.natLsbVal bs.toList = (transcriptHash pkR uR).val := by
      have hsq : ((Kimchi.natLsbVal bs.toList : ℕ) : Fq) = transcriptHash pkR uR := by
        rw [hbsum, ‹CVar.val _ V = Poseidon.RandomOracle.hash _ _›]
        simp only [List.map_cons, List.map_nil, CVar.val]
        rw [hpkR.1, hpkR.2, huR.1, huR.2]
        rfl
      exact (toNat_eq_of_natCast_eq (F := Fq) hsq hbslt).symm
    -- the challenge leg, at the deployed reading
    have hnL : preChallenge pkR uR < 2 ^ 128 := Nat.mod_lt _ (by positivity)
    have hcpk := EndoMul.vesta_endoMul_read (n := preChallenge pkR uR) hnL
      (by
        rw [packLow_val (n := 255) (k := 128) (by norm_num) hbread, toList_takeVec,
          Kimchi.natLsbVal_take_eq_mod, hNfull]
        rfl)
      ‹∀ T : Vesta.curve.toAffine.Point, _› _ hpkAt
    -- the ladder leg, at the carrier's decode and the constant generator
    have hzact := vesta_varBaseMul_read (Z := raw.z) hzR hband
      ‹∀ T : HasCurve.vesta.W.Point, _› _ hgenAt ‹∀ bs : Vector Bool 255, _ → _›
    rw [verify_iff]
    refine ⟨hpkC, huC, hz0, ?_⟩
    -- `u + [c]·pk` is finite: an odd prime order has no 2-torsion
    obtain ⟨hinf0, hsum⟩ :=
      ‹CVar.val _ V = 0 ∧
        ∀ P Q : Vesta.curve.toAffine.Point, _ → _ → _ → _ ∨ _›
    rcases hsum _ _ huAt hcpk
      (HasCurve.two_torsion_free HasCurve.vesta _ (Point.some_ne_zero _)) with
      ⟨hinf1, -⟩ | ⟨-, hfin⟩
    · exact absurd hinf1 (by rw [hinf0]; decide)
    · show ((raw.z.toScalarZ : ℤ) : Fp) • _ = _
      rw [Int.cast_smul_eq_zsmul]
      exact OnCurveAt.eq hzact hfin
        ‹CVar.val _ V = CVar.val _ V› ‹CVar.val _ V = CVar.val _ V›

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open WeierstrassCurve.Affine in
/-- **The complete endpoint.** A statement the wire verifier accepts, whose response
decode is off the ladder's forbidden band, makes the circuit run: the honest prover's
witness exists and every row it emits is satisfied at every extension of where the run
lands.

The two hypotheses are the sound endpoint's two conclusions, read backwards — the on-curve
grants and the zero-response exclusion arrive inside `verify`, and the band exclusion is
the ladder's non-degeneracy pricing, which soundness charges and completeness pays. The
canonicity locks cost nothing here: a transcript hash's representative is below the field's
own order, and so is a carrier's. -/
theorem verifyCircuit_complete (stv : Statement (FVar Fq)) (raw : Statement Fq)
    (hv : verify raw = true)
    (hband : raw.z.toScalarZ ∉ forbiddenValues PALLAS_BASE_CARD) :
    Complete (F := Fq) (c := KimchiConstraint Fq)
      (fun st => CircuitType.ReadsAs (val := Statement Fq) st stv raw)
      (verifyCircuit (c := KimchiConstraint Fq) stv)
      (fun _ _ => True) := by
  rw [verify_iff] at hv
  obtain ⟨hpkC, huC, hz0, hcheck⟩ := hv
  unfold challenge at hcheck
  simp only [verifyCircuit]
  -- a cell reading, packed
  have hk : ∀ (st : ProverState Fq) (x : FVar Fq) (v : Fq), CVar.Scoped st x →
      x.val st.env.get = v → CircuitType.ReadsAs (val := Fq) st x v :=
    fun _ _ _ hs hv => ⟨CircuitType.scoped_fvar.mpr hs, CircuitType.reads_fvar.mpr hv⟩
  -- the six absorbed coordinates, off the statement's reading
  have habs : ∀ st : ProverState Fq, CircuitType.ReadsAs (val := Statement Fq) st stv raw →
      List.Forall₂ (CircuitType.ReadsAs (val := Fq) st)
        [CVar.const gen.x, CVar.const gen.y, stv.pk.point.x, stv.pk.point.y,
          stv.u.point.x, stv.u.point.y]
        [gen.x, gen.y, raw.pk.point.x, raw.pk.point.y, raw.u.point.x, raw.u.point.y] := by
    rintro st ⟨hsc, hrd⟩
    rw [scoped_statement] at hsc
    rw [reads_statement] at hrd
    exact .cons (hk _ _ _ (CVar.scoped_const _ _) rfl)
      (.cons (hk _ _ _ (CVar.scoped_const _ _) rfl)
      (.cons (hk _ _ _ hsc.1.1 hrd.1.1) (.cons (hk _ _ _ hsc.1.2 hrd.1.2)
      (.cons (hk _ _ _ hsc.2.1.1 hrd.2.1.1) (.cons (hk _ _ _ hsc.2.1.2 hrd.2.1.2) .nil)))))
  -- the statement's points, in the curve vocabulary the gadget laws speak
  have hpkAs : ∀ st : ProverState Fq, CircuitType.ReadsAs (val := Statement Fq) st stv raw →
      OnCurveAs Vesta.curve.toAffine st stv.pk.point
        (Point.some raw.pk.point.x raw.pk.point.y (nonsingular_toW hpkC)) := by
    rintro st ⟨hsc, hrd⟩
    rw [scoped_statement] at hsc
    rw [reads_statement] at hrd
    exact ⟨scoped_affinePoint.mpr hsc.1, OnCurveAt.of_reads hrd.1.1 hrd.1.2 _⟩
  have huAs : ∀ st : ProverState Fq, CircuitType.ReadsAs (val := Statement Fq) st stv raw →
      OnCurveAs Vesta.curve.toAffine st stv.u.point
        (Point.some raw.u.point.x raw.u.point.y (nonsingular_toW huC)) := by
    rintro st ⟨hsc, hrd⟩
    rw [scoped_statement] at hsc
    rw [reads_statement] at hrd
    exact ⟨scoped_affinePoint.mpr hsc.2.1, OnCurveAt.of_reads hrd.2.1.1 hrd.2.1.2 _⟩
  have hzAs : ∀ st : ProverState Fq, CircuitType.ReadsAs (val := Statement Fq) st stv raw →
      CircuitType.ReadsAs (val := Fq) st stv.z.val raw.z.val := by
    rintro st ⟨hsc, hrd⟩
    rw [scoped_statement] at hsc
    rw [reads_statement] at hrd
    exact hk _ _ _ hsc.2.2 hrd.2.2
  have hgenAs : ∀ st : ProverState Fq,
      OnCurveAs Vesta.curve.toAffine st
        (⟨CVar.const gen.x, CVar.const gen.y⟩ : AffinePoint (FVar Fq))
        (Point.some gen.x gen.y gen_nonsingular) :=
    fun _ => ⟨scoped_affinePoint.mpr ⟨CVar.scoped_const _ _, CVar.scoped_const _ _⟩,
      gen_nonsingular, rfl⟩
  -- the transcript hash
  refine Complete.bind (Complete.frame
    (P := fun st => CircuitType.ReadsAs (val := Statement Fq) st stv raw)
    (fun hnv hle h => h.mono hnv hle) (fun _ h => h)
    (Complete.imp habs (fun _ _ h => h)
      (RandomOracle.hashVec_complete Poseidon.fqParams fqParams_size _ _))) fun sq => ?_
  -- the transcript hash's canonical bits: a representative is below the field's order
  have hbound : ToNat.toNat (transcriptHash raw.pk raw.u) < PALLAS_SCALAR_CARD :=
    ZMod.val_lt _
  have hfit : ToNat.toNat (transcriptHash raw.pk raw.u) < 2 ^ 255 :=
    lt_of_lt_of_le hbound (by decide)
  refine Complete.bind (Complete.frame
    (P := fun st => CircuitType.ReadsAs (val := Statement Fq) st stv raw)
    (fun hnv hle h => h.mono hnv hle) (fun _ h => h.2)
    (Complete.imp (fun _ h => h.1) (fun _ _ h => h)
      (unpackFull_complete PALLAS_SCALAR_CARD 255 (by decide) sq
        (transcriptHash raw.pk raw.u) hfit hbound))) fun hbits => ?_
  -- the challenge leg, on the low 128 bits
  have hnL : preChallenge raw.pk raw.u < 2 ^ 128 := Nat.mod_lt _ (by positivity)
  have hlow : ∀ st : ProverState Fq,
      CircuitType.ReadsAs (val := Vector Bool 255) st hbits
        (unpackPure (transcriptHash raw.pk raw.u) 255) →
      CircuitType.ReadsAs (val := Fq) st (packLow 128 (by omega) hbits)
        ((preChallenge raw.pk raw.u : ℕ) : Fq) := by
    rintro st ⟨hsc, hrd⟩
    rw [CircuitType.scoped_vector] at hsc
    rw [CircuitType.reads_vector] at hrd
    refine hk _ _ _ (CVar.Scoped.packLow fun i hi =>
      CircuitType.scoped_boolVar.mp (hsc i hi)) ?_
    rw [packLow_val (n := 255) (k := 128) (by omega)
        (fun i hi => CircuitType.reads_boolVar.mp (hrd i hi)),
      toList_takeVec, Kimchi.natLsbVal_take_eq_mod, natLsbVal_unpackPure hfit]
    rfl
  refine Complete.bind (Complete.frame
    (P := fun st => CircuitType.ReadsAs (val := Statement Fq) st stv raw)
    (fun hnv hle h => h.mono hnv hle) (fun _ h => h.2)
    (Complete.imp (fun st h => ⟨hpkAs st h.2, hlow st h.1⟩) (fun _ _ h => h)
      (EndoMul.vesta_endoMul_complete (nonsingular_toW hpkC) hnL))) fun cpk => ?_
  -- the ladder leg, on the constant generator
  refine Complete.bind (Complete.frame
    (P := fun st => CircuitType.ReadsAs (val := Statement Fq) st stv raw ∧
      OnCurveAs Vesta.curve.toAffine st cpk
        ((Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam
            (preChallenge raw.pk raw.u) : Fp)
          • Point.some raw.pk.point.x raw.pk.point.y (nonsingular_toW hpkC)))
    (fun hnv hle h => ⟨h.1.mono hnv hle, OnCurveAs.mono hnv hle h.2⟩)
    (fun _ h => ⟨h.2, h.1⟩)
    (Complete.imp (fun st h => ⟨hgenAs st, hzAs st h.2⟩) (fun _ _ h => h)
      (vesta_varBaseMul_complete gen_nonsingular hband))) fun zr => ?_
  -- the ladder's bits, locked below the scalar order
  have hzfit : ToNat.toNat raw.z.val < 2 ^ 255 :=
    lt_of_lt_of_le (ZMod.val_lt _) (by decide)
  have hzlock : Kimchi.natLsbVal (unpackPure raw.z.val 255).toList < PALLAS_SCALAR_CARD := by
    rw [natLsbVal_unpackPure hzfit]
    exact ZMod.val_lt _
  have hbitsAs : ∀ st : ProverState Fq,
      (∀ (i : ℕ) (hi : i < 255), CircuitType.ReadsAs (val := Fq) st (zr.lsbBits[i]'hi)
        (bit (unpackPure raw.z.val 255)[i])) →
      CircuitType.ReadsAs (val := Vector Bool 255) st
        (mapVec BoolVar.unchecked zr.lsbBits) (unpackPure raw.z.val 255) := by
    intro st h
    refine ⟨CircuitType.scoped_vector.mpr fun i hi => ?_,
      CircuitType.reads_vector.mpr fun i hi => ?_⟩
    · rw [getElem_mapVec]
      exact CircuitType.scoped_boolVar.mpr (CircuitType.scoped_fvar.mp (h i hi).1)
    · rw [getElem_mapVec]
      exact CircuitType.reads_boolVar.mpr (CircuitType.reads_fvar.mp (h i hi).2)
  refine Complete.bind (Complete.frame
    (P := fun st => CircuitType.ReadsAs (val := Statement Fq) st stv raw ∧
      OnCurveAs Vesta.curve.toAffine st cpk
        ((Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam
            (preChallenge raw.pk raw.u) : Fp)
          • Point.some raw.pk.point.x raw.pk.point.y (nonsingular_toW hpkC)) ∧
      OnCurveAs Vesta.curve.toAffine st zr.g
        (raw.z.toScalarZ • Point.some gen.x gen.y gen_nonsingular))
    (fun hnv hle h => ⟨h.1.mono hnv hle, OnCurveAs.mono hnv hle h.2.1,
      OnCurveAs.mono hnv hle h.2.2⟩)
    (fun _ h => ⟨h.2.1, h.2.2, h.1.2⟩)
    (Complete.imp (fun st h => hbitsAs st h.1.1) (fun _ _ h => h)
      (assertBitsBelow_complete PALLAS_SCALAR_CARD (by decide)
        (mapVec BoolVar.unchecked zr.lsbBits) (unpackPure raw.z.val 255) hzlock)))
    fun _ => ?_
  -- the wire's check, in the ladder's currency: the sum IS the ladder's point
  have hne : ∀ (st : ProverState Fq) (p : AffinePoint (FVar Fq))
      (Q : Vesta.curve.toAffine.Point), OnCurveAs Vesta.curve.toAffine st p Q → Q ≠ 0 := by
    rintro st p Q ⟨-, hns, rfl⟩
    exact Point.some_ne_zero hns
  have hsum : Point.some raw.u.point.x raw.u.point.y (nonsingular_toW huC)
      + (Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam
          (preChallenge raw.pk raw.u) : Fp)
        • Point.some raw.pk.point.x raw.pk.point.y (nonsingular_toW hpkC)
      = raw.z.toScalarZ • Point.some gen.x gen.y gen_nonsingular := by
    rw [show (raw.z.toScalarZ : ℤ) • Point.some gen.x gen.y gen_nonsingular
      = ((raw.z.toScalarZ : ℤ) : Fp) • Point.some gen.x gen.y gen_nonsingular from
        (Int.cast_smul_eq_zsmul ..).symm]
    exact hcheck.symm
  have hUU : Point.some raw.u.point.x raw.u.point.y (nonsingular_toW huC)
      + Point.some raw.u.point.x raw.u.point.y (nonsingular_toW huC) ≠ 0 :=
    HasCurve.two_torsion_free HasCurve.vesta _ (Point.some_ne_zero _)
  -- the complete addition
  refine Complete.bind (Complete.frame
    (P := fun st => CircuitType.ReadsAs (val := Statement Fq) st stv raw ∧
      OnCurveAs Vesta.curve.toAffine st zr.g
        (raw.z.toScalarZ • Point.some gen.x gen.y gen_nonsingular))
    (fun hnv hle h => ⟨h.1.mono hnv hle, OnCurveAs.mono hnv hle h.2⟩)
    (fun _ h => ⟨h.2.1, h.2.2.2⟩)
    (Complete.imp (fun st h => ⟨huAs st h.2.1, h.2.2.1, hUU,
        fun _ h0 => hne st zr.g _ h.2.2.2 (hsum ▸ h0)⟩) (fun _ _ h => h)
      (addFast_complete Finiteness.checkFinite Vesta.curve.toAffine ⟨rfl, rfl, rfl, rfl⟩
        (by decide) stv.u.point cpk _ _))) fun rhs => ?_
  -- the ladder's point is finite, so both operands' cells read as its coordinates
  have hZne : raw.z.toScalarZ • Point.some gen.x gen.y gen_nonsingular ≠ 0 := by
    haveI : Fact (Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0
        ∧ Vesta.curve.toAffine.a₃ = 0) := ⟨rfl, rfl, rfl⟩
    haveI : Fact (Nat.Prime Vesta.curve.toAffine.order) := ⟨HasCurve.vesta.prime⟩
    intro h0
    refine hz0 ?_
    have hdvd := (Kimchi.Gate.VarBaseMul.zsmul_eq_zero_iff_order_dvd Vesta.curve.toAffine
      (Point.some_ne_zero gen_nonsingular) _).mp h0
    rw [Pasta.vesta_card] at hdvd
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  obtain ⟨zx, zy, hzns, hZeq⟩ :
      ∃ (zx : Fq) (zy : Fq) (h : Vesta.curve.toAffine.Nonsingular zx zy),
        raw.z.toScalarZ • Point.some gen.x gen.y gen_nonsingular = Point.some zx zy h := by
    rcases hZG : raw.z.toScalarZ • Point.some gen.x gen.y gen_nonsingular with _ | ⟨x, y, h⟩
    · exact absurd hZG hZne
    · exact ⟨x, y, h, rfl⟩
  have hcx : ∀ (st : ProverState Fq) (p : AffinePoint (FVar Fq)),
      OnCurveAs Vesta.curve.toAffine st p
        (raw.z.toScalarZ • Point.some gen.x gen.y gen_nonsingular) →
      CircuitType.ReadsAs (val := Fq) st p.x zx ∧
        CircuitType.ReadsAs (val := Fq) st p.y zy := by
    rintro st p ⟨hsc, hip⟩
    obtain ⟨hx, hy⟩ := Kimchi.Gate.AddComplete.IsPoint.coords_eq hip ⟨hzns, hZeq⟩
    exact ⟨hk st p.x zx (scoped_affinePoint.mp hsc).1 hx,
      hk st p.y zy (scoped_affinePoint.mp hsc).2 hy⟩
  refine Complete.bind (Complete.frame
    (P := fun st => CircuitType.ReadsAs (val := Statement Fq) st stv raw ∧
      OnCurveAs Vesta.curve.toAffine st zr.g
        (raw.z.toScalarZ • Point.some gen.x gen.y gen_nonsingular) ∧
      OnCurveAs Vesta.curve.toAffine st rhs.p
        (raw.z.toScalarZ • Point.some gen.x gen.y gen_nonsingular))
    (fun hnv hle h => ⟨h.1.mono hnv hle, OnCurveAs.mono hnv hle h.2.1,
      OnCurveAs.mono hnv hle h.2.2⟩)
    (fun st h => ⟨h.2.1, h.2.2,
      hsum ▸ h.1.2.2 fun h0 => hne st zr.g _ h.2.2 (hsum ▸ h0)⟩)
    (Complete.imp (fun st h => ⟨(hcx st zr.g h.2.2).1,
        (hcx st rhs.p (hsum ▸ h.1.2.2 fun h0 => hne st zr.g _ h.2.2 (hsum ▸ h0))).1⟩)
      (fun _ _ h => h) (assertEqual_complete zr.g.x rhs.p.x zx))) fun _ => ?_
  refine Complete.bind (Complete.frame
    (P := fun st => CircuitType.ReadsAs (val := Statement Fq) st stv raw)
    (fun hnv hle h => h.mono hnv hle) (fun _ h => h.2.1)
    (Complete.imp (fun st h => ⟨(hcx st zr.g h.2.2.1).2, (hcx st rhs.p h.2.2.2).2⟩)
      (fun _ _ h => h) (assertEqual_complete zr.g.y rhs.p.y zy))) fun _ => ?_
  -- the response's decode is nonzero
  have hz0' : raw.z.val ≠ Type1.zeroCarrier :=
    fun h => hz0 ((Type1.toScalar_eq_zero_iff _).mpr h)
  exact Complete.imp (fun st h => ⟨hzAs st h.2,
      hk st (CVar.const Type1.zeroCarrier) _ (CVar.scoped_const _ _) rfl⟩)
    (fun _ _ _ => trivial)
    (assertNotEqual_complete stv.z.val (CVar.const Type1.zeroCarrier) raw.z.val
      Type1.zeroCarrier hz0')

end Schnorr
