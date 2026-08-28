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
  rw [show CircuitType.Reads V stv raw ↔ _ from CircuitType.reads_ofEquiv _ _,
    CircuitType.reads_prod, CircuitType.reads_prod] at hread
  obtain ⟨hpkR, huR, hzR⟩ := hread
  rw [CircuitType.reads_ofEquiv, CircuitType.reads_fvar] at hzR
  rw [CircuitType.reads_ofEquiv, reads_affinePoint] at hpkR huR
  simp only [Statement.equivProd_apply, CurvePoint.equivPoint_apply] at hpkR huR
  refine ⟨fun h0 => hzne ?_, fun hband => ?_⟩
  · rw [show (CVar.const Type1.zeroCarrier).val V = Type1.zeroCarrier from rfl,
      ← (Type1.toScalar_eq_zero_iff _).mp h0]
    exact hzR
  · -- the read points, as Mathlib points
    set pkR : VestaPoint Fq := ⟨⟨raw.pk.point.x, raw.pk.point.y⟩⟩ with hpkRdef
    set uR : VestaPoint Fq := ⟨⟨raw.u.point.x, raw.u.point.y⟩⟩ with huRdef
    have hpkNS : Vesta.curve.toAffine.Nonsingular raw.pk.point.x raw.pk.point.y :=
      nonsingular_toW hpkC
    have huNS : Vesta.curve.toAffine.Nonsingular raw.u.point.x raw.u.point.y :=
      nonsingular_toW huC
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
      ‹∀ hT : Vesta.curve.toAffine.Nonsingular _ _, _›
    -- the ladder leg, at the carrier's decode
    have hzr := vesta_varBaseMul_read (Z := raw.z) hzR hband
      ‹∀ T : HasCurve.vesta.W.Point, _›
    rw [verify_iff]
    refine ⟨hpkC, huC, fun h0 => hzne ?_, ?_⟩
    · rw [show (CVar.const Type1.zeroCarrier).val V = Type1.zeroCarrier from rfl,
        ← (Type1.toScalar_eq_zero_iff _).mp h0]
      exact hzR
    -- the ladder's point, at the constant generator
    have hgenAt : OnCurveAt Vesta.curve.toAffine V
        (⟨CVar.const gen.x, CVar.const gen.y⟩ : AffinePoint (FVar Fq))
        (WeierstrassCurve.Affine.Point.some gen.x gen.y gen_nonsingular) :=
      ⟨gen_nonsingular, rfl⟩
    have hzact := hzr _ hgenAt ‹∀ bs : Vector Bool 255, _ → _›
    obtain ⟨hfinC, hseq⟩ := hcpk (hpkR.1 ▸ hpkR.2 ▸ hpkNS)
    -- `u` is finite: an odd prime order has no 2-torsion
    have huy0 : raw.u.point.y ≠ 0 :=
      Kimchi.Gate.VarBaseMul.y_ne_zero_of_odd_order Vesta.curve.toAffine
        (by rw [Pasta.vesta_card]; decide) huNS
    obtain ⟨hinf0, hsum⟩ :=
      ‹CVar.val _ V = 0 ∧
        ∀ P Q : Vesta.curve.toAffine.Point, _ → _ → _ → _ ∨ _›
    have huNS' : Vesta.curve.toAffine.Nonsingular (stv.u.point.x.val V) (stv.u.point.y.val V) := by
      rw [huR.1, huR.2]; exact huNS
    have huAt : OnCurveAt Vesta.curve.toAffine V stv.u.point
        (WeierstrassCurve.Affine.Point.some _ _ huNS') := ⟨huNS', rfl⟩
    have hPP : WeierstrassCurve.Affine.Point.some _ _ huNS'
        + WeierstrassCurve.Affine.Point.some _ _ huNS' ≠ 0 :=
      HasCurve.two_torsion_free HasCurve.vesta _
        (WeierstrassCurve.Affine.Point.some_ne_zero huNS')
    rcases hsum _ (WeierstrassCurve.Affine.Point.some _ _ hfinC) huAt ⟨hfinC, rfl⟩ hPP with
      ⟨hinf1, -⟩ | ⟨-, hfin⟩
    · exact absurd hinf1 (by rw [hinf0]; decide)
    · obtain ⟨hzg, hzeq⟩ := hzact
      obtain ⟨hrp, hreq⟩ := hfin
      have hglue : WeierstrassCurve.Affine.Point.some _ _ hzg
          = WeierstrassCurve.Affine.Point.some _ _ hrp :=
        Kimchi.Gate.EndoMul.some_congr Vesta.curve.toAffine hzg hrp
          ‹CVar.val _ V = CVar.val _ V› ‹CVar.val _ V = CVar.val _ V›
      have hpkP : WeierstrassCurve.Affine.Point.some (stv.pk.point.x.val V)
            (stv.pk.point.y.val V) (hpkR.1 ▸ hpkR.2 ▸ hpkNS)
          = WeierstrassCurve.Affine.Point.some raw.pk.point.x raw.pk.point.y hpkNS :=
        Kimchi.Gate.EndoMul.some_congr Vesta.curve.toAffine _ _ hpkR.1 hpkR.2
      have huP : WeierstrassCurve.Affine.Point.some _ _ huNS'
          = WeierstrassCurve.Affine.Point.some raw.u.point.x raw.u.point.y huNS :=
        Kimchi.Gate.EndoMul.some_congr Vesta.curve.toAffine _ _ huR.1 huR.2
      show ((raw.z.toScalarZ : ℤ) : Fp) • _ = _
      rw [Int.cast_smul_eq_zsmul, hzeq, hglue, ← hreq, hseq, hpkP, huP]
      rfl

end Schnorr
