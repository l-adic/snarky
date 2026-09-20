import Pickles.IncrementallyVerify
import Pickles.FinalizeOtherProof
import Pickles.PublicInputCommit
import Pickles.Statement

/-!
# `verify` (the step side)

The port of OCaml `Step_verifier.verify` (`step_verifier.ml:1340–1413`), the `verify` call of
PS `Pickles.Step.VerifyOne.verifyOne`.

`verify` is the group half with its public input fixed: the wrap statement is packed into the
`x_hat` leaves (`Spec.pack`, PS `packStatement`), `incrementally_verify_proof` runs with the
claims of the unfinalized proof (`xi`, `combined_inner_product`, `b`, `plonk`), and its two
outputs other than the success bit are asserted against that proof: the digest equals the
claimed `sponge_digest_before_evaluations`, and each returned round prechallenge equals the
claimed one — except in the base case, where the claim is compared with itself.

The two circuits that touch one proof, the group half here and the scalar half
(`finalize_other_proof`) one circuit later over the other field, compose to the wire
verifier in `Pickles.TwoHalves`; `Step_main.verify_one`, which runs them on two different
proofs in one circuit, is not ported.

## Main definitions

* `WrapStatement.packed`, `packLeaves`: the wrap statement as the `x_hat` leaf list;
* `verifyProof`: `Step_verifier.verify`.

## Main results

* `VerifyReads` / `verifyProof_reads`: on any group side and `x_hat` side, `verify` reads as
  the group half's `IvpReads` at the public input `pubOf (packLeaves statement)`, the wire's
  public input being the packed statement, with the claimed digest equal to the wire's digest
  element and, off the base case, the claimed round prechallenges equal to the returned ones
  pair by pair (hence, through `IvpReads`, the wire's). The `x_hat`
  chunks read through `xHatKnown_reads_publicCommitment` at the tables' binding
  (`XhatTable.Bound`), the group half through `incrementallyVerifyProof_reads` at `IvpHyps`,
  and the assertion loop by its invariant. `verifyProof_step_reads` is the step side.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass

/-! ## Packing the wrap statement -/

section Pack

variable {F : Type} [Field F] [DecidableEq F] {nc k : ℕ}

/-- `Branch_data.pack`: `4·domain_log2 + m₀ + 2·m₁`, a 10-bit value (PS `packStatement`). A
missing mask bit reads as `0`. -/
def BranchData.packed (bd : BranchData (FVar F) (BoolVar F)) : FVar F :=
  let bit (i : ℕ) : CVar F := match bd.proofsVerifiedMask.toList[i]? with
    | some b => (↑b : CVar F)
    | none => .const 0
  CVar.add_ (CVar.scale_ 4 bd.domainLog2) (CVar.add_ (bit 0) (CVar.scale_ 2 (bit 1)))

/-- A packed public-input scalar with its ladder width: a full field element, a 128-bit
value, or the 10-bit packed branch data. -/
inductive PackedScalar (F : Type) [Field F] where
  /-- A 255-bit field element. -/
  | full (s : FVar F)
  /-- A 128-bit value. -/
  | b128 (s : FVar F)
  /-- A 10-bit value. -/
  | b10 (s : FVar F)
  /-- A boolean cell: a conditional add of its base. -/
  | bit (b : BoolVar F)

/-- `Spec.pack (Wrap.Statement.In_circuit.to_data statement)` (PS `packStatement`), in walk
order: the five shifted scalars `cip, b, ζ^{2^k}, ζⁿ, perm` (full), `β, γ` (128), `α, ζ, ξ`
(128), the three digests `sponge_digest, msg_wrap, msg_step` (full), the round challenges
(128), the packed branch data (10). The shifted scalars are the step proof's `Fp` values in
their `Type1` representative, a full field element each. -/
def WrapStatement.packed (st : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F))) :
    List (PackedScalar F) :=
  let dv := st.proofState.deferredValues
  let pl := dv.plonk
  [.full dv.combinedInnerProduct.val, .full dv.b.val, .full pl.zetaToSrsLength.val,
   .full pl.zetaToDomainSize.val, .full pl.perm.val,
   .b128 pl.beta.val, .b128 pl.gamma.val,
   .b128 pl.alpha.val, .b128 pl.zeta.val, .b128 dv.xi.val,
   .full st.proofState.spongeDigestBeforeEvaluations,
   .full st.proofState.messagesForNextWrapProof, .full st.messagesForNextStepProof]
  ++ dv.bulletproofChallenges.toList.map (fun c => .b128 c.val)
  ++ [.b10 dv.branchData.packed]

/-- A packed scalar that is not a boolean cell. -/
def PackedScalar.IsScalar : PackedScalar F → Prop
  | .bit _ => False
  | _ => True

/-- A packed wrap statement has no boolean cell: the branch data is one 10-bit scalar. -/
theorem WrapStatement.packed_isScalar
    (st : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F))) :
    ∀ k ∈ st.packed, k.IsScalar := by
  simp only [WrapStatement.packed, PackedScalar.IsScalar, List.cons_append, List.nil_append,
    List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false, forall_eq_or_imp,
    true_and]
  rintro a (⟨c, -, rfl⟩ | rfl) <;> trivial

/-- The `x_hat` leaves of a packed scalar list: scalar `i` with Lagrange base `i` and its shift
correction from the table (`lagrange_with_correction`); a boolean cell adds its base under
the bit, with no correction. -/
def packLeavesOf (ks : List (PackedScalar F)) (tab : XhatTable F nc) : List (Leaf F nc) :=
  List.zipWith (fun k bc => match k with
    | .full s => Leaf.full s bc.1 bc.2
    | .b128 s => Leaf.b128 s bc.1 bc.2
    | .b10 s => Leaf.b10 s bc.1 bc.2
    | .bit b => Leaf.condAdd b bc.1) ks (tab.bases.zip tab.corrs)

/-- The `x_hat` leaves of a wrap statement: `packLeavesOf` its packing. -/
def packLeaves (st : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F)))
    (tab : XhatTable F nc) : List (Leaf F nc) :=
  packLeavesOf st.packed tab

/-- `Spec.pack` of a step statement (PS `PackedStepPublicInput`), in walk order: per slot, the
five split claims `cip, b, ζ^{2^k}, ζⁿ, perm` as a full half and a boolean parity, the digest
full, `β, γ, α, ζ, ξ` and the `k` round challenges 128-bit, `should_finalize` boolean; then
`messages_for_next_step_proof` and the slots' `messages_for_next_wrap_proof` digests, full. -/
def StepStatement.packed {n : ℕ}
    (st : StepStatement k n (FVar F) (BoolVar F) (Type2 (SplitField (FVar F) (BoolVar F)))) :
    List (PackedScalar F) :=
  let slot (u : UnfinalizedProof k (FVar F) (BoolVar F) (Type2 (SplitField (FVar F) (BoolVar F)))) :
      List (PackedScalar F) :=
    let dv := u.deferredValues
    let pl := dv.plonk
    let split (x : Type2 (SplitField (FVar F) (BoolVar F))) : List (PackedScalar F) :=
      [.full x.val.sDiv2, .bit x.val.sOdd]
    split dv.combinedInnerProduct ++ split dv.b ++ split pl.zetaToSrsLength
      ++ split pl.zetaToDomainSize ++ split pl.perm
      ++ [.full u.spongeDigestBeforeEvaluations,
          .b128 pl.beta.val, .b128 pl.gamma.val, .b128 pl.alpha.val, .b128 pl.zeta.val,
          .b128 dv.xi.val]
      ++ dv.bulletproofChallenges.toList.map (fun c => .b128 c.val)
      ++ [.bit u.shouldFinalize]
  st.proofState.unfinalizedProofs.toList.flatMap slot
    ++ [.full st.proofState.messagesForNextStepProof]
    ++ st.messagesForNextWrapProof.toList.map .full

/-- The group half's input with its claims taken from an unfinalized proof
(`step_verifier.ml:1366–1385`): `xi`, `combined_inner_product`, `b` and the plonk claims
of `unfinalized.deferred_values`; the key, proof and `sg_old` cells as given. -/
def IvpInput.withClaims {sf : Type} (inp : IvpInput k (FVar F) (BoolVar F) sf)
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf) :
    IvpInput k (FVar F) (BoolVar F) sf :=
  let dv := u.deferredValues
  { inp with
    plonk := ⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩,
      dv.plonk.perm, dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩
    xi := dv.xi
    deferred := ⟨dv.combinedInnerProduct, dv.b⟩ }

end Pack

/-! ## The group half's input, from its records -/

section Records

open Kimchi

/-- The key's cells as the group half's key records: `σ₆`, the six selectors, the 15
coefficients, `σ₀…σ₅`. -/
def keyRecords {F : Type} (comms : List (List (AffinePoint (FVar F)))) :
    List (AffinePoint (FVar F)) × List (List (AffinePoint (FVar F))) ×
      List (List (AffinePoint (FVar F))) × List (List (AffinePoint (FVar F))) :=
  (comms.getD 6 [], comms.drop 22, (comms.drop 7).take 15, comms.take 6)

/-- A one-chunk proof as the group half reads it: the 15 witness commitments, `z_comm`, the 7
quotient chunks, the opening at `k` rounds. `IvpInput` holds these as chunk lists; the
product is their sized form, so it is a `CircuitType` by its factors. -/
abbrev IvpProof (k : ℕ) (f sf : Type) : Type :=
  Vector (AffinePoint f) wCols × AffinePoint f × Vector (AffinePoint f) 7 ×
    BulletproofOpening k f sf

/-- The group half's input from a proof's deferred values (its claims), the `sg_old` points
under their keep bits, a key's commitments and the proof. -/
def ivpInputOf {F sf : Type} {k : ℕ} (dv : DeferredValues k (FVar F) sf)
    (sgOld : List (Option (BoolVar F) × AffinePoint (FVar F)))
    (comms : List (List (AffinePoint (FVar F)))) (pr : IvpProof k (FVar F) sf) :
    IvpInput k (FVar F) (BoolVar F) sf :=
  let (sigmaLast, indexComms, coefficientsComm, sigmaComm) := keyRecords comms
  let (wComm, zComm, tComm, opening) := pr
  { plonk := ⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩, dv.plonk.perm,
      dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩
    xi := dv.xi
    deferred := ⟨dv.combinedInnerProduct, dv.b⟩
    sgOld, sigmaLast, indexComms, coefficientsComm, sigmaComm
    wComm := wComm.toList.map ([·])
    zComm := [zComm]
    tComm := tComm.toList
    opening }

/-- The circuit's key cells read as the key. The cells are in the index digest's order —
`σ₀…σ₆`, the 15 coefficient commitments, the six selectors, as `keyRecords` splits them — and
the sponge after the index digest squeezes to the key's digest. -/
structure VkReads {C : KimchiCurve} {nc : ℕ} (cvk : KimchiVK C nc) (V : Valuation C.BaseField)
    (spongeAfterIndex : SpongeVar C.BaseField)
    (keyCells : List (List (AffinePoint (FVar C.BaseField)))) : Prop where
  /-- The sponge after the index digest squeezes to the key's digest. -/
  idx : ∃ st : Poseidon.State C.BaseField, SpongeVar.ReadsAt V spongeAfterIndex st ∧
    (Poseidon.squeeze C.sponge.params st).1 = cvk.digest
  /-- The six selector commitments. -/
  index : ColumnsRead C V (keyCells.drop 22)
    [cvk.genericComm, cvk.poseidonComm, cvk.completeAddComm, cvk.mulComm, cvk.emulComm,
     cvk.endomulScalarComm]
  /-- The coefficient commitments. -/
  coefficients : ColumnsRead C V ((keyCells.drop 7).take 15) cvk.coefficientsComm.toList
  /-- The permutation commitments `σ₀…σ₅`. -/
  sigma : ColumnsRead C V (keyCells.take 6) (cvk.sigmaComm.take sigmaRows).toList
  /-- The last permutation commitment `σ₆`. -/
  sigmaLast : CommReads C V (keyCells.getD 6 []) (cvk.sigmaComm[6]).toList

end Records

/-! ## The `x_hat` table of a key

The Lagrange bases and shift corrections are data of the verifier key, so the table is
computed from it as constant cells rather than taken as an argument and then assumed to be
the key's. It depends on the statement's packing only through the leaf kinds: each kind has
its own shift. -/

section OfKey

open WeierstrassCurve.Affine

variable {C : KimchiCurve} {nc : ℕ} {V : Valuation C.BaseField}

/-- A wire point as a constant cell. -/
def constPt (P : C.Point) : AffinePoint (FVar C.BaseField) := ⟨.const P.x, .const P.y⟩

theorem onCurveAt_constPt (P : C.Point) (hP : P ≠ 0) :
    OnCurveAt C.E.toAffine V (constPt P) (SWPoint.equivPoint C.E P) :=
  ⟨nonsingular_toW (SWPoint.onCurve_of_ne_zero hP),
    SWPoint.equivPoint_eq_some P (SWPoint.onCurve_of_ne_zero hP)⟩

/-- The shift correction `-(2^L)·P`, computed through the curve's verified fast
multi-scalar multiplication. The group's own `•` is a recursion as deep as its scalar, so a
table built with it states the right point and can never be run; this one a driver runs. -/
def negShift (C : KimchiCurve) (L : ℕ) (P : C.Point) : C.Point :=
  -(C.fastMsm (n := 1) (fun _ => P) (fun _ => ((2 ^ L : ℕ) : ZMod C.scalar)))

theorem negShift_eq (L : ℕ) (P : C.Point) : negShift C L P = (-(2 ^ L : ℤ)) • P := by
  have hcard : C.scalar • P = 0 := by
    have h := card_nsmul_eq_zero' (G := C.Point) (x := P)
    rwa [C.card] at h
  have hmod : (2 ^ L % C.scalar) • P = (2 ^ L) • P := by
    conv_rhs => rw [← Nat.mod_add_div (2 ^ L) C.scalar, add_nsmul, mul_nsmul, hcard,
      nsmul_zero, _root_.add_zero]
  rw [negShift, C.fastMsm_spec, Fin.sum_univ_one, ZMod.val_natCast, hmod, neg_smul]
  congr 1
  exact_mod_cast (natCast_zsmul P (2 ^ L)).symm

/-- A leaf over constants: the Lagrange points as its base, their honest shifts as its
correction. -/
def constLeaf (k : PackedScalar C.BaseField) (Ps : Vector C.Point nc) : Leaf C.BaseField nc :=
  match k with
  | .full x => .full x (Ps.map constPt) (Ps.map fun P => constPt (negShift C 255 P))
  | .b128 x => .b128 x (Ps.map constPt) (Ps.map fun P => constPt (negShift C 130 P))
  | .b10 x => .b10 x (Ps.map constPt) (Ps.map fun P => constPt (negShift C 10 P))
  | .bit b => .condAdd b (Ps.map constPt)

theorem leafBaseAt_constLeaf (ci : Fin nc) (k : PackedScalar C.BaseField) (Ps : Vector C.Point nc) :
    leafBaseAt ci (constLeaf k Ps) = constPt Ps[ci] := by
  cases k <;> simp [constLeaf, leafBaseAt]

/-- The point group has odd prime order, so a nonzero point shifted by a power of two stays
nonzero: a constant correction cell is a finite point whenever its base is. -/
theorem two_pow_zsmul_ne_zero (s : PastaShape C) (P : C.Point) (hP : P ≠ 0) (L : ℕ) :
    (-(2 ^ L : ℤ)) • P ≠ 0 := by
  haveI : Fact C.scalar.Prime := inferInstance
  have hcard : Nat.card C.Point = C.scalar := C.card
  intro h0
  have hdvd : (addOrderOf P : ℤ) ∣ -(2 ^ L : ℤ) := (addOrderOf_dvd_iff_zsmul_eq_zero).2 h0
  have hord : addOrderOf P = C.scalar := by
    have h1 : addOrderOf P ∣ C.scalar := hcard ▸ addOrderOf_dvd_natCard P
    rcases (Nat.dvd_prime (Fact.out : C.scalar.Prime)).1 h1 with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) hP
    · exact h
  rw [hord, Int.dvd_neg] at hdvd
  have h2 : C.scalar ∣ 2 ^ L := by exact_mod_cast hdvd
  have h3 : C.scalar ∣ 2 := (Fact.out : C.scalar.Prime).dvd_of_dvd_pow h2
  have h4 : C.scalar ≤ 2 := Nat.le_of_dvd (by norm_num) h3
  have := s.scalar_lo
  omega

theorem getElem_map_fin {α β : Type} {n : ℕ} (f : α → β) (Ps : Vector α n) (ci : Fin n) :
    (Ps.map f)[ci] = f Ps[ci] := by
  simp [Fin.getElem_fin]

/-- The correction point a constant leaf's correction cell reads as. -/
noncomputable def constCp (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) : s.d.W.Point :=
  match k with
  | .full _ => (-(2 ^ 255 : ℤ)) • SWPoint.equivPoint C.E Ps[ci]
  | .b128 _ => (-(2 ^ 130 : ℤ)) • SWPoint.equivPoint C.E Ps[ci]
  | .b10 _ => (-(2 ^ 10 : ℤ)) • SWPoint.equivPoint C.E Ps[ci]
  | .bit _ => 0

theorem onCurveAt_shift (s : PastaShape C) (P : C.Point) (hP : P ≠ 0) (L : ℕ) :
    OnCurveAt s.d.W V (constPt (negShift C L P))
      ((-(2 ^ L : ℤ)) • SWPoint.equivPoint C.E P) := by
  rw [← map_zsmul, ← negShift_eq]
  exact onCurveAt_constPt _ (negShift_eq L P ▸ two_pow_zsmul_ne_zero s P hP L)

theorem leafPre_const (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) (hP : Ps[ci] ≠ 0)
    (hbit : ∀ b, k = .bit b → ∃ bb : Bool, (↑b : CVar C.BaseField).val V = bit bb) :
    LeafPre (d := s.d) ci V (constLeaf k Ps) (SWPoint.equivPoint C.E Ps[ci]) := by
  cases k with
  | bit b => exact ⟨by simpa [constLeaf] using onCurveAt_constPt (V := V) Ps[ci] hP, hbit b rfl⟩
  | _ => simpa [constLeaf, LeafPre] using onCurveAt_constPt (V := V) Ps[ci] hP

theorem corrPre_const (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) (hP : Ps[ci] ≠ 0) :
    CorrPre (d := s.d) ci V (constLeaf k Ps) (constCp s ci k Ps) := by
  cases k with
  | bit b => rfl
  | full x =>
    simp only [constLeaf, CorrPre, constCp]
    rw [getElem_map_fin]
    exact onCurveAt_shift (V := V) s _ hP 255
  | b128 x =>
    simp only [constLeaf, CorrPre, constCp]
    rw [getElem_map_fin]
    exact onCurveAt_shift (V := V) s _ hP 130
  | b10 x =>
    simp only [constLeaf, CorrPre, constCp]
    rw [getElem_map_fin]
    exact onCurveAt_shift (V := V) s _ hP 10

theorem corrHonest_const (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) (hP : Ps[ci] ≠ 0) :
    CorrHonest s.d ci V (constLeaf k Ps) := by
  have key : ∀ (L : ℕ) (T : s.d.W.Point),
      OnCurveAt s.d.W V (constPt Ps[ci]) T →
      OnCurveAt s.d.W V (constPt (negShift C L Ps[ci])) ((-(2 ^ L : ℤ)) • T) := by
    intro L T hT
    have hT' : T = SWPoint.equivPoint C.E Ps[ci] :=
      OnCurveAt.eq hT (onCurveAt_constPt (V := V) Ps[ci] hP) rfl rfl
    subst hT'
    exact onCurveAt_shift s _ hP L
  cases k with
  | bit b => trivial
  | full x =>
    simp only [constLeaf, CorrHonest]
    rw [getElem_map_fin, getElem_map_fin]
    exact key 255
  | b128 x =>
    simp only [constLeaf, CorrHonest]
    rw [getElem_map_fin, getElem_map_fin]
    exact key 130
  | b10 x =>
    simp only [constLeaf, CorrHonest]
    rw [getElem_map_fin, getElem_map_fin]
    exact key 10

theorem forall₂_zipWith {α β γ δ : Type} (R : γ → δ → Prop) (f : α → β → γ) (g : α → β → δ) :
    ∀ (ks : List α) (lb : List β), (∀ p ∈ ks.zip lb, R (f p.1 p.2) (g p.1 p.2)) →
      List.Forall₂ R (List.zipWith f ks lb) (List.zipWith g ks lb)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | k :: ks, P :: lb, h => by
      simp only [List.zipWith_cons_cons]
      exact List.Forall₂.cons (h (k, P) (by simp))
        (forall₂_zipWith R f g ks lb fun p hp => h p (by simp [hp]))

/-- **The table computed from the key is bound to the key.** Constant cells — the Lagrange
points as bases, their honest shifts as corrections, the SRS blinding base — satisfy
`XhatBinding` given only what is not table bookkeeping: the blinding base and the Lagrange
points are finite (at the `(0, 0)` sentinel no cell reads as the point, so this is necessary
too), the boolean leaves are boolean — which `xHat_reads_publicCommitment` supplies from the
gadget's own bit pre-pass — and `offBand`. -/
theorem xhatBinding_const (s : PastaShape C) (ci : Fin nc) (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (ks : List (PackedScalar C.BaseField))
    (hh : σ.h ≠ 0)
    (hL : ∀ Ps ∈ cvk.lagrangeBasis.toList, Ps[ci] ≠ 0)

    (hbits : ∀ leaf ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList, leaf.bitBoolean V)
    (hoff : ∀ leaf ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList,
      Leaf.offBand C.scalar V leaf) :
    XhatBinding s ci V σ cvk (constPt σ.h)
      (List.zipWith constLeaf ks cvk.lagrangeBasis.toList)
      (List.zipWith (fun _ Ps => SWPoint.equivPoint C.E Ps[ci]) ks cvk.lagrangeBasis.toList)
      (List.zipWith (constCp s ci) ks cvk.lagrangeBasis.toList) where
  blinding := onCurveAt_constPt σ.h hh
  pre := forall₂_zipWith _ _ _ _ _ fun p hp =>
    leafPre_const s ci p.1 p.2 (hL _ (List.of_mem_zip hp).2) fun b hb => by
      have hmem : constLeaf p.1 p.2 ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList := by
        rw [← List.map_uncurry_zip_eq_zipWith]
        exact List.mem_map.2 ⟨p, hp, rfl⟩
      have := hbits _ hmem
      rw [hb] at this
      exact this
  corr := forall₂_zipWith _ _ _ _ _ fun p hp =>
    corrPre_const s ci p.1 p.2 (hL _ (List.of_mem_zip hp).2)
  hon := by
    intro leaf hl
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hl
    rw [List.getElem_zipWith]
    exact corrHonest_const s ci _ _ (hL _ (List.getElem_mem _))
  offBand := hoff
  hsize := by simp [List.length_zipWith]
  bases := by
    intro i hi
    rw [List.getElem_zipWith, leafBaseAt_constLeaf]
    have h := onCurveAt_constPt (V := V) _ (hL _ (List.getElem_mem
      (l := cvk.lagrangeBasis.toList) (n := i) (by
        simp only [List.length_zipWith, Array.length_toList] at hi; simp; omega)))
    simpa using h

/-- The ladder width of a packed scalar's kind; a boolean leaf has no correction. -/
def shiftBits : PackedScalar C.BaseField → Option ℕ
  | .full _ => some 255
  | .b128 _ => some 130
  | .b10 _ => some 10
  | .bit _ => none

/-- The `x_hat` table computed from the key's Lagrange points, at a statement's packing. A
boolean leaf's correction slot is never read (`packLeavesOf` drops it); it holds the base. -/
def XhatTable.ofKey (ks : List (PackedScalar C.BaseField)) (lb : List (Vector C.Point nc)) :
    XhatTable C.BaseField nc where
  bases := lb.map (·.map constPt)
  corrs := List.zipWith (fun k Ps => Ps.map fun P =>
    constPt (match shiftBits k with | some L => negShift C L P | none => P)) ks lb
  corrHead := Vector.replicate nc (constPt 0)
  corrSum := Vector.replicate nc (constPt 0)

/-- The library's `packLeavesOf` at that table is the constant leaves. -/
theorem packLeavesOf_ofKey : ∀ (ks : List (PackedScalar C.BaseField))
    (lb : List (Vector C.Point nc)),
    packLeavesOf ks (XhatTable.ofKey ks lb) = List.zipWith constLeaf ks lb
  | [], _ => by simp [packLeavesOf]
  | _ :: _, [] => by simp [packLeavesOf, XhatTable.ofKey]
  | k :: ks, Ps :: lb => by
      have ih := packLeavesOf_ofKey ks lb
      simp only [packLeavesOf, XhatTable.ofKey, List.map_cons, List.zipWith_cons_cons,
        List.zip_cons_cons] at ih ⊢
      refine congrArg₂ _ ?_ ih
      cases k <;> simp [constLeaf, shiftBits]

/-! ### The known-domain fold's table

`publicInputCommitKnown` takes the corrections' sum as one constant, where
`publicInputCommitFull` adds each leaf's correction. The table below carries that sum; the cell
reads as a point only when the sum is a finite point, which no invariant of the key gives: it
is one fixed relation among the Lagrange points. -/

/-- The correction point of a packed scalar at a Lagrange point: its honest shift `-(2^L)·P`,
none for a boolean cell. -/
def corrPt (k : PackedScalar C.BaseField) (P : C.Point) : C.Point :=
  match shiftBits k with
  | some L => negShift C L P
  | none => 0

/-- The constant correction sum of the known-domain fold, at chunk `ci`. -/
def corrSumPt (ks : List (PackedScalar C.BaseField)) (lb : List (Vector C.Point nc))
    (ci : Fin nc) : C.Point :=
  (List.zipWith (fun k Ps => corrPt k Ps[ci]) ks lb).sum

/-- The `x_hat` table of the known-domain fold, computed from the key's Lagrange points: the
bases and corrections of `XhatTable.ofKey`, the fold's seed the first correction, its constant
the correction sum. -/
def XhatTable.ofKeyKnown (ks : List (PackedScalar C.BaseField))
    (lb : List (Vector C.Point nc)) : XhatTable C.BaseField nc :=
  { XhatTable.ofKey ks lb with
    corrHead := Vector.ofFn fun ci => constPt
      (match ks, lb with
       | k :: _, Ps :: _ => corrPt k Ps[ci]
       | _, _ => 0)
    corrSum := Vector.ofFn fun ci => constPt (corrSumPt ks lb ci) }

/-- The library's `packLeavesOf` at that table is the constant leaves. -/
theorem packLeavesOf_ofKeyKnown (ks : List (PackedScalar C.BaseField))
    (lb : List (Vector C.Point nc)) :
    packLeavesOf ks (XhatTable.ofKeyKnown ks lb) = List.zipWith constLeaf ks lb :=
  packLeavesOf_ofKey ks lb

/-- A scalar's constant leaf is trivially bit-boolean. -/
theorem bitBoolean_constLeaf_of_isScalar (ks : List (PackedScalar C.BaseField))
    (lb : List (Vector C.Point nc)) (hks : ∀ k ∈ ks, k.IsScalar) :
    ∀ leaf ∈ List.zipWith constLeaf ks lb, leaf.bitBoolean V := by
  intro leaf hl
  rw [← List.map_uncurry_zip_eq_zipWith] at hl
  obtain ⟨⟨k, Ps⟩, hp, rfl⟩ := List.mem_map.1 hl
  have hk := hks k (List.of_mem_zip hp).1
  cases k with
  | bit b => exact absurd hk (by simp [PackedScalar.IsScalar])
  | _ => trivial

private theorem equivPoint_corrPt (s : PastaShape C) (ci : Fin nc)
    (k : PackedScalar C.BaseField) (Ps : Vector C.Point nc) :
    SWPoint.equivPoint C.E (corrPt k Ps[ci]) = constCp s ci k Ps := by
  cases k <;> simp [corrPt, shiftBits, constCp, negShift_eq, map_zsmul]

/-- The correction sum, crossed to the point group, is the sum of the leaves' correction
points. -/
private theorem equivPoint_corrSumPt (s : PastaShape C) (ci : Fin nc)
    (ks : List (PackedScalar C.BaseField)) (lb : List (Vector C.Point nc)) :
    SWPoint.equivPoint C.E (corrSumPt ks lb ci)
      = ((List.zipWith (fun k Ps => fun ci => constCp s ci k Ps) ks lb).map (· ci)).sum := by
  have hfun : (fun (k : PackedScalar C.BaseField) (Ps : Vector C.Point nc) =>
        SWPoint.equivPoint C.E (corrPt k Ps[ci]))
      = fun k Ps => constCp s ci k Ps := by
    funext k Ps
    exact equivPoint_corrPt s ci k Ps
  rw [corrSumPt, map_list_sum, List.map_zipWith, List.map_zipWith, hfun]

/-- **The known-domain table computed from the key is bound to the key.** Beyond
`xhatBinding_const`'s premises, the correction sum is a finite point at every chunk. -/
theorem bound_ofKeyKnown (s : PastaShape C) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (ks : List (PackedScalar C.BaseField))
    (hh : σ.h ≠ 0) (hL : ∀ Ps ∈ cvk.lagrangeBasis.toList, ∀ ci : Fin nc, Ps[ci] ≠ 0)
    (hks : ks ≠ []) (hlb : cvk.lagrangeBasis.toList ≠ [])
    (hbits : ∀ leaf ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList, leaf.bitBoolean V)
    (hoff : ∀ leaf ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList,
      Leaf.offBand C.scalar V leaf)
    (hsum : ∀ ci : Fin nc, corrSumPt ks cvk.lagrangeBasis.toList ci ≠ 0) :
    (XhatTable.ofKeyKnown ks cvk.lagrangeBasis.toList).Bound s V σ cvk (constPt σ.h)
      (List.zipWith constLeaf ks cvk.lagrangeBasis.toList) where
  chunks := by
    refine ⟨List.zipWith (fun _ Ps => fun ci => SWPoint.equivPoint C.E Ps[ci]) ks
        cvk.lagrangeBasis.toList,
      List.zipWith (fun k Ps => fun ci => constCp s ci k Ps) ks cvk.lagrangeBasis.toList,
      fun ci => ⟨?_, ?_⟩⟩
    · have hb := xhatBinding_const (V := V) s ci σ cvk ks hh (fun Ps h => hL Ps h ci) hbits hoff
      simpa only [List.map_zipWith] using hb
    · have hc : (XhatTable.ofKeyKnown ks cvk.lagrangeBasis.toList).corrSum[ci]
          = constPt (corrSumPt ks cvk.lagrangeBasis.toList ci) := by
        simp [XhatTable.ofKeyKnown, Fin.getElem_fin]
      rw [hc, ← equivPoint_corrSumPt s ci]
      exact onCurveAt_constPt _ (hsum ci)
  bases_ne := by
    simpa [XhatTable.ofKeyKnown, XhatTable.ofKey] using hlb
  corrs_ne := by
    cases ks with
    | nil => exact absurd rfl hks
    | cons k ks =>
      cases hl : cvk.lagrangeBasis.toList with
      | nil => exact absurd hl hlb
      | cons Ps lb => simp [XhatTable.ofKeyKnown, XhatTable.ofKey]

/-! ### The correction sum's coefficients

Where the Lagrange points are commitments `msm g a`, the correction sum is one too, at the
coefficients `corrCoeffs`; so that it is a finite point is a relation the SRS avoids
(`SRS.Avoids`). The vector is nonzero where the Lagrange vectors past the first sum to zero
and the first to one: its coefficients then sum to the first leaf's shift. -/

/-- The shift coefficient of a packed scalar: `-(2^L)` at its ladder width, none for a boolean
cell. -/
def shiftCoeff (k : PackedScalar C.BaseField) : C.ScalarField :=
  match shiftBits k with
  | some L => -(2 ^ L)
  | none => 0

theorem corrPt_eq_smul (k : PackedScalar C.BaseField) (P : C.Point) :
    corrPt k P = shiftCoeff k • P := by
  unfold corrPt shiftCoeff
  cases shiftBits k with
  | none => simp
  | some L =>
      show negShift C L P = (-(2 ^ L) : C.ScalarField) • P
      rw [negShift_eq, ← Int.cast_smul_eq_zsmul C.ScalarField]
      push_cast
      rfl

theorem shiftCoeff_ne_zero (s : PastaShape C) (k : PackedScalar C.BaseField)
    (hk : k.IsScalar) : shiftCoeff k ≠ 0 := by
  cases k <;> simp [shiftCoeff, shiftBits, PackedScalar.IsScalar, s.scalar_two_ne] at hk ⊢

/-- The coefficients of the known-domain fold's correction sum, against the coefficient
vectors `ls` of its Lagrange points. -/
def corrCoeffs {m : ℕ} (ks : List (PackedScalar C.BaseField))
    (ls : List (Fin m → C.ScalarField)) : Fin m → C.ScalarField :=
  (List.zipWith (fun k a => shiftCoeff k • a) ks ls).sum

/-- The correction sum is the commitment to its coefficients. -/
theorem corrSumPt_map_msm {m : ℕ} (g : Fin m → C.Point) :
    ∀ (ks : List (PackedScalar C.BaseField)) (ls : List (Fin m → C.ScalarField)),
      corrSumPt ks (ls.map fun a => #v[Ipa.msm C g a]) 0 = Ipa.msm C g (corrCoeffs ks ls)
  | [], _ => by simp [corrSumPt, corrCoeffs, Ipa.msm_zero]
  | _ :: _, [] => by simp [corrSumPt, corrCoeffs, Ipa.msm_zero]
  | k :: ks, a :: ls => by
      have ih := corrSumPt_map_msm g ks ls
      simp only [corrSumPt, corrCoeffs, List.map_cons, List.zipWith_cons_cons,
        List.sum_cons] at ih ⊢
      rw [ih, Ipa.msm_add, Ipa.msm_smul, corrPt_eq_smul]
      simp

private theorem sum_corrCoeffs_range' {m N : ℕ} (L : ℕ → Fin m → C.ScalarField)
    (hL : ∀ i, 0 < i → i < N → ∑ j, L i j = 0) :
    ∀ (ks : List (PackedScalar C.BaseField)) (s len : ℕ), 0 < s → s + len ≤ N →
      ∑ j, corrCoeffs ks ((List.range' s len).map L) j = 0
  | [], _, _, _, _ => by simp [corrCoeffs]
  | _ :: _, _, 0, _, _ => by simp [corrCoeffs]
  | k :: ks, s, len + 1, hs, hle => by
      have ih := sum_corrCoeffs_range' L hL ks (s + 1) len (by omega) (by omega)
      simp only [corrCoeffs, List.range'_succ, List.map_cons, List.zipWith_cons_cons,
        List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum] at ih ⊢
      rw [ih, hL s hs (by omega)]
      simp

/-- The correction sum's coefficients sum to the first leaf's shift coefficient, where the
first vector's sum to one and the later ones' to zero. -/
theorem sum_corrCoeffs {m N : ℕ} (L : ℕ → Fin m → C.ScalarField) (h0 : ∑ j, L 0 j = 1)
    (hL : ∀ i, 0 < i → i < N → ∑ j, L i j = 0) (k : PackedScalar C.BaseField)
    (ks : List (PackedScalar C.BaseField)) (size : ℕ) (hpos : 0 < size) (hle : size ≤ N) :
    ∑ j, corrCoeffs (k :: ks) ((List.range size).map L) j = shiftCoeff k := by
  obtain ⟨len, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have ih := sum_corrCoeffs_range' L hL ks 1 len one_pos (by omega)
  rw [List.range_eq_range', List.range'_succ]
  simp only [corrCoeffs, List.map_cons, List.zipWith_cons_cons, List.sum_cons, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at ih ⊢
  rw [ih, h0]
  simp

end OfKey

/-! ## The gadgets -/

section Gadget

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
  {ks k : ℕ}

/-- `Step_verifier.verify` (`step_verifier.ml:1340`): `x_hat` from the packed statement
(`publicInputCommitKnown`, chunk by chunk, with the constant correction seed and sum), the
group half at the unfinalized proof's claims, then the two assertions: the digest equals the
claimed `sponge_digest_before_evaluations`; each returned round prechallenge equals the
claimed one, the claim compared with itself in the base case. Returns the success bit. -/
def verifyProof {sf : Type} (ops : IpaScalarOps F c sf) (e : IpaEndo F) (p : Poseidon.Params F)
    (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (blindingH : AffinePoint (FVar F)) {nc : ℕ} (tab : XhatTable F nc)
    (spongeAfterIndex : SpongeVar F) (isBaseCase : BoolVar F)
    (statement : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F)))
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf)
    (cells : IvpInput k (FVar F) (BoolVar F) sf) : CircuitM F c (BoolVar F) := do
  let leaves := packLeaves statement tab
  let computeXHat : CircuitM F c (List (AffinePoint (FVar F))) :=
    (List.finRange nc).mapM fun ci =>
      publicInputCommitKnown ci blindingH tab.corrHead[ci] tab.corrSum[ci] leaves
  let o ← incrementallyVerifyProof ops e p endo gm sqrtF false blindingH spongeAfterIndex
    computeXHat (cells.withClaims u)
  assertEqual u.spongeDigestBeforeEvaluations o.spongeDigest
  for c12 in u.deferredValues.bulletproofChallenges.toList.zip o.bulletproofChallenges do
    let c2' ← selectField isBaseCase c12.1.val c12.2.val
    assertEqual c12.1.val c2'
  pure o.success

end Gadget

/-! ## The reads -/

section Read

variable {C : KimchiCurve} {V : Valuation C.BaseField} {sf : Type} {ks : ℕ}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- The group half's claim cells from a `DeferredValues` record: the plonk claims, `ξ`, and
`cip`, `b`. -/
def DeferredValues.toIvpClaims {F sf : Type} {k : ℕ} (dv : DeferredValues k (FVar F) sf) :
    IvpClaims (FVar F) sf :=
  ⟨⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩,
    dv.plonk.perm, dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩,
   dv.xi, ⟨dv.combinedInnerProduct, dv.b⟩⟩

/-- `verify`'s read: some group-half output `o` satisfying `IvpReads` at the wire's public
input `pub`, whose success bit is the returned bit, whose digest cell reads as the claimed
`sponge_digest_before_evaluations` (so the claim is the wire's digest element), and whose
round prechallenges read as the claimed ones off the base case, pair by pair over the zip
(the gadget compares the two lists as far as both reach; their lengths are the statement's
and the opening's, not the gadget's), so the claims are the wire's `ipaRunAt` prechallenges. -/
def VerifyReads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (u : UnfinalizedProof σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf) (base : Bool)
    (v : BoolVar C.BaseField) : Prop :=
  ∃ o : IvpOutput C.BaseField,
    IvpReads S σ cvk cp pub u.deferredValues.toIvpClaims o ∧
    o.success = v ∧
    u.spongeDigestBeforeEvaluations.val V = o.spongeDigest.val V ∧
    (base = false → ∀ p ∈ u.deferredValues.bulletproofChallenges.toList.zip o.bulletproofChallenges,
      p.1.val.val V = p.2.val.val V)

/-- **`verify` reads as the group half at the packed statement, on either side.** On the group
side `S` and the `x_hat` side `X`: the wire's public input is `pubOf (packLeaves statement)`,
the statement's scalars reduced to the scalar field; the `x_hat` tables are bound to the key
at those leaves (`XhatTable.Bound`); the group half's premises hold at the claims-substituted
cells (`IvpHyps`). -/
theorem verifyProof_reads
    {nc : ℕ}
    (S : IvpSide C V ops)
    (X : PastaShape C)
    -- the wire objects
    (σ : SRS C.Point)
    (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k)
    -- the circuit's constants
    (endo : FVar C.BaseField)
    (sqrtF : C.BaseField → Option C.BaseField)
    (blindingH : AffinePoint (FVar C.BaseField))
    -- the `x_hat` tables
    (tab : XhatTable C.BaseField nc)
    -- the cells: the sponge after the index digest, the base-case bit, the wrap statement,
    -- the unfinalized proof it is checked against, the group half's commitment cells
    (spongeAfterIndex : SpongeVar C.BaseField)
    (isBaseCase : BoolVar C.BaseField)
    (statement : WrapStatement ks (FVar C.BaseField) (BoolVar C.BaseField)
      (Type1 (FVar C.BaseField)))
    (u : UnfinalizedProof σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (cells : IvpInput σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf)
    -- the values the premises speak about: the base-case bit, the `sg_old` points under their
    -- bits
    (base : Bool)
    (oldsW : List (C.Point × Bool))
    -- the base-case bit's reading, the tables bound to the key at the packed statement's
    -- leaves, the group half's premises at the claims-substituted cells
    (hbase : CircuitType.Reads V isBaseCase base)
    (htab : tab.Bound X V σ cvk blindingH (packLeaves statement tab))
    (hivp : IvpHyps S σ cvk cp (pubOf C V (packLeaves statement tab)) false
      spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    verifyProof (c := Builder V (KimchiConstraint C.BaseField)) ops S.curve.e C.sponge.params endo
      (.ofSpec C.groupMap)
      sqrtF blindingH tab spongeAfterIndex isBaseCase statement u cells
    ⦃⇓ v _ => ⌜VerifyReads S σ cvk cp (pubOf C V (packLeaves statement tab)) u base v⌝⦄ := by
  obtain ⟨⟨Ts, cps, hxhat⟩, hbases, hcorrs⟩ := htab
  -- the leaves are headed by a scalar leaf: the first packed scalar is `cip`
  have hhead : leafHeadScalar (packLeaves statement tab) := by
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hbases
    obtain ⟨c', cs, hc⟩ := List.exists_cons_of_ne_nil hcorrs
    simp [packLeaves, packLeavesOf, WrapStatement.packed, leafHeadScalar, hb, hc]
  -- `x_hat`, chunk by chunk, reads as the wire's public commitment, crossed to `C.E`
  have hXhat : ⦃⌜True⌝⦄
      (List.finRange nc).mapM (fun ci => publicInputCommitKnown
        (S := Builder V (KimchiConstraint C.BaseField)) ci blindingH tab.corrHead[ci]
        tab.corrSum[ci] (packLeaves statement tab))
      ⦃⇓ pts _ => ⌜CommReads C V pts
        (publicCommitment C σ cvk (pubOf C V (packLeaves statement tab))).toList⌝⦄ := by
    have hvec : (publicCommitment C σ cvk (pubOf C V (packLeaves statement tab))).toList
        = (List.finRange nc).map fun ci =>
            (publicCommitment C σ cvk (pubOf C V (packLeaves statement tab)))[ci] := by
      apply List.ext_getElem <;> simp
    unfold CommReads
    rw [hvec]
    refine builder_spec_imp _ _ _
      (builder_spec_mapM _ (fun r P => OnCurveAt X.d.W V r (SWPoint.equivPoint C.E P)) _
        (fun ci => xHatKnown_reads_publicCommitment X ci σ cvk blindingH tab.corrHead[ci]
          tab.corrSum[ci] _ _ _ (hxhat ci).1 hhead (hxhat ci).2) _)
      fun pts hp => hp.imp fun _ _ h => h
  -- the blinding cell's read is the tables' own: every chunk's binding carries it
  have hh : OnCurveAt C.E.toAffine V blindingH (SWPoint.equivPoint C.E σ.h) :=
    (hxhat ⟨0, hivp.nc_pos⟩).1.blinding
  have hivp := incrementallyVerifyProof_reads S σ cvk cp _ endo sqrtF false blindingH
    spongeAfterIndex _ (cells.withClaims u) oldsW hXhat hh hivp
  have hb := CircuitType.reads_boolVar.mp hbase
  simp only [verifyProof]
  mvcgen [hivp] invariants
    · ⇓⟨xs, _⟩ => ⌜base = false → ∀ p ∈ xs.prefix, p.1.val.val V = p.2.val.val V⌝
  · -- the loop step: the selected cell reads as the returned prechallenge off the base case
    rename_i pref cur suff _ _ _ hinv r _ hsel _ _ heq
    intro hbf p hp
    rw [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hinv hbf p hp
    · rw [heq, hsel base hb, hbf]
      simp
  · -- the loop entry: nothing compared yet
    intro _ p hp
    exact absurd hp List.not_mem_nil
  · -- the exit: the read
    rename_i o _ hivp' _ _ hdig _ _ hall
    exact ⟨o, hivp', rfl, hdig, hall⟩

end Read

section StepRead

/-- **`verify` reads as the group half on the step side**: `verifyProof_reads` at `stepSide`
and `pastaShapePallas`. -/
theorem verifyProof_step_reads {nc : ℕ} {V : Valuation Fp}
    (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc σ.k)
    (endo : FVar Fp) (sqrtF : Fp → Option Fp) (blindingH : AffinePoint (FVar Fp))
    (tab : XhatTable Fp nc) (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof σ.k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput σ.k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (base : Bool) (oldsW : List (IpaPallas.curve.Point × Bool))
    (hbase : CircuitType.Reads V isBaseCase base)
    (htab : tab.Bound pastaShapePallas V σ cvk blindingH (packLeaves statement tab))
    (hivp : IvpHyps (stepSide V) σ cvk cp (pubOf IpaPallas.curve V (packLeaves statement tab))
      false spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    verifyProof (c := Builder V (KimchiConstraint Fp)) IpaScalarOps.step IpaEndo.pallas
      IpaPallas.curve.sponge.params endo groupMapParamsPallas sqrtF blindingH tab
      spongeAfterIndex isBaseCase statement u cells
    ⦃⇓ v _ => ⌜VerifyReads (stepSide V) σ cvk cp
      (pubOf IpaPallas.curve V (packLeaves statement tab)) u base v⌝⦄ :=
  verifyProof_reads (stepSide V) pastaShapePallas σ cvk cp endo sqrtF blindingH tab
    spongeAfterIndex
    isBaseCase statement u cells base oldsW hbase htab hivp

end StepRead

/-! The gadget is sealed after its read: a consumer composes `verifyProof_step_reads`, never the
body. -/
attribute [irreducible] verifyProof

end Pickles
