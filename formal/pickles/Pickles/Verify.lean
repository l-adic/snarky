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

/-- A leaf over constants: the Lagrange points as its base, their honest shifts as its
correction. -/
def constLeaf (k : PackedScalar C.BaseField) (Ps : Vector C.Point nc) : Leaf C.BaseField nc :=
  match k with
  | .full x => .full x (Ps.map constPt) (Ps.map fun P => constPt ((-(2 ^ 255 : ℤ)) • P))
  | .b128 x => .b128 x (Ps.map constPt) (Ps.map fun P => constPt ((-(2 ^ 130 : ℤ)) • P))
  | .b10 x => .b10 x (Ps.map constPt) (Ps.map fun P => constPt ((-(2 ^ 10 : ℤ)) • P))
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
    OnCurveAt s.d.W V (constPt ((-(2 ^ L : ℤ)) • P))
      ((-(2 ^ L : ℤ)) • SWPoint.equivPoint C.E P) := by
  rw [← map_zsmul]
  exact onCurveAt_constPt _ (two_pow_zsmul_ne_zero s P hP L)

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
      OnCurveAt s.d.W V (constPt ((-(2 ^ L : ℤ)) • Ps[ci])) ((-(2 ^ L : ℤ)) • T) := by
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
too), the boolean leaves are boolean, and `offBand`. -/
theorem xhatBinding_const (s : PastaShape C) (ci : Fin nc) (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (ks : List (PackedScalar C.BaseField))
    (hh : σ.h ≠ 0)
    (hL : ∀ Ps ∈ cvk.lagrangeBasis.toList, Ps[ci] ≠ 0)

    (hbits : ∀ b, PackedScalar.bit b ∈ ks → ∃ bb : Bool, (↑b : CVar C.BaseField).val V = bit bb)
    (hoff : ∀ leaf ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList,
      Leaf.offBand C.scalar V leaf) :
    XhatBinding s ci V σ cvk (constPt σ.h)
      (List.zipWith constLeaf ks cvk.lagrangeBasis.toList)
      (List.zipWith (fun _ Ps => SWPoint.equivPoint C.E Ps[ci]) ks cvk.lagrangeBasis.toList)
      (List.zipWith (constCp s ci) ks cvk.lagrangeBasis.toList) where
  blinding := onCurveAt_constPt σ.h hh
  pre := forall₂_zipWith _ _ _ _ _ fun p hp =>
    leafPre_const s ci p.1 p.2 (hL _ (List.of_mem_zip hp).2)
      fun b hb => hbits b (hb ▸ (List.of_mem_zip hp).1)
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

/-- The shift a packed scalar's ladder carries; a boolean leaf has no correction. -/
def shiftOf : PackedScalar C.BaseField → ℤ
  | .full _ => -(2 ^ 255 : ℤ)
  | .b128 _ => -(2 ^ 130 : ℤ)
  | .b10 _ => -(2 ^ 10 : ℤ)
  | .bit _ => 0

/-- The `x_hat` table computed from the key's Lagrange points, at a statement's packing. -/
def XhatTable.ofKey (ks : List (PackedScalar C.BaseField)) (lb : List (Vector C.Point nc)) :
    XhatTable C.BaseField nc where
  bases := lb.map (·.map constPt)
  corrs := List.zipWith (fun k Ps => Ps.map fun P => constPt (shiftOf k • P)) ks lb
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
      cases k <;> simp [constLeaf, shiftOf]

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
