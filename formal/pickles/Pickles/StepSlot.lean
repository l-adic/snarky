import Kimchi.Columns
import Pickles.Encoding
import Pickles.Verify
import Pickles.VkComms
import Snarky.Kimchi.Circuit.CheckedPoint
import Snarky.Kimchi.Circuit.EndoScalar

set_option mvcgen.warning false

/-!
# The step circuit's per-slot allocation

Transcribed from `Pickles/Step/Types.purs`: what the step circuit allocates for one previous
proof, in the order the deployed allocation lays its cells out and with the checks it emits.
The records here pin that order; they carry the same data as the statement records the
gadgets read, with every point checked on the curve.

## Main definitions

* `PallasPt`: a Pallas point over the step field, allocated with its on-curve check;
* `AllocBranchData`: the branch data, the mask bits before the domain's `log2`, which is
  range-checked to 16 bits;
* `AllocEvals`: the previous step proof's evaluations, column by column, `ft(ζω)` last;
* `SlotWitness`: one previous proof's witness: the wrap proof, its proof state, the step
  proof's evaluations, and the accumulators it verified.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-- A Pallas point over the step field, checked on `y² = x³ + 5`. -/
abbrev PallasPt (α : Type) : Type := CheckedPoint (F := Fp) 0 5 α

/-! ## The branch data -/

/-- The branch data as allocated: the two mask bits, then the domain's `log2`. -/
structure AllocBranchData (f bc : Type) where
  /-- The first mask bit. -/
  mask0 : bc
  /-- The second mask bit. -/
  mask1 : bc
  /-- `log2` of the verified proof's domain size. -/
  domainLog2 : f

/-- The branch data is its two bits and its `log2`. -/
def AllocBranchData.equivProd (f bc : Type) : AllocBranchData f bc ≃ bc × bc × f :=
  ⟨fun d => (d.mask0, d.mask1, d.domainLog2), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl,
    fun _ => rfl⟩

instance instAllocBranchDataCircuitType {F f w b vb : Type} [CircuitType F f w]
    [CircuitType F b vb] : CircuitType F (AllocBranchData f b) (AllocBranchData w vb) :=
  CircuitType.ofEquiv (AllocBranchData.equivProd f b) (AllocBranchData.equivProd w vb)

/-- The branch data's check: the mask bits' booleanity, then the `log2` range-checked by
expanding its 16 bits through the endo at one row. -/
def AllocBranchData.check {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c]
    [LawfulBasicSystem Fp c] [KimchiSystem Fp c]
    (d : AllocBranchData (FVar Fp) (BoolVar Fp)) : CircuitM Fp c PUnit := do
  CheckedType.check (c := c) (val := Bool × Bool × Fp) (d.mask0, d.mask1, d.domainLog2)
  let _ ← EndoScalar.toField 1 d.domainLog2 (.const Pasta.pallasEndo)

/-- Under any valuation satisfying the emitted constraints, the mask cells read as bits and
the `log2` cell as a number below `2 ^ 16`. -/
theorem AllocBranchData.check_spec {V : Valuation Fp}
    (d : AllocBranchData (FVar Fp) (BoolVar Fp)) :
    ⦃⌜True⌝⦄ AllocBranchData.check (c := Builder V (KimchiConstraint Fp)) d
    ⦃⇓ _ _ => ⌜(∃ b : Bool, (↑d.mask0 : CVar Fp).val V = bit b) ∧
      (∃ b : Bool, (↑d.mask1 : CVar Fp).val V = bit b) ∧
      ∃ n : ℕ, n < 2 ^ 16 ∧ d.domainLog2.val V = (n : Fp)⌝⦄ := by
  have hck : ⦃⌜True⌝⦄ CheckedType.check (F := Fp) (c := Builder V (KimchiConstraint Fp))
      (val := Bool × Bool × Fp) (d.mask0, d.mask1, d.domainLog2)
      ⦃⇓ _ _ => ⌜CheckedType.post (F := Fp) (c := Builder V (KimchiConstraint Fp))
        (val := Bool × Bool × Fp) V (d.mask0, d.mask1, d.domainLog2)⌝⦄ :=
    (builder_spec_iff _ _).mpr fun nv h => CheckedType.check_sound V _ nv h
  have htf := EndoScalar.toField_spec_rows (V := V) (by decide) (by decide) 1 d.domainLog2
    (.const Pasta.pallasEndo)
  simp only [AllocBranchData.check]
  mvcgen [hck, htf]
  rename_i _ _ hp _ _ hn
  obtain ⟨n, hlt, hv, -⟩ := hn
  exact ⟨hp.1, hp.2.1, n, hlt, hv⟩

/-- The branch data is checked by `AllocBranchData.check`: its mask cells read as bits, its
`log2` cell as a number below `2 ^ 16`. -/
instance instAllocBranchDataCheckedType :
    CheckedType Fp (KimchiConstraint Fp) (AllocBranchData Fp Bool)
      (AllocBranchData (FVar Fp) (BoolVar Fp)) where
  check := AllocBranchData.check
  post V d := (∃ b : Bool, (↑d.mask0 : CVar Fp).val V = bit b) ∧
    (∃ b : Bool, (↑d.mask1 : CVar Fp).val V = bit b) ∧
    ∃ n : ℕ, n < 2 ^ 16 ∧ d.domainLog2.val V = (n : Fp)
  check_sound V d nv h := (builder_spec_iff _ _).mp (AllocBranchData.check_spec d) nv h
  check_complete := by
    rintro ⟨m0, m1, dl⟩ ⟨a0, a1, x⟩ hv
    -- an admissible `log2` is below `2 ^ 16`
    have hc := CircuitType.reads_constVar (F := Fp) (var := AllocBranchData (FVar Fp) (BoolVar Fp))
      (fun _ => 0) (⟨a0, a1, x⟩ : AllocBranchData Fp Bool)
    obtain ⟨_, _, n, hn, hx⟩ := hv _ _ hc
    replace hx : x = (n : Fp) :=
      (CircuitType.reads_fvar.mp (CircuitType.reads_prod.mp
        (CircuitType.reads_prod.mp hc).2).2).symm.trans hx
    have hlt : ToNat.toNat x < 2 ^ (16 * 1) := by
      rw [hx, LawfulToNat.toNat_natCast n
        (show n < PALLAS_BASE_CARD from lt_trans hn (by decide))]
      exact hn
    refine Complete.bind (Complete.imp (fun st (h : CircuitType.ReadsAs
        (val := Bool × Bool × Fp) st (m0, m1, dl) (a0, a1, x)) =>
          ⟨h, (CircuitType.scoped_prod.mp (CircuitType.scoped_prod.mp h.1).2).2,
            (CircuitType.reads_prod.mp (CircuitType.reads_prod.mp h.2).2).2⟩)
        (fun _ _ h => h.2)
        (Complete.frame CircuitType.monotone_readsAs
          (CheckedType.check_complete (c := KimchiConstraint Fp) (val := Bool × Bool × Fp)
            (m0, m1, dl) (a0, a1, x) (show CheckedType.Valid (F := Fp) (c := KimchiConstraint Fp)
              (var := BoolVar Fp × BoolVar Fp × FVar Fp) (a0, a1, x) by simp)))) fun _ => ?_
    exact Complete.bind
      (Complete.imp (fun st h => ⟨h, CircuitType.scoped_fvar.mpr (CVar.scoped_const _ _),
          CircuitType.reads_fvar.mpr rfl⟩) (fun _ _ _ => trivial)
        (EndoScalar.toField_complete_rows (by decide) (by decide) 1 dl _ x _ hlt))
      fun _ => Complete.pure

/-- The branch data's check, read at a valuation. -/
instance instAllocBranchDataCheckedTypeBuilder {V : Valuation Fp} :
    CheckedType Fp (Builder V (KimchiConstraint Fp)) (AllocBranchData Fp Bool)
      (AllocBranchData (FVar Fp) (BoolVar Fp)) :=
  instAllocBranchDataCheckedType

/-! ## The evaluations -/

/-- The previous step proof's evaluations as allocated: the public column, the witness, the
coefficients, `z`, the six permutation columns, the six selectors, each column's `ζ` chunks
before its `ζω` chunks, then `ft(ζω)`. -/
structure AllocEvals (nc : ℕ) (f : Type) where
  /-- The public-input polynomial's chunks. -/
  pub : PointEvaluations (Vector f nc)
  /-- The witness columns. -/
  w : Vector (PointEvaluations (Vector f nc)) wCols
  /-- The coefficient columns. -/
  coefficients : Vector (PointEvaluations (Vector f nc)) coeffCols
  /-- The permutation accumulator. -/
  z : PointEvaluations (Vector f nc)
  /-- The permutation columns `σ₀…σ₅`. -/
  s : Vector (PointEvaluations (Vector f nc)) sigmaRows
  /-- The selectors: generic, poseidon, complete-add, mul, emul, endomul-scalar. -/
  index : Vector (PointEvaluations (Vector f nc)) 6
  /-- `ft(ζω)`. -/
  ftEval1 : f

/-- The evaluations are their columns, in allocation order. -/
def AllocEvals.equivProd (nc : ℕ) (f : Type) :
    AllocEvals nc f ≃ PointEvaluations (Vector f nc) ×
      Vector (PointEvaluations (Vector f nc)) wCols ×
      Vector (PointEvaluations (Vector f nc)) coeffCols × PointEvaluations (Vector f nc) ×
      Vector (PointEvaluations (Vector f nc)) sigmaRows ×
      Vector (PointEvaluations (Vector f nc)) 6 × f :=
  ⟨fun e => (e.pub, e.w, e.coefficients, e.z, e.s, e.index, e.ftEval1),
    fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

instance instAllocEvalsCircuitType {F v w : Type} {nc : ℕ} [CircuitType F v w] :
    CircuitType F (AllocEvals nc v) (AllocEvals nc w) :=
  CircuitType.ofEquiv (AllocEvals.equivProd nc v) (AllocEvals.equivProd nc w)

/-- The evaluations are checked column by column. -/
instance instAllocEvalsCheckedType {F c v w : Type} {nc : ℕ} [Field F] [BasicSystem F c]
    [ConstraintHolds F c] [CircuitType F v w] [CheckedType F c v w] :
    CheckedType F c (AllocEvals nc v) (AllocEvals nc w) :=
  CheckedType.ofEquiv (AllocEvals.equivProd nc v) (AllocEvals.equivProd nc w)

/-- The evaluations as the record the finalize reads. -/
def AllocEvals.toChunked {nc : ℕ} {f : Type} (e : AllocEvals nc f) : ChunkedEvals nc f :=
  ⟨e.ftEval1, e.pub, ⟨e.w, e.z, e.s, e.coefficients, e.index[0], e.index[1], e.index[2],
    e.index[3], e.index[4], e.index[5]⟩⟩

/-! ## The step statement -/

/-! ## One slot's witness -/

/-- One previous proof's witness, as allocated: the wrap proof's commitments (`ncw` chunks)
and opening, the proof state it carries (the deferred values of the step proof it verified, and
its branch data), that step proof's evaluations (`ncs` chunks), and the `w` accumulators that
step proof verified. -/
structure SlotWitness (w ncw ncs k ks : ℕ) (f bc sf pt : Type) where
  /-- The witness commitments. -/
  wComm : Vector (Vector pt ncw) wCols
  /-- The permutation accumulator's commitment. -/
  zComm : Vector pt ncw
  /-- The quotient commitment, `ncw` chunks per piece. -/
  tComm : Vector (Vector pt ncw) quotChunks
  /-- The opening's `(L, R)` pairs. -/
  lr : Vector (pt × pt) k
  /-- The opening's `z₁`. -/
  z1 : sf
  /-- The opening's `z₂`. -/
  z2 : sf
  /-- The opening's `δ`. -/
  delta : pt
  /-- The opening's `sg`. -/
  sg : pt
  /-- The carried combined inner product, shifted. -/
  cip : f
  /-- The carried `b`, shifted. -/
  b : f
  /-- The carried `ζ^(srs length)`, shifted. -/
  zetaToSrsLength : f
  /-- The carried `ζⁿ`, shifted. -/
  zetaToDomainSize : f
  /-- The carried permutation scalar, shifted. -/
  perm : f
  /-- The carried fq-sponge digest. -/
  spongeDigest : f
  /-- The carried `β`. -/
  beta : f
  /-- The carried `γ`. -/
  gamma : f
  /-- The carried `α` prechallenge. -/
  alpha : f
  /-- The carried `ζ` prechallenge. -/
  zeta : f
  /-- The carried `ξ` prechallenge. -/
  xi : f
  /-- The carried bulletproof challenges. -/
  bulletproofChallenges : Vector f ks
  /-- The carried branch data. -/
  branch : AllocBranchData f bc
  /-- The verified step proof's evaluations. -/
  evals : AllocEvals ncs f
  /-- The round challenges of the accumulators that step proof verified. -/
  prevChallenges : Vector (Vector f ks) w
  /-- Their `sg` points. -/
  prevSgs : Vector pt w

section SlotEncoding

variable (w ncw ncs k ks : ℕ) (f bc sf pt : Type)

/-- The wrap proof's part of a slot witness. -/
abbrev SlotWitness.ProofPart : Type :=
  Vector (Vector pt ncw) wCols × Vector pt ncw × Vector (Vector pt ncw) quotChunks ×
    Vector (pt × pt) k × sf × sf × pt × pt

/-- The proof state's part of a slot witness. -/
abbrev SlotWitness.StatePart : Type :=
  f × f × f × f × f × f × f × f × f × f × f × Vector f ks × AllocBranchData f bc

/-- A slot witness is its wrap proof, its proof state, the evaluations and the accumulators, in
allocation order. -/
def SlotWitness.equivProd :
    SlotWitness w ncw ncs k ks f bc sf pt ≃
      SlotWitness.ProofPart ncw k sf pt × SlotWitness.StatePart ks f bc × AllocEvals ncs f ×
        Vector (Vector f ks) w × Vector pt w where
  toFun s := ((s.wComm, s.zComm, s.tComm, s.lr, s.z1, s.z2, s.delta, s.sg),
    (s.cip, s.b, s.zetaToSrsLength, s.zetaToDomainSize, s.perm, s.spongeDigest, s.beta, s.gamma,
      s.alpha, s.zeta, s.xi, s.bulletproofChallenges, s.branch),
    s.evals, s.prevChallenges, s.prevSgs)
  invFun p :=
    let (pr, st, ev, pc, ps) := p
    let (wComm, zComm, tComm, lr, z1, z2, delta, sg) := pr
    let (cip, b, zs, zd, perm, sd, beta, gamma, alpha, zeta, xi, bp, br) := st
    ⟨wComm, zComm, tComm, lr, z1, z2, delta, sg, cip, b, zs, zd, perm, sd, beta, gamma, alpha,
      zeta, xi, bp, br, ev, pc, ps⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SlotEncoding

instance instSlotWitnessCircuitType {F f fv b bv s sv p pv : Type} {w ncw ncs k ks : ℕ}
    [CircuitType F f fv] [CircuitType F b bv] [CircuitType F s sv] [CircuitType F p pv] :
    CircuitType F (SlotWitness w ncw ncs k ks f b s p) (SlotWitness w ncw ncs k ks fv bv sv pv) :=
  CircuitType.ofEquiv (SlotWitness.equivProd w ncw ncs k ks f b s p)
    (SlotWitness.equivProd w ncw ncs k ks fv bv sv pv)

/-- A slot witness is checked component by component, in allocation order. -/
instance instSlotWitnessCheckedType {F c f fv b bv s sv p pv : Type} {w ncw ncs k ks : ℕ}
    [Field F] [BasicSystem F c] [ConstraintHolds F c] [CircuitType F f fv] [CircuitType F b bv]
    [CircuitType F s sv] [CircuitType F p pv] [CheckedType F c f fv] [CheckedType F c s sv]
    [CheckedType F c p pv] [CheckedType F c (AllocBranchData f b) (AllocBranchData fv bv)] :
    CheckedType F c (SlotWitness w ncw ncs k ks f b s p) (SlotWitness w ncw ncs k ks fv bv sv pv) :=
  CheckedType.ofEquiv (SlotWitness.equivProd w ncw ncs k ks f b s p)
    (SlotWitness.equivProd w ncw ncs k ks fv bv sv pv)

/-- A slot's points lie on Pallas's curve: the wrap proof's commitments, `(L, R)` pairs, `δ` and
`sg`, and the accumulators' `sg`s, as the slot check's point checks leave them. -/
def SlotWitness.PointsOnCurve {w ncw ncs k ks : ℕ} (V : Valuation Fp)
    (s : SlotWitness w ncw ncs k ks (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))) (PallasPt (FVar Fp))) : Prop :=
  CheckedType.post (F := Fp) (c := Builder V (KimchiConstraint Fp))
      (val := SlotWitness.ProofPart ncw k (Type2 (SplitField Fp Bool)) (PallasPt Fp)) V
      (s.wComm, s.zComm, s.tComm, s.lr, s.z1, s.z2, s.delta, s.sg) ∧
    CheckedType.post (F := Fp) (c := Builder V (KimchiConstraint Fp))
      (val := Vector (PallasPt Fp) w) V s.prevSgs

/-- A slot witness's check forces the opening's `z₁`, `z₂` parity cells and the branch data's
mask cells to read as bits, its `log2` cell as a number below `2 ^ 16`, and its points onto the
curve (`PointsOnCurve`). -/
theorem SlotWitness.of_post {V : Valuation Fp} {w ncw ncs k ks : ℕ}
    {s : SlotWitness w ncw ncs k ks (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))) (PallasPt (FVar Fp))}
    (h : CheckedType.post (F := Fp) (c := Builder V (KimchiConstraint Fp))
      (val := SlotWitness w ncw ncs k ks Fp Bool (Type2 (SplitField Fp Bool)) (PallasPt Fp))
      V s) :
    (∃ b : Bool, (↑s.z1.val.sOdd : CVar Fp).val V = bit b) ∧
      (∃ b : Bool, (↑s.z2.val.sOdd : CVar Fp).val V = bit b) ∧
      (∃ b : Bool, (↑s.branch.mask0 : CVar Fp).val V = bit b) ∧
      (∃ b : Bool, (↑s.branch.mask1 : CVar Fp).val V = bit b) ∧
      (∃ n : ℕ, n < 2 ^ 16 ∧ s.branch.domainLog2.val V = (n : Fp)) ∧
      SlotWitness.PointsOnCurve V s := by
  obtain ⟨hp, ⟨-, -, -, -, -, -, -, -, -, -, -, -, hb0, hb1, hd⟩, -, -, hs⟩ := h
  exact ⟨hp.2.2.2.2.1.2, hp.2.2.2.2.2.1.2, hb0, hb1, hd, hp, hs⟩

/-! ## The key -/

/-- A key's commitments are its permutation, coefficient and six selector commitments, in
absorb order. -/
def VkComms.equivProd (nc : ℕ) (f : Type) :
    VkComms nc f ≃ Vector (Vector f nc) permCols × Vector (Vector f nc) coeffCols ×
      Vector f nc × Vector f nc × Vector f nc × Vector f nc × Vector f nc × Vector f nc :=
  ⟨fun k => (k.sigmaComm, k.coefficientsComm, k.genericComm, k.poseidonComm, k.completeAddComm,
      k.mulComm, k.emulComm, k.endomulScalarComm),
    fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

instance instVkCommsCircuitType {F v w : Type} {nc : ℕ} [CircuitType F v w] :
    CircuitType F (VkComms nc v) (VkComms nc w) :=
  CircuitType.ofEquiv (VkComms.equivProd nc v) (VkComms.equivProd nc w)

/-- A key is checked commitment by commitment: at checked points, every chunk on the curve. -/
instance instVkCommsCheckedType {F c v w : Type} {nc : ℕ} [Field F]
    [BasicSystem F c] [ConstraintHolds F c] [CircuitType F v w] [CheckedType F c v w] :
    CheckedType F c (VkComms nc v) (VkComms nc w) :=
  CheckedType.ofEquiv (VkComms.equivProd nc v) (VkComms.equivProd nc w)

/-- The key's commitments as the points the gadgets read. -/
def VkComms.points {nc : ℕ} {α : Type} (k : VkComms nc (PallasPt α)) :
    VkComms nc (AffinePoint α) :=
  ⟨k.sigmaComm.map (·.map CheckedPoint.pt), k.coefficientsComm.map (·.map CheckedPoint.pt),
    k.genericComm.map CheckedPoint.pt, k.poseidonComm.map CheckedPoint.pt,
    k.completeAddComm.map CheckedPoint.pt, k.mulComm.map CheckedPoint.pt,
    k.emulComm.map CheckedPoint.pt,
    k.endomulScalarComm.map CheckedPoint.pt⟩

end Pickles
