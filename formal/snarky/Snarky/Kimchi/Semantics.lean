import Snarky.Kimchi.Constraint
import Snarky.WP
import Snarky.Prover.WP
import Kimchi.Gate.AddComplete
import Kimchi.Gate.Poseidon
import Kimchi.Gate.EndoScalar
import Kimchi.Gate.EndoMul

/-!
# The kimchi constraint semantics

The reading of `KimchiConstraint` at a total valuation (`KimchiConstraint.Holds`): the
layer the gadget laws, sound and complete, are stated against, with no rows, reduction,
or wiring in sight. `.basic` is the reference `Basic` reading, so the
`LawfulBasicSystem` instance below transfers every backend-generic base gadget law to
this backend.

The landed gate payloads read as the verified gates' own predicates at the payload's
operand values:
- `.addComplete`: one witness record (`AddComplete.read`, one field per gate column);
- `.poseidon`: a chain of five-round windows over the state list (`Poseidon.chainHolds`
  at the payload's parameter data);
- `.endoScalar`, `.varBaseMul`: one witness record per round (the scale round carries
  all 26 gate cells itself, output accumulator and register included, so no successor
  read is needed);
- `.endoMul`: a successor chain over the round list (each round's output cells read
  from the NEXT round's `p`/`nAcc`, the last from the payload finals — the two-row
  gate's next-row read, value-level).

`.pad` reads vacuously (a padding row asserts nothing): the reading is deliberately
per-constructor, and a vacuous case marks a constructor outside the landed gadget
surface.
-/

namespace Snarky.Kimchi

open Snarky

-- `Field` rather than `CommRing`: the EndoScalar gate's crumb-interpolation
-- polynomials carry inverse-of-small-integer coefficients.
variable {F : Type} [Field F] [DecidableEq F]

/-- The payload's operand values under a valuation, as the verified gate's witness
record — one field per gate column, in the gate's column order. -/
def AddComplete.read (V : Valuation F) (c : AddComplete F) :
    Kimchi.Gate.AddComplete.Witness F where
  x1 := c.p1.x.val V
  y1 := c.p1.y.val V
  x2 := c.p2.x.val V
  y2 := c.p2.y.val V
  x3 := c.p3.x.val V
  y3 := c.p3.y.val V
  inf := c.inf.val V
  sameX := c.sameX.val V
  s := c.s.val V
  infZ := c.infZ.val V
  x21Inv := c.x21Inv.val V

/-- The payload's MDS rows as the gate's matrix record. -/
def Poseidon.mdsOf (m : (F × F × F) × (F × F × F) × (F × F × F)) :
    Kimchi.Gate.Poseidon.Mds F :=
  { m00 := m.1.1, m01 := m.1.2.1, m02 := m.1.2.2,
    m10 := m.2.1.1, m11 := m.2.1.2.1, m12 := m.2.1.2.2,
    m20 := m.2.2.1, m21 := m.2.2.2.1, m22 := m.2.2.2.2 }

/-- Window `k`'s five constant triples off the payload's table (rounds `5k … 5k+4`,
the offsets the reducer writes into row `k`'s coefficient cells). -/
def Poseidon.rcRow (rc : List (F × F × F)) (k : ℕ) : Fin 5 → F × F × F :=
  fun j => rc.getD (5 * k + j.1) (0, 0, 0)

/-- The payload's state values under a valuation, in round order. -/
def Poseidon.read (V : Valuation F) (c : PoseidonConstraint F) : List (F × F × F) :=
  c.state.map fun t => (t.1.val V, t.2.1.val V, t.2.2.val V)

/-- The chain reading of a state list: one gate window per five states from position
`5k`, each window's sixth state opening the next — the wire layout's next-row read,
value-level, so the chain's links are shared list elements. Off the deployed
`11·5 + 1` shape, partial tails assert nothing, matching the reducer's row
fallbacks. -/
def Poseidon.chainHolds (M : Kimchi.Gate.Poseidon.Mds F) (rc : List (F × F × F)) :
    ℕ → List (F × F × F) → Prop
  | k, s0 :: s1 :: s2 :: s3 :: s4 :: rest =>
    match rest with
    | s5 :: _ =>
      Kimchi.Gate.Poseidon.Holds M (rcRow rc k) ⟨s0, s1, s2, s3, s4, s5⟩ ∧
        chainHolds M rc (k + 1) rest
    | [] => True
  | _, _ => True

/-- The payload round's operand values under a valuation, as the verified gate's
witness record — one field per gate cell, the crumbs in index order. -/
def EndoScalarRound.read (V : Valuation F) (r : EndoScalarRound F) :
    Kimchi.Gate.EndoScalar.Witness F where
  a0 := r.a0.val V
  b0 := r.b0.val V
  n0 := r.n0.val V
  a8 := r.a8.val V
  b8 := r.b8.val V
  n8 := r.n8.val V
  crumbs := r.xs.toList.map (·.val V)

/-- The scale round's operand values under a valuation, as the verified gate's
witness record — one field per gate cell; the round carries its own output
accumulator and register, so the reading is self-contained. -/
def ScaleRound.read (V : Valuation F) (r : ScaleRound F) :
    Kimchi.Gate.VarBaseMul.Witness F where
  xT := r.base.x.val V
  yT := r.base.y.val V
  x0 := r.acc0.x.val V
  y0 := r.acc0.y.val V
  x1 := r.acc1.x.val V
  y1 := r.acc1.y.val V
  x2 := r.acc2.x.val V
  y2 := r.acc2.y.val V
  x3 := r.acc3.x.val V
  y3 := r.acc3.y.val V
  x4 := r.acc4.x.val V
  y4 := r.acc4.y.val V
  x5 := r.acc5.x.val V
  y5 := r.acc5.y.val V
  n := r.nPrev.val V
  nPrime := r.nNext.val V
  b0 := r.bit0.val V
  b1 := r.bit1.val V
  b2 := r.bit2.val V
  b3 := r.bit3.val V
  b4 := r.bit4.val V
  s0 := r.slope0.val V
  s1 := r.slope1.val V
  s2 := r.slope2.val V
  s3 := r.slope3.val V
  s4 := r.slope4.val V

/-- The payload round's operand values under a valuation, as the verified gate's
witness record — one field per gate cell, with the output cells `xS`/`yS`/`nPrime`
supplied by the caller: the gate is two-row, and a round's outputs live in its
successor's cells (the next round's `p`/`nAcc`, or the payload finals). -/
def EndoMulRound.readWith (V : Valuation F) (r : EndoMulRound F) (xS yS nPrime : F) :
    Kimchi.Gate.EndoMul.Witness F where
  xT := r.t.x.val V
  yT := r.t.y.val V
  xP := r.p.x.val V
  yP := r.p.y.val V
  n := r.nAcc.val V
  nPrime := nPrime
  b1 := r.bit0.val V
  b2 := r.bit1.val V
  b3 := r.bit2.val V
  b4 := r.bit3.val V
  s1 := r.s1.val V
  xR := r.r.x.val V
  yR := r.r.y.val V
  s3 := r.s3.val V
  xS := xS
  yS := yS
  inv := r.inv.val V

/-- The successor-chain reading of the round list: the gate per round at the
payload's endo coefficient, each round's output cells read from the NEXT round's
`p`/`nAcc` values and the last round's from the finals `fin` — the wire layout's
next-row read, value-level, so the chain's links are shared round fields. -/
def EndoMul.chainHolds (V : Valuation F) (endo : F) (fin : F × F × F) :
    List (EndoMulRound F) → Prop
  | [] => True
  | [r] =>
    Kimchi.Gate.EndoMul.Holds endo (EndoMulRound.readWith V r fin.1 fin.2.1 fin.2.2)
  | r :: r' :: rest =>
    Kimchi.Gate.EndoMul.Holds endo
      (EndoMulRound.readWith V r (r'.p.x.val V) (r'.p.y.val V) (r'.nAcc.val V)) ∧
      chainHolds V endo fin (r' :: rest)

/-- The constraint-level semantics: `.basic` is the reference reading, the landed gate
payloads the verified gates' predicates at the operand values, and the rest vacuous
(module docstring). -/
def KimchiConstraint.Holds (V : Valuation F) : KimchiConstraint F → Prop
  | .basic con => ConstraintHolds.Holds V con
  | .addComplete c => Kimchi.Gate.AddComplete.Holds (AddComplete.read V c)
  | .poseidon c => Poseidon.chainHolds (Poseidon.mdsOf c.mds) c.rc 0 (Poseidon.read V c)
  | .endoScalar rounds => ∀ r ∈ rounds, Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read V r)
  | .varBaseMul rounds =>
    ∀ r ∈ rounds, Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read V r)
  | .endoMul c =>
    EndoMul.chainHolds V c.endo (c.s.x.val V, c.s.y.val V, c.nAcc.val V) c.state
  | .pad _ => True

/-- The Poseidon chain reading is decidable, window by window. -/
instance Poseidon.decidableChainHolds (M : Kimchi.Gate.Poseidon.Mds F) (rc : List (F × F × F)) :
    (k : ℕ) → (l : List (F × F × F)) → Decidable (Poseidon.chainHolds M rc k l)
  | k, _ :: _ :: _ :: _ :: _ :: s5 :: rest => by
    haveI := Poseidon.decidableChainHolds M rc (k + 1) (s5 :: rest)
    unfold Poseidon.chainHolds; infer_instance
  | _, [] | _, [_] | _, [_, _] | _, [_, _, _] | _, [_, _, _, _] | _, [_, _, _, _, _] =>
    isTrue (by simp [Poseidon.chainHolds])

/-- The endomorphism-multiplication chain reading is decidable, round by round. -/
instance EndoMul.decidableChainHolds (V : Valuation F) (endo : F) (fin : F × F × F) :
    (rs : List (EndoMulRound F)) → Decidable (EndoMul.chainHolds V endo fin rs)
  | [] => isTrue trivial
  | [_] => by unfold EndoMul.chainHolds; infer_instance
  | _ :: r' :: rest => by
    haveI := EndoMul.decidableChainHolds V endo fin (r' :: rest)
    unfold EndoMul.chainHolds; infer_instance

/-- The constraint-level semantics is decidable: each arm is a verified gate's decidable
predicate, a chain of them, or a reference row. -/
instance KimchiConstraint.decidableHolds (V : Valuation F) (c : KimchiConstraint F) :
    Decidable (KimchiConstraint.Holds V c) := by
  cases c <;> unfold KimchiConstraint.Holds
  · exact Basic.decidableHolds V _
  all_goals infer_instance

/-- The cells a constraint reads: a `Basic` row's operands, each gate payload's operands (the
rounds' and the Poseidon states' in list order, an `endoScalar` round's crumbs last, an
`endoMul` payload's finals last), and the padding row's seven. -/
def KimchiConstraint.cells : KimchiConstraint F → List (CVar F)
  | .basic con => Basic.cells con
  | .addComplete c => c.operands.toList
  | .poseidon c => c.state.flatMap fun t => [t.1, t.2.1, t.2.2]
  | .endoScalar rounds =>
    rounds.flatMap fun r => [r.n0, r.n8, r.a0, r.b0, r.a8, r.b8] ++ r.xs.toList
  | .varBaseMul rounds => rounds.flatMap fun r => (r.cellsA ++ r.cellsB).filterMap id
  | .endoMul c => c.state.flatMap (fun r => r.cells.filterMap id) ++ [c.s.x, c.s.y, c.nAcc]
  | .pad vs => vs.toList

/-- The semantic reading, packaged for the triple machinery. -/
instance KimchiConstraint.instConstraintHolds :
    ConstraintHolds F (KimchiConstraint F) :=
  ⟨KimchiConstraint.Holds, KimchiConstraint.cells⟩

omit [DecidableEq F] in
/-- The `endoMul` successor chain reads only its rounds' cells and its finals. -/
private theorem EndoMul.chainHolds_congr {V V' : Valuation F} {endo : F} {fin : F × F × F} :
    ∀ rs : List (EndoMulRound F),
      (∀ x ∈ rs.flatMap (fun r => r.cells.filterMap id), x.val V = x.val V') →
        (EndoMul.chainHolds V endo fin rs ↔ EndoMul.chainHolds V' endo fin rs)
  | [], _ => Iff.rfl
  | [r], h => by
    simp (disch := simp [EndoMulRound.cells]) only [EndoMul.chainHolds,
      EndoMulRound.readWith, h]
  | r :: r' :: rest, h => by
    have ih := EndoMul.chainHolds_congr (endo := endo) (fin := fin) (r' :: rest) fun x hx =>
      h x (by rw [List.flatMap_cons]; exact List.mem_append_right _ hx)
    rw [EndoMul.chainHolds, EndoMul.chainHolds, ih]
    simp (disch := simp [EndoMulRound.cells]) only [EndoMulRound.readWith, h]

/-- The backend is lawful: `.basic` embeds the reference constraints verbatim, so
each law is `Basic`'s own. -/
instance KimchiConstraint.instLawfulBasicSystem :
    LawfulBasicSystem F (KimchiConstraint F) where
  holds_equal V a b := LawfulBasicSystem.holds_equal (c := Basic F) V a b
  holds_r1cs V l r o := LawfulBasicSystem.holds_r1cs (c := Basic F) V l r o
  holds_square V a sq := LawfulBasicSystem.holds_square (c := Basic F) V a sq
  holds_boolean V x := LawfulBasicSystem.holds_boolean (c := Basic F) V x
  holds_congr con V V' h := by
    show KimchiConstraint.Holds V con ↔ KimchiConstraint.Holds V' con
    replace h : ∀ x ∈ KimchiConstraint.cells con, x.val V = x.val V' := h
    cases con with
    | basic b => exact LawfulBasicSystem.holds_congr (c := Basic F) b V V' h
    | addComplete c =>
      have hm : ∀ x ∈ [c.p1.x, c.p1.y, c.p2.x, c.p2.y, c.p3.x, c.p3.y, c.inf, c.sameX, c.s,
          c.infZ, c.x21Inv], x.val V = x.val V' := h
      simp only [List.forall_mem_cons] at hm
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hm
      simp only [KimchiConstraint.Holds, AddComplete.read, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10, h11]
    | poseidon c =>
      have hr : Poseidon.read V c = Poseidon.read V' c := by
        unfold Poseidon.read
        refine List.map_congr_left fun t ht => ?_
        have hm : ∀ y ∈ [t.1, t.2.1, t.2.2], y.val V = y.val V' := fun y hy =>
          h y (List.mem_flatMap.mpr ⟨t, ht, hy⟩)
        simp only [List.forall_mem_cons] at hm
        rw [hm.1, hm.2.1, hm.2.2.1]
      simp only [KimchiConstraint.Holds, hr]
    | endoScalar rounds =>
      have hr : ∀ r ∈ rounds, EndoScalarRound.read V r = EndoScalarRound.read V' r := by
        intro r hr
        have hm : ∀ y ∈ [r.n0, r.n8, r.a0, r.b0, r.a8, r.b8] ++ r.xs.toList,
            y.val V = y.val V' := fun y hy => h y (List.mem_flatMap.mpr ⟨r, hr, hy⟩)
        have hxs : r.xs.toList.map (·.val V) = r.xs.toList.map (·.val V') :=
          List.map_congr_left fun y hy => hm y (List.mem_append_right _ hy)
        simp (disch := simp) only [EndoScalarRound.read, hxs, hm]
      simp only [KimchiConstraint.Holds]
      exact forall₂_congr fun r hr' => by rw [hr r hr']
    | varBaseMul rounds =>
      have hr : ∀ r ∈ rounds, ScaleRound.read V r = ScaleRound.read V' r := by
        intro r hr
        have hm : ∀ y ∈ (r.cellsA ++ r.cellsB).filterMap id, y.val V = y.val V' := fun y hy =>
          h y (List.mem_flatMap.mpr ⟨r, hr, hy⟩)
        simp (disch := simp [ScaleRound.cellsA, ScaleRound.cellsB]) only [ScaleRound.read, hm]
      simp only [KimchiConstraint.Holds]
      exact forall₂_congr fun r hr' => by rw [hr r hr']
    | endoMul c =>
      have hs : ∀ x ∈ c.state.flatMap (fun r => r.cells.filterMap id), x.val V = x.val V' :=
        fun x hx => h x (List.mem_append_left _ hx)
      have hf : ∀ x ∈ [c.s.x, c.s.y, c.nAcc], x.val V = x.val V' := fun x hx =>
        h x (List.mem_append_right _ hx)
      simp only [List.forall_mem_cons] at hf
      simp only [KimchiConstraint.Holds, hf.1, hf.2.1, hf.2.2.1]
      exact EndoMul.chainHolds_congr c.state hs
    | pad _ => exact Iff.rfl
  cells_equal _ _ := rfl
  cells_r1cs _ _ _ := rfl
  cells_square _ _ := rfl
  cells_boolean _ := rfl

/-- The kimchi constraint vocabulary, as a class over the carrier. NOT a backend
seam: kimchi is the terminal constraint layer, and the three instances below — the sum
itself, its soundness tag `Builder V c` and its completeness tag `Prover c` — are the
only three. The class exists because a triple elaborates the gadget body at a tag, so
the gadget definitions are polymorphic between exactly these carriers. One method per
landed gadget law. -/
class KimchiSystem (F c : Type) where
  /-- Embed a complete-addition payload. -/
  addComplete : AddComplete F → c
  /-- Embed a Poseidon block payload. -/
  poseidon : PoseidonConstraint F → c
  /-- Embed a challenge-decomposition payload. -/
  endoScalar : EndoScalar F → c
  /-- Embed an endomorphism-multiplication payload. -/
  endoMul : EndoMul F → c
  /-- Embed a variable-base scalar-multiplication payload. -/
  varBaseMul : VarBaseMul F → c

instance : KimchiSystem F (KimchiConstraint F) :=
  ⟨.addComplete, .poseidon, .endoScalar, .endoMul, .varBaseMul⟩

instance [inst : KimchiSystem F c] {V : Valuation F} :
    KimchiSystem F (Builder V c) := inst

instance [inst : KimchiSystem F c] : KimchiSystem F (Prover c) := inst

end Snarky.Kimchi
