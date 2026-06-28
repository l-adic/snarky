import Kimchi.Checker.Row

/-! # The kimchi `Poseidon` gate (5 rounds per row).

Transcribed from proof-systems `.../polynomials/poseidon.rs` (15 constraints = 5 rounds × 3
state elements). Each round applies `state' = MDS · sbox(state) + roundConstants`, with the
S-box `sbox(x) = x⁷` (Pasta `PERM_SBOX = 7`) and the 3×3 `MDS` matrix below (the Pasta `fp`
kimchi constants). The 15 round constants are the gate's coefficient row `c[0..14]`.

Witness column layout (the kimchi permuted order, `STATE_ORDER = [0,2,3,4,1]`):
round inputs/outputs live at curr cols `0..2`(s0), `6..8`(s1), `9..11`(s2), `12..14`(s3),
`3..5`(s4), and next row cols `0..2`(s5). The five rounds chain:
`s0→s1→s2→s3→s4→s5`. -/

namespace Kimchi.Gate.Poseidon

variable {F : Type*}

/-! ## The 3×3 MDS matrix (Pasta `fp` kimchi constants). -/
def m00 [CommRing F] : F :=
  12035446894107573964500871153637039653510326950134440362813193268448863222019
def m01 [CommRing F] : F :=
  25461374787957152039031444204194007219326765802730624564074257060397341542093
def m02 [CommRing F] : F :=
  27667907157110496066452777015908813333407980290333709698851344970789663080149
def m10 [CommRing F] : F :=
  4491931056866994439025447213644536587424785196363427220456343191847333476930
def m11 [CommRing F] : F :=
  14743631939509747387607291926699970421064627808101543132147270746750887019919
def m12 [CommRing F] : F :=
  9448400033389617131295304336481030167723486090288313334230651810071857784477
def m20 [CommRing F] : F :=
  10525578725509990281643336361904863911009900817790387635342941550657754064843
def m21 [CommRing F] : F :=
  27437632000253211280915908546961303399777448677029255413769125486614773776695
def m22 [CommRing F] : F :=
  27566319851776897085443681456689352477426926500749993803132851225169606086988

/-- One full round: outputs `(o0,o1,o2) = MDS · sbox(x0,x1,x2) + (r0,r1,r2)`. -/
def roundHolds [CommRing F] (x0 x1 x2 o0 o1 o2 r0 r1 r2 : F) : Prop :=
  o0 - (r0 + m00 * x0 ^ 7 + m01 * x1 ^ 7 + m02 * x2 ^ 7) = 0
  ∧ o1 - (r1 + m10 * x0 ^ 7 + m11 * x1 ^ 7 + m12 * x2 ^ 7) = 0
  ∧ o2 - (r2 + m20 * x0 ^ 7 + m21 * x1 ^ 7 + m22 * x2 ^ 7) = 0

def roundOk [CommRing F] [DecidableEq F] (x0 x1 x2 o0 o1 o2 r0 r1 r2 : F) : Bool :=
  (o0 - (r0 + m00 * x0 ^ 7 + m01 * x1 ^ 7 + m02 * x2 ^ 7) == 0)
  && (o1 - (r1 + m10 * x0 ^ 7 + m11 * x1 ^ 7 + m12 * x2 ^ 7) == 0)
  && (o2 - (r2 + m20 * x0 ^ 7 + m21 * x1 ^ 7 + m22 * x2 ^ 7) == 0)

theorem roundOk_iff [CommRing F] [DecidableEq F] (x0 x1 x2 o0 o1 o2 r0 r1 r2 : F) :
    roundOk x0 x1 x2 o0 o1 o2 r0 r1 r2 = true ↔ roundHolds x0 x1 x2 o0 o1 o2 r0 r1 r2 := by
  simp only [roundOk, roundHolds, Bool.and_eq_true, beq_iff_eq, and_assoc]

def holds [CommRing F] (coeffs : Array F) (curr next : Row F) : Prop :=
  let w := fun i => curr.getD i 0
  let wn := fun i => next.getD i 0
  let c := fun i => coeffs.getD i 0
  roundHolds (w 0) (w 1) (w 2) (w 6) (w 7) (w 8) (c 0) (c 1) (c 2)
  ∧ roundHolds (w 6) (w 7) (w 8) (w 9) (w 10) (w 11) (c 3) (c 4) (c 5)
  ∧ roundHolds (w 9) (w 10) (w 11) (w 12) (w 13) (w 14) (c 6) (c 7) (c 8)
  ∧ roundHolds (w 12) (w 13) (w 14) (w 3) (w 4) (w 5) (c 9) (c 10) (c 11)
  ∧ roundHolds (w 3) (w 4) (w 5) (wn 0) (wn 1) (wn 2) (c 12) (c 13) (c 14)

def ok [CommRing F] [DecidableEq F] (coeffs : Array F) (curr next : Row F) : Bool :=
  let w := fun i => curr.getD i 0
  let wn := fun i => next.getD i 0
  let c := fun i => coeffs.getD i 0
  roundOk (w 0) (w 1) (w 2) (w 6) (w 7) (w 8) (c 0) (c 1) (c 2)
  && roundOk (w 6) (w 7) (w 8) (w 9) (w 10) (w 11) (c 3) (c 4) (c 5)
  && roundOk (w 9) (w 10) (w 11) (w 12) (w 13) (w 14) (c 6) (c 7) (c 8)
  && roundOk (w 12) (w 13) (w 14) (w 3) (w 4) (w 5) (c 9) (c 10) (c 11)
  && roundOk (w 3) (w 4) (w 5) (wn 0) (wn 1) (wn 2) (c 12) (c 13) (c 14)

theorem ok_iff [CommRing F] [DecidableEq F] (coeffs : Array F) (curr next : Row F) :
    ok coeffs curr next = true ↔ holds coeffs curr next := by
  simp only [ok, holds, roundOk_iff, Bool.and_eq_true, and_assoc]

end Kimchi.Gate.Poseidon
