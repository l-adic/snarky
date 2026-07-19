import Mathlib

/-! # The kimchi `Poseidon` gate (5 rounds per row).

Transcribed from proof-systems `.../polynomials/poseidon.rs` (15 constraints = 5 rounds × 3
state elements). Each round maps the 3-element state through
`state' = MDS · sbox(state) + roundConstants`, with the S-box `sbox(x) = x⁷` (Pasta
`PERM_SBOX = 7`) and the 3×3 `MDS` matrix below (the Pasta `fp` kimchi constants). The five
rounds chain `s0 → s1 → s2 → s3 → s4 → s5`, so one gate row applies five permutation rounds.

Unlike the elliptic-curve gates there is no external Mathlib spec: the gate *defines* the
permutation. Soundness (`sound`) is therefore that a satisfying witness's output state is the
5-round permutation `perm` of its input state, and completeness (`complete`) is that the honest
witness built by iterating `round` satisfies the constraints.

The witness holds the six 3-element states `s0 .. s5` (`s0` = input, `s5` = output); the 15
round constants are the gate's coefficient row, supplied as `rc : Fin 5 → F × F × F`. The
mapping of these states/constants onto the dumped 15-column row is a *checker* concern and lives
with the ingestion layer, not here. -/

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

/-! ## The round function and the 5-round permutation. -/

/-- The S-box: `x ↦ x⁷` (Pasta `PERM_SBOX = 7`). -/
def sbox [CommRing F] (x : F) : F := x ^ 7

/-- One full round: `state' = MDS · sbox(state) + roundConstants`. -/
def round [CommRing F] (s r : F × F × F) : F × F × F :=
  (r.1 + m00 * sbox s.1 + m01 * sbox s.2.1 + m02 * sbox s.2.2,
   r.2.1 + m10 * sbox s.1 + m11 * sbox s.2.1 + m12 * sbox s.2.2,
   r.2.2 + m20 * sbox s.1 + m21 * sbox s.2.1 + m22 * sbox s.2.2)

/-- The gate's 5-round permutation of the initial state. -/
def perm [CommRing F] (s0 : F × F × F) (rc : Fin 5 → F × F × F) : F × F × F :=
  round (round (round (round (round s0 (rc 0)) (rc 1)) (rc 2)) (rc 3)) (rc 4)

/-! ## Witness and constraint model. -/

/-- One `Poseidon` row: the six chained 3-element states, `s0` (input) through `s5` (output). -/
structure Witness (F : Type*) where
  s0 : F × F × F
  s1 : F × F × F
  s2 : F × F × F
  s3 : F × F × F
  s4 : F × F × F
  s5 : F × F × F

/-- Map `f` componentwise across all six state triples of a witness. -/
def Witness.map {R S : Type*} (f : R → S) (w : Witness R) : Witness S where
  s0 := (f w.s0.1, f w.s0.2.1, f w.s0.2.2)
  s1 := (f w.s1.1, f w.s1.2.1, f w.s1.2.2)
  s2 := (f w.s2.1, f w.s2.2.1, f w.s2.2.2)
  s3 := (f w.s3.1, f w.s3.2.1, f w.s3.2.2)
  s4 := (f w.s4.1, f w.s4.2.1, f w.s4.2.2)
  s5 := (f w.s5.1, f w.s5.2.1, f w.s5.2.2)

/-- The 15 constraint expressions: for each of the five rounds, the three components of
    `sᵢ₊₁ − round(sᵢ, rcᵢ)`. -/
def constraints [CommRing F] (rc : Fin 5 → F × F × F) (w : Witness F) : List F :=
  [ w.s1.1 - (round w.s0 (rc 0)).1, w.s1.2.1 - (round w.s0 (rc 0)).2.1,
    w.s1.2.2 - (round w.s0 (rc 0)).2.2,
    w.s2.1 - (round w.s1 (rc 1)).1, w.s2.2.1 - (round w.s1 (rc 1)).2.1,
    w.s2.2.2 - (round w.s1 (rc 1)).2.2,
    w.s3.1 - (round w.s2 (rc 2)).1, w.s3.2.1 - (round w.s2 (rc 2)).2.1,
    w.s3.2.2 - (round w.s2 (rc 2)).2.2,
    w.s4.1 - (round w.s3 (rc 3)).1, w.s4.2.1 - (round w.s3 (rc 3)).2.1,
    w.s4.2.2 - (round w.s3 (rc 3)).2.2,
    w.s5.1 - (round w.s4 (rc 4)).1, w.s5.2.1 - (round w.s4 (rc 4)).2.1,
    w.s5.2.2 - (round w.s4 (rc 4)).2.2 ]

/-- Naturality of the constraint list: a ring hom `f` distributes over all 15 constraint
    expressions, so mapping `f` over `constraints rc w` equals the constraints of the mapped
    round constants and mapped witness. -/
theorem constraints_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (rc : Fin 5 → R × R × R) (w : Witness R) :
    (constraints rc w).map f
      = constraints (fun j => (f (rc j).1, f (rc j).2.1, f (rc j).2.2)) (Witness.map f w) := by
  simp [constraints, round, sbox, Witness.map, map_ofNat, m00, m01, m02, m10, m11, m12,
    m20, m21, m22]

/-- RELATIONAL spec: all 15 constraint expressions vanish. -/
def Holds [CommRing F] (rc : Fin 5 → F × F × F) (w : Witness F) : Prop :=
  ∀ e ∈ constraints rc w, e = 0

instance [CommRing F] [DecidableEq F] (rc : Fin 5 → F × F × F) (w : Witness F) :
    Decidable (Holds rc w) := by
  unfold Holds
  infer_instance

/-- Executable checker: every constraint expression is zero. -/
def ok [CommRing F] [DecidableEq F] (rc : Fin 5 → F × F × F) (w : Witness F) : Bool :=
  (constraints rc w).all (· == 0)

/-- Reflection: the `Bool` checker agrees with the relational spec. -/
theorem ok_iff [CommRing F] [DecidableEq F] (rc : Fin 5 → F × F × F) (w : Witness F) :
    ok rc w = true ↔ Holds rc w := by
  simp only [ok, Holds, List.all_eq_true, beq_iff_eq]

end Kimchi.Gate.Poseidon
