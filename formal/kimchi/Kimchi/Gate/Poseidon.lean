import Mathlib

/-! # The kimchi `Poseidon` gate (5 rounds per row).

Transcribed from proof-systems `.../polynomials/poseidon.rs` (15 constraints = 5 rounds × 3
state elements). Each round maps the 3-element state through
`state' = MDS · sbox(state) + roundConstants`, with the S-box `sbox(x) = x⁷` (Pasta
`PERM_SBOX = 7`) and a 3×3 `MDS` matrix carried as a PARAMETER (`Mds F`): production
evaluates the gate with `G::sponge_params().mds`, a DIFFERENT table per curve (`fp_kimchi`
for Vesta proofs, `fq_kimchi` for Pallas proofs), so the matrix is gate data, not gate
constants — exactly like `EndoMul`'s endomorphism coefficient. The five rounds chain
`s0 → s1 → s2 → s3 → s4 → s5`, so one gate row applies five permutation rounds.

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

/-! ## The 3×3 MDS matrix, as gate data. -/

/-- The 3×3 MDS matrix of the round function — per-curve data
(`G::sponge_params().mds`), one named field per entry. -/
structure Mds (F : Type*) where
  /-- The MDS matrix entry at row 0, column 0. -/
  m00 : F
  /-- The MDS matrix entry at row 0, column 1. -/
  m01 : F
  /-- The MDS matrix entry at row 0, column 2. -/
  m02 : F
  /-- The MDS matrix entry at row 1, column 0. -/
  m10 : F
  /-- The MDS matrix entry at row 1, column 1. -/
  m11 : F
  /-- The MDS matrix entry at row 1, column 2. -/
  m12 : F
  /-- The MDS matrix entry at row 2, column 0. -/
  m20 : F
  /-- The MDS matrix entry at row 2, column 1. -/
  m21 : F
  /-- The MDS matrix entry at row 2, column 2. -/
  m22 : F

/-- Map `f` over every matrix entry. -/
def Mds.map {R S : Type*} (f : R → S) (M : Mds R) : Mds S where
  m00 := f M.m00
  m01 := f M.m01
  m02 := f M.m02
  m10 := f M.m10
  m11 := f M.m11
  m12 := f M.m12
  m20 := f M.m20
  m21 := f M.m21
  m22 := f M.m22

/-! ## The round function and the 5-round permutation. -/

/-- The S-box: `x ↦ x⁷` (Pasta `PERM_SBOX = 7`). -/
def sbox [CommRing F] (x : F) : F := x ^ 7

/-- One full round: `state' = MDS · sbox(state) + roundConstants`. -/
def round [CommRing F] (M : Mds F) (s r : F × F × F) : F × F × F :=
  (r.1 + M.m00 * sbox s.1 + M.m01 * sbox s.2.1 + M.m02 * sbox s.2.2,
   r.2.1 + M.m10 * sbox s.1 + M.m11 * sbox s.2.1 + M.m12 * sbox s.2.2,
   r.2.2 + M.m20 * sbox s.1 + M.m21 * sbox s.2.1 + M.m22 * sbox s.2.2)

/-- The gate's 5-round permutation of the initial state. -/
def perm [CommRing F] (M : Mds F) (s0 : F × F × F) (rc : Fin 5 → F × F × F) : F × F × F :=
  round M (round M (round M (round M (round M s0 (rc 0)) (rc 1)) (rc 2)) (rc 3)) (rc 4)

/-! ## Witness and constraint model. -/

/-- One `Poseidon` row: the six chained 3-element states, `s0` (input) through `s5` (output). -/
structure Witness (F : Type*) where
  /-- The 3-element input state, fed to round 0. -/
  s0 : F × F × F
  /-- The state after round 0. -/
  s1 : F × F × F
  /-- The state after round 1. -/
  s2 : F × F × F
  /-- The state after round 2. -/
  s3 : F × F × F
  /-- The state after round 3. -/
  s4 : F × F × F
  /-- The output state, after round 4. -/
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
def constraints [CommRing F] (M : Mds F) (rc : Fin 5 → F × F × F) (w : Witness F) : List F :=
  [ w.s1.1 - (round M w.s0 (rc 0)).1, w.s1.2.1 - (round M w.s0 (rc 0)).2.1,
    w.s1.2.2 - (round M w.s0 (rc 0)).2.2,
    w.s2.1 - (round M w.s1 (rc 1)).1, w.s2.2.1 - (round M w.s1 (rc 1)).2.1,
    w.s2.2.2 - (round M w.s1 (rc 1)).2.2,
    w.s3.1 - (round M w.s2 (rc 2)).1, w.s3.2.1 - (round M w.s2 (rc 2)).2.1,
    w.s3.2.2 - (round M w.s2 (rc 2)).2.2,
    w.s4.1 - (round M w.s3 (rc 3)).1, w.s4.2.1 - (round M w.s3 (rc 3)).2.1,
    w.s4.2.2 - (round M w.s3 (rc 3)).2.2,
    w.s5.1 - (round M w.s4 (rc 4)).1, w.s5.2.1 - (round M w.s4 (rc 4)).2.1,
    w.s5.2.2 - (round M w.s4 (rc 4)).2.2 ]

/-- Naturality of the constraint list: a ring hom `f` distributes over all 15 constraint
    expressions, so mapping `f` over `constraints rc w` equals the constraints of the mapped
    round constants and mapped witness. -/
theorem constraints_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Mds R) (rc : Fin 5 → R × R × R) (w : Witness R) :
    (constraints M rc w).map f
      = constraints (M.map f) (fun j => (f (rc j).1, f (rc j).2.1, f (rc j).2.2))
          (Witness.map f w) := by
  simp [constraints, round, sbox, Witness.map, Mds.map]

/-- RELATIONAL spec: all 15 constraint expressions vanish. -/
def Holds [CommRing F] (M : Mds F) (rc : Fin 5 → F × F × F) (w : Witness F) : Prop :=
  ∀ e ∈ constraints M rc w, e = 0

instance [CommRing F] [DecidableEq F] (M : Mds F) (rc : Fin 5 → F × F × F) (w : Witness F) :
    Decidable (Holds M rc w) := by
  unfold Holds
  infer_instance

/-- Executable checker: every constraint expression is zero. -/
def ok [CommRing F] [DecidableEq F] (M : Mds F) (rc : Fin 5 → F × F × F) (w : Witness F) :
    Bool :=
  (constraints M rc w).all (· == 0)

/-- Reflection: the `Bool` checker agrees with the relational spec. -/
theorem ok_iff [CommRing F] [DecidableEq F] (M : Mds F) (rc : Fin 5 → F × F × F)
    (w : Witness F) :
    ok M rc w = true ↔ Holds M rc w := by
  simp only [ok, Holds, List.all_eq_true, beq_iff_eq]

end Kimchi.Gate.Poseidon
