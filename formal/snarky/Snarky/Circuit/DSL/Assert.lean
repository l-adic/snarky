import Snarky.Circuit.DSL.Boolean

/-!
# Assertion gadgets

Port of `Snarky.Circuit.DSL.Assert` (packages/snarky/src/Snarky/Circuit/DSL/Assert.purs):
constraints enforced without returning values — equality, non-zeroness (an inverse
witness, which is what fails on zero), squares, boolean assertions — plus the generic
`AssertEqual` class and `allBools`.

Name map (D7; underscores drop): `assertEqual_` → `assertEqual`, `assertNonZero_` →
`assertNonZero`, `assertNotEqual_` → `assertNotEqual`, `assertSquare_` → `assertSquare`,
`assert_` → `assert`, `assertAny_`/`assertAll_`/`assertExactlyOne_` drop likewise,
`allBools` keeps its PS name; the class method `assertEq` keeps its PS name — the barrel's
transitional `assertEq` is subsumed by the class (`FVar` call sites are unchanged).

Deviations from the PS original (per `formal/docs/snarky-ps-alignment.md`):
- PS CRASHES at circuit construction on impossible constant assertions (`unsafeThrow` on
  unequal constants in `assertEqual_`; on the constant zero through `inv_` in
  `assertNonZero_`). The total rendering emits the impossible constraint instead —
  `assertEqual` emits the unsatisfiable `equal` row verbatim, `assertNonZero` the
  canonical falsum `0 = 1` — so the prover rejects, and soundness treats the branch by
  contradiction.
- The `AssertEqual` class: fundeps unmodelled (house precedent); base instances only
  (`FVar`, `BoolVar`, `PUnit`, the pair — components FIRST THEN SECOND, PS order, unlike
  `IfThenElse`); the `Vector`/`Record` instances and the `GAssertEqual`/`RAssertEqual`
  deriving machinery land with their first consumers (D8; monadic vector traversal needs
  a kernel-reducible helper in `Snarky/Vec.lean` first).
- `allBools` keeps the OCaml/PS constant-FIRST argument order in its three-plus case
  (`equals (const n) (sum bs)`) — the order matters for the constraint's coefficient
  signs downstream.

D9 survey (the `snarky-test-utils` Assert spec), in the D12 form, laws beside their
gadgets: the `assertNonZero`/`assertEqual`/`assertNotEqual`/`assertSquare` rows land as
the `_sound`/`_complete` pairs below (`assert` gets its pair too — it is the workhorse
that pins a verifier's output bit). The sum-based `assertAny`/`assertAll`/
`assertExactlyOne` and `allBools`'s three-plus case share `any`/`all`'s standing
characteristic obligation (a sum of `n` bits detects `n` only below the characteristic)
and defer with it. Assertions allocate nothing (except `assertNonZero`'s inverse
witness), so their completeness laws are exact run equations, not existentials.

Public results: `assertEqual_sound`/`_complete`, `assertNonZero_sound`/`_complete`,
`assertNotEqual_sound`/`_complete`, `assertSquare_sound`/`_complete`,
`assert_sound`/`_complete` — all `roots.txt` entries.
-/

namespace Snarky

variable {F c : Type u}

/-! ## The gadgets -/

/-- Assert equality (PS `assertEqual_`): equal constants fold to nothing; unequal
constants emit the unsatisfiable `equal` row (PS crashes at construction instead);
otherwise one `equal` constraint. -/
def assertEqual [DecidableEq F] [BasicSystem F c] (x y : FVar F) : CircuitM F c PUnit :=
  match x, y with
  | .const f, .const g =>
    if f = g then pure PUnit.unit else addConstraint (BasicSystem.equal x y)
  | _, _ => addConstraint (BasicSystem.equal x y)

/-- Assert non-zeroness by witnessing the inverse (PS `assertNonZero_ = void ∘ inv_`):
a nonzero constant folds to nothing; the constant zero emits the canonical falsum
`0 = 1` (PS crashes at construction instead). -/
def assertNonZero [Field F] [DecidableEq F] [BasicSystem F c] (v : FVar F) :
    CircuitM F c PUnit :=
  match v with
  | .const f =>
    if f = 0 then addConstraint (BasicSystem.equal (.const 0 : CVar F) (.const 1))
    else pure PUnit.unit
  | _ => do
    let _ ← inv v
    pure PUnit.unit

/-- Assert inequality: the difference is nonzero (PS `assertNotEqual_`). -/
def assertNotEqual [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c PUnit :=
  assertNonZero (CVar.sub_ x y)

/-- Assert a square identity `x · x = y` with one dedicated constraint
(PS `assertSquare_`). -/
def assertSquare [BasicSystem F c] (x y : FVar F) : CircuitM F c PUnit :=
  addConstraint (BasicSystem.square x y)

/-- Assert a boolean holds: its bit equals `1` (PS `assert_`). -/
def assert [One F] [DecidableEq F] [BasicSystem F c] (v : BoolVar F) :
    CircuitM F c PUnit :=
  assertEqual ↑v (.const 1)

/-- Assert at least one bit is set: the bit-sum is nonzero (PS `assertAny_`, OCaml
`Boolean.Assert.any` — no two-element special case). -/
def assertAny [Field F] [DecidableEq F] [BasicSystem F c] (bs : List (BoolVar F)) :
    CircuitM F c PUnit :=
  assertNonZero (sum (bs.map BoolVar.toCVar))

/-- Assert exactly one bit is set: the bit-sum equals `1` (PS `assertExactlyOne_`,
OCaml `Boolean.Assert.exactly_one` — the one-hot validator). -/
def assertExactlyOne [Field F] [DecidableEq F] [BasicSystem F c]
    (bs : List (BoolVar F)) : CircuitM F c PUnit :=
  assertEqual (sum (bs.map BoolVar.toCVar)) (.const 1)

/-- Assert every bit is set: the bit-sum equals the length (PS `assertAll_`, OCaml
`Boolean.Assert.all`). -/
def assertAll [Field F] [DecidableEq F] [BasicSystem F c] (bs : List (BoolVar F)) :
    CircuitM F c PUnit :=
  assertEqual (sum (bs.map BoolVar.toCVar)) (.const (bs.length : F))

/-- AND a list of bits, `sum`-based beyond two elements (PS `allBools`, OCaml
`Boolean.all`): empty is true, a singleton is itself, a pair is `and`, and three or
more test the bit-sum against the length — constant FIRST, whose coefficient signs the
OCaml constraint depends on. -/
def allBools {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    (bs : List (BoolVar F)) : CircuitM F c (BoolVar F) :=
  match bs with
  | [] => pure true_
  | [b] => pure b
  | [b₁, b₂] => Snarky.and b₁ b₂
  | _ => equals (.const (bs.length : F)) (sum (bs.map BoolVar.toCVar))

/-! ## The `AssertEqual` class -/

/-- Generic equality assertion and test over variable bundles (PS `AssertEqual`;
fundeps unmodelled, the house precedent). -/
class AssertEqual (F c : Type) (var : Type) where
  /-- Assert componentwise equality (PS `assertEq`). -/
  assertEq : var → var → CircuitM F c PUnit
  /-- Test componentwise equality (PS `isEqual`). -/
  isEqual : var → var → CircuitM F c (BoolVar F)

export AssertEqual (assertEq isEqual)

/-- Field variables assert with `assertEqual` and test with `equals`. -/
instance {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] :
    AssertEqual F c (FVar F) where
  assertEq := assertEqual
  isEqual := equals

/-- Boolean variables assert and test through their field expressions (PS coerces). -/
instance {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] :
    AssertEqual F c (BoolVar F) where
  assertEq x y := assertEqual ↑x ↑y
  isEqual x y := equals ↑x ↑y

/-- Nothing to compare (PS `Unit` instance). -/
instance {F c : Type} [One F] : AssertEqual F c PUnit where
  assertEq _ _ := pure PUnit.unit
  isEqual _ _ := pure true_

/-- Pairs compare componentwise, first component THEN second — PS order (unlike
`IfThenElse`, which reverses). -/
instance {F c : Type} {a b : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [AssertEqual F c a] [AssertEqual F c b] :
    AssertEqual F c (a × b) where
  assertEq p q := do
    assertEq p.1 q.1
    assertEq p.2 q.2
  isEqual p q := do
    let r₁ ← isEqual p.1 q.1
    let r₂ ← isEqual p.2 q.2
    Snarky.and r₁ r₂

/-! ## The `assertEqual` laws (D12) -/

/-- The constant branch of `assertEqual`, over the syntactic `if`: satisfiable only
when the constants agree. -/
private theorem assertEqual_consts_sound {F : Type u} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] {f g : F} {nv : Nat} {env : Assignments F}
    (hsat : ∀ con ∈ (build (if f = g then (pure PUnit.unit : CircuitM F (Basic F) PUnit)
        else addConstraint (BasicSystem.equal (.const f) (.const g))) nv).constraints,
      con.holds env = true) :
    f = g := by
  split_ifs at hsat with hfg
  · exact hfg
  · obtain ⟨x, y, hx, hy, hxy⟩ := Basic.equal_inv (hsat _ (List.mem_cons_self ..))
    have hfx : f = x := by simpa [CVar.eval] using hx
    have hgy : g = y := by simpa [CVar.eval] using hy
    rw [hfx, hgy]
    exact hxy

/-- The general branch of `assertEqual`: the `equal` row forces the values equal. -/
private theorem assertEqual_row_sound {F : Type u} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hsat : ∀ con ∈ (build (addConstraint (BasicSystem.equal x y) :
        CircuitM F (Basic F) PUnit) nv).constraints, con.holds env = true)
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) : xv = yv := by
  obtain ⟨a, b, ha, hb, hab⟩ := Basic.equal_inv (hsat _ (List.mem_cons_self ..))
  rw [hx] at ha
  rw [hy] at hb
  injection ha with ha'
  injection hb with hb'
  rw [ha', hb']
  exact hab

/-- **`assertEqual` soundness** (D12): a satisfying assignment forces the operands'
values equal — through the fold, the unsatisfiable-constants row, and the general row. -/
theorem assertEqual_sound {F : Type u} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hsat : ∀ con ∈ (build (assertEqual (c := Basic F) x y) nv).constraints,
      con.holds env = true)
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) : xv = yv := by
  unfold assertEqual at hsat
  cases x <;> cases y <;>
    first
    | (rename_i f g
       have hf : f = xv := by simpa [CVar.eval] using hx
       have hg : g = yv := by simpa [CVar.eval] using hy
       rw [← hf, ← hg]
       exact assertEqual_consts_sound hsat)
    | exact assertEqual_row_sound hsat hx hy

/-- The general branch of `assertEqual`, completeness side: the check passes on equal
values. -/
private theorem assertEqual_row_run {F : Type u} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) (hxy : xv = yv) :
    prove Basic.holds (addConstraint (BasicSystem.equal x y) :
        CircuitM F (Basic F) PUnit) nv env = .ok ⟨PUnit.unit, nv, env⟩ := by
  have hch : Basic.holds (.equal x y) env = true := by
    simp [Basic.holds, hx, hy, hxy]
  show prove Basic.holds (.addConstraintOp (Basic.equal x y) (.pure PUnit.unit)) nv env = _
  simp only [prove, hch, if_true]

/-- The constant branch of `assertEqual`, completeness side. -/
private theorem assertEqual_consts_run {F : Type u} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] {f g : F} {nv : Nat} {env : Assignments F} (hfg : f = g) :
    prove Basic.holds (if f = g then (pure PUnit.unit : CircuitM F (Basic F) PUnit)
        else addConstraint (BasicSystem.equal (.const f) (.const g))) nv env
      = .ok ⟨PUnit.unit, nv, env⟩ := by
  rw [if_pos hfg]
  rfl

/-- **`assertEqual` completeness** (D12): on equal values the run succeeds, allocating
nothing — an exact equation. -/
theorem assertEqual_complete {F : Type u} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) (hxy : xv = yv) :
    prove Basic.holds (assertEqual (c := Basic F) x y) nv env
      = .ok ⟨PUnit.unit, nv, env⟩ := by
  unfold assertEqual
  cases x <;> cases y <;>
    first
    | (rename_i f g
       have hf : f = xv := by simpa [CVar.eval] using hx
       have hg : g = yv := by simpa [CVar.eval] using hy
       exact assertEqual_consts_run (by rw [hf, hg]; exact hxy))
    | exact assertEqual_row_run hx hy hxy

/-! ## The `assertNonZero` laws (D12) -/

/-- The constant branch of `assertNonZero`, over the syntactic `if`: satisfiable only
when the constant is nonzero (the zero branch carries the falsum `0 = 1`). -/
private theorem assertNonZero_consts_sound {F : Type u} [Field F] [DecidableEq F]
    {f : F} {nv : Nat} {env : Assignments F}
    (hsat : ∀ con ∈ (build (if f = 0
        then (addConstraint (BasicSystem.equal (.const 0 : CVar F) (.const 1)) :
          CircuitM F (Basic F) PUnit)
        else pure PUnit.unit) nv).constraints, con.holds env = true) :
    f ≠ 0 := by
  split_ifs at hsat with h0
  · obtain ⟨x, y, hx, hy, hxy⟩ := Basic.equal_inv (hsat _ (List.mem_cons_self ..))
    have h1 : (0 : F) = x := by simpa [CVar.eval] using hx
    have h2 : (1 : F) = y := by simpa [CVar.eval] using hy
    exact absurd (h1.trans (hxy.trans h2.symm)) zero_ne_one
  · exact h0

/-- The witnessing branch of `assertNonZero`: the inverse's `r1cs` row forces the value
nonzero (stated over `invCore`, which has no scrutinee — `build` reduces for any `v`). -/
private theorem assertNonZero_core_sound {F : Type u} [Field F] [DecidableEq F]
    {v : FVar F} {nv : Nat} {env : Assignments F} {vv : F}
    (hsat : ∀ con ∈ (build (invCore (c := Basic F) v >>= fun _ => pure PUnit.unit)
        nv).constraints, con.holds env = true)
    (hv : v.eval env = .ok vv) : vv ≠ 0 := by
  rw [build_bind] at hsat
  obtain ⟨a, b, o, ha, hb, ho, hab⟩ := Basic.r1cs_inv
    (hsat _ (List.mem_append_left _ (List.mem_cons_self ..)))
  rw [hv] at ha
  injection ha with ha'
  have ho' : (1 : F) = o := by simpa [CVar.eval] using ho
  rw [ha']
  exact left_ne_zero_of_mul_eq_one (ho'.symm ▸ hab)

/-- **`assertNonZero` soundness** (D12): a satisfying assignment forces the value
nonzero — through the folds and the inverse-witness row. -/
theorem assertNonZero_sound {F : Type u} [Field F] [DecidableEq F]
    {v : FVar F} {nv : Nat} {env : Assignments F} {vv : F}
    (hsat : ∀ con ∈ (build (assertNonZero (c := Basic F) v) nv).constraints,
      con.holds env = true)
    (hv : v.eval env = .ok vv) : vv ≠ 0 := by
  unfold assertNonZero at hsat
  cases v <;>
    first
    | (rename_i f
       have hf : f = vv := by simpa [CVar.eval] using hv
       rw [← hf]
       exact assertNonZero_consts_sound hsat)
    | exact assertNonZero_core_sound hsat hv

/-- The witnessing branch of `assertNonZero`, completeness side. -/
private theorem assertNonZero_core_run {F : Type u} [Field F] [DecidableEq F]
    {v : FVar F} {nv : Nat} {env : Assignments F} {vv : F}
    (hfresh : env.FreshFrom nv) (hv : v.eval env = .ok vv) (hvv : vv ≠ 0) :
    ∃ out, prove Basic.holds (inv (c := Basic F) v >>= fun _ => pure PUnit.unit) nv env
        = .ok out ∧ out.assignments.FreshFrom out.nextVar := by
  rw [prove_bind]
  obtain ⟨o₁, hr₁, he₁, hf₁⟩ := inv_complete hfresh hv hvv
  rw [hr₁]
  exact ⟨⟨PUnit.unit, o₁.nextVar, o₁.assignments⟩, rfl, hf₁⟩

/-- **`assertNonZero` completeness** (D12): on a nonzero value the run succeeds and
re-establishes freshness. -/
theorem assertNonZero_complete {F : Type u} [Field F] [DecidableEq F]
    {v : FVar F} {nv : Nat} {env : Assignments F} {vv : F}
    (hfresh : env.FreshFrom nv) (hv : v.eval env = .ok vv) (hvv : vv ≠ 0) :
    ∃ out, prove Basic.holds (assertNonZero (c := Basic F) v) nv env = .ok out ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold assertNonZero
  cases v <;>
    first
    | (rename_i f
       have hf : f = vv := by simpa [CVar.eval] using hv
       refine ⟨⟨PUnit.unit, nv, env⟩, ?_, hfresh⟩
       show prove Basic.holds (if f = 0
           then (addConstraint (BasicSystem.equal (.const 0 : CVar F) (.const 1)) :
             CircuitM F (Basic F) PUnit)
           else pure PUnit.unit) nv env = _
       rw [if_neg (by rw [hf]; exact hvv)]
       rfl)
    | exact assertNonZero_core_run hfresh hv hvv

/-! ## The `assertNotEqual`, `assertSquare`, and `assert` laws (D12) -/

/-- **`assertNotEqual` soundness** (D12), composed from `assertNonZero`. -/
theorem assertNotEqual_sound {F : Type u} [Field F] [DecidableEq F]
    {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hsat : ∀ con ∈ (build (assertNotEqual (c := Basic F) x y) nv).constraints,
      con.holds env = true)
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) : xv ≠ yv := by
  unfold assertNotEqual at hsat
  exact sub_ne_zero.mp (assertNonZero_sound hsat (CVar.eval_sub_ hx hy))

/-- **`assertNotEqual` completeness** (D12), composed from `assertNonZero`. -/
theorem assertNotEqual_complete {F : Type u} [Field F] [DecidableEq F]
    {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hfresh : env.FreshFrom nv)
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) (hne : xv ≠ yv) :
    ∃ out, prove Basic.holds (assertNotEqual (c := Basic F) x y) nv env = .ok out ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold assertNotEqual
  exact assertNonZero_complete hfresh (CVar.eval_sub_ hx hy) (sub_ne_zero.mpr hne)

/-- **`assertSquare` soundness** (D12): the row forces the square identity. -/
theorem assertSquare_sound {F : Type u} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hsat : ∀ con ∈ (build (assertSquare (c := Basic F) x y) nv).constraints,
      con.holds env = true)
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) : xv * xv = yv := by
  obtain ⟨a, z, ha, hz, hsq⟩ := Basic.square_inv (hsat _ (List.mem_cons_self ..))
  rw [hx] at ha
  rw [hy] at hz
  injection ha with ha'
  injection hz with hz'
  rw [ha', hz']
  exact hsq

/-- **`assertSquare` completeness** (D12): an exact run equation on a true square. -/
theorem assertSquare_complete {F : Type u} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) (hsq : xv * xv = yv) :
    prove Basic.holds (assertSquare (c := Basic F) x y) nv env
      = .ok ⟨PUnit.unit, nv, env⟩ := by
  have hch : Basic.holds (.square x y) env = true := by
    simp [Basic.holds, hx, hy, hsq]
  show prove Basic.holds (.addConstraintOp (Basic.square x y) (.pure PUnit.unit)) nv env
    = _
  simp only [prove, hch, if_true]

/-- **`assert` soundness** (D12): a satisfying assignment forces the bit true — the
law that pins a verifier's output bit. -/
theorem assert_sound {F : Type u} [Field F] [DecidableEq F]
    {v : BoolVar F} {nv : Nat} {env : Assignments F} {ab : Bool}
    (hsat : ∀ con ∈ (build (assert (c := Basic F) v) nv).constraints,
      con.holds env = true)
    (hv : (↑v : CVar F).eval env = .ok (bit ab)) : ab = true := by
  unfold assert at hsat
  have h := assertEqual_sound hsat hv (rfl : (CVar.const (1 : F)).eval env = .ok 1)
  cases ab
  · exact absurd h (by simp [bit])
  · rfl

/-- **`assert` completeness** (D12): an exact run equation on a true bit. -/
theorem assert_complete {F : Type u} [Field F] [DecidableEq F]
    {v : BoolVar F} {nv : Nat} {env : Assignments F} {ab : Bool}
    (hv : (↑v : CVar F).eval env = .ok (bit ab)) (hab : ab = true) :
    prove Basic.holds (assert (c := Basic F) v) nv env = .ok ⟨PUnit.unit, nv, env⟩ := by
  unfold assert
  exact assertEqual_complete hv (rfl : (CVar.const (1 : F)).eval env = .ok 1)
    (by rw [hab]; simp [bit])

end Snarky
