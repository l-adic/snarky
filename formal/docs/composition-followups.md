# Composition-proof follow-ups: plans for #4 and #6

Two planned extensions to the `Circuits/*Step.lean` composition proofs. **Not yet implemented** —
this document is the design. The four gates now have: reconstructed-circuit soundness
(`circuit_sound`, wiring + gate identities derived from `Satisfies`), Pasta specializations
(curve non-degeneracy discharged), dump-validated reconstructions (`CheckReconstruction.lean`), and
heterogeneous pair examples (`Combinations.lean`). What remains is (#4) sourcing the *initial state*
from the circuit too, and (#6) lifting the resulting integer scalar into the scalar field.

---

## #4 — Ground the init in public-input / setup rows

### The gap
Each composition theorem still takes the chain's **initial state** as a hypothesis rather than
deriving it from `Satisfies`:

| Gate | Init hypothesis | Real dump's source rows (from the fixtures) |
| --- | --- | --- |
| VarBaseMul | `hinit : P₀ = a•T` (here `a = 2`) | row 5 `CompleteAdd` (base doubling `[2]T`) + rows 0–4 `Generic` (public base) |
| EndoMul | `hP0 : P₀ = 2•T + 2•φT` | rows 6–7 `CompleteAdd` (two adds) + rows 0–5 `Generic` |
| EndoScalar | `ha0/hb0/hn0 : (a₀,b₀,n₀) = (2,2,0)` | rows 0–2 `Generic` (constant-pinning rows) |

`AddCompleteStep.lean` already shows the technique: its `addCompleteCircuit` prepends six `genPub`
`Generic` rows, and `addComplete_sound` derives `w.cell (6,k) = pub[k]` from `gatesHold`
(`Generic.eval` on a `[1,0,0,0,0]` coeff row) + `copyHolds` (the public value carried into the
gate's input cell). Reuse that pattern.

### Plan, easiest first

**(a) EndoScalar — the clean case (constants, no EC).** The init `(2,2,0)` are *constants*, so the
setup rows are `Generic` gates whose coefficient row pins the constant and whose wire copies it into
row 0's input cells (cols 2/3/0).
1. Define `esInitGate (c : F) (target : Cell) : Gate F` — a `Generic` gate `coeffs = [0,0,0,0,c]`
   (constant term) or `[1,0,0,0,-c]` reading nothing, i.e. asserting `w[r][0] = c`, wired to the
   first EndoMulScalar row's input cell.  Cross-check the exact coeff layout against the real
   `endoscalar_step` fixture rows 0–2 (`Kimchi.Json` already parses them; read them with a small
   `#eval`).
2. Define `esCircuitGrounded m` = `#[initA0, initB0, initN0] ++ esCircuit m`'s gates, with the init
   rows wired to row 3's cols 2/3/0.
3. Prove `esCircuitGrounded_sound`: from `Satisfies` derive `ha0/hb0/hn0` exactly as
   `addComplete_sound` derives its `key`, then call `circuit_sound`. Result: soundness with **no
   init hypotheses**.
4. Add a `CheckReconstruction` case: slice `endoscalar_step` rows 0–10 and confirm
   `esCircuitGrounded 7` accepts — validating the setup-row wiring against the dump.

**(b) VarBaseMul / EndoMul — the EC init.** Here the init is produced by `CompleteAdd` rows, so
grounding must *compose the AddComplete soundness* for those rows:
1. Prepend the init `CompleteAdd` row(s) to `vbmCircuit` / `emCircuit`, wired so the doubling's
   inputs are the (public) base `T` and its output feeds gate 0's input accumulator.
2. From `Satisfies`, extract the `CompleteAdd` row's `AddComplete.Holds` (via
   `rowHolds_completeAdd`) and apply `AddComplete.sound_point_noninf` to get
   `P_out = T + T = [2]•T`, with the output nonsingularity **produced** (existential).
3. Thread that produced nonsingularity into `RowCurve.a0` / `GateStep.a0` of gate 0 (the copy
   constraint equates the CompleteAdd output cells with gate 0's `x0,y0`), discharging `hinit`.
4. EndoMul needs two adds (`2•T` then `+2•φT`); reuse the same step twice. `φT` requires the
   `pallas_endo`/`pallas_eigen` handle already used in `pallas_endoMul_circuit`.

### Deliverable
`*_circuit_grounded_sound` per gate with the init hypotheses removed, plus reconstruction-check
cases over the full fixtures (including the setup rows). Register the new roots in
`scripts/check_axioms.lean`.

### Effort / risk
EndoScalar: low (mirrors `addComplete_sound`). VarBaseMul/EndoMul: medium — the AddComplete-output
→ gate-0-input threading through the produced nonsingularity is the delicate part; the copy
constraint gives coordinate equality, and `some_congr` (already in `Curve.lean`) lines up the
`Point.some` terms.

---

## #6 — Scalar-field lift (the 2-cycle account)

### The gap
`circuit_sound` concludes `P_final = n • T` with **`n : ℤ`** (a signed-digit integer, bounded by
`32^m`/`4^m`). The genuine scalar of a scalar multiplication lives in the **scalar field**
`ZMod q`, `q = W.order` — and for the Pasta 2-cycle, `q` of one curve is the *base field
characteristic of the other*. Lifting `n` to its residue mod `q` is the cross-field bridge Pickles'
Step/Wrap recursion consumes. (Note: there is no `Kimchi/Cycle/` on this branch; CLAUDE.md's Cycle
section is aspirational. The tools below already exist in `Curve.lean`.)

### The tools (already proven, no new axioms)
- `WeierstrassCurve.Affine.order W : ℕ := Nat.card W.Point`.
- `order_smul : (W.order : ℤ) • P = 0` — the order annihilates every point (from Lagrange; **not**
  an axiom).
- `zsmul_mod : n • P = (n % W.order) • P` — reduce an integer scalar mod the order.
- `Kimchi.Pasta.{pallas,vesta}_card` — the concrete Pasta orders (derived from the Hasse-bound
  axioms).

### Plan
1. **Generic `_scalar` lift.** For each gate's `circuit_sound`/Pasta specialization producing
   `P_final = n • T`, derive `P_final = (n % W.order) • T` by `rw [zsmul_mod]`, and expose the
   canonical residue `s := (n % W.order)` with `0 ≤ s < W.order`. This is a thin wrapper theorem
   `*_scalar : P_final = s • T ∧ s = n % W.order ∧ 0 ≤ s < W.order`.
2. **Uniqueness mod order.** Show the scalar is *well-defined* independent of the witness's
   signed-digit representation: two satisfying witnesses with the same challenge give scalars
   congruent mod `W.order` (they annihilate to the same point). This is the honest "the circuit
   computes a scalar-field element" statement. `EndoScalar.endoScalar_unique` already does the
   analogous thing for the effective scalar under a no-wrap bound; port that shape.
3. **Pasta 2-cycle instantiation.** Specialize `s : ZMod (Pallas.order)`. Since
   `Pallas.order = Vesta`'s base-field characteristic (state and prove the numeral equality from
   `pallas_card`/`vesta_card`), the Pallas scalar-mul's scalar is a *Vesta base-field element* —
   the cross-field value the Wrap verifier reads. Deliver `pallas_*_scalar_vesta : (s : VestaBaseField) = …`.
4. **Tie to the shifted-scalar contract.** `VarBaseMul.scalarMul_shifted` / `EndoScalar.toField`
   already give the pickles `Shifted_value` form (`2t + 2^numBits + 1`). Compose the mod-order
   reduction with that so the final statement is `[unshift(s)]•T` with `unshift(s)` a genuine
   scalar-field element — closing the loop to the Pickles `Type1`/`Type2` shifting the
   `pickles-expert` skill documents.

### Deliverable
`*_scalar` wrappers (generic, mod-`order`) and their Pasta 2-cycle instantiations mapping the
scalar into the sister curve's base field, plus the uniqueness-mod-order statement. No new axioms
(only the existing Pasta Hasse bounds, already in the allowlist). Register roots in
`check_axioms.lean`.

### Effort / risk
Step 1 is low (a `zsmul_mod` rewrite). Steps 2–3 are medium: the numeral equality
`Pallas.order = VestaBaseField characteristic` must be proved from the concrete cards (a
`decide`/`norm_num` over the committed constants), and the uniqueness argument needs a no-wrap /
range bound analogous to `endoScalar_unique`'s `4^#crumbs ≤ p`.
