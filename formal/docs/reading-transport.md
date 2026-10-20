# Carrying readings across a run

A law at the prover's reading (`Snarky/Prover/WP.lean`) states its result at its exit table in
terms of its operands at its entry table. `Prover.mul_spec`, for one:

```lean
⦃⌜st = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀⌝⦄ mul x y
⦃⇓ r st' => ⌜r.Scoped st' ∧ st'.read r = st₀.read x * st₀.read y ∧ st₀ ≤ st'⌝⦄
```

Composed, n steps leave n tables `s₀ ≤ s₁ ≤ … ≤ sₙ` with one step fact `sᵢ₋₁ ≤ sᵢ` each, and
every reading is stated at the table that made it. A cell made at `sᵢ` and read at a later `u`
is carried there by `ProverState.read_of_le`, whose side condition is `sᵢ ≤ u`.

## Three ways to carry, measured

GroupMap's laws (`Snarky/Kimchi/Circuit/GroupMap.lean`) are the measurement: the candidates
stage (10 steps), the selection stage (10 steps over 9 input cells), and the map's law over its
4 stages.

- **By hand.** One fact per cell, `∀ u, sᵢ ≤ u → u.read rᵢ = <closed form>`, each proved from its
  step's equation and the earlier facts, at order facts built as `.trans` chains.
- **By conditional rewriting with `order`.** `ProverState.read_of_le _ h`, partially applied to
  the scope fact `h : rᵢ.Scoped sᵢ`, is the rewrite `?u.read rᵢ = sᵢ.read rᵢ` under the side
  condition `sᵢ ≤ ?u`. `simp (disch := order) only [ProverState.read_of_le _ h, …, the step
  equations]` unwinds every reading by normalization, and nothing is named.
- **By conditional rewriting with `le_chain`.** The same `simp` line, discharged by `le_chain`
  (`Snarky/Prover/WP.lean`), which walks back from the later table along the step facts.

Whole-proof cost on v4.30, in thousands of `maxHeartbeats` units, where the default budget of
200 000 is 200:

| Law | by hand | `order` | `le_rfl`, `assumption`, then `order` | `le_chain` |
|---|---|---|---|---|
| candidates | 50 | 128 | 74 | 53 |
| selection | 83 | 478, over budget | 187 | 113 |
| map | 38 | 172 | 83 | 47 |

With a discharger that does no work, the rewriting alone costs 42, 95 and 54, so `order` is the
cost, for two reasons. `simp` attempts the side condition once per occurrence, including the
trivial `sᵢ ≤ sᵢ` at every reading it has already carried, and each `order` call rebuilds its
graph from the whole context. `le_chain` closes `sᵢ ≤ sᵢ` by `le_rfl` and a one-step fact by
`assumption`, and walks the rest one hypothesis at a time.

Proof lines, by hand against `le_chain`: candidates 79 and 33, selection 68 and 41, map 50
and 44. The 31 named facts become 4 and the 75 `.trans` steps go.

## Measuring

`#count_heartbeats in` alone does not see a tactic proof, which elaborates asynchronously;
measure with `set_option Elab.async false in` beneath it. The command also sets
`maxHeartbeats 0`, so an over-budget proof still compiles under it: read its "greater than the
current maximum" line.

## The toolchain case

Lean's `vcgen` selects, per monad, a frame inference procedure registered with `@[frameproc]`
(`Lean.Elab.Tactic.VCGen.FrameProc`): at each spec application it may peel a frame off the
goal's precondition and carry it across the call. A procedure for `CircuitM` at the `Prover` tag
whose frame is the cells in scope with their readings carries each reading past the later steps
itself, which is the `simp` line's whole job: on the candidates stage it closes the law with no
`le_chain` and no carrying lemma, at 19 against 35 for the `le_chain` proof on v4.35
([toolchain-4.35.md](toolchain-4.35.md), §3). It needs `vcgen`, which reads only `Std.WP`
laws.

The stages stay either way: each states its result in closed form of its entry readings, a
better specification than one triple over the map's thirty tables.
