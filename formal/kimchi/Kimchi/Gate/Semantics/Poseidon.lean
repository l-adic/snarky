import Kimchi.Gate.Poseidon
import Poseidon.Basic

/-! # Poseidon semantics

    Two layers. **Per row**: the gate computes the 5-round permutation `perm` (soundness), and
    the honest witness satisfies it (completeness). That spec is internal — `perm` is defined in
    `Kimchi/Gate/Poseidon.lean` — so on its own it checks the gate against itself.

    **Per eleven-row chain**: the deployed block computes `Poseidon.blockCipher`, the 55-round
    `mina_poseidon` permutation the duplex sponge runs, at the production `fq_kimchi` /
    `fp_kimchi` parameters. That spec is *external* and is pinned to recorded production traces
    by `poseidon/scripts/check_sponge_vectors.sh`, which is what makes it a faithfulness oracle
    in the sense the elliptic-curve gates get from Mathlib's group law. `55 = 11 × 5` exactly, so
    the deployed block is eleven rows of five rounds with no ragged tail.

    Contents, bottom-up: the ℕ-indexed round iterate `rounds` and its algebra; `mdsOfParams` /
    `round_eq_fullRound` (the two round functions are the same map) and `blockCipher_eq_rounds`
    (the sponge's whole-table fold *is* that iterate); the `Chain` predicate with `chain_rounds`
    / `chain_blockCipher` and the honest `buildChain` companion; and the deployed per-curve
    entry points `fq_/fp_poseidonChain_blockCipher` with their completeness twins. -/

namespace Kimchi.Gate.Poseidon

variable {F : Type*}

/-! ## Soundness: a satisfying row computes the permutation. -/

/-- Each round's three componentwise constraints assemble into `sᵢ₊₁ = round(sᵢ, rcᵢ)`. -/
private theorem step_eq [CommRing F] {a b : F × F × F}
    (h1 : a.1 - b.1 = 0) (h2 : a.2.1 - b.2.1 = 0) (h3 : a.2.2 - b.2.2 = 0) : a = b :=
  Prod.ext (sub_eq_zero.mp h1) (Prod.ext (sub_eq_zero.mp h2) (sub_eq_zero.mp h3))

/-- **Soundness of the Poseidon gate.** A satisfying witness's output state `s5` is the 5-round
    permutation of its input state `s0`. -/
theorem sound [CommRing F] (M : Mds F) (rc : Fin 5 → F × F × F) (w : Witness F)
    (h : Holds M rc w) :
    w.s5 = perm M w.s0 rc := by
  simp only [Holds, constraints, List.forall_mem_cons] at h
  obtain ⟨h1a, h1b, h1c, h2a, h2b, h2c, h3a, h3b, h3c,
    h4a, h4b, h4c, h5a, h5b, h5c, -⟩ := h
  have hs1 : w.s1 = round M w.s0 (rc 0) := step_eq h1a h1b h1c
  have hs2 : w.s2 = round M w.s1 (rc 1) := step_eq h2a h2b h2c
  have hs3 : w.s3 = round M w.s2 (rc 2) := step_eq h3a h3b h3c
  have hs4 : w.s4 = round M w.s3 (rc 3) := step_eq h4a h4b h4c
  have hs5 : w.s5 = round M w.s4 (rc 4) := step_eq h5a h5b h5c
  rw [perm, ← hs1, ← hs2, ← hs3, ← hs4, ← hs5]

/-! ## Completeness: the honest witness satisfies the gate. -/

/-- Build the canonical satisfying row by iterating `round` from the input state. -/
def build [CommRing F] (M : Mds F) (s0 : F × F × F) (rc : Fin 5 → F × F × F) : Witness F :=
  let s1 := round M s0 (rc 0)
  let s2 := round M s1 (rc 1)
  let s3 := round M s2 (rc 2)
  let s4 := round M s3 (rc 3)
  { s0, s1, s2, s3, s4, s5 := round M s4 (rc 4) }

/-- **Completeness of the Poseidon gate.** The honest witness (`build`) satisfies all 15
    constraints — unconditionally (the permutation is total). -/
theorem complete [CommRing F] (M : Mds F) (s0 : F × F × F) (rc : Fin 5 → F × F × F) :
    Holds M rc (build M s0 rc) := by
  intro e he
  fin_cases he <;> simp [build]

/-! ## Runnable example. -/

/-- A small-field MDS for the runnable example. -/
def egMds : Mds (ZMod 101) := ⟨2, 3, 5, 7, 11, 13, 17, 19, 23⟩

/-- A concrete satisfying row over a small field: `build` always satisfies `ok`. -/
def egPoseidon : Witness (ZMod 101) :=
  build egMds (1, 2, 3) (fun _ => (1, 1, 1))

#eval ok egMds (fun _ => (1, 1, 1)) egPoseidon   -- expect true

/-! ## The ℕ-indexed round iterate.

    One gate row is five rounds, so a chain of rows is a fold of rounds whose constant index
    keeps counting across the row boundary. `rounds M rc n` is that fold: `n` rounds from a
    state, reading the round constants off an ℕ-indexed family at `0, 1, …, n-1`. It is the
    common refinement of the gate's five-at-a-time `perm` and the sponge's whole-table fold. -/

/-- `n` rounds of the gate's round function applied to `s`, reading the round constants off
    `rc` at `0, 1, …, n-1`. The gate's `perm` is the case `n = 5`; `Poseidon.blockCipher` is
    the case `n = p.roundConstants.size`. -/
def rounds [CommRing F] (M : Mds F) (rc : ℕ → F × F × F) : ℕ → F × F × F → F × F × F
  | 0, s => s
  | n + 1, s => round M (rounds M rc n s) (rc n)

/-- Only the first `n` round constants are read, so families agreeing below `n` give the same
    iterate. This is what lets a chain be stated at any family that carries the deployed
    constants on the range it uses. -/
theorem rounds_congr [CommRing F] (M : Mds F) (rc rc' : ℕ → F × F × F) (n : ℕ)
    (h : ∀ i < n, rc i = rc' i) (s : F × F × F) :
    rounds M rc n s = rounds M rc' n s := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [rounds]
    rw [ih fun i hi => h i (by omega), h k (by omega)]

/-- Splitting the iterate: `a + b` rounds are `a` rounds followed by `b` rounds at the
    constants shifted by `a`. This is the row-boundary lemma — row `i` of a chain reads
    constants `5i … 5i+4` while its own five-round fold counts from `0`. -/
theorem rounds_add [CommRing F] (M : Mds F) (rc : ℕ → F × F × F) (a b : ℕ) (s : F × F × F) :
    rounds M rc (a + b) s = rounds M (fun i => rc (a + i)) b (rounds M rc a s) := by
  induction b with
  | zero => rfl
  | succ k ih =>
    show round M (rounds M rc (a + k) s) (rc (a + k))
      = round M (rounds M (fun i => rc (a + i)) k (rounds M rc a s)) (rc (a + k))
    rw [ih]

/-- The gate's five-round permutation is the iterate at `n = 5`, for any ℕ-indexed family
    agreeing with the row's `Fin 5`-indexed coefficient family. -/
theorem perm_eq_rounds [CommRing F] (M : Mds F) (s : F × F × F) (rc : Fin 5 → F × F × F)
    (rc' : ℕ → F × F × F) (h : ∀ j : Fin 5, rc' (j : ℕ) = rc j) :
    perm M s rc = rounds M rc' 5 s := by
  have e0 : rc' 0 = rc 0 := h 0
  have e1 : rc' 1 = rc 1 := h 1
  have e2 : rc' 2 = rc 2 := h 2
  have e3 : rc' 3 = rc 3 := h 3
  have e4 : rc' 4 = rc 4 := h 4
  simp only [perm, rounds, e0, e1, e2, e3, e4]

/-! ## The production sponge permutation as the gate's external spec.

    Everything above checks the gate against `perm`, which `Kimchi/Gate/Poseidon.lean` defines
    three declarations before `sound` uses it: the gate defines the permutation it is proved to
    compute. This section replaces that with an **external** oracle. `Poseidon.blockCipher`
    (`poseidon/Poseidon/Basic.lean`) is the 55-round `mina_poseidon` permutation
    (`permutation.rs` `poseidon_block_cipher`) the duplex sponge runs on every rate crossing,
    which `Poseidon.FqSponge` drives to produce every Fiat–Shamir challenge the kimchi verifier
    reads, and which `poseidon/scripts/check_sponge_vectors.sh` validates against recorded
    production `mina_poseidon` absorb/squeeze traces. Proving the gate chain computes *that*
    function is a link to production data rather than to another Lean definition.

    The two round functions are literally the same map, packaged differently: the gate carries
    the MDS matrix as nine named fields and adds the constants first, the sponge carries it as
    three rows and adds them last. `mdsOfParams` is the repackaging and `round_eq_fullRound` is
    the identity, which is an `add_comm` away from `rfl`. -/

section Sponge

variable [Field F]

/-- The gate's nine-field MDS matrix, read off a sponge parameter set. The gate takes the
    matrix as data (`G::sponge_params().mds`, a different table per curve) and the sponge
    carries the same table as three rows, so this is a repackaging and nothing more. -/
def mdsOfParams (p : Poseidon.Params F) : Mds F where
  m00 := p.mds.1.1
  m01 := p.mds.1.2.1
  m02 := p.mds.1.2.2
  m10 := p.mds.2.1.1
  m11 := p.mds.2.1.2.1
  m12 := p.mds.2.1.2.2
  m20 := p.mds.2.2.1
  m21 := p.mds.2.2.2.1
  m22 := p.mds.2.2.2.2

/-- **The gate's round function is the sponge's round function.** Same S-box (`x ^ 7` on both
    sides — Pasta `PERM_SBOX = 7`), same MDS row indexing, constants added after the MDS pass
    on both sides, no initial ARK on either; the two differ only in argument order and in how
    the matrix is packaged. Everything downstream is this identity plus bookkeeping. -/
theorem round_eq_fullRound (p : Poseidon.Params F) (s r : F × F × F) :
    round (mdsOfParams p) s r = Poseidon.fullRound p.mds r s := by
  simp only [round, Poseidon.fullRound, sbox, _root_.Poseidon.sbox, mdsOfParams, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- A parameter set's round constants as an ℕ-indexed family, reading `(0, 0, 0)` out of
    range. Stated with `Array.getD` rather than `a[i]!` deliberately: `getD` takes the default
    as an argument, so it needs no `Inhabited F` instance on a bare field. -/
def paramsRc (p : Poseidon.Params F) (i : ℕ) : F × F × F :=
  p.roundConstants.getD i (0, 0, 0)

/-- The fold bridge, over lists: folding the sponge's round function along a list of constants
    is the gate's iterate at any family that carries that list. Proved by induction from the
    front, splicing the head off with `rounds_add` at `a = 1` (the iterate peels from the
    *end*, a left fold from the front, so one of the two has to be turned around). -/
private theorem foldl_fullRound_eq_rounds (p : Poseidon.Params F) :
    ∀ (l : List (F × F × F)) (rc : ℕ → F × F × F) (s : F × F × F),
      (∀ i (hi : i < l.length), l[i] = rc i) →
      l.foldl (fun s r => Poseidon.fullRound p.mds r s) s
        = rounds (mdsOfParams p) rc l.length s := by
  intro l
  induction l with
  | nil => intro rc s _; rfl
  | cons a t ih =>
    intro rc s h
    have ha : a = rc 0 := by simpa using h 0 (by simp)
    have ht : ∀ i (hi : i < t.length), t[i] = (fun k => rc (1 + k)) i := by
      intro i hi
      simpa [Nat.add_comm] using h (i + 1) (by simpa using hi)
    have hlen : (a :: t).length = 1 + t.length := by simp [Nat.add_comm]
    rw [List.foldl_cons, ih _ _ ht, hlen, rounds_add]
    congr 1
    show Poseidon.fullRound p.mds a s = round (mdsOfParams p) (rounds (mdsOfParams p) rc 0 s) (rc 0)
    rw [rounds, round_eq_fullRound, ha]

/-- **The sponge permutation is the gate's iterate.** `Poseidon.blockCipher p` is exactly
    `p.roundConstants.size` rounds of the gate's round function at `mdsOfParams p`, reading the
    constants off `paramsRc p`. This is the bridge the chain theorems below compose with: it
    turns the sponge's whole-table `Array.foldl` into the ℕ-indexed iterate a row chain
    produces. -/
theorem blockCipher_eq_rounds (p : Poseidon.Params F) (s : F × F × F) :
    Poseidon.blockCipher p s = rounds (mdsOfParams p) (paramsRc p) p.roundConstants.size s := by
  have h : ∀ i (hi : i < p.roundConstants.toList.length),
      p.roundConstants.toList[i] = paramsRc p i := by
    intro i hi
    rw [Array.length_toList] at hi
    rw [Array.getElem_toList hi]
    simp only [paramsRc]
    exact Array.getElem_eq_getD _
  simp only [Poseidon.blockCipher, ← Array.foldl_toList]
  rw [foldl_fullRound_eq_rounds p p.roundConstants.toList (paramsRc p) s h, Array.length_toList]

end Sponge

/-! ## The row chain.

    The deployed circuit is read off the PureScript that emits it.
    `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/Poseidon.purs` witnesses 55 round outputs,
    prepends the caller's input state and returns `state[55]`, so the Poseidon block is 56
    states and 55 rounds. `packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/Poseidon.purs`
    splits the first 55 states into eleven chunks of five (`Vector.chunks @5`), emits one
    `PoseidonGate` row per chunk with coefficients `getRoundConstants (5i) … (5i+4)` in round
    order, and appends a final `Zero` row carrying `state[55]`. `55 = 11 × 5` exactly, so the
    chain is eleven rows with no ragged tail.

    `Chain` is that shape as a predicate; `chain_rounds` folds it into the ℕ-indexed iterate and
    `chain_blockCipher` lands it on the sponge permutation. `buildChain` is the honest prover's
    table and `buildChain_chain` says it satisfies the predicate — without that pair the chain
    theorems would be statements about a set nobody has shown to be non-empty. -/

/-- An `n`-row Poseidon chain: each row satisfies the gate at its own block of five round
    constants, and consecutive rows are linked through the state. -/
structure Chain [CommRing F] (M : Mds F) (rc : ℕ → F × F × F) (w : ℕ → Witness F) (n : ℕ) :
    Prop where
  /-- Row `i` satisfies the gate at the round constants of its own block — `rc (5i + j)` for
      `j < 5`, which is what `Constraint/Kimchi/Poseidon.purs` writes into row `i`'s
      coefficient cells. -/
  holds : ∀ i < n, Holds M (fun j : Fin 5 => rc (5 * i + (j : ℕ))) (w i)
  /-- Row `i`'s output state is row `i + 1`'s input state. This is kimchi's two-row Poseidon
      convention: the output register `s5` is read off the *next* row. -/
  link : ∀ i, i + 1 < n → (w i).s5 = (w (i + 1)).s0

/-- A prefix of a chain is a chain. Used to feed the induction in `chain_rounds`. -/
theorem Chain.mono [CommRing F] {M : Mds F} {rc : ℕ → F × F × F} {w : ℕ → Witness F} {m n : ℕ}
    (h : Chain M rc w n) (hmn : m ≤ n) : Chain M rc w m :=
  ⟨fun i hi => h.holds i (lt_of_lt_of_le hi hmn),
   fun i hi => h.link i (lt_of_lt_of_le hi hmn)⟩

/-- `chain_rounds` in the shape the induction runs in. -/
private theorem chain_rounds_succ [CommRing F] (M : Mds F) (rc : ℕ → F × F × F)
    (w : ℕ → Witness F) (m : ℕ) (h : Chain M rc w (m + 1)) :
    (w m).s5 = rounds M rc (5 * (m + 1)) (w 0).s0 := by
  induction m with
  | zero =>
    have hs := sound M (fun j : Fin 5 => rc (5 * 0 + (j : ℕ))) (w 0) (h.holds 0 (by omega))
    rw [hs, perm_eq_rounds M (w 0).s0 _ rc fun j => by simp]
  | succ k ih =>
    have hprev := ih (h.mono (by omega))
    have hlink := h.link k (by omega)
    have hs := sound M (fun j : Fin 5 => rc (5 * (k + 1) + (j : ℕ))) (w (k + 1))
      (h.holds (k + 1) (by omega))
    have hsplit : 5 * (k + 1 + 1) = 5 * (k + 1) + 5 := by ring
    rw [hsplit, rounds_add, ← hprev, hs,
      perm_eq_rounds M (w (k + 1)).s0 _ (fun i => rc (5 * (k + 1) + i)) fun j => rfl, ← hlink]

/-- **A satisfying chain computes the round iterate.** An `n`-row chain carries its first row's
    input state through `5n` rounds: the last row's output register is `rounds M rc (5 * n)` of
    the first row's input. Each step applies `sound` to one row, `perm_eq_rounds` to read its
    five-round conclusion as an iterate, and `rounds_add` to splice that onto the prefix. -/
theorem chain_rounds [CommRing F] (M : Mds F) (rc : ℕ → F × F × F) (w : ℕ → Witness F) (n : ℕ)
    (h : Chain M rc w n) (hn : 0 < n) :
    (w (n - 1)).s5 = rounds M rc (5 * n) (w 0).s0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using chain_rounds_succ M rc w m h

/-- **A satisfying chain computes the production sponge permutation.** The payoff of the
    section: when the chain's MDS matrix and round constants are the ones a `Poseidon.Params`
    set carries, and the table has exactly `5n` entries, the chain's last output register is
    `Poseidon.blockCipher` of its first input state — the permutation `mina_poseidon` runs, not
    a permutation this file defines.

    The parameters enter as **data**: `M` is `mdsOfParams p` and the constants agree with
    `paramsRc p` below `5n`. That a real index carries those same values is an ingestion-layer
    fact, not proved here; the `Chain` hypothesis is what a satisfying witness table supplies. -/
theorem chain_blockCipher [Field F] (p : Poseidon.Params F) (rc : ℕ → F × F × F)
    (w : ℕ → Witness F) (n : ℕ) (h : Chain (mdsOfParams p) rc w n) (hn : 0 < n)
    (hsize : p.roundConstants.size = 5 * n) (hrc : ∀ i < 5 * n, rc i = paramsRc p i) :
    (w (n - 1)).s5 = Poseidon.blockCipher p (w 0).s0 := by
  rw [chain_rounds _ rc w n h hn, blockCipher_eq_rounds, hsize,
    rounds_congr _ rc (paramsRc p) (5 * n) hrc]

/-! ## Completeness: the honest chain. -/

/-- The honest prover's `n`-row table: row `0` is `build` from the input state at constants
    `rc 0 … rc 4`, and row `i + 1` is `build` from row `i`'s output at constants
    `rc (5(i+1)) … rc (5(i+1)+4)`. -/
def buildChain [CommRing F] (M : Mds F) (rc : ℕ → F × F × F) (s0 : F × F × F) :
    ℕ → Witness F
  | 0 => build M s0 fun j : Fin 5 => rc (5 * 0 + (j : ℕ))
  | i + 1 => build M (buildChain M rc s0 i).s5 fun j : Fin 5 => rc (5 * (i + 1) + (j : ℕ))

/-- The honest table's first row carries the requested input state. -/
theorem buildChain_s0 [CommRing F] (M : Mds F) (rc : ℕ → F × F × F) (s0 : F × F × F) :
    (buildChain M rc s0 0).s0 = s0 := rfl

/-- **Completeness of the chain.** For every input state and every length there *is* a
    satisfying chain: the honest table. Each row satisfies the gate by `complete`, and the link
    hypothesis holds by construction because row `i + 1` is built from row `i`'s output. -/
theorem buildChain_chain [CommRing F] (M : Mds F) (rc : ℕ → F × F × F) (s0 : F × F × F)
    (n : ℕ) : Chain M rc (buildChain M rc s0) n where
  holds i _ := by cases i <;> exact complete _ _ _
  link _ _ := rfl

/-- **Completeness against the sponge permutation.** The honest `n`-row table's last output
    register is `Poseidon.blockCipher p` of the input state it was built from, so the set
    `chain_blockCipher` quantifies over is non-empty at every input. -/
theorem buildChain_blockCipher [Field F] (p : Poseidon.Params F) (rc : ℕ → F × F × F)
    (s0 : F × F × F) (n : ℕ) (hn : 0 < n) (hsize : p.roundConstants.size = 5 * n)
    (hrc : ∀ i < 5 * n, rc i = paramsRc p i) :
    (buildChain (mdsOfParams p) rc s0 (n - 1)).s5 = Poseidon.blockCipher p s0 := by
  have := chain_blockCipher p rc (buildChain (mdsOfParams p) rc s0) n
    (buildChain_chain _ _ _ _) hn hsize hrc
  rwa [buildChain_s0] at this

/-! ## The deployed per-curve entry points.

    The eleven-row chain at the two parameter sets kimchi actually runs: `fq_kimchi` over the
    Vesta base field (the sponge of proofs over Vesta) and `fp_kimchi` over the Pallas base
    field. `Fq`/`Fp` are `CompElliptic.Fields.Pasta` `abbrev`s down to `ZMod`, so the `Field`
    instance is found by instance search and no characteristic is threaded by hand.

    **What is gained.** The gate is no longer checked against a permutation it defines itself.
    Eleven satisfying rows compute `Poseidon.blockCipher` at the production `fq_kimchi` /
    `fp_kimchi` tables — the same function the duplex sponge runs on every rate crossing, the
    same function `Poseidon.FqSponge` drives to produce every Fiat–Shamir challenge, and the
    same function `poseidon/scripts/check_sponge_vectors.sh` validates against recorded
    `mina_poseidon` traces. That driver is what makes this a link to production rather than to
    another Lean definition.

    **What is assumed.** The MDS matrix and the round constants enter as **data**: the theorems
    are stated at `mdsOfParams fqParams` and at constants agreeing with `paramsRc fqParams`.
    That the index a real proof carries holds those same values is an ingestion-layer fact this
    file does not prove. The `Chain` hypothesis is what a satisfying witness table supplies —
    eleven rows holding, linked through the state.

    **What is not claimed.** Nothing about the sponge's absorb/squeeze automaton, the
    rate/capacity discipline, or the challenge derivation — only the permutation. And nothing
    about security: this is a faithfulness result, not a hardness one. -/

section Deployed

open CompElliptic.Fields.Pasta

/-- The `fq_kimchi` round-constant table has `5 × 11` entries, so eleven five-round rows cover
    the permutation exactly with no ragged tail. `Array.size_map` carries the count off the
    generated `FqKimchi.roundConstants`, so only the array *spine* is reduced and no 254-bit
    numeral is ever evaluated. -/
theorem fqParams_size : Poseidon.fqParams.roundConstants.size = 5 * 11 := by
  show (Poseidon.FqKimchi.roundConstants.map _).size = 5 * 11
  rw [Array.size_map]
  rfl

/-- The `fp_kimchi` round-constant table has `5 × 11` entries — the Pallas-side twin of
    `fqParams_size`. -/
theorem fpParams_size : Poseidon.fpParams.roundConstants.size = 5 * 11 := by
  show (Poseidon.FpKimchi.roundConstants.map _).size = 5 * 11
  rw [Array.size_map]
  rfl

/-- **The deployed Vesta-side Poseidon chain computes the production sponge permutation.**
    Eleven satisfying gate rows at the `fq_kimchi` MDS matrix and round constants carry the
    first row's input state to `Poseidon.blockCipher fqParams` of it. See the section preamble
    for what this does and does not establish. -/
theorem fq_poseidonChain_blockCipher (rc : ℕ → Fq × Fq × Fq) (w : ℕ → Witness Fq)
    (hrc : ∀ i < 5 * 11, rc i = paramsRc Poseidon.fqParams i)
    (h : Chain (mdsOfParams Poseidon.fqParams) rc w 11) :
    (w 10).s5 = Poseidon.blockCipher Poseidon.fqParams (w 0).s0 :=
  chain_blockCipher Poseidon.fqParams rc w 11 h (by omega) fqParams_size hrc

/-- **The deployed Pallas-side Poseidon chain computes the production sponge permutation** —
    the twin of `fq_poseidonChain_blockCipher` at `fp_kimchi`. -/
theorem fp_poseidonChain_blockCipher (rc : ℕ → Fp × Fp × Fp) (w : ℕ → Witness Fp)
    (hrc : ∀ i < 5 * 11, rc i = paramsRc Poseidon.fpParams i)
    (h : Chain (mdsOfParams Poseidon.fpParams) rc w 11) :
    (w 10).s5 = Poseidon.blockCipher Poseidon.fpParams (w 0).s0 :=
  chain_blockCipher Poseidon.fpParams rc w 11 h (by omega) fpParams_size hrc

/-- **Completeness at `fq_kimchi`.** For every input state an eleven-row satisfying chain
    exists, its first row carries that state, and its last output register is
    `Poseidon.blockCipher fqParams` of it. Without this `fq_poseidonChain_blockCipher` would be
    a statement about a set nobody has shown to be non-empty. -/
theorem fq_poseidonChain_complete (s0 : Fq × Fq × Fq) :
    ∃ w : ℕ → Witness Fq,
      Chain (mdsOfParams Poseidon.fqParams) (paramsRc Poseidon.fqParams) w 11
        ∧ (w 0).s0 = s0
        ∧ (w 10).s5 = Poseidon.blockCipher Poseidon.fqParams s0 :=
  ⟨buildChain (mdsOfParams Poseidon.fqParams) (paramsRc Poseidon.fqParams) s0,
    buildChain_chain _ _ _ _, buildChain_s0 _ _ _,
    buildChain_blockCipher Poseidon.fqParams _ s0 11 (by omega) fqParams_size fun _ _ => rfl⟩

/-- **Completeness at `fp_kimchi`** — the twin of `fq_poseidonChain_complete`. -/
theorem fp_poseidonChain_complete (s0 : Fp × Fp × Fp) :
    ∃ w : ℕ → Witness Fp,
      Chain (mdsOfParams Poseidon.fpParams) (paramsRc Poseidon.fpParams) w 11
        ∧ (w 0).s0 = s0
        ∧ (w 10).s5 = Poseidon.blockCipher Poseidon.fpParams s0 :=
  ⟨buildChain (mdsOfParams Poseidon.fpParams) (paramsRc Poseidon.fpParams) s0,
    buildChain_chain _ _ _ _, buildChain_s0 _ _ _,
    buildChain_blockCipher Poseidon.fpParams _ s0 11 (by omega) fpParams_size fun _ _ => rfl⟩

end Deployed

end Kimchi.Gate.Poseidon
