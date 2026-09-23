# Probabilistic soundness is out of scope

Nothing in the tree claims, assumes, or needs discrete-log hardness, a random-oracle
idealisation, or any other cryptographic hypothesis. The removed knowledge-soundness tree is in
git history.

## Why it is out of scope

A knowledge-soundness statement for the deployed kimchi and IPA verifiers, over a forking
extractor with Pasta discrete-log hardness as a hypothesis, does not pay for itself. The
extractor's cost bound is exponential in `k` and in the challenge domain, so at deployed
parameters a reduction permitted that many oracle calls solves Pasta discrete log outright and
the hardness hypothesis holds only at advantage close to 1. A conditional-average bound would
need a fork-spread property that nothing witnesses at deployed parameters. The result is a
theorem whose name suggests more than it delivers, at a cost of a large dependency and a large
share of the build.

## What the verifiers are

`Kimchi.Verifier.kimchiVerify` and `Bulletproof.Ipa.verify` / `verifyFrom` are
specifications: transcriptions of proof-systems' `kimchi/src/verifier.rs` and
`poly-commitment`, and the anchors circuit implementations are proved faithful to.
`Kimchi/Verifier/Reflect.lean` names every intermediate of `kimchiVerify`'s body as a closed
form, the per-stage targets a fragment of an in-circuit verifier lands on.

The circuit-side statement is relative faithfulness: `Pickles.twoHalves_kimchiVerify` says the
two halves of an in-circuit verifier accept exactly when `kimchiVerify` does. It neither assumes
the wire verifier is sound nor establishes that it is.

## The deterministic algebra that remains

- `Kimchi.Index.satisfies_iff_fullFamily_dvd`: the arithmetization, linking `Index.Satisfies`
  to divisibility of the committed polynomial family by `Z_H`.
- `Kimchi.Index.satisfies_of_evalCheck`: the same from an evaluation check, which is what
  makes checking at a single point legitimate.
- `Kimchi.Index.copy_soundness_of_dvd` over the multiset core in `Kimchi/GrandProduct.lean`:
  the permutation argument's conclusion.
- `Kimchi/SchwartzZippel.lean`: `dvd_separation` concludes
  `Z_H ∣ aggregate(α, C) → ∀ k, Z_H ∣ C k` for `α` outside an explicit finite set, with
  `card_badAlphas_le` and `card_badZetas_le` bounding those sets
  (`GrandProduct.card_bad{Betas,Gammas}_le` likewise for `β`, `γ`).
- `Lift.Argument.bridge` and the index's derived columns: what the verifier's commitments
  commit to.

None of this is a soundness claim. Every statement is an implication about explicit field
elements outside explicit finite sets whose cardinalities are proved; no probability,
adversary, or hardness assumption appears. Reading the cardinality bounds as soundness error
requires a model of how challenges are drawn, and that model is exactly what is out of scope.
`kimchi/scripts/check_index_fixture.sh` and `check_perm_fixture.sh` replay this layer against
production data.
