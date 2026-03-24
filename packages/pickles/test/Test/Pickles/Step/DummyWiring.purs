module Test.Pickles.Step.DummyWiring
  ( spec
  ) where

-- | Compares stepDummyFopProofState values against OCaml's verify_one dump.
-- |
-- | The OCaml dump comes from instrumenting step_main.ml:verify_one with
-- | as_prover logging. The dump shows the Per_proof_witness.proof_state
-- | deferred values that the Step circuit receives for the base case (Step₀).
-- |
-- | Wrap₀ validation: The Wrap₀ FOP input comes from Tock.Oracles on the
-- | Step₀ proof (not static dummies), so it's validated by WrapE2E and
-- | WrapFinalizeOtherProof.realDataSpec which run the full Wrap circuit.
-- |
-- | Reference: mina/src/lib/crypto/pickles/step_main.ml (STEP WIRING DUMP)

import Prelude

import JS.BigInt as BigInt
import Pickles.Dummy (stepDummyFopProofState)
import Pickles.Types (StepField)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Circuit.DSL (F(..), SizedF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (Type1(..))
import Snarky.Curves.Class (toBigInt)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | OCaml Step₀ verify_one dump values for Simple_Chain (N1, proofs_verified=1).
-- | These come from expand_proof on Proof.dummy N1 N1 ~domain_log2:14.
spec :: Spec Unit
spec = describe "Step₀ dummy wiring (proofs_verified=1)" do
  let
    du :: UnfinalizedProof _ (F StepField) (Type1 (F StepField)) Boolean
    du = stepDummyFopProofState { proofsVerified: 1 }
    dv = du.deferredValues
    p = dv.plonk

    showFp :: StepField -> String
    showFp x = BigInt.toString (toBigInt x)
    unwrapT1 (Type1 (F x)) = x

    rawChal :: SizedF 128 (F StepField) -> StepField
    rawChal c = SizedF.toField (SizedF.unwrapF c)

  it "plonk.alpha.inner matches OCaml dump" do
    showFp (rawChal p.alpha) `shouldEqual` "31714329958175783727477075551945886853"

  it "plonk.beta matches OCaml dump" do
    showFp (rawChal p.beta) `shouldEqual` "205913416174691502893106945792091291792"

  it "plonk.gamma matches OCaml dump" do
    showFp (rawChal p.gamma) `shouldEqual` "336749301731200029198653052774605635264"

  it "plonk.zeta.inner matches OCaml dump" do
    showFp (rawChal p.zeta) `shouldEqual` "158734529890406899856543714254821979093"

  it "plonk.perm matches OCaml dump" do
    showFp (unwrapT1 p.perm) `shouldEqual` "1842021825410117045889991149454044477862267393274733947471587023950533248540"

  it "plonk.zeta_to_srs_length matches OCaml dump" do
    showFp (unwrapT1 p.zetaToSrsLength) `shouldEqual` "7495766992897478704655999722725764608652561011206572130562024999418855590739"

  it "plonk.zeta_to_domain_size matches OCaml dump" do
    showFp (unwrapT1 p.zetaToDomainSize) `shouldEqual` "14549911688440141793290148588352505886063498529159055413088139050794674178883"

  it "combined_inner_product matches OCaml dump" do
    showFp (unwrapT1 dv.combinedInnerProduct) `shouldEqual` "1850878998537086432558089636670542876017885783503305476169213713605401284811"

  it "b matches OCaml dump" do
    showFp (unwrapT1 dv.b) `shouldEqual` "19925063465561849200200816926432839360204635399078768535232904150958365984703"

  it "sponge_digest is zero" do
    let F d = du.spongeDigestBeforeEvaluations
    showFp d `shouldEqual` "0"

  it "should_finalize is false" do
    du.shouldFinalize `shouldEqual` false
