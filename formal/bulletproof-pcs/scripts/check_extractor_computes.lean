import Bulletproof.Forking.Convention

open Bulletproof Bulletproof.Forking

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
abbrev K := ZMod 7

-- A concrete accepting depth-1 kimchi transcript over ZMod 7, built by honest folding
-- from the witness a = ![4,6] against generators g = ![2,3] and eval vector b = ![1,5].
def gg : Fin 2 → K := ![2, 3]
def bb : Fin 2 → K := ![1, 5]
def PP : K := 2*4 + 3*6
def vv : K := 1*4 + 5*6
def tt : IpaTreeV K K 1 :=
  .node (2*6) (3*4) (1*6) (5*4) 1 2 3 (.leaf 3) (.leaf 0) (.leaf 6)

-- The tree really is accepted: every component decided, nothing asserted.
theorem hacc : IpaAcceptV gg bb PP vv tt := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

-- Ironwood's extractor, run through the transport, on this kimchi transcript.
def out : Fin 2 → K := (ipaExtract gg bb PP vv tt hacc).1

#eval (out 0, out 1)
#eval (Bulletproof.commitGen gg out == PP, Bulletproof.commitGen bb out == vv)
