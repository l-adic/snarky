import Bulletproof.Forking.Adapter

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

-- `decide` works because `Forking.decIpaAcceptV` transports ironwood's decidability.
theorem hacc : IpaAcceptV gg bb PP vv tt := by decide

-- (1) Ironwood's extractor, run through the fold-convention transport.
def out : Fin 2 → K := (ipaExtract gg bb PP vv tt hacc).1

#eval (out 0, out 1)
#eval (Bulletproof.commitGen gg out == PP, Bulletproof.commitGen bb out == vv)

-- (2) The Stage-1 composite, through our own *blinded* opening relation: same SRS with
-- blinding base h = 1 and blinder ρ = 2, so the blinded commitment is PP + 2.
def σσ : SRS K := ⟨1, gg, 1, 1⟩
def PPb : K := PP + 2

theorem haccb : IpaAcceptV σσ.g bb (PPb - (2 : K) • σσ.h) vv tt := by decide

def outb : Fin 2 → K := (openingOfAcceptV σσ PPb bb vv 2 tt haccb).1

#eval (outb 0, outb 1)
#eval (Bulletproof.commit σσ outb 2 == PPb, vv == Bulletproof.innerProduct outb bb)
