import Bulletproof.Forking.Adapter
import Bulletproof.Forking.Capstone

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

-- (3) The full capstone at depth 0: an honest Schnorr 2-fork over the SRS
-- σ = ⟨k=0, g=![3], h=5, U=2⟩, witness a=![4], blinder pw=1, so P = 4•3+1•5 = 3 and
-- v = ⟨a,b⟩ = 4·2 = 1 against b = ![2]. Two honest transcripts (d=1, rδ=2):
--   c=1: z1 = 4·1+1 = 5, z2 = 1·1+2 = 3;  c'=2: z1' = 4·2+1 = 2, z2' = 1·2+2 = 4.
def σ0 : SRS K := ⟨0, ![3], 5, 2⟩
def b0v : Fin (2 ^ σ0.k) → K := ![2]
def P0 : K := 3
def cert0 : KimchiForkCert K K σ0.k := .leaf 3 3 1 5 3 2 2 4

theorem hv0 : KimchiForkValid σ0.U σ0.h 1 σ0.g b0v P0 cert0 :=
  ⟨by decide, by decide, by decide, by decide⟩

def cap : Option (K × K) :=
  match kimchiOpeningOrBreak σ0 b0v 1 P0 ![4] 1 (by decide) cert0 hv0 with
  | PSum.inl ⟨a, ρ, _⟩ => some (a 0, ρ)
  | PSum.inr _ => none

#eval cap
