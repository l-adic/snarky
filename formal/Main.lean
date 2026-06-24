import Kimchi.Gate.Generic

open Kimchi.Gate

def main : IO Unit := do
  IO.println s!"satisfies [mulGate] egGood = {satisfies [mulGate] egGood}"  -- true
  IO.println s!"satisfies [mulGate] egBad  = {satisfies [mulGate] egBad}"   -- false
