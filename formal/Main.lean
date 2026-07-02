import Kimchi.Gate.Generic

open Kimchi.Gate

def main : IO Unit := do
  IO.println s!"satisfies [egGood] = {satisfies [egGood]}"  -- true
  IO.println s!"satisfies [egBad]  = {satisfies [egBad]}"   -- false
