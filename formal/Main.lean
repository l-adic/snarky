import Kimchi.Gates.Generic

open Kimchi

/-- A runnable demo: the shape of "ingest a dumped (circuit, witness) and run the
    verified checker". Here the generic gate + witness are inline; later they are
    read from the JSON your PureScript dumpers emit. -/
def main : IO Unit := do
  IO.println s!"satisfies [mulGate] egGood = {satisfies [mulGate] egGood}"  -- true
  IO.println s!"satisfies [mulGate] egBad  = {satisfies [mulGate] egBad}"   -- false
