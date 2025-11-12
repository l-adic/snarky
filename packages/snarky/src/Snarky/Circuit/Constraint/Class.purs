module Snarky.Circuit.Constraint.Class where

class R1CSSystem i c | c -> i where
  r1cs :: { left :: i, right :: i, output :: i } -> c
  boolean :: i -> c