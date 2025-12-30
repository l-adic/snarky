module Test.Snarky.Circuit.Kimchi.EndoScale where

import Prelude

import Data.Array as Array
import Data.Identity (Identity)
import Data.Traversable (foldl)
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, add_, const_, Bool(..))
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Circuit.Kimchi.EndoScale (ScalarChallenge(..), toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, endoBase, fromInt)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Fin (Finite, finites, relax, scale, translate, unsafeFinite)
import Snarky.Data.Vector (Vector, (!!))
import Snarky.Data.Vector as Vector
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-- Test input: 128-bit boolean array (like OCaml QuickCheck)
type TestInput = Vector 128 Boolean

-- Constant reference implementation (functional version of OCaml to_field_constant)
toFieldConstant :: forall f n _l. PrimeField f => FieldSizeInBits f n => Add 128 _l n => f -> f -> f
toFieldConstant f endo =
  let
    bits :: Vector 128 Boolean
    bits = Vector.reverse $ Vector.take @128 $ unpackPure f

    chunks :: Vector 64 (Vector 2 Boolean)
    chunks = Vector.chunks @2 bits

    -- Process bits in pairs: for i = (128/2)-1 downto 0 (i.e., from 63 down to 0)
    processChunk :: { a :: f, b :: f } -> Vector 2 Boolean  -> { a :: f, b :: f }
    processChunk { a, b } v =
      let
        -- OCaml: bits.(2 * i) and bits.((2 * i) + 1)
        bit_even = v !! unsafeFinite 0 -- bits.(2*i) - the even index  
        bit_odd = v !! unsafeFinite 1 -- bits.(2*i + 1) - the odd index

        -- s = if bits.(2*i) then 1 else -1 (OCaml uses even bit for sign)
        s = if bit_even then one else (zero - one)

        -- Double both a and b: a := a + a, b := b + b  
        a2 = a + a
        b2 = b + b

      -- r_2i1 = bits.((2*i) + 1)
      -- if r_2i1 then a := a + s else b := b + s
      in
        if bit_odd then { a: a2 + s, b: b2 } -- a := a + s
        else { a: a2, b: b2 + s } -- b := b + s

    -- Initial values: a = 2, b = 2
    initial = { a: fromInt 2, b: fromInt 2 }

    -- Process from i = 63 downto 0 (reverse order)
    final = foldl processChunk initial chunks
  in
    -- Return: (a * endo) + b
    final.a * endo + final.b

-- Reference implementation using the pure constant algorithm
refEndoScale :: F Vesta.ScalarField -> F Vesta.ScalarField
refEndoScale (F f) =
  let
    -- Use the endomorphism coefficient for Vesta scalar field  
    endo = endoBase :: Vesta.ScalarField -- from HasEndo Vesta.ScalarField Pallas.ScalarField

    -- Apply the constant algorithm directly to the boolean array
    result = toFieldConstant f endo
  in
    F result

-- Circuit implementation: convert bool array to scalar, then apply endoscale
circuit
  :: forall t
   . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
  => FVar Vesta.ScalarField
  -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity (FVar Vesta.ScalarField)
circuit scalarValue = do

  -- Create scalar challenge from the field element  
  let challenge = ScalarChallenge scalarValue

  -- Use the same endomorphism coefficient as reference function
  let
    endoCoeff = endoBase :: Vesta.ScalarField -- from HasEndo Vesta.ScalarField Pallas.ScalarField
    endoVar = const_ endoCoeff

  -- Apply the endoscale algorithm and return the FVar
  toField challenge endoVar

-- Generator for 128-bit boolean arrays (like OCaml QuickCheck test)
gen128BitElem :: Gen (F Vesta.ScalarField)
gen128BitElem = do 
  v <- Vector.generator (Proxy @128) arbitrary
  let v' = v `Vector.append` (Vector.generate $ const false)
  pure $ F $ packPure v'

-- Convert boolean array to scalar field element (LSB first)
boolArrayToScalar :: forall f n. PrimeField f => Vector n (BoolVar f) -> (FVar f)
boolArrayToScalar bits =
  foldl (\acc bit -> acc `add_` coerce bit) (const_ zero) bits

-- Test specification (following OCaml QuickCheck pattern)
spec :: Spec Unit
spec = do
  describe "EndoScale" do
    it "Circuit output matches constant implementation (like OCaml test)" $
      let
        -- Reference function: apply constant algorithm to boolean array
        f :: F Vesta.ScalarField -> F Vesta.ScalarField
        f = refEndoScale

        -- Solver and constraint compilation
        solver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit

        { constraints } = compilePure
          (Proxy @(F Vesta.ScalarField))
          (Proxy @(F Vesta.ScalarField))
          (Proxy @(KimchiConstraint Vesta.ScalarField))
          circuit
          Kimchi.initialState
      in
        -- Test that circuit matches reference on random 128-bit boolean arrays
        circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) gen128BitElem