# OCaml to PureScript Snarky Circuit Translator

You are an expert in both OCaml and PureScript, with deep knowledge of the snarky DSL and its implementation in both languages. Your task is to translate OCaml snarky circuits into their PureScript equivalents.

Below are several examples of such translations. Use these as a guide for your translation.

---

## Example 1: Poseidon

### OCaml

**File:** `mina/src/lib/snarky/sponge/sponge.ml`
**Module:** `Poseidon`

```ocaml
module Poseidon (Inputs : Intf.Inputs.Poseidon) = struct
  open Inputs
  include Operations
  module Field = Field

  let first_half_rounds_full = rounds_full / 2

  let add_block ~state block = Array.iteri block ~f:(add_assign ~state)

  (* Poseidon goes

        ARK_0 -> SBOX -> MDS
     -> ARK_1 -> SBOX -> MDS
     -> ...
     -> ARK_{half_rounds_full - 1} -> SBOX -> MDS
     -> ARK_{half_rounds_full} -> SBOX0 -> MDS
     -> ...
     -> ARK_{half_rounds_full + rounds_partial - 1} -> SBOX0 -> MDS
     -> ARK_{half_rounds_full + rounds_partial} -> SBOX -> MDS
     -> ...
     -> ARK_{half_rounds_full + rounds_partial + half_rounds_full - 1} -> SBOX -> MDS

     It is best to apply the matrix and add the round constants at the same
     time for Marlin constraint efficiency, so that is how this implementation does it.
     Like,

        ARK_0
     -> SBOX -> (MDS -> ARK_1)
     -> SBOX -> (MDS -> ARK_2)
     -> ...
     -> SBOX -> (MDS -> ARK_{half_rounds_full - 1})
     -> SBOX -> (MDS -> ARK_{half_rounds_full})
     -> SBOX0 -> (MDS -> ARK_{half_rounds_full + 1})
     -> ...
     -> SBOX0 -> (MDS -> ARK_{half_rounds_full + rounds_partial - 1})
     -> SBOX0 -> (MDS -> ARK_{half_rounds_full + rounds_partial})
     -> SBOX -> (MDS -> ARK_{half_rounds_full + rounds_partial + 1})
     -> ...
     -> SBOX -> (MDS -> ARK_{half_rounds_full + rounds_partial + half_rounds_full - 1})
     -> SBOX -> MDS ->* ARK_{half_rounds_full + rounds_partial + half_rounds_full}

      *this last round is a deviation from standard poseidon made for efficiency reasons.
       clearly it does not impact security to add round constants
  *)
  let block_cipher { Params.round_constants; mds } state =
    let sbox = to_the_alpha in
    let state = ref state in
    let constant_offset =
      if initial_ark then (
        add_block ~state:!state round_constants.(0) ;
        1 )
      else 0
    in
    let range =
      (constant_offset, constant_offset + first_half_rounds_full - 1)
    in
    for i = fst range to snd range do
      (* SBOX -> MDS -> ARK *)
      Array.map_inplace !state ~f:sbox ;
      state := apply_affine_map (mds, round_constants.(i)) !state
    done ;
    let range = (snd range + 1, snd range + rounds_partial) in
    for i = fst range to snd range do
      !state.(0) <- sbox !state.(0) ;
      state := apply_affine_map (mds, round_constants.(i)) !state
    done ;
    let second_half_rounds_full = rounds_full - first_half_rounds_full in
    let range = (snd range + 1, snd range + second_half_rounds_full) in
    for i = fst range to snd range do
      Array.map_inplace !state ~f:sbox ;
      state := apply_affine_map (mds, round_constants.(i)) !state
    done ;
    !state
end
```

### PureScript

**File:** `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/Poseidon.purs`
**Module:** `Snarky.Circuit.Kimchi.Poseidon`

```purescript
module Snarky.Circuit.Kimchi.Poseidon
  ( poseidon
  ) where

import Prelude

import Data.Traversable (traverse)
import Poseidon.Class (class PoseidonField, fullRound)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (Snarky, addConstraint, exists, readCVar)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(KimchiPoseidon))
import Data.Fin (getFinite, unsafeFinite)
import Data.Vector (Vector)
import Data.Vector as Vector

poseidon
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
poseidon initialState = do
  state <- exists do
    initialValues <- traverse readCVar initialState
    let
      rounds = Vector.generate (\i -> \state -> fullRound state (getFinite i))
      roundOutputs = Vector.scanl (\state roundFn -> roundFn state) (coerce initialValues) rounds
      allStates = (coerce initialValues) Vector.:< roundOutputs
    pure (map (map F) allStates)
  addConstraint $ KimchiPoseidon { state }
  pure $
    (Vector.index (Vector.index state (unsafeFinite 55)) (unsafeFinite 2))
```

---

## Example 2: CompleteAdd

### OCaml

**File:** `mina/src/lib/pickles/plonk_curve_ops.ml`
**Module:** `Make_add`

```ocaml
module Make_add (Impl : Kimchi_pasta_snarky_backend.Snark_intf) = struct
  module Utils = Util.Make (Impl)

  let seal = Tuple_lib.Double.map ~f:Utils.seal

  let add_fast ?(check_finite = true) ((x1, y1) as p1) ((x2, y2) as p2) :
      Impl.Field.t * Impl.Field.t =
    let p1 = seal p1 in
    let p2 = seal p2 in
    let open Impl in
    let open Field.Constant in
    let bool b = if b then one else zero in
    let eq a b = As_prover.(equal (read_var a) (read_var b)) in
    let same_x_bool = lazy (eq x1 x2) in
    let ( ! ) = Lazy.force in
    let ( !! ) = As_prover.read_var in
    let mk f = exists Field.typ ~compute:f in
    let same_x = mk (fun () -> bool !same_x_bool) in
    let inf =
      if check_finite then Field.zero
      else mk (fun () -> bool (!same_x_bool && not (eq y1 y2)))
    in
    let inf_z =
      mk (fun () ->
          if eq y1 y2 then zero
          else if !same_x_bool then inv (!!y2 - !!y1)
          else zero )
    in
    let x21_inv =
      mk (fun () -> if !same_x_bool then zero else inv (!!x2 - !!x1))
    in
    let s =
      mk (fun () ->
          if !same_x_bool then
            let x1_squared = square !!x1 in
            let y1 = !!y1 in
            (x1_squared + x1_squared + x1_squared) / (y1 + y1)
          else (!!y2 - !!y1) / (!!x2 - !!x1) )
    in
    let x3 = mk (fun () -> square !!s - (!!x1 + !!x2)) in
    let y3 = mk (fun () -> (!!s * (!!x1 - !!x3)) - !!y1) in
    let p3 = (x3, y3) in
    with_label "add_fast" (fun () ->
        assert_
          (EC_add_complete
             { p1; p2; p3; inf; same_x; slope = s; inf_z; x21_inv } ) ;
        p3 )
end
```

### PureScript

**File:** `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/AddComplete.purs`
**Module:** `Snarky.Circuit.Kimchi.AddComplete`

```purescript
module Snarky.Circuit.Kimchi.AddComplete where

import Prelude

import Control.Apply (lift2)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, addConstraint, exists, read, readCVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (fromInt)
import Snarky.Data.EllipticCurve (AffinePoint)

addComplete
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky (KimchiConstraint f) t m
       { p :: AffinePoint (FVar f)
       , isInfinity :: BoolVar f
       }
addComplete p1 p2 = do
  sameX <- exists $
    lift2 eq (readCVar p1.x) (readCVar p2.x)
  inf <- exists
    let
      sameY = lift2 eq (readCVar p1.y) (readCVar p2.y)
    in
      read sameX && not sameY
  infZ <- exists $
    lift2 eq (readCVar p1.y) (readCVar p2.y) >>=
      if _ then zero
      else
        read sameX >>=
          if _ then recip (readCVar p2.y - readCVar p1.y)
          else zero
  x21Inv <- exists $
    read sameX >>=
      if _ then zero
      else recip (readCVar p2.x - readCVar p1.x)
  s <- exists $
    read sameX >>=
      if _ then do
        x1 <- readCVar p1.x
        y1 <- readCVar p1.y
        pure $ (fromInt 3 * x1 * x1) / (fromInt 2 * y1)
      else
        (readCVar p2.y - readCVar p1.y) / (readCVar p2.x - readCVar p1.x)
  x3 <- exists
    let
      sVal = readCVar s
    in
      sVal * sVal - (readCVar p1.x + readCVar p2.x)
  y3 <- exists $
    readCVar s * (readCVar p1.x - readCVar x3) - readCVar p1.y
  addConstraint $ KimchiAddComplete
    { p1, p2, sameX: coerce sameX, inf: coerce inf, infZ, x21Inv, s, p3: { x: x3, y: y3 } }
  pure
    { p: { x: x3, y: y3 }
    , isInfinity: inf
    }
```

---

## Example 3: VarBaseMul

### OCaml

**File:** `mina/src/lib/pickles/plonk_curve_ops.ml`
**Module:** `Make`

```ocaml
  let scale_fast_msb_bits base
      (Pickles_types.Shifted_value.Type1.Shifted_value
        (bits_msb : Boolean.var array) ) : Field.t * Field.t =
    let ((x_base, y_base) as base) = seal base in
    let ( !! ) = As_prover.read_var in
    let mk f = exists Field.typ ~compute:f in
    (* MSB bits *)
    let num_bits = Array.length bits_msb in
    let chunks = num_bits / bits_per_chunk in
    [%test_eq: int] (num_bits mod bits_per_chunk) 0 ;
    let acc = ref (add_fast base base) in
    let n_acc = ref Field.zero in
    let rounds_rev = ref [] in
    for chunk = 0 to chunks - 1 do
      let open Field.Constant in
      let double x = x + x in
      let bs =
        Array.init bits_per_chunk ~f:(fun i ->
            (bits_msb.(Int.((chunk * bits_per_chunk) + i)) :> Field.t) )
      in
      let n_acc_prev = !n_acc in
      n_acc :=
        mk (fun () ->
            Array.fold bs ~init:!!n_acc_prev ~f:(fun acc b -> double acc + !!b) ) ;
      let accs, slopes =
        Array.fold_map bs ~init:!acc ~f:(fun (x_acc, y_acc) b ->
            let s1 =
              mk (fun () ->
                  (!!y_acc - (!!y_base * (double !!b - one)))
                  / (!!x_acc - !!x_base) )
            in
            let s1_squared = mk (fun () -> square !!s1) in
            let s2 =
              mk (fun () ->
                  (double !!y_acc / (double !!x_acc + !!x_base - !!s1_squared))
                  - !!s1 )
            in
            let x_res = mk (fun () -> !!x_base + square !!s2 - !!s1_squared) in
            let y_res = mk (fun () -> ((!!x_acc - !!x_res) * !!s2) - !!y_acc) in
            let acc' = (x_res, y_res) in
            (acc', (acc', s1)) )
        |> snd |> Array.unzip
      in
      let accs = Array.append [| !acc |] accs in
      acc := Array.last accs ;
      rounds_rev :=
        { Kimchi_backend_common.Scale_round.accs
        ; bits = bs
        ; ss = slopes
        ; n_prev = n_acc_prev
        ; n_next = !n_acc
        ; base
        }
        :: !rounds_rev
    done ;
    assert_ (EC_scale { state = Array.of_list_rev !rounds_rev }) ;
    (* TODO: Return n_acc ? *)
    !acc
```

### PureScript

**File:** `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/VarBaseMul.purs`
**Module:** `Snarky.Circuit.Kimchi.VarBaseMul`

```purescript
varBaseMul
  :: forall t m @n bitsUsed l @nChunks f
   . FieldSizeInBits f n
  => Add bitsUsed l n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> Type1 (FVar f)
  -> Snarky (KimchiConstraint f) t m
       { g :: AffinePoint (FVar f)
       , lsbBits :: Vector n (FVar f)
       }
varBaseMul base (Type1 t) = do
  lsbBits <- exists do
    F vVal <- readCVar t
    pure $ unpackPure vVal
  { p } <- addComplete base base
  let
    msbBits :: Vector n (FVar f)
    msbBits = coerce $ Vector.reverse lsbBits

    msbBitsUsed = Vector.take @bitsUsed msbBits

    chunks :: Vector nChunks (Vector 5 (FVar f))
    chunks = Vector.chunks @5 msbBitsUsed
  Tuple rounds_rev { nAccPrev: nAcc, acc: g } <- mapAccumM
    ( \s bs -> do
        nAcc <- exists do
          nAccPrevVal :: F f <- readCVar s.nAccPrev
          bsVal <- read @(Vector _ _) bs
          pure $ foldl (\a b -> double a + b) nAccPrevVal bsVal
        Tuple accs slopes <- Vector.unzip <<< fst <$> do
          mapAccumM
            ( \a b -> exists do
                { x: xAcc, y: yAcc } <- read @(AffinePoint _) a
                bVal <- readCVar b
                { x: xBase, y: yBase } <- read @(AffinePoint _) base
                s1 <-
                  let
                    d = xAcc - xBase
                  in
                    if d == zero then throwAsProver $ DivisionByZero
                      { context: "varBaseMul"
                      , expression: Just "xAcc - xBase"
                      }
                    else pure $ (yAcc - (yBase * (double bVal - one))) / d
                let
                  s1Squared = s1 * s1
                  s2 = (double yAcc / (double xAcc + xBase - s1Squared)) - s1
                  xRes = (xBase + (s2 * s2) - s1Squared)
                  yRes = (xAcc - xRes) * s2 - yAcc
                  a' = { x: xRes, y: yRes }
                pure $ Tuple (Tuple a' s1) a'
            )
            s.acc
            bs
        pure $ Tuple
          ( { accs: s.acc :< accs
            , bits: bs
            , slopes
            , nPrev: s.nAccPrev
            , nNext: nAcc
            , base
            } :: ScaleRound f
          )
          { nAccPrev: nAcc, acc: Vector.last accs }

    )
    { nAccPrev: const_ zero, acc: p }
    chunks
  let rounds = Vector.reverse rounds_rev
  addConstraint $ KimchiVarBaseMul $ Vector.toUnfoldable rounds
  assertEqual_ nAcc t
  pure { g, lsbBits: coerce lsbBits }
  where
  double x = x + x
```

---

## Example 4: EndoScalar

### OCaml

**File:** `mina/src/lib/pickles/scalar_challenge.ml`
**Module:** `(top level)`

```ocaml
let to_field_checked' (type f) ?(num_bits = num_bits)
    (module Impl : Kimchi_pasta_snarky_backend.Snark_intf with type field = f)
    { SC.inner = (scalar : Impl.Field.t) } =
  let open Impl in
  let neg_one = Field.Constant.(negate one) in
  let a_func = function
    | 0 ->
        Field.Constant.zero
    | 1 ->
        Field.Constant.zero
    | 2 ->
        neg_one
    | 3 ->
        Field.Constant.one
    | _ ->
        raise (Invalid_argument "a_func")
  in
  let b_func = function
    | 0 ->
        neg_one
    | 1 ->
        Field.Constant.one
    | 2 ->
        Field.Constant.zero
    | 3 ->
        Field.Constant.zero
    | _ ->
        raise (Invalid_argument "a_func")
  in
  let ( !! ) = As_prover.read_var in
  (* MSB bits *)
  let bits_msb =
    lazy
      (let open Field.Constant in
      unpack !!scalar |> Fn.flip List.take num_bits |> Array.of_list_rev)
  in
  let nybbles_per_row = 8 in
  let bits_per_row = 2 * nybbles_per_row in
  [%test_eq: int] (num_bits mod bits_per_row) 0 ;
  let rows = num_bits / bits_per_row in
  let nybbles_by_row =
    lazy
      (Array.init rows ~f:(fun i ->
           Array.init nybbles_per_row ~f:(fun j ->
               let bit = (bits_per_row * i) + (2 * j) in
               let b0 = (Lazy.force bits_msb).(bit + 1) in
               let b1 = (Lazy.force bits_msb).(bit) in
               Bool.to_int b0 + (2 * Bool.to_int b1) ) ) )
  in
  let two = Field.of_int 2 in
  let a = ref two in
  let b = ref two in
  let n = ref Field.zero in
  let mk f = exists Field.typ ~compute:f in
  let state = ref [] in
  for i = 0 to rows - 1 do
    let n0 = !n in
    let a0 = !a in
    let b0 = !b in
    let xs =
      Array.init nybbles_per_row ~f:(fun j ->
          mk (fun () ->
              Field.Constant.of_int (Lazy.force nybbles_by_row).(i).(j) ) )
    in
    let open Field.Constant in
    let double x = x + x in
    let n8 =
      mk (fun () ->
          Array.fold xs ~init:!!n0 ~f:(fun acc x ->
              (acc |> double |> double) + !!x ) )
    in
    let a8 =
      mk (fun () ->
          Array.fold
            (Lazy.force nybbles_by_row).(i)
            ~init:!!a0
            ~f:(fun acc x -> (acc |> double) + a_func x) )
    in
    let b8 =
      mk (fun () ->
          Array.fold
            (Lazy.force nybbles_by_row).(i)
            ~init:!!b0
            ~f:(fun acc x -> (acc |> double) + b_func x) )
    in
    state :=
      { Kimchi_backend_common.Endoscale_scalar_round.a0
      ; a8
      ; b0
      ; b8
      ; n0
      ; n8
      ; x0 = xs.(0)
      ; x1 = xs.(1)
      ; x2 = xs.(2)
      ; x3 = xs.(3)
      ; x4 = xs.(4)
      ; x5 = xs.(5)
      ; x6 = xs.(6)
      ; x7 = xs.(7)
      }
      :: !state ;
    n := n8 ;
    a := a8 ;
    b := b8 ;
    ()
  done ;
  with_label __LOC__ (fun () ->
      assert_ (EC_endoscalar { state = Array.of_list_rev !state }) ) ;
  (!a, !b, !n)
```

### PureScript

**File:** `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/EndoScalar.purs`
**Module:** `Snarky.Circuit.Kimchi.EndoScalar`

```purescript
module Snarky.Circuit.Kimchi.EndoScalar where

import Prelude

import Data.Traversable (foldl)
import Data.Tuple (Tuple(..))
import Effect.Exception.Unsafe (unsafeThrow)
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (EvaluationError(..))
import Snarky.Circuit.Curves as EllipticCurve
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, addConstraint, add_, assertEqual_, const_, exists, mul_, read, readCVar, scale_)
import Snarky.Circuit.DSL.Bits (unpackPure)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (class FieldSizeInBits, fromInt)
import Data.Fin (unsafeFinite)
import Data.Vector (Vector, chunks, (!!))
import Data.Vector as Vector

newtype ScalarChallenge f = ScalarChallenge f

toField
  :: forall f t m n _l
   . FieldSizeInBits f n
  => Add 128 _l n
  => CircuitM f (KimchiConstraint f) t m
  => ScalarChallenge (FVar f)
  -> FVar f
  -> Snarky (KimchiConstraint f) t m (FVar f)
toField (ScalarChallenge scalar) endo = do
  lsbBits :: Vector 128 (BoolVar f) <- exists do
    F vVal <- readCVar scalar
    pure $ Vector.take @128 $ unpackPure $ vVal
  let
    msbBits :: Vector 128 (FVar f)
    msbBits = coerce $ Vector.reverse lsbBits

    nibblesByRow :: Vector 8 (Vector 8 (FVar f))
    nibblesByRow =
      let
        f :: Vector 2 (FVar f) -> FVar f
        f v = (v !! unsafeFinite 1) `add_` scale_ (fromInt 2) (v !! unsafeFinite 0)
      in
        chunks @8 $ map f (chunks @2 msbBits)

  Tuple rowsRev { a, b, n } <- mapAccumM
    ( \st nibble -> do
        let
          double x = x + x
        { n8, a8, b8 } <- exists do
          xs :: Vector 8 _ <- read nibble
          { a: a0, b: b0, n: n0 } <- read @{ a :: F f, b :: F f, n :: F f } st
          let
            n8 = foldl (\acc x -> double (double acc) + x) n0 xs
            a8 = foldl (\acc x -> double acc + aF x) a0 xs
            b8 = foldl (\acc x -> double acc + bF x) b0 xs
          pure { n8, a8, b8 }
        pure $ Tuple
          { n0: st.n, a0: st.a, b0: st.b, xs: nibble, n8, a8, b8 }
          { n: n8, a: a8, b: b8 }
    )
    { a: const_ $ fromInt 2
    , b: const_ $ fromInt 2
    , n: const_ $ zero
    }
    nibblesByRow
  addConstraint $ KimchiEndoScalar rowsRev
  assertEqual_ n scalar
  a `mul_` endo <#>
    add_ b

  where
  aF :: F f -> F f
  aF x
    | x == zero = zero
    | x == one = zero
    | x == fromInt 2 = -one
    | x == fromInt 3 = one
    | otherwise = unsafeThrow ("Unexpected aF application: " <> show x)

  bF :: F f -> F f
  bF x
    | x == zero = -one
    | x == one = one
    | x == fromInt 2 = zero
    | x == fromInt 3 = zero
    | otherwise = unsafeThrow ("Unexpected bF application: " <> show x)
```

---

## Example 5: EndoMul

### OCaml

**File:** `mina/src/lib/pickles/scalar_challenge.ml`
**Module:** `Make`

```ocaml
  let endo ?(num_bits = num_bits) t { SC.inner = (scalar : Field.t) } =
    let ( !! ) = As_prover.read_var in
    (* MSB bits *)
    let bits =
      lazy
        (let open Field.Constant in
        unpack !!scalar |> Fn.flip List.take num_bits
        |> Array.of_list_rev_map ~f:(fun b -> if b then one else zero))
    in
    let bits () = Lazy.force bits in
    let xt, yt = Tuple_lib.Double.map t ~f:seal in
    let bits_per_row = 4 in
    let rows = num_bits / bits_per_row in
    let acc =
      with_label __LOC__ (fun () ->
          let p = G.( + ) t (seal (Field.scale xt Endo.base), yt) in
          ref G.(p + p) )
    in
    let n_acc = ref Field.zero in
    let mk f = exists Field.typ ~compute:f in
    let rounds_rev = ref [] in
    for i = 0 to rows - 1 do
      let n_acc_prev = !n_acc in
      let b1 = mk (fun () -> (bits ()).(i * bits_per_row)) in
      let b2 = mk (fun () -> (bits ()).((i * bits_per_row) + 1)) in
      let b3 = mk (fun () -> (bits ()).((i * bits_per_row) + 2)) in
      let b4 = mk (fun () -> (bits ()).((i * bits_per_row) + 3)) in
      let open Field.Constant in
      let double x = x + x in
      let xp, yp = !acc in
      let xq1 = mk (fun () -> (one + ((Endo.base - one) * !!b1)) * !!xt) in
      let yq1 = mk (fun () -> (double !!b2 - one) * !!yt) in

      let s1 = mk (fun () -> (!!yq1 - !!yp) / (!!xq1 - !!xp)) in
      let s1_squared = mk (fun () -> square !!s1) in
      let s2 =
        mk (fun () ->
            (double !!yp / (double !!xp + !!xq1 - !!s1_squared)) - !!s1 )
      in

      let xr = mk (fun () -> !!xq1 + square !!s2 - !!s1_squared) in
      let yr = mk (fun () -> ((!!xp - !!xr) * !!s2) - !!yp) in

      let xq2 = mk (fun () -> (one + ((Endo.base - one) * !!b3)) * !!xt) in
      let yq2 = mk (fun () -> (double !!b4 - one) * !!yt) in
      let s3 = mk (fun () -> (!!yq2 - !!yr) / (!!xq2 - !!xr)) in
      let s3_squared = mk (fun () -> square !!s3) in
      let s4 =
        mk (fun () ->
            (double !!yr / (double !!xr + !!xq2 - !!s3_squared)) - !!s3 )
      in

      let xs = mk (fun () -> !!xq2 + square !!s4 - !!s3_squared) in
      let ys = mk (fun () -> ((!!xr - !!xs) * !!s4) - !!yr) in
      acc := (xs, ys) ;
      n_acc :=
        mk (fun () ->
            !!n_acc_prev |> double |> ( + ) !!b1 |> double |> ( + ) !!b2
            |> double |> ( + ) !!b3 |> double |> ( + ) !!b4 ) ;
      rounds_rev :=
        { Kimchi_backend_common.Endoscale_round.xt
        ; yt
        ; xp
        ; yp
        ; n_acc = n_acc_prev
        ; xr
        ; yr
        ; s1
        ; s3
        ; b1
        ; b2
        ; b3
        ; b4
        }
        :: !rounds_rev
    done ;
    let xs, ys = !acc in
    with_label __LOC__ (fun () ->
        assert_
          (EC_endoscale
             { xs; ys; n_acc = !n_acc; state = Array.of_list_rev !rounds_rev }
          ) ) ;
    with_label __LOC__ (fun () -> Field.Assert.equal !n_acc scalar) ;
    !acc
```

### PureScript

**File:** `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/EndoMul.purs`
**Module:** `Snarky.Circuit.Kimchi.EndoMul`

```purescript
module Snarky.Circuit.Kimchi.EndoMul (endo) where

import Prelude

import Data.Tuple (Tuple(..))
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky, addConstraint, assertEqual_, const_, exists, read, readCVar, scale_)
import Snarky.Circuit.DSL.Bits (unpackPure)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, endoBase)
import Snarky.Data.EllipticCurve (AffinePoint)
import Data.Fin (unsafeFinite)
import Data.Vector (Vector, (!!))
import Data.Vector as Vector

endo
  :: forall f f' t m n _l
   . FieldSizeInBits f n
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => Add 128 _l n
  => AffinePoint (FVar f)
  -> FVar f
  -> Snarky (KimchiConstraint f) t m
       (AffinePoint (FVar f))
endo g scalar = do
  msbBits <- exists do
    F vVal <- readCVar scalar
    let lsbBits = Vector.take @128 $ unpackPure vVal
    pure $ map (\x -> if x then (one :: F f) else zero) (Vector.reverse lsbBits)
  -- acc = [2] (g + \phi g)
  let
    chunks :: Vector 32 (Vector 4 (FVar f))
    chunks = Vector.chunks @4 msbBits
  accInit <- do
    { p } <- addComplete g (g { x = scale_ (endoBase @f @f') g.x })
    _.p <$> addComplete p p
  Tuple rounds { nAcc, acc } <- mapAccumM
    ( \st bs -> do
        { p, r, s, s1, s3, nAccNext, nAccPrev } <- exists do
          { x: xt, y: yt } <- read @(AffinePoint _) g
          bits <- read bs
          let
            b1 = bits !! unsafeFinite 0
            b2 = bits !! unsafeFinite 1
            b3 = bits !! unsafeFinite 2
            b4 = bits !! unsafeFinite 3
          { x: xp, y: yp } <- read @(AffinePoint _) st.acc
          let
            xq1 = (one + (F (endoBase @f @f') - one) * b1) * xt
            yq1 = (double b2 - one) * yt
            s1 = (yq1 - yp) / (xq1 - xp)
            s1_squared = square s1
            s2 = (double yp / (double xp + xq1 - s1_squared)) - s1
            xr = xq1 + square s2 - s1_squared
            yr = ((xp - xr) * s2) - yp
            xq2 = (one + (F (endoBase @f @f') - one) * b3) * xt
            yq2 = (double b4 - one) * yt
            s3 = (yq2 - yr) / (xq2 - xr)
            s3_squared = square s3
            s4 = (double yr / (double xr + xq2 - s3_squared)) - s3
            xs = xq2 + square s4 - s3_squared
            ys = ((xr - xs) * s4) - yr
          nAccPrevVal <- readCVar st.nAcc
          pure
            { p: { x: xp, y: yp }
            , r: { x: xr, y: yr }
            , s1
            , s3
            , s: { x: xs, y: ys }
            , nAccPrev: nAccPrevVal
            , nAccNext: double (double (double (double nAccPrevVal + b1) + b2) + b3) + b4
            }
        pure $ Tuple
          { bits: bs, p, r, s1, s3, t: g, nAcc: nAccPrev, nAccNext, s }
          { nAcc: nAccNext, acc: s }
    )
    { nAcc: const_ zero, acc: accInit }
    chunks
  assertEqual_ nAcc scalar
  addConstraint $ KimchiEndoMul { nAcc, s: acc, state: rounds }
  pure acc
  where
  double x = x + x
  square x = x * x
```

---

## Example 6: Curve Circuits

### OCaml

**File:** `mina/src/lib/snarky_curves/snarky_curves.ml`
**Module:** `Make_weierstrass_checked`

```ocaml
module Make_weierstrass_checked
    (F : Snarky_field_extensions.Intf.S) (Scalar : sig
      type t

      val of_int : int -> t
    end) (Curve : sig
      type t

      val random : unit -> t

      val to_affine_exn : t -> F.Unchecked.t * F.Unchecked.t

      val of_affine : F.Unchecked.t * F.Unchecked.t -> t

      val double : t -> t

      val ( + ) : t -> t -> t

      val negate : t -> t

      val scale : t -> Scalar.t -> t
    end)
    (Params : Params_intf with type field := F.Unchecked.t) (Override : sig
      val add : (F.t * F.t -> F.t * F.t -> (F.t * F.t) F.Impl.Checked.t) option
    end) :
  Weierstrass_checked_intf
    with module Impl := F.Impl
     and type unchecked := Curve.t
     and type t = F.t * F.t = struct
  open F.Impl

  type t = F.t * F.t

  let assert_on_curve (x, y) =
    let open F in
    let%bind x2 = square x in
    let%bind x3 = x2 * x in
    let%bind ax = constant Params.a * x in
    assert_square y (x3 + ax + constant Params.b)

  let typ : (t, Curve.t) Typ.t =
    let (Typ unchecked) =
      Typ.transport
        Typ.(tuple2 F.typ F.typ)
        ~there:Curve.to_affine_exn ~back:Curve.of_affine
    in
    Typ { unchecked with check = assert_on_curve }

  let negate ((x, y) : t) : t = (x, F.negate y)

  let constant (t : Curve.t) : t =
    let x, y = Curve.to_affine_exn t in
    F.(constant x, constant y)

  let assert_equal (x1, y1) (x2, y2) =
    let%map () = F.assert_equal x1 x2 and () = F.assert_equal y1 y2 in
    ()

  module Assert = struct
    let on_curve = assert_on_curve

    let equal = assert_equal
  end

  open Let_syntax

  let%snarkydef_ add' ~div (ax, ay) (bx, by) =
    let open F in
    let%bind lambda = div (by - ay) (bx - ax) in
    let%bind cx =
      exists typ
        ~compute:
          (let open As_prover in
          let open Let_syntax in
          let%map ax = read typ ax
          and bx = read typ bx
          and lambda = read typ lambda in
          Unchecked.(square lambda - (ax + bx)))
    in
    let%bind () =
      (* lambda^2 = cx + ax + bx
            cx = lambda^2 - (ax + bc)
      *)
      assert_square lambda F.(cx + ax + bx)
    in
    let%bind cy =
      exists typ
        ~compute:
          (let open As_prover in
          let open Let_syntax in
          let%map ax = read typ ax
          and ay = read typ ay
          and cx = read typ cx
          and lambda = read typ lambda in
          Unchecked.((lambda * (ax - cx)) - ay))
    in
    let%map () = assert_r1cs lambda (ax - cx) (cy + ay) in
    (cx, cy)

  let add' ~div p1 p2 =
    match Override.add with Some add -> add p1 p2 | None -> add' ~div p1 p2

  (* This function MUST NOT be called UNLESS you are certain the two points
     on which it is called are not equal. If it is called on equal points,
     the prover can return almost any curve point they want to from this function. *)
  let add_unsafe p q =
    let%map r = add' ~div:F.div_unsafe p q in
    `I_thought_about_this_very_carefully r

  let add_exn p q = add' ~div:(fun x y -> F.inv_exn y >>= F.(( * ) x)) p q

  (* TODO-someday: Make it so this doesn't have to compute both branches *)
  let if_ b ~then_:(tx, ty) ~else_:(ex, ey) =
    let%map x = F.if_ b ~then_:tx ~else_:ex
    and y = F.if_ b ~then_:ty ~else_:ey in
    (x, y)

  let%snarkydef_ double (ax, ay) =
    let open F in
    let%bind x_squared = square ax in
    let%bind lambda =
      exists typ
        ~compute:
          As_prover.(
            map2 (read typ x_squared) (read typ ay) ~f:(fun x_squared ay ->
                let open F.Unchecked in
                (x_squared + x_squared + x_squared + Params.a) * inv (ay + ay) ))
    in
    let%bind bx =
      exists typ
        ~compute:
          As_prover.(
            map2 (read typ lambda) (read typ ax) ~f:(fun lambda ax ->
                let open F.Unchecked in
                square lambda - (ax + ax) ))
    in
    let%bind by =
      exists typ
        ~compute:
          (let open As_prover in
          let open Let_syntax in
          let%map lambda = read typ lambda
          and ax = read typ ax
          and ay = read typ ay
          and bx = read typ bx in
          F.Unchecked.((lambda * (ax - bx)) - ay))
    in
    let two = Field.of_int 2 in
    let%map () =
      assert_r1cs (F.scale lambda two) ay
        (F.scale x_squared (Field.of_int 3) + F.constant Params.a)
    and () = assert_square lambda (bx + F.scale ax two)
    and () = assert_r1cs lambda (ax - bx) (by + ay) in
    (bx, by)
end
```

### PureScript

**File:** `packages/snarky-curves/src/Snarky/Circuit/Curves.purs`

```purescript
module Snarky.Circuit.Curves
  ( assertOnCurve
  , assertEqual
  , negate
  , if_
  , add_
  , double
  ) where

import Prelude

import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, UnChecked(..), addConstraint, assertEqual_, assertSquare_, const_, div_, exists, mul_, negate_, pow_, r1cs, readCVar, scale_, sub_)
import Snarky.Circuit.DSL as Snarky
import Snarky.Curves.Class (class PrimeField, fromInt)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)

assertOnCurve
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => CurveParams (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky c t m Unit
assertOnCurve { a, b } { x, y } = do
  rhs <- (x `pow_` 3) + (a `mul_` x) + (pure b)
  y2 <- mul_ y y
  assertEqual_ y2 rhs

assertEqual
  :: forall f c t m
   . CircuitM f c t m
  => AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky c t m Unit
assertEqual { x: x1, y: y1 } { x: x2, y: y2 } = do
  assertEqual_ x1 x2
  assertEqual_ y1 y2

negate
  :: forall f c t m
   . CircuitM f c t m
  => AffinePoint (FVar f)
  -> Snarky c t m (AffinePoint (FVar f))
negate { x, y } = do
  pure { x, y: negate_ y }

if_
  :: forall f c t m
   . CircuitM f c t m
  => BoolVar f
  -> AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky c t m (AffinePoint (FVar f))
if_ b { x: x1, y: y1 } { x: x2, y: y2 } = do
  x <- Snarky.if_ b x1 x2
  y <- Snarky.if_ b y1 y2
  pure { x, y }

-- N.B. This function is unsafe, if the x value is the same for both points
-- bad things can happen, i.e.
--   1. If the points are equal 
--   2. If the points are mutual inverses
add_
  :: forall f c t m
   . Partial
  => CircuitM f c t m
  => AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky c t m (AffinePoint (FVar f))
add_ { x: ax, y: ay } { x: bx, y: by } = do
  lambda <- div_ (sub_ by ay) (sub_ bx ax)

  UnChecked cx <- exists do
    axVal <- readCVar ax
    bxVal <- readCVar bx
    lambdaVal <- readCVar lambda
    pure $ UnChecked $ (lambdaVal * lambdaVal) - (axVal + bxVal)

  assertSquare_ lambda (Snarky.add_ (Snarky.add_ cx ax) bx)

  UnChecked cy <- exists do
    axVal <- readCVar ax
    ayVal <- readCVar ay
    cxVal <- readCVar cx
    lambdaVal <- readCVar lambda
    pure $ UnChecked $ (lambdaVal * (axVal - cxVal)) - ayVal

  addConstraint $ r1cs
    { left: lambda
    , right: sub_ ax cx
    , output: Snarky.add_ cy ay
    }

  pure { x: cx, y: cy }

double
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => CurveParams f
  -> AffinePoint (FVar f)
  -> Snarky c t m (AffinePoint (FVar f))
double { a } { x: ax, y: ay } = do
  xSquared <- mul_ ax ax

  lambda <- exists do
    xSquaredVal <- readCVar xSquared
    ayVal <- readCVar ay
    pure $ (xSquaredVal + xSquaredVal + xSquaredVal + F a) / (ayVal + ayVal)

  UnChecked bx <- exists do
    lambdaVal <- readCVar lambda
    axVal <- readCVar ax
    pure $ UnChecked $ (lambdaVal * lambdaVal) - (axVal + axVal)

  assertSquare_ lambda (Snarky.add_ bx (scale_ (fromInt 2) ax))

  UnChecked by <- exists do
    lambdaVal <- readCVar lambda
    axVal <- readCVar ax
    ayVal <- readCVar ay
    bxVal <- readCVar bx
    pure $ UnChecked $ (lambdaVal * (axVal - bxVal)) - ayVal

  let aConst = const_ a

  addConstraint $ r1cs
    { left: scale_ (fromInt 2) lambda
    , right: ay
    , output: Snarky.add_ (scale_ (fromInt 3) xSquared) aConst
    }

  addConstraint $ r1cs
    { left: lambda
    , right: sub_ ax bx
    , output: Snarky.add_ by ay
    }

  pure { x: bx, y: by }
```

---

## Example 7: Snarky Base

### OCaml

**File:** `mina/src/lib/snarky/src/base/snark0.ml`
**Module:** `Field`

```ocaml
module Field = struct
    include Field0

    let gen =
      Quickcheck.Generator.map
        Bignum_bigint.(gen_incl zero (size - one))
        ~f:(fun x -> Bigint.(to_field (of_bignum_bigint x)))

    let gen_incl lo hi =
      let lo_bigint = Bigint.(to_bignum_bigint @@ of_field lo) in
      let hi_bigint = Bigint.(to_bignum_bigint @@ of_field hi) in
      Quickcheck.Generator.map
        Bignum_bigint.(gen_incl lo_bigint hi_bigint)
        ~f:(fun x -> Bigint.(to_field (of_bignum_bigint x)))

    let gen_uniform =
      Quickcheck.Generator.map
        Bignum_bigint.(gen_uniform_incl zero (size - one))
        ~f:(fun x -> Bigint.(to_field (of_bignum_bigint x)))

    let gen_uniform_incl lo hi =
      let lo_bigint = Bigint.(to_bignum_bigint @@ of_field lo) in
      let hi_bigint = Bigint.(to_bignum_bigint @@ of_field hi) in
      Quickcheck.Generator.map
        Bignum_bigint.(gen_uniform_incl lo_bigint hi_bigint)
        ~f:(fun x -> Bigint.(to_field (of_bignum_bigint x)))

    let typ = Typ.field

    module Var = Cvar1

    let parity x = Bigint.(test_bit (of_field x) 0)

    module Checked = struct
      include Cvar1

      let equal = Checked.equal

      let mul x y = Checked.mul ~label:"Field.Checked.mul" x y

      let square x = Checked.square ~label:"Field.Checked.square" x

      let div x y = Checked.div ~label:"Field.Checked.div" x y

      let inv x = Checked.inv ~label:"Field.Checked.inv" x

      let sqrt (x : Cvar.t) : Cvar.t Checked.t =
        match Cvar.to_constant x with
        | Some x ->
            Checked.return (Cvar.constant (Field.sqrt x))
        | _ ->
            let open Checked in
            let open Let_syntax in
            let%bind y =
              exists ~compute:As_prover.(map (read_var x) ~f:Field.sqrt) typ
            in
            let%map () = assert_square y x in
            y
            
      let choose_preimage_var = Checked.choose_preimage

      type comparison_result =
        { less : Checked.Boolean.var; less_or_equal : Checked.Boolean.var }

      let if_ = Checked.if_

      let compare ~bit_length a b =
        (* Overview of the logic:
           let n = bit_length
           We have 0 <= a < 2^n, 0 <= b < 2^n, and so
             -2^n < b - a < 2^n
           If (b - a) >= 0, then
             2^n <= 2^n + b - a < 2^{n+1},
           and so the n-th bit must be set.
           If (b - a) < 0 then
             0 < 2^n + b - a < 2^n
           and so the n-th bit must not be set.
           Thus, we can use the n-th bit of 2^n + b - a to determine whether
             (b - a) >= 0 <-> a <= b.

           We also need that the maximum value
             2^n + (2^n - 1) - 0 = 2^{n+1} - 1
           fits inside the field, so for the max field element f,
             2^{n+1} - 1 <= f -> n+1 <= log2(f) = size_in_bits - 1
        *)
        assert (Int.(bit_length <= size_in_bits - 2)) ;
        let open Checked in
        let open Let_syntax in
        [%with_label_ "compare"] (fun () ->
            let alpha_packed =
              Cvar.(constant (two_to_the bit_length) + b - a)
            in
            let%bind alpha = unpack alpha_packed ~length:Int.(bit_length + 1) in
            let prefix, less_or_equal =
              match Core_kernel.List.split_n alpha bit_length with
              | p, [ l ] ->
                  (p, l)
              | _ ->
                  failwith "compare: Invalid alpha"
            in
            let%bind not_all_zeros = Boolean.any prefix in
            let%map less = Boolean.(less_or_equal && not_all_zeros) in
            { less; less_or_equal } )
    end
end
```

### PureScript

**File:** `packages/snarky/src/Snarky/Circuit/DSL/Field.purs`

```purescript
module Snarky.Circuit.DSL.Field
  ( equals
  , equals_
  , neq_
  , sum_
  , pow_
  ) where

import Prelude

import Control.Apply (lift2)
import Data.Array (foldl)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(..), const_)
import Snarky.Circuit.CVar as CVar
import Snarky.Constraint.Basic (r1cs)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, addConstraint, exists, readCVar)
import Snarky.Circuit.Types (Bool(..), BoolVar, F, FVar)
import Snarky.Curves.Class (class PrimeField)

equals
  :: forall f c t m
   . CircuitM f c t m
  => Snarky c t m (FVar f)
  -> Snarky c t m (FVar f)
  -> Snarky c t m (BoolVar f)
equals a b = join $ lift2 equals_ a b

equals_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky c t m (BoolVar f)
equals_ a b = case a `CVar.sub_` b of
  Const f -> pure $ Const $ if f == zero then one else zero
  _ -> do
    let z = a `CVar.sub_` b
    { r, zInv } <- exists do
      zVal <- readCVar z
      pure $
        if zVal == zero then { r: one @(F f), zInv: zero }
        else { r: zero, zInv: recip zVal }
    addConstraint $ r1cs { left: r, right: z, output: const_ zero }
    addConstraint $ r1cs { left: zInv, right: z, output: const_ one `CVar.sub_` r }
    pure $ coerce r

neq_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky c t m (BoolVar f)
neq_ (a :: FVar f) (b :: FVar f) = not $ equals_ a b

sum_
  :: forall f
   . PrimeField f
  => Array (FVar f)
  -> FVar f
sum_ = foldl CVar.add_ (Const zero)

pow_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Int
  -> Snarky c t m (FVar f)
pow_ x n
  | n == 0 = one
  | n == 1 = pure x
  | otherwise = pure x * pow_ x (n - 1)
```

---

## Example 8: Merkle Tree

### OCaml

**File:** `mina/src/lib/snarky/src/base/merkle_tree.ml`
**Module:** `Merkle_tree`

```ocaml
open Core_kernel

module Address = struct
  type t = int
end

module Free_hash = struct
  type 'a t = Hash_value of 'a | Hash_empty | Merge of 'a t * 'a t
  [@@deriving sexp]

  let diff t1 t2 =
    let module M = struct
      exception Done of bool list
    end in
    let rec go path t1 t2 =
      match (t1, t2) with
      | Hash_empty, Hash_empty ->
          None
      | Hash_value x, Hash_value y ->
          (* poly equality; we don't know type of x and y *)
          if Caml.( = ) x y then None else raise (M.Done path)
      | Merge (l1, r1), Merge (l2, r2) ->
          ignore (go (false :: path) l1 l2) ;
          ignore (go (true :: path) r1 r2) ;
          None
      | Hash_empty, Hash_value _
      | Hash_empty, Merge _
      | Hash_value _, Hash_empty
      | Hash_value _, Merge _
      | Merge _, Hash_empty
      | Merge _, Hash_value _ ->
          raise (M.Done path)
    in
    try go [] t1 t2 with M.Done addr -> Some addr

  let rec run t ~hash ~merge =
    match t with
    | Hash_value x ->
        hash (Some x)
    | Hash_empty ->
        hash None
    | Merge (l, r) ->
        merge (run ~hash ~merge l) (run ~hash ~merge r)
end

type ('hash, 'a) non_empty_tree =
  | Node of 'hash * ('hash, 'a) tree * ('hash, 'a) tree
  | Leaf of 'hash * 'a

and ('hash, 'a) tree = Non_empty of ('hash, 'a) non_empty_tree | Empty
[@@deriving sexp]

type ('hash, 'a) t =
  { tree : ('hash, 'a) non_empty_tree
  ; depth : int
  ; count : int
  ; hash : 'a option -> 'hash
  ; merge : 'hash -> 'hash -> 'hash
  }
[@@deriving sexp]

let check_exn { tree; hash; merge; _ } =
  let default = hash None in
  let rec check_hash = function
    | Non_empty t ->
        check_hash_non_empty t
    | Empty ->
        default
  and check_hash_non_empty = function
    | Leaf (h, x) ->
        (* poly equality; don't know the hash type *)
        assert (Caml.( = ) h (hash (Some x))) ;
        h
    | Node (h, l, r) ->
        (* poly equality *)
        assert (Caml.( = ) (merge (check_hash l) (check_hash r)) h) ;
        h
  in
  ignore (check_hash_non_empty tree)

let non_empty_hash = function Node (h, _, _) -> h | Leaf (h, _) -> h

let depth { depth; _ } = depth

let tree_hash ~default = function
  | Empty ->
      default
  | Non_empty t ->
      non_empty_hash t

let to_list : ('hash, 'a) t -> 'a list =
  let rec go acc = function
    | Empty ->
        acc
    | Non_empty (Leaf (_, x)) ->
        x :: acc
    | Non_empty (Node (_h, l, r)) ->
        let acc' = go acc r in
        go acc' l
  in
  fun t -> go [] (Non_empty t.tree)

let left_tree hash merge depth x =
  let empty_hash = hash None in
  let rec go i h acc =
    if i = depth then (h, acc)
    else
      let h' = merge h empty_hash in
      go (i + 1) h' (Node (h', Non_empty acc, Empty))
  in
  let h = hash (Some x) in
  go 0 h (Leaf (h, x))

let insert hash merge t0 mask0 address x =
  let default = hash None in
  let rec go mask t =
    if mask = 0 then
      match t with
      | Empty ->
          Leaf (hash (Some x), x)
      | Non_empty _ ->
          failwith "Tree should be empty"
    else
      let go_left = mask land address = 0 in
      let mask' = mask lsr 1 in
      match t with
      | Empty ->
          if go_left then
            let t_l' = go mask' Empty in
            Node (merge (non_empty_hash t_l') default, Non_empty t_l', Empty)
          else
            let t_r' = go mask' Empty in
            Node (merge default (non_empty_hash t_r'), Empty, Non_empty t_r')
      | Non_empty (Node (_h, t_l, t_r)) ->
          if go_left then
            let t_l' = go mask' t_l in
            Node
              ( merge (non_empty_hash t_l') (tree_hash ~default t_r)
              , Non_empty t_l'
              , t_r )
          else
            let t_r' = go mask' t_r in
            Node
              ( merge (tree_hash ~default t_l) (non_empty_hash t_r')
              , t_l
              , Non_empty t_r' )
      | Non_empty (Leaf _) ->
          failwith "Cannot insert into leaf"
  in
  go mask0 t0

let ith_bit n i = (n lsr i) land 1 = 1

let get { tree; depth; _ } addr0 =
  let rec get t i =
    match t with Empty -> None | Non_empty t -> get_non_empty t i
  and get_non_empty t i =
    match t with
    | Node (_, l, r) ->
        let go_right = ith_bit addr0 i in
        if go_right then get r (i - 1) else get l (i - 1)
    | Leaf (_, x) ->
        Some x
  in
  get_non_empty tree (depth - 1)

let get_exn t addr = Option.value_exn (get t addr)

let set_dirty default tree addr x =
  let rec go tree addr =
    match (tree, addr) with
    | Empty, go_right :: bs ->
        let t = Non_empty (go Empty bs) in
        let l, r = if go_right then (Empty, t) else (t, Empty) in
        Node (default, l, r)
    | Empty, [] ->
        Leaf (default, x)
    | Non_empty t, _ ->
        go_non_empty t addr
  and go_non_empty tree addr =
    match (tree, addr) with
    | Leaf _, [] ->
        Leaf (default, x)
    | Node (_, l, r), go_right :: bs ->
        let l', r' =
          if go_right then (l, Non_empty (go r bs)) else (Non_empty (go l bs), r)
        in
        Node (default, l', r')
    | Leaf _, _ :: _ | Node _, [] ->
        failwith "Merkle_tree.set_dirty (go_non_empty): Mismatch"
  in
  go_non_empty tree (List.rev addr)

let recompute_hashes { tree; hash; merge; _ } =
  let h =
    let default = hash None in
    fun t -> tree_hash ~default t
  in
  let rec go = function
    | Non_empty t ->
        Non_empty (go_non_empty t)
    | Empty ->
        Empty
  and go_non_empty = function
    | Leaf (_, x) ->
        Leaf (hash (Some x), x)
    | Node (_, l, r) ->
        let l' = go l in
        let r' = go r in
        Node (merge (h l') (h r'), l', r')
  in
  go_non_empty tree

let address_of_int ~depth n : bool list =
  List.init depth ~f:(fun i -> n land (1 lsl i) <> 0)

let add_many t xs =
  let default = t.hash None in
  let left_tree_dirty depth x =
    let rec go i acc =
      if i = depth then acc
      else go (i + 1) (Node (default, Non_empty acc, Empty))
    in
    go 0 (Leaf (default, x))
  in
  let add_one_dirty { tree; depth; count; hash; merge } x =
    if count = 1 lsl depth then
      let t_r = left_tree_dirty depth x in
      { tree = Node (default, Non_empty tree, Non_empty t_r)
      ; count = count + 1
      ; depth = depth + 1
      ; hash
      ; merge
      }
    else
      { tree = set_dirty default tree (address_of_int ~depth count) x
      ; count = count + 1
      ; depth
      ; hash

      ; merge
      }
  in
  let t = List.fold_left xs ~init:t ~f:add_one_dirty in
  { t with tree = recompute_hashes t }

let add { tree; depth; count; hash; merge } x =
  if count = 1 lsl depth then
    let h_r, t_r = left_tree hash merge depth x in
    let h_l = non_empty_hash tree in
    { tree = Node (merge h_l h_r, Non_empty tree, Non_empty t_r)
    ; count = count + 1
    ; depth = depth + 1
    ; hash
    ; merge
    }
  else
    { tree = insert hash merge (Non_empty tree) (1 lsl (depth - 1)) count x
    ; count = count + 1
    ; depth
    ; hash
    ; merge
    }

let root { tree; _ } = non_empty_hash tree

let create ~hash ~merge x =
  { tree = Leaf (hash (Some x), x); count = 1; depth = 0; hash; merge }

let get_path { tree; hash; depth; _ } addr0 =
  let default = hash None in
  let rec go acc t i =
    if i < 0 then acc
    else
      let go_right = ith_bit addr0 i in
      if go_right then
        match t with
        | Leaf _ ->
            failwith "get_path"
        | Node (_h, _t_l, Empty) ->
            failwith "get_path"
        | Node (_h, t_l, Non_empty t_r) ->
            go (tree_hash ~default t_l :: acc) t_r (i - 1)
      else
        match t with
        | Leaf _ ->
            failwith "get_path"
        | Node (_h, Empty, _t_r) ->
            failwith "get_path"
        | Node (_h, Non_empty t_l, t_r) ->
            go (tree_hash ~default t_r :: acc) t_l (i - 1)
  in
  go [] tree (depth - 1)

let implied_root ~merge addr0 entry_hash path0 =
  let rec go acc i path =
    match path with
    | [] ->
        acc
    | h :: hs ->
        go (if ith_bit addr0 i then merge h acc else merge acc h) (i + 1) hs
  in
  go entry_hash 0 path0

let rec free_tree_hash = function
  | Empty ->
      Free_hash.Hash_empty
  | Non_empty (Leaf (_, x)) ->
      Hash_value x
  | Non_empty (Node (_, l, r)) ->
      Merge (free_tree_hash l, free_tree_hash r)

let free_root { tree; _ } = free_tree_hash (Non_empty tree)

let get_free_path { tree; depth; _ } addr0 =
  let rec go acc t i =
    if i < 0 then acc
    else
      let go_right = ith_bit addr0 i in
      if go_right then
        match t with
        | Leaf _ ->
            failwith "get_path"
        | Node (_h, _t_l, Empty) ->
            failwith "get_path"
        | Node (_h, t_l, Non_empty t_r) ->
            go (free_tree_hash t_l :: acc) t_r (i - 1)
      else
        match t with
        | Leaf _ ->
            failwith "get_path"
        | Node (_h, Empty, _t_r) ->
            failwith "get_path"
        | Node (_h, Non_empty t_l, t_r) ->
            go (free_tree_hash t_r :: acc) t_l (i - 1)
  in
  go [] tree (depth - 1)

let implied_free_root addr0 x path0 =
  implied_root
    ~merge:(fun a b -> Free_hash.Merge (a, b))
    addr0 (Hash_value x) path0

type ('hash, 'a) merkle_tree = ('hash, 'a) t

module Checked
    (Impl : Snark_intf.Basic) (Hash : sig
      type var

      type value

      val typ : (var, value) Impl.Typ.t

      val merge : height:int -> var -> var -> var Impl.Checked.t

      val if_ : Impl.Boolean.var -> then_:var -> else_:var -> var Impl.Checked.t

      val assert_equal : var -> var -> unit Impl.Checked.t
    end) (Elt : sig
      type var

      type value

      val typ : (var, value) Impl.Typ.t

      val hash : var -> Hash.var Impl.Checked.t
    end) =
struct
  open Impl

  module Address = struct
    type var = Boolean.var list

    type value = int

    let typ ~depth : (var, value) Typ.t =
      Typ.transport
        (Typ.list ~length:depth Boolean.typ)
        ~there:(address_of_int ~depth)
        ~back:
          (List.foldi ~init:0 ~f:(fun i acc b ->
               if b then acc lor (1 lsl i) else acc ) )
  end

  module Path = struct
    type value = Hash.value list

    type var = Hash.var list

    let typ ~depth : (var, value) Typ.t = Typ.(list ~length:depth Hash.typ)
  end

  let implied_root entry_hash addr0 path0 =
    let rec go height acc addr path =
      let open Let_syntax in
      match (addr, path) with
      | [], [] ->
          return acc
      | b :: bs, h :: hs ->
          let%bind l = Hash.if_ b ~then_:h ~else_:acc
          and r = Hash.if_ b ~then_:acc ~else_:h in
          let%bind acc' = Hash.merge ~height l r in
          go (height + 1) acc' bs hs
      | _, _ ->
          failwith
            "Merkle_tree.Checked.implied_root: address, path length mismatch"
    in
    go 0 entry_hash addr0 path0

  type _ Request.t +=
    | Get_element : Address.value -> (Elt.value * Path.value) Request.t
    | Get_path : Address.value -> Path.value Request.t
    | Set : Address.value * Elt.value -> unit Request.t

  (* addr0 should have least significant bit first *)
  let%snarkydef_ fetch_and_update_req ~(depth : int) root addr0 ~f :
      (Hash.var * [ `Old of Elt.var ] * [ `New of Elt.var ]) Checked.t =
    let open Let_syntax in
    let%bind prev, prev_path =
      request_witness
        Typ.(Elt.typ * Path.typ ~depth)
        Impl.As_prover.(
          read (Address.typ ~depth) addr0 >>| fun addr -> Get_element addr)
    in
    let%bind () =
      let%bind prev_entry_hash = Elt.hash prev in
      implied_root prev_entry_hash addr0 prev_path >>= Hash.assert_equal root
    in
    let%bind next = f prev in
    let%bind next_entry_hash = Elt.hash next in
    let%bind () =
      perform
        (let open Impl.As_prover in
        let open Let_syntax in
        let%map addr = read (Address.typ ~depth) addr0
        and next = read Elt.typ next in
        Set (addr, next))
    in
    let%map new_root = implied_root next_entry_hash addr0 prev_path in
    (new_root, `Old prev, `New next)

  (* addr0 should have least significant bit first *)
  let%snarkydef_ modify_req ~(depth : int) root addr0 ~f : Hash.var Checked.t =
    let%map root, _, _ = fetch_and_update_req ~depth root addr0 ~f in
    root

  (* addr0 should have least significant bit first *)
  let%snarkydef_ get_req ~(depth : int) root addr0 : Elt.var Checked.t =
    let open Let_syntax in
    let%bind prev, prev_path =
      request_witness
        Typ.(Elt.typ * Path.typ ~depth)
        Impl.As_prover.(
          map (read (Address.typ ~depth) addr0) ~f:(fun a -> Get_element a))
    in
    let%bind () =
      let%bind prev_entry_hash = Elt.hash prev in
      implied_root prev_entry_hash addr0 prev_path >>= Hash.assert_equal root
    in
    return prev

  (* addr0 should have least significant bit first *)
  let%snarkydef_ update_req ~(depth : int) ~root ~prev ~next addr0 :
      Hash.var Checked.t =
    let open Let_syntax in
    let%bind prev_entry_hash = Elt.hash prev
    and next_entry_hash = Elt.hash next
    and prev_path =
      request_witness (Path.typ ~depth)
        Impl.As_prover.(
          map (read (Address.typ ~depth) addr0) ~f:(fun a -> Get_path a))
    in
    let%bind () =
      implied_root prev_entry_hash addr0 prev_path >>= Hash.assert_equal root
    in
    let%bind () =
      perform
        (let open Impl.As_prover in
        let open Let_syntax in
        let%map addr = read (Address.typ ~depth) addr0
        and next = read Elt.typ next in
        Set (addr, next))
    in
    implied_root next_entry_hash addr0 prev_path
end

module Run = struct
  module Make
      (Impl : Snark_intf.Run_basic) (Hash : sig
        type var

        type value

        val typ : (var, value) Impl.Typ.t

        val merge : height:int -> var -> var -> var

        val if_ : Impl.Boolean.var -> then_:var -> else_:var -> var

        val assert_equal : var -> var -> unit
      end) (Elt : sig
        type var

        type value

        val typ : (var, value) Impl.Typ.t

        val hash : var -> Hash.var
      end) =
  struct
    open Impl

    include
      Checked
        (Impl.Internal_Basic)
        (struct
          include Hash

          let merge ~height x y = make_checked (fun () -> merge ~height x y)

          let if_ x ~then_ ~else_ = make_checked (fun () -> if_ x ~then_ ~else_)

          let assert_equal x y = make_checked (fun () -> assert_equal x y)
        end)
        (struct
          include Elt

          let hash var = make_checked (fun () -> hash var)
        end)

    let implied_root entry_hash addr0 path0 =
      run_checked (implied_root entry_hash addr0 path0)

    let modify_req ~depth root addr0 ~f =
      run_checked
        (modify_req ~depth root addr0 ~f:(fun x -> make_checked (fun () -> f x)))

    let get_req ~depth root addr0 = run_checked (get_req ~depth root addr0)

    let update_req ~depth ~root ~prev ~next addr0 =
      run_checked (update_req ~depth ~root ~prev ~next addr0)
  end
end
```

### PureScript

**File:** `packages/merkle-tree/src/Snarky/Circuit/MerkleTree.purs`
**Module:** `Snarky.Circuit.MerkleTree`

```purescript
module Snarky.Circuit.MerkleTree
  ( class MerkleRequestM
  , getElement
  , getPath
  , setValue
  , get
  , impliedRoot
  , fetchAndUpdate
  , update
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class MerkleHashable, hash, mergeCircuit)
import Data.MerkleTree.Sized (Address, AddressVar(..), Path(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Poseidon.Class (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertEqual_, exists, if_, read)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Circuit.Types (class CheckedType, class CircuitType)
import Snarky.Constraint.Kimchi (KimchiConstraint)

class
  ( Monad m
  , MerkleHashable v (Digest (F f))
  , CircuitType f v var
  , CheckedType var c
  ) <=
  MerkleRequestM m f v c (d :: Int) var
  | v f -> var
  , c -> f
  , m -> v where
  getElement :: Address d -> m { value :: v, path :: Path d (Digest (F f)) }
  getPath :: Address d -> m (Path d (Digest (F f)))
  setValue :: Address d -> v -> m Unit

get
  :: forall t m f d v var
   . Reflectable d Int
  => PoseidonField f
  => MerkleRequestM m f v (KimchiConstraint f) d var
  => CircuitM f (KimchiConstraint f) t m
  => MerkleHashable var (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => AddressVar d f
  -> Digest (FVar f)
  -> Snarky (KimchiConstraint f) t m var
get addr (Digest root) = do
  { value, path } <- exists do
    a <- read addr
    lift $ getElement @_ @_ @v @(KimchiConstraint f) @d a
  h <- hash $ Just value
  impliedRoot addr h path >>= \(Digest d) ->
    assertEqual_ root d
  pure value

-- | Fetch an element, apply a modification, and update the tree.
-- |
-- | This function:
-- | 1. Witnesses the current element and path
-- | 2. Verifies the old element hashes to the given root
-- | 3. Applies the modification function to get the new element
-- | 4. Updates the underlying tree state via setValue
-- | 5. Computes and returns the new root along with old and new elements
fetchAndUpdate
  :: forall t m f d v var
   . Reflectable d Int
  => PoseidonField f
  => MerkleRequestM m f v (KimchiConstraint f) d var
  => MerkleHashable var (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => CircuitM f (KimchiConstraint f) t m
  => AddressVar d f
  -> Digest (FVar f)
  -> (var -> Snarky (KimchiConstraint f) t m var)
  -> Snarky (KimchiConstraint f) t m
       { root :: Digest (FVar f)
       , old :: var
       , new :: var
       }
fetchAndUpdate addr (Digest root) f = do
  -- Get element and path as witnesses
  { value: prev, path } <- exists do
    a <- read addr
    lift $ getElement @m @_ @v @(KimchiConstraint f) @d a
  -- Hash old element and verify against root
  prevHash <- hash $ Just prev
  impliedRoot addr prevHash path >>= \(Digest d) ->
    assertEqual_ root d
  -- Apply modification function
  next <- f prev
  -- Update the tree with the new value
  _ <- exists do
    a <- read addr
    n <- read @v next
    lift $ setValue @_ @_ @v @(KimchiConstraint f) @d a n
  -- Hash new element and compute new root
  nextHash <- hash $ Just next
  newRoot <- impliedRoot addr nextHash path
  pure { root: newRoot, old: prev, new: next }

-- | Update an element when you already have both old and new values.
-- |
-- | This function:
-- | 1. Witnesses only the path (not the element)
-- | 2. Verifies the old element hashes to the given root
-- | 3. Updates the underlying tree state via setValue
-- | 4. Computes and returns the new root
update
  :: forall t m f d v var
   . Reflectable d Int
  => PoseidonField f
  => MerkleRequestM m f v (KimchiConstraint f) d var
  => MerkleHashable var (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => CircuitM f (KimchiConstraint f) t m
  => AddressVar d f
  -> Digest (FVar f)
  -> var
  -> var
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
update addr (Digest root) prev next = do
  -- Witness only the path
  path <- exists do
    a <- read addr
    lift $ getPath @m @_ @v @(KimchiConstraint f) @d a
  -- Hash old element and verify against root
  prevHash <- hash $ Just prev
  impliedRoot addr prevHash path >>= \(Digest d) ->
    assertEqual_ root d
  -- Update the tree with the new value
  _ <- exists do
    a <- read addr
    n <- read @v next
    lift $ setValue @_ @_ @v @(KimchiConstraint f) @d a n
  -- Hash new element and compute new root
  nextHash <- hash $ Just next
  impliedRoot addr nextHash path

impliedRoot
  :: forall t m f d
   . Reflectable d Int
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => AddressVar d f
  -> Digest (FVar f)
  -> Path d (Digest (FVar f))
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
impliedRoot (AddressVar addr) initialHash (Path path) =
  foldM
    ( \(Digest acc) (Tuple b (Digest h)) -> do
        l <- if_ b h acc
        r <- if_ b acc h
        mergeCircuit (Digest l) (Digest r)
    )
    initialHash
    (Vector.zip addr path)
```