import Lean.Data.Json
import Std.Data.HashMap

/-!
# CoreFn: evaluating compiled PureScript inside Lean

The PureScript circuit programs are *pure*, and `purs` emits its whole-program IR — CoreFn —
as `output/<Module>/corefn.json` for every module. This file ingests that IR and evaluates it
**inside Lean**: a call-by-value interpreter over the (deliberately tiny) CoreFn expression
language, with a registry of `foreign` primitives bound to Lean implementations.

This is the certified-pipeline direction's first rung: instead of trusting the JS runtime, the
native backend, and the dumper, a Lean evaluation of the *actual compiled artifact* reproduces a
value the formalization independently specifies. The trusted base for such a cross-check is the
`purs` frontend (source → CoreFn) plus this interpreter — auditable, and eventually provable.

Scope (a spike, honestly stated):

* the full expression language: literals, constructors, records, accessors/updates, lambdas,
  application, `case` (including guards, named/nested binders), `let`/`letrec`;
* module loading on demand (`corefn.json`, parsed lazily, one `IO.Ref` cache), with top-level
  values memoized per `(module, identifier)`;
* foreigns are *first-order registry entries* (`Value.vForeign name arity args`), dispatched by
  `applyForeign` when saturated — no Lean closures inside `Value`, so the evaluator's value
  space stays a plain inductive, ready for a later fuel-indexed, provable variant;
* `partial def`s throughout: this is an executable tool (driven by `CheckCoreFn.lean`), not yet
  a semantics to prove against. Floats are carried opaquely and error on use.

The demo target (see `CheckCoreFn.lean`): `Snarky.Types.Shifted.forbiddenShiftedValues` — the
shift-protocol wraparound guard — evaluated from the compiled artifact and compared against an
independent Lean statement of its spec.
-/

namespace Kimchi.CoreFn

/-! ## Syntax -/

/-- Scalar literals. Numbers (floats) are carried as raw strings and rejected at use. -/
inductive Lit where
  | int (n : Int)
  | num (raw : String)
  | str (s : String)
  | chr (c : String)
  | bool (b : Bool)
  deriving Repr, BEq

mutual

/-- CoreFn expressions (the JSON `type` field). -/
inductive Expr where
  | var (mod : Option String) (ident : String)
  | lit (l : Lit)
  | arrayL (es : List Expr)
  | objectL (fs : List (String × Expr))
  | ctor (tyName ctorName : String) (fields : List String)
  | accessor (field : String) (e : Expr)
  | objUpdate (e : Expr) (updates : List (String × Expr))
  | abs (arg : String) (body : Expr)
  | app (f a : Expr)
  | caseE (scruts : List Expr) (alts : List Alt)
  | letE (binds : List Bind) (body : Expr)

/-- One `case` alternative: binders (one per scrutinee) and a plain or guarded result. -/
inductive Alt where
  | plain (binders : List Binder) (result : Expr)
  | guarded (binders : List Binder) (arms : List (Expr × Expr))

/-- Binders. Literal array/object binders carry sub-binders. -/
inductive Binder where
  | wild
  | varB (n : String)
  | litB (l : Lit)
  | arrB (bs : List Binder)
  | objB (fs : List (String × Binder))
  | ctorB (tyName ctorName : String) (isNewtype : Bool) (args : List Binder)
  | namedB (n : String) (b : Binder)

/-- A `let` binding group. -/
inductive Bind where
  | nonRec (name : String) (e : Expr)
  | recB (group : List (String × Expr))

end

/-! ## JSON decoding -/

private def getStr (j : Lean.Json) : Except String String :=
  j.getStr?

private def getArr (j : Lean.Json) : Except String (Array Lean.Json) :=
  j.getArr?

private def field (j : Lean.Json) (k : String) : Except String Lean.Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error e => .error s!"missing field {k}: {e}"

private def parseLit (litType : String) (v : Lean.Json) : Except String Lit := do
  match litType with
  | "IntLiteral" =>
      match v.getInt? with
      | .ok n => return .int n
      | .error e => .error s!"IntLiteral: {e}"
  | "NumberLiteral" => return .num (toString v)
  | "StringLiteral" => return .str (← getStr v)
  | "CharLiteral" => return .chr (← getStr v)
  | "BooleanLiteral" =>
      match v.getBool? with
      | .ok b => return .bool b
      | .error e => .error s!"BooleanLiteral: {e}"
  | t => .error s!"unknown scalar literal type {t}"

/-- Is this node annotated `meta: {metaType: "IsNewtype"}`? Newtype constructors are
    runtime-transparent (identity at construction, pass-through at matching). -/
private def isNewtypeMeta (j : Lean.Json) : Bool :=
  match j.getObjVal? "annotation" with
  | .ok ann =>
      match ann.getObjVal? "meta" with
      | .ok mj =>
          match mj.getObjVal? "metaType" with
          | .ok (.str "IsNewtype") => true
          | _ => false
      | _ => false
  | _ => false

mutual

partial def parseExpr (j : Lean.Json) : Except String Expr := do
  let ty ← getStr (← field j "type")
  match ty with
  | "Var" =>
      let v ← field j "value"
      let ident ← getStr (← field v "identifier")
      let mod := match field v "moduleName" with
        | .ok m =>
            match m.getArr? with
            | .ok parts => some (".".intercalate (parts.toList.filterMap (·.getStr?.toOption)))
            | .error _ => none
        | .error _ => none
      return .var mod ident
  | "Literal" =>
      let v ← field j "value"
      let lt ← getStr (← field v "literalType")
      let inner ← field v "value"
      match lt with
      | "ArrayLiteral" =>
          let es ← (← getArr inner).toList.mapM parseExpr
          return .arrayL es
      | "ObjectLiteral" =>
          let fs ← (← getArr inner).toList.mapM fun p => do
            let pair ← getArr p
            let k ← getStr pair[0]!
            let e ← parseExpr pair[1]!
            return (k, e)
          return .objectL fs
      | _ => return .lit (← parseLit lt inner)
  | "Constructor" =>
      -- newtype constructors are runtime-transparent: emit the identity function
      if isNewtypeMeta j then
        return .abs "$nt" (.var none "$nt")
      let tyName ← getStr (← field j "typeName")
      let ctorName ← getStr (← field j "constructorName")
      let fs := match field j "fieldNames" with
        | .ok arr => (arr.getArr?.toOption.getD #[]).toList.filterMap (·.getStr?.toOption)
        | .error _ => []
      return .ctor tyName ctorName fs
  | "Accessor" =>
      return .accessor (← getStr (← field j "fieldName")) (← parseExpr (← field j "expression"))
  | "ObjectUpdate" =>
      let e ← parseExpr (← field j "expression")
      let ups ← (← getArr (← field j "updates")).toList.mapM fun p => do
        let pair ← getArr p
        return ((← getStr pair[0]!), (← parseExpr pair[1]!))
      return .objUpdate e ups
  | "Abs" =>
      return .abs (← getStr (← field j "argument")) (← parseExpr (← field j "body"))
  | "App" =>
      return .app (← parseExpr (← field j "abstraction")) (← parseExpr (← field j "argument"))
  | "Case" =>
      let scruts ← (← getArr (← field j "caseExpressions")).toList.mapM parseExpr
      let alts ← (← getArr (← field j "caseAlternatives")).toList.mapM parseAlt
      return .caseE scruts alts
  | "Let" =>
      let binds ← (← getArr (← field j "binds")).toList.mapM parseBind
      return .letE binds (← parseExpr (← field j "expression"))
  | t => .error s!"unknown expression type {t}"

partial def parseAlt (j : Lean.Json) : Except String Alt := do
  let binders ← (← getArr (← field j "binders")).toList.mapM parseBinder
  let isGuarded := (field j "isGuarded").toOption.bind (·.getBool?.toOption) |>.getD false
  if isGuarded then
    let arms ← (← getArr (← field j "expressions")).toList.mapM fun a => do
      return ((← parseExpr (← field a "guard")), (← parseExpr (← field a "expression")))
    return .guarded binders arms
  else
    return .plain binders (← parseExpr (← field j "expression"))

partial def parseBinder (j : Lean.Json) : Except String Binder := do
  let ty ← getStr (← field j "binderType")
  match ty with
  | "NullBinder" => return .wild
  | "VarBinder" => return .varB (← getStr (← field j "identifier"))
  | "LiteralBinder" =>
      let v ← field j "literal"
      let lt ← getStr (← field v "literalType")
      let inner ← field v "value"
      match lt with
      | "ArrayLiteral" => return .arrB (← (← getArr inner).toList.mapM parseBinder)
      | "ObjectLiteral" =>
          let fs ← (← getArr inner).toList.mapM fun p => do
            let pair ← getArr p
            return ((← getStr pair[0]!), (← parseBinder pair[1]!))
          return .objB fs
      | _ => return .litB (← parseLit lt inner)
  | "ConstructorBinder" =>
      -- names may be dotted strings or qualified-name objects `{moduleName, identifier}`
      let qualName (j : Lean.Json) : Except String String :=
        match j.getStr? with
        | .ok s => .ok s
        | .error _ => do getStr (← field j "identifier")
      let tyName ← qualName (← field j "typeName")
      let ctorName ← qualName (← field j "constructorName")
      let args ← (← getArr (← field j "binders")).toList.mapM parseBinder
      return .ctorB tyName ctorName (isNewtypeMeta j) args
  | "NamedBinder" =>
      return .namedB (← getStr (← field j "identifier")) (← parseBinder (← field j "binder"))
  | t => .error s!"unknown binder type {t}"

partial def parseBind (j : Lean.Json) : Except String Bind := do
  let bt ← getStr (← field j "bindType")
  match bt with
  | "NonRec" =>
      return .nonRec (← getStr (← field j "identifier")) (← parseExpr (← field j "expression"))
  | "Rec" =>
      let group ← (← getArr (← field j "binds")).toList.mapM fun b => do
        return ((← getStr (← field b "identifier")), (← parseExpr (← field b "expression")))
      return .recB group
  | t => .error s!"unknown bind type {t}"

end

/-- Strip the qualified-name prefix from `typeName`/`constructorName` (`A.B.C` → `C`). -/
private def shortName (s : String) : String :=
  (s.splitOn ".").getLast!

/-! ## Values

First-order: closures carry list environments; recursive-group members are references into the
group re-materialized at application; foreigns are `(name, arity, collected args)` dispatched by
the registry. No Lean functions inside `Value`. -/

inductive Value where
  | vInt (n : Int)
  | vBig (n : Int)
  | vStr (s : String)
  | vChar (s : String)
  | vBool (b : Bool)
  | vNum (raw : String)
  | vArr (es : Array Value)
  | vObj (fs : List (String × Value))
  | vCtor (tyName ctorName : String) (arity : Nat) (args : List Value)
  | vClosure (env : List (String × Value)) (arg : String) (body : Expr)
  | vRecRef (env : List (String × Value)) (group : List (String × Expr)) (name : String)
  | vForeign (mod name : String) (arity : Nat) (args : List Value)
  | vRef (idx : Nat)

instance : Inhabited Value := ⟨.vObj []⟩

def Value.describe : Value → String
  | .vInt n => s!"Int {n}"
  | .vBig n => s!"BigInt {n}"
  | .vStr s => s!"String {s}"
  | .vChar c => s!"Char {c}"
  | .vBool b => s!"Bool {b}"
  | .vNum r => s!"Number {r}"
  | .vArr es => s!"Array(size {es.size})"
  | .vObj fs => s!"Object({fs.map Prod.fst})"
  | .vCtor ty c _ args => s!"{ty}.{c}(" ++ ", ".intercalate (args.map fun a =>
      match a with
      | .vObj fs => s!"Object({fs.map Prod.fst})"
      | .vCtor ty' c' _ as' => s!"{ty'}.{c'}({as'.length})"
      | .vInt n => s!"Int {n}"
      | .vBig n => s!"Big {n}"
      | .vArr es => s!"Arr({es.size})"
      | .vClosure _ n _ => s!"Clo(\\{n})"
      | .vForeign m' n' _ _ => s!"For {m'}.{n'}"
      | .vRef i => s!"Ref{i}"
      | _ => "?") ++ ")"
  | .vClosure _ a _ => s!"Closure(\\{a} -> _)"
  | .vRecRef _ _ n => s!"RecRef {n}"
  | .vForeign m n a args => s!"Foreign {m}.{n} ({args.length}/{a})"
  | .vRef i => s!"Ref #{i}"

/-! ## The foreign registry

Each entry is `(module, name) ↦ arity`; `applyForeign` implements the saturated call. JS BigInt
division/remainder truncate toward zero — Lean's `Int.tdiv`/`Int.tmod`. The registry grows on
demand: an unbound foreign raises a named error identifying exactly what to add. -/

private def ordering (n : Int) : Value :=
  if n < 0 then .vCtor "Data.Ordering.Ordering" "LT" 0 []
  else if n = 0 then .vCtor "Data.Ordering.Ordering" "EQ" 0 []
  else .vCtor "Data.Ordering.Ordering" "GT" 0 []

/-- Arities of the `Snarky.Curves.Pasta` napi boundary (the `_vestaScalarField*` family is the
    `Fp` the circuits run over; bound to `Int` mod `p` below). Unlisted names get arity 1 and
    error at application. -/
def pastaArity (name : String) : Nat :=
  if name ∈ ["_vestaScalarFieldZero", "_vestaScalarFieldOne", "_vestaScalarFieldModulus"] then 1
  else if name ∈ ["_vestaScalarFieldAdd", "_vestaScalarFieldMul", "_vestaScalarFieldSub",
    "_vestaScalarFieldDiv", "_vestaScalarFieldEq", "_vestaScalarFieldPow"] then 2
  else 1

def foreignArity (mod name : String) : Option Nat :=
  match mod, name with
  | "JS.BigInt", "fromInt" => some 1
  | "JS.BigInt", "biAdd" => some 2
  | "JS.BigInt", "biSub" => some 2
  | "JS.BigInt", "biMul" => some 2
  | "JS.BigInt", "biMod" => some 2
  | "JS.BigInt", "biDiv" => some 2
  | "JS.BigInt", "biZero" => some 0
  | "JS.BigInt", "biOne" => some 0
  | "JS.BigInt", "pow" => some 2
  | "JS.BigInt", "biEquals" => some 2
  | "JS.BigInt", "biCompare" => some 2
  | "JS.BigInt", "biDegree" => some 1
  | "JS.BigInt", "toString" => some 1
  | "Data.Unfoldable", "unfoldrArrayImpl" => some 6
  | "Data.Unfoldable1", "unfoldr1ArrayImpl" => some 7
  | "Data.Array", "sortByImpl" => some 3
  | "Data.Array", "fromFoldableImpl" => some 2
  | "Data.Array", "unsafeIndexImpl" => some 2
  | "Data.Array", "anyImpl" => some 2
  | "Data.Array", "allImpl" => some 2
  | "$builtin", "listCons" => some 2
  | "Data.Array", "length" => some 1
  | "Data.Array", "concat" => some 1
  | "Data.Array", "indexImpl" => some 4
  | "Data.Array", "rangeImpl" => some 2
  | "Data.Array", "replicateImpl" => some 2
  | "Data.Array", "unconsImpl" => some 3
  | "Data.Semiring", "intAdd" => some 2
  | "Data.Semiring", "intMul" => some 2
  | "Data.Ring", "intSub" => some 2
  | "Data.Eq", "eqIntImpl" => some 2
  | "Data.HeytingAlgebra", "boolConj" => some 2
  | "Data.HeytingAlgebra", "boolDisj" => some 2
  | "Data.HeytingAlgebra", "boolNot" => some 1
  | "Data.Eq", "eqStringImpl" => some 2
  | "Data.Eq", "eqBooleanImpl" => some 2
  | "Data.Eq", "eqArrayImpl" => some 3
  | "Data.Ord", "ordIntImpl" => some 5
  | "Data.Ord", "ordStringImpl" => some 5
  | "Data.Semigroup", "concatArray" => some 2
  | "Data.Semigroup", "concatString" => some 2
  | "Data.Foldable", "foldrArray" => some 3
  | "Data.FunctorWithIndex", "mapWithIndexArray" => some 2
  | "Data.Functor", "arrayMap" => some 2
  | "Control.Bind", "arrayBind" => some 2
  | "Control.Apply", "arrayApply" => some 2
  | "Data.Array", "zipWithImpl" => some 3
  | "Data.Array", "filterImpl" => some 2
  | "Data.Array", "reverse" => some 1
  | "Data.Array", "sliceImpl" => some 3
  | "Data.Foldable", "foldlArray" => some 3
  | "Data.Function.Uncurried", "mkFn2" => some 1
  | "Data.Function.Uncurried", "mkFn3" => some 1
  | "Data.Function.Uncurried", "mkFn4" => some 1
  | "Data.Function.Uncurried", "runFn2" => some 3
  | "Data.Function.Uncurried", "runFn3" => some 4
  | "Data.Function.Uncurried", "runFn4" => some 5
  | "Partial.Unsafe", "_unsafePartial" => some 1
  | "Control.Monad.ST.Internal", "run" => some 1
  | "Control.Monad.ST.Internal", "pure_" => some 1
  | "Control.Monad.ST.Internal", "bind_" => some 2
  | "Control.Monad.ST.Internal", "map_" => some 2
  | "Control.Monad.ST.Internal", "foreach" => some 2
  | "Control.Monad.ST.Internal", "for" => some 3
  | "Control.Monad.ST.Internal", "while" => some 2
  | "Control.Monad.ST.Internal", "new" => some 1
  | "Control.Monad.ST.Internal", "read" => some 1
  | "Control.Monad.ST.Internal", "write" => some 2
  | "Control.Monad.ST.Internal", "modifyImpl" => some 2
  | "Control.Monad.ST.Uncurried", "runSTFn1" => some 2
  | "Control.Monad.ST.Uncurried", "runSTFn2" => some 3
  | "Control.Monad.ST.Uncurried", "runSTFn3" => some 4
  | "Control.Monad.ST.Uncurried", "runSTFn4" => some 5
  | "Data.Array.ST", "unsafeThawImpl" => some 1
  | "Data.Array.ST", "unsafeFreezeImpl" => some 1
  | "Data.Array.ST", "pushImpl" => some 2
  | "Data.Array.ST", "pushAllImpl" => some 2
  | "Data.Array.ST", "lengthImpl" => some 1
  | "Data.Array.ST", "peekImpl" => some 4
  | "Data.Array.ST", "pokeImpl" => some 3
  | "Data.Array.ST", "newImpl" => some 0
  | "Data.Show", "showIntImpl" => some 1
  | "Data.Unit", "unit" => some 0
  | "Effect", "pureE" => some 1
  | "Effect", "bindE" => some 2
  | "Effect", "untilE" => some 1
  | "Effect", "whileE" => some 2
  | "Effect", "forE" => some 3
  | "Effect", "foreachE" => some 2
  | "Effect.Ref", "_new" => some 1
  | "Effect.Ref", "read" => some 1
  | "Effect.Ref", "write" => some 2
  | "Effect.Ref", "modifyImpl" => some 2
  | "Effect.Unsafe", "unsafePerformEffect" => some 1
  | "Unsafe.Coerce", "unsafeCoerce" => some 1
  | "Data.Reflectable", "unsafeCoerce" => some 1
  | "Record.Unsafe", "unsafeHas" => some 2
  | "Record.Unsafe", "unsafeGet" => some 2
  | "Record.Unsafe", "unsafeSet" => some 3
  | "Record.Unsafe", "unsafeDelete" => some 2
  | "Data.Int", "quot" => some 2
  | "Data.Int", "rem" => some 2
  | "Data.Int", "pow" => some 2
  | "Data.Traversable", "traverseArrayImpl" => some 5
  | "$builtin", "arrPush" => some 2
  | "$builtin", "array1" => some 1
  | "$builtin", "concat2" => some 2
  | "Snarky.Curves.Pasta", _ => some (pastaArity name)
  | "Data.Ordering", _ => none
  | "Data.Show", "showStringImpl" => some 1
  | _, _ => none

/-- Binary modular exponentiation on `Nat` (the toolchain has no `Nat.powMod`). -/
partial def powMod (b e m : Nat) : Nat :=
  if m ≤ 1 then 0
  else if e == 0 then 1
  else
    let h := powMod (b * b % m) (e / 2) m
    if e % 2 == 1 then h * b % m else h

/-- `Fp = Vesta.ScalarField` modulus (the Pallas base-field cardinality). -/
def vestaScalarModulus : Int :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

/-! ## Module loading and evaluation -/

structure ModuleData where
  name : String
  decls : Std.HashMap String Expr
  recGroups : List (List (String × Expr))
  foreigns : List String

structure Ctx where
  outDir : System.FilePath
  modules : IO.Ref (Std.HashMap String ModuleData)
  globals : IO.Ref (Std.HashMap (String × String) Value)
  /-- The ST heap: `Value.vRef i` indexes a slot (both `STRef`s and `STArray`s). -/
  heap : IO.Ref (Array Value)
  /-- Diagnostic ring buffer: recent evaluation events, dumped on error. -/
  trace : IO.Ref (Array String)

def Ctx.new (outDir : System.FilePath) : IO Ctx := do
  return { outDir, modules := ← IO.mkRef {}, globals := ← IO.mkRef {},
           heap := ← IO.mkRef #[], trace := ← IO.mkRef #[] }

private def err {α : Type} (msg : String) : IO α :=
  throw (IO.userError msg)

def loadModule (ctx : Ctx) (m : String) : IO ModuleData := do
  if let some md := (← ctx.modules.get).get? m then
    return md
  let path := ctx.outDir / m / "corefn.json"
  let txt ← IO.FS.readFile path
  let json ← match Lean.Json.parse txt with
    | .ok j => pure j
    | .error e => err s!"parse {path}: {e}"
  let declsJson ← match json.getObjVal? "decls" with
    | .ok (.arr a) => pure a
    | _ => err s!"{m}: no decls"
  let mut decls : Std.HashMap String Expr := {}
  let mut recGroups : List (List (String × Expr)) := []
  for dj in declsJson do
    match parseBind dj with
    | .ok (.nonRec name e) => decls := decls.insert name e
    | .ok (.recB group) =>
        recGroups := group :: recGroups
        for (name, e) in group do
          decls := decls.insert name e
    | .error e => err s!"{m}: decl parse: {e}"
  let foreigns := match json.getObjVal? "foreign" with
    | .ok (.arr a) => a.toList.filterMap (·.getStr?.toOption)
    | _ => []
  let md : ModuleData := { name := m, decls, recGroups, foreigns }
  ctx.modules.modify (·.insert m md)
  return md

def pushTrace (ctx : Ctx) (msg : String) : IO Unit := do
  ctx.trace.modify fun t => (if t.size > 400 then t.extract 200 t.size else t).push msg

def dumpTrace (ctx : Ctx) : IO Unit := do
  let t ← ctx.trace.get
  IO.eprintln "=== last evaluation events ==="
  for msg in t.toList.reverse.take 60 do
    IO.eprintln s!"  {msg}"

mutual

/-- Look up (and memoize) a top-level value. Top-level recursion resolves through this lookup
    at application time, so no cyclic environments are needed. -/
partial def globalValue (ctx : Ctx) (m ident : String) : IO Value := do
  -- the compiler's virtual module: `Prim.undefined` stands in for erased arguments
  if m == "Prim" then
    return .vObj []
  if let some v := (← ctx.globals.get).get? (m, ident) then
    return v
  let md ← loadModule ctx m
  pushTrace ctx s!"decl {m}.{ident}"
  let v ← do
    if let some e := md.decls.get? ident then
      try
        eval ctx [] e
      catch ex =>
        err s!"{ex.toString}\n  in {m}.{ident}"
    else if md.foreigns.contains ident then
      match foreignArity m ident with
      | some 0 => applyForeign ctx m ident []
      | some ar => pure (.vForeign m ident ar [])
      | none =>
          -- unbound: stay symbolic; the error surfaces only if it is actually applied
          -- (dictionaries eagerly reference foreigns their consumers never call)
          pure (.vForeign m ident 1000000 [])
    else
      err s!"unknown identifier {m}.{ident}"
  ctx.globals.modify (·.insert (m, ident) v)
  return v

partial def eval (ctx : Ctx) (env : List (String × Value)) : Expr → IO Value
  | .var none ident => do
      match env.find? (·.1 == ident) with
      | some (_, v) => pure v
      | none => err s!"unbound local {ident}"
  | .var (some m) ident => globalValue ctx m ident
  | .lit (.int n) => pure (.vInt n)
  | .lit (.num r) => pure (.vNum r)
  | .lit (.str s) => pure (.vStr s)
  | .lit (.chr c) => pure (.vChar c)
  | .lit (.bool b) => pure (.vBool b)
  | .arrayL es => do
      let vs ← es.mapM (eval ctx env)
      pure (.vArr vs.toArray)
  | .objectL fs => do
      let vs ← fs.mapM fun (k, e) => do pure (k, ← eval ctx env e)
      pure (.vObj vs)
  | .ctor tyName ctorName fields =>
      pure (.vCtor (shortName tyName) (shortName ctorName) fields.length [])
  | .accessor f e => do
      match ← eval ctx env e with
      | .vObj fs =>
          match fs.find? (·.1 == f) with
          | some (_, v) => pure v
          | none => err s!"record has no field {f}"
      | v => err s!"accessor .{f} on non-record: {v.describe}"
  | .objUpdate e ups => do
      match ← eval ctx env e with
      | .vObj fs => do
          let newFs ← ups.mapM fun (k, ue) => do pure (k, ← eval ctx env ue)
          pure (.vObj (fs.map fun (k, v) =>
            match newFs.find? (·.1 == k) with
            | some (_, nv) => (k, nv)
            | none => (k, v)))
      | v => err s!"update on non-record: {v.describe}"
  | .abs arg body => pure (.vClosure env arg body)
  | .app f a => do
      let fv ← eval ctx env f
      let av ← eval ctx env a
      apply ctx fv av
  | .caseE scruts alts => do
      let vs ← scruts.mapM (eval ctx env)
      matchAlts ctx env vs [] alts
  | .letE binds body => do
      let mut env' := env
      for b in binds do
        match b with
        | .nonRec name e => env' := (name, ← eval ctx env' e) :: env'
        | .recB group =>
            let base := env'
            env' := group.foldl (fun acc (n, _) => (n, Value.vRecRef base group n) :: acc) env'
      eval ctx env' body

/-- Apply a value. Constructors and foreigns collect args until saturated; recursive-group
    references materialize the group on first application. -/
partial def apply (ctx : Ctx) (f a : Value) : IO Value := do
  match f with
  | .vClosure env arg body => do
      pushTrace ctx s!"app (\\{arg}) ← {a.describe}"
      eval ctx ((arg, a) :: env) body
  | .vCtor "$ST" tag ar args =>
      -- JS semantics: an Effect/ST action is a zero-arg thunk; calling it with an argument
      -- runs it and discards the argument (the Snarky monad's reader/Effect coercion relies
      -- on exactly this)
      pushTrace ctx s!"APPLY-DISCARD on $ST.{tag} arg={a.describe}"
      runST ctx (.vCtor "$ST" tag ar args)
  | .vCtor ty c arity args =>
      let args' := args ++ [a]
      pure (.vCtor ty c arity args')
  | .vForeign m n arity args =>
      let args' := args ++ [a]
      if args'.length == arity then applyForeign ctx m n args'
      else pure (.vForeign m n arity args')
  | .vRecRef env group name => do
      match group.find? (·.1 == name) with
      | some (_, .abs arg body) =>
          let env' := group.foldl (fun acc (n, _) => (n, Value.vRecRef env group n) :: acc) env
          eval ctx ((arg, a) :: env') body
      | some _ => err s!"letrec member {name} is not a lambda"
      | none => err s!"letrec member {name} not found"
  | v => err s!"apply on non-function: {v.describe}"

partial def describeBinder : Binder → String
  | .wild => "_"
  | .varB n => n
  | .litB _ => "lit"
  | .arrB bs => s!"[{bs.map describeBinder}]"
  | .objB fs => s!"obj({fs.map Prod.fst})"
  | .ctorB ty c nt args => s!"{ty}.{c}{if nt then "*" else ""}({args.map describeBinder})"
  | .namedB n b => s!"{n}@{describeBinder b}"

partial def matchAlts (ctx : Ctx) (env : List (String × Value)) (vs : List Value)
    (dbg : List (List Binder)) :
    List Alt → IO Value
  | [] => err s!"case: no alternative matched for {vs.map (·.describe)}; alts were \
      {dbg.map (·.map describeBinder)}"
  | alt :: rest => do
      let (binders, result) := match alt with
        | .plain bs r => (bs, Sum.inl r)
        | .guarded bs arms => (bs, Sum.inr arms)
      match matchBinders vs binders with
      | some binds =>
          let env' := binds ++ env
          match result with
          | .inl e => eval ctx env' e
          | .inr arms => do
              match ← firstGuard ctx env' arms with
              | some v => pure v
              | none => matchAlts ctx env vs (dbg ++ [binders]) rest
      | none => matchAlts ctx env vs (dbg ++ [binders]) rest

partial def firstGuard (ctx : Ctx) (env : List (String × Value)) :
    List (Expr × Expr) → IO (Option Value)
  | [] => pure none
  | (g, e) :: rest => do
      match ← eval ctx env g with
      | .vBool true => some <$> eval ctx env e
      | .vBool false => firstGuard ctx env rest
      | v => err s!"guard evaluated to non-bool: {v.describe}"

partial def matchBinders (vs : List Value) (bs : List Binder) :
    Option (List (String × Value)) := do
  match vs, bs with
  | [], [] => some []
  | v :: vs', b :: bs' => do
      let m1 ← matchBinder v b
      let m2 ← matchBinders vs' bs'
      some (m1 ++ m2)
  | _, _ => none

partial def matchBinder (v : Value) : Binder → Option (List (String × Value))
  | .wild => some []
  | .varB n => some [(n, v)]
  | .namedB n b => do
      let m ← matchBinder v b
      some ((n, v) :: m)
  | .litB (.int n) => match v with | .vInt m => if m == n then some [] else none | _ => none
  | .litB (.str s) => match v with | .vStr t => if t == s then some [] else none | _ => none
  | .litB (.chr c) => match v with | .vChar t => if t == c then some [] else none | _ => none
  | .litB (.bool b) => match v with | .vBool t => if t == b then some [] else none | _ => none
  | .litB (.num _) => none
  | .arrB bs =>
      match v with
      | .vArr es =>
          if es.size == bs.length then matchBinders es.toList bs else none
      | _ => none
  | .objB fs => do
      match v with
      | .vObj vfs => do
          let mut acc : List (String × Value) := []
          for (k, b) in fs do
            match vfs.find? (·.1 == k) with
            | some (_, fv) =>
                match matchBinder fv b with
                | some m => acc := acc ++ m
                | none => none
            | none => none
          some acc
      | _ => none
  | .ctorB _ ctorName isNewtype args =>
      if isNewtype then
        -- transparent: match the single sub-binder against the value itself
        match args with
        | [b] => matchBinder v b
        | _ => none
      else
        match v with
        | .vCtor _ c _ cargs =>
            if c == shortName ctorName && cargs.length == args.length then
              matchBinders cargs args
            else none
        | _ => none

/-- Interpret a defunctionalized ST action against the heap. -/
partial def runST (ctx : Ctx) (v : Value) : IO Value := do
  match v with
  | .vCtor "$ST" "pure_" _ [a] => pure a
  | .vCtor "$ST" "bind_" _ [m, f] => do
      let a ← runST ctx m
      let next ← apply ctx f a
      match next with
      | .vCtor "$ST" .. => runST ctx next
      | .vForeign .. => runST ctx next
      | v =>
          -- JS: `f(a())()` — but PS code coerced so the continuation's result is already
          -- the final value (a zero-arg call on it never happens for pure payloads
          -- threaded through the Snarky reader). Pass it through.
          pure v
  | .vCtor "$ST" "map_" _ [f, m] => do
      apply ctx f (← runST ctx m)
  | .vCtor "$ST" "foreach" _ [.vArr es, f] => do
      for e in es do
        let _ ← runST ctx (← apply ctx f e)
      pure (.vObj [])
  | .vCtor "$ST" "new" _ [a] => do
      let heap ← ctx.heap.get
      ctx.heap.set (heap.push a)
      pure (.vRef heap.size)
  | .vCtor "$ST" "read" _ [.vRef i] => do
      pure (← ctx.heap.get)[i]!
  | .vCtor "$ST" "write" _ [a, .vRef i] => do
      ctx.heap.modify (·.set! i a)
      pure a
  | .vCtor "$ST" "modifyImpl" _ [f, .vRef i] => do
      let old := (← ctx.heap.get)[i]!
      match ← apply ctx f old with
      | .vObj fs => do
          let some (_, st) := fs.find? (·.1 == "state") | err "modifyImpl: no state"
          let some (_, val) := fs.find? (·.1 == "value") | err "modifyImpl: no value"
          ctx.heap.modify (·.set! i st)
          pure val
      | v => err s!"modifyImpl: {v.describe}"
  | .vCtor "$ST" "untilE" _ [act] => do
      let mut fuel := 10000000
      while fuel > 0 do
        fuel := fuel - 1
        match ← runST ctx act with
        | .vBool true => return (.vObj [])
        | .vBool false => pure ()
        | v => err s!"untilE: {v.describe}"
      err "untilE: fuel exhausted"
  | .vCtor "$ST" "whileE" _ [cond, act] => do
      let mut fuel := 10000000
      while fuel > 0 do
        fuel := fuel - 1
        match ← runST ctx cond with
        | .vBool true => let _ ← runST ctx act
        | .vBool false => return (.vObj [])
        | v => err s!"whileE: {v.describe}"
      err "whileE: fuel exhausted"
  | .vCtor "$ST" "while" _ [cond, act] => do
      let mut fuel := 10000000
      while fuel > 0 do
        fuel := fuel - 1
        match ← runST ctx cond with
        | .vBool true => let _ ← runST ctx act
        | .vBool false => return (.vObj [])
        | v => err s!"ST.while: {v.describe}"
      err "ST.while: fuel exhausted"
  | .vCtor "$ST" "for" _ [.vInt lo, .vInt hi, f] => do
      for k in [0 : (hi - lo).toNat] do
        let _ ← runST ctx (← apply ctx f (.vInt (lo + k)))
      pure (.vObj [])
  | .vCtor "$ST" "forE" _ [.vInt lo, .vInt hi, f] => do
      for k in [0 : (hi - lo).toNat] do
        let _ ← runST ctx (← apply ctx f (.vInt (lo + k)))
      pure (.vObj [])
  | .vForeign "Data.Array.ST" "new" _ _ => do
      let heap ← ctx.heap.get
      ctx.heap.set (heap.push (.vArr #[]))
      pure (.vRef heap.size)
  | .vCtor "$ST" "STFn" _ (fn :: fnArgs) => stPrim ctx fn fnArgs
  | .vCtor "$ST" tag _ args =>
      err s!"ST node {tag}/{args.length} not interpreted: {args.map (·.describe)}"
  | .vClosure env arg body =>
      -- JS: a zero-arg invocation of a real closure binds its parameter to `undefined`;
      -- the sentinel errors loudly if the body ever inspects it
      pushTrace ctx s!"RUNST-CLOSURE (\\{arg})"
      eval ctx ((arg, Value.vCtor "$U" "undefined" 0 []) :: env) body
  | v =>
      -- already-run payloads reaching action position pass through (reader/Effect coercion)
      pure v

/-- The `Data.Array.ST` primitives (mutable arrays as heap slots holding `vArr`). -/
partial def stPrim (ctx : Ctx) (fn : Value) (args : List Value) : IO Value := do
  match fn, args with
  | .vForeign "Data.Array.ST" "thawImpl" _ _, [.vArr xs] => do
      let heap ← ctx.heap.get
      ctx.heap.set (heap.push (.vArr xs))
      pure (.vRef heap.size)
  | .vForeign "Data.Array.ST" "freezeImpl" _ _, [.vRef i] => do
      pure (← ctx.heap.get)[i]!
  | .vForeign "Data.Array.ST" "popImpl" _ _, [just, nothing, .vRef i] => do
      let heap ← ctx.heap.get
      match heap[i]! with
      | .vArr xs =>
          if xs.isEmpty then pure nothing
          else do
            ctx.heap.set (heap.set! i (.vArr xs.pop))
            apply ctx just xs.back!
      | v => err s!"popImpl: slot holds {v.describe}"
  | .vForeign "Data.Array.ST" "spliceImpl" _ _, [.vInt k, .vInt hm, .vArr bs, .vRef i] => do
      let heap ← ctx.heap.get
      match heap[i]! with
      | .vArr xs => do
          let removed := xs.extract k.toNat (k.toNat + hm.toNat)
          let newArr := xs.extract 0 k.toNat ++ bs ++ xs.extract (k.toNat + hm.toNat) xs.size
          ctx.heap.set (heap.set! i (.vArr newArr))
          pure (.vArr removed)
      | v => err s!"spliceImpl: slot holds {v.describe}"
  | .vForeign "Data.Array.ST" "unsafeThawImpl" _ _, [.vArr xs] => do
      let heap ← ctx.heap.get
      ctx.heap.set (heap.push (.vArr xs))
      pure (.vRef heap.size)
  | .vForeign "Data.Array.ST" "unsafeFreezeImpl" _ _, [.vRef i] => do
      pure (← ctx.heap.get)[i]!
  | .vForeign "Data.Array.ST" "pushImpl" _ _, [a, .vRef i] => do
      let heap ← ctx.heap.get
      match heap[i]! with
      | .vArr xs => do
          ctx.heap.set (heap.set! i (.vArr (xs.push a)))
          pure (.vInt (xs.size + 1))
      | v => err s!"pushImpl: slot holds {v.describe}"
  | .vForeign "Data.Array.ST" "pushAllImpl" _ _, [.vArr as, .vRef i] => do
      let heap ← ctx.heap.get
      match heap[i]! with
      | .vArr xs => do
          ctx.heap.set (heap.set! i (.vArr (xs ++ as)))
          pure (.vInt (xs.size + as.size))
      | v => err s!"pushAllImpl: slot holds {v.describe}"
  | .vForeign "Data.Array.ST" "lengthImpl" _ _, [.vRef i] => do
      match (← ctx.heap.get)[i]! with
      | .vArr xs => pure (.vInt xs.size)
      | v => err s!"lengthImpl: slot holds {v.describe}"
  | .vForeign "Data.Array.ST" "peekImpl" _ _, [just, nothing, .vInt k, .vRef i] => do
      match (← ctx.heap.get)[i]! with
      | .vArr xs =>
          if k ≥ 0 ∧ k.toNat < xs.size then apply ctx just xs[k.toNat]! else pure nothing
      | v => err s!"peekImpl: slot holds {v.describe}"
  | .vForeign "Data.Array.ST" "pokeImpl" _ _, [.vInt k, a, .vRef i] => do
      let heap ← ctx.heap.get
      match heap[i]! with
      | .vArr xs => do
          if k ≥ 0 ∧ k.toNat < xs.size then do
            ctx.heap.set (heap.set! i (.vArr (xs.set! k.toNat a)))
            pure (.vBool true)
          else pure (.vBool false)
      | v => err s!"pokeImpl: slot holds {v.describe}"
  | .vForeign m n _ _, _ => err s!"ST primitive {m}.{n}/{args.length} not implemented"
  | v, _ => err s!"STFn head is not a foreign: {v.describe}"

partial def applyForeign (ctx : Ctx) (m n : String) (args : List Value) : IO Value := do
  let int2 (f : Int → Int → Value) : IO Value := do
    match args with
    | [.vInt a, .vInt b] => pure (f a b)
    | _ => err s!"{m}.{n}: expected 2 ints, got {args.map (·.describe)}"
  let big2 (f : Int → Int → Value) : IO Value := do
    match args with
    | [.vBig a, .vBig b] => pure (f a b)
    | _ => err s!"{m}.{n}: expected 2 bigints, got {args.map (·.describe)}"
  match m, n with
  | "JS.BigInt", "fromInt" =>
      match args with
      | [.vInt a] => pure (.vBig a)
      | _ => err "fromInt: expected int"
  | "JS.BigInt", "biAdd" => big2 (fun a b => .vBig (a + b))
  | "JS.BigInt", "biSub" => big2 (fun a b => .vBig (a - b))
  | "JS.BigInt", "biMul" => big2 (fun a b => .vBig (a * b))
  | "JS.BigInt", "biMod" => big2 (fun a b => .vBig (a.tmod b))
  | "JS.BigInt", "biDiv" => big2 (fun a b => .vBig (a.tdiv b))
  | "JS.BigInt", "biZero" => pure (.vBig 0)
  | "JS.BigInt", "biOne" => pure (.vBig 1)
  | "JS.BigInt", "pow" => big2 (fun a b => .vBig (a ^ b.toNat))
  | "JS.BigInt", "biEquals" => big2 (fun a b => .vBool (a == b))
  | "JS.BigInt", "biCompare" => big2 (fun a b => .vInt (if a < b then -1 else if a == b then 0
      else 1))
  | "JS.BigInt", "toString" =>
      match args with
      | [.vBig a] => pure (.vStr (toString a))
      | _ => err "toString: expected bigint"
  | "Data.Unfoldable", "unfoldrArrayImpl" =>
      -- isNothing, fromJust, fst, snd, f, b — build the array by iterating `f`
      match args with
      | [isNothing, fromJust, fst, snd, f, b0] => do
          let mut acc : Array Value := #[]
          let mut b := b0
          let mut fuel := 1000000
          while fuel > 0 do
            fuel := fuel - 1
            let mb ← apply ctx f b
            match ← apply ctx isNothing mb with
            | .vBool true => return (.vArr acc)
            | .vBool false =>
                let pair ← apply ctx fromJust mb
                acc := acc.push (← apply ctx fst pair)
                b ← apply ctx snd pair
            | v => err s!"unfoldr isNothing: {v.describe}"
          err "unfoldrArrayImpl: fuel exhausted"
      | _ => err "unfoldrArrayImpl: expected 6 args"
  | "$builtin", "listCons" =>
      match args with
      | [a, b] => pure (.vCtor "$L" "Cons" 2 [a, b])
      | _ => err "listCons: bad args"
  | "Data.Array", "fromFoldableImpl" =>
      -- (foldr, xs): build a cons-list with a synthetic builtin, then flatten
      match args with
      | [foldr, xs] => do
          let consF := Value.vForeign "$builtin" "listCons" 2 []
          let nilV := Value.vCtor "$L" "Nil" 0 []
          let lst ← apply ctx (← apply ctx (← apply ctx foldr consF) nilV) xs
          let mut acc : Array Value := #[]
          let mut cur := lst
          let mut fuel := 10000000
          while fuel > 0 do
            fuel := fuel - 1
            match cur with
            | .vCtor "$L" "Nil" _ _ => return (.vArr acc)
            | .vCtor "$L" "Cons" _ [h, t] =>
                acc := acc.push h
                cur := t
            | v => err s!"fromFoldableImpl: bad list node {v.describe}"
          err "fromFoldableImpl: fuel exhausted"
      | _ => err "fromFoldableImpl: bad args"
  | "Data.Array", "sortByImpl" =>
      -- comparison (a → a → Ordering-as-int via wrapper), ordering→int, array
      match args with
      | [cmp, toInt, .vArr es] => do
          let withKeysM ← es.mapM fun e => do pure e
          -- insertion sort with the provided comparison (small arrays only)
          let mut arr := withKeysM
          for i in [1:arr.size] do
            let mut j := i
            while j > 0 do
              let a := arr[j-1]!
              let b := arr[j]!
              let ord ← apply ctx cmp a >>= fun f => apply ctx f b
              let c ← apply ctx toInt ord
              match c with
              | .vInt v =>
                  if v > 0 then
                    arr := arr.set! (j-1) b |>.set! j a
                    j := j - 1
                  else j := 0
              | v => err s!"sortByImpl ordering→int: {v.describe}"
          pure (.vArr arr)
      | _ => err "sortByImpl: expected (cmp, toInt, array)"
  | "Data.Array", "unsafeIndexImpl" =>
      match args with
      | [.vArr es, .vInt i] =>
          if h : i.toNat < es.size then pure es[i.toNat] else err "unsafeIndexImpl: OOB"
      | _ => err s!"unsafeIndexImpl: bad args {args.map (·.describe)}"
  | "Data.Array", "anyImpl" =>
      match args with
      | [f, .vArr es] => do
          for e in es do
            if let .vBool true ← apply ctx f e then return (.vBool true)
          pure (.vBool false)
      | _ => err "anyImpl: bad args"
  | "Data.Array", "allImpl" =>
      match args with
      | [f, .vArr es] => do
          for e in es do
            if let .vBool false ← apply ctx f e then return (.vBool false)
          pure (.vBool true)
      | _ => err "allImpl: bad args"
  | "Data.Array", "length" =>
      match args with
      | [.vArr es] => pure (.vInt es.size)
      | _ => err "length: expected array"
  | "Data.Array", "concat" =>
      match args with
      | [.vArr ess] => do
          let mut acc : Array Value := #[]
          for e in ess do
            match e with
            | .vArr inner => acc := acc ++ inner
            | v => err s!"concat: inner non-array {v.describe}"
          pure (.vArr acc)
      | _ => err "concat: expected array of arrays"
  | "Data.Array", "indexImpl" =>
      match args with
      | [just, nothing, .vArr es, .vInt i] =>
          if h : i.toNat < es.size then
            if i ≥ 0 then apply ctx just es[i.toNat] else pure nothing
          else pure nothing
      | _ => err "indexImpl: bad args"
  | "Data.Array", "rangeImpl" =>
      match args with
      | [.vInt lo, .vInt hi] => do
          let mut acc : Array Value := #[]
          if lo ≤ hi then
            for k in [0 : (hi - lo + 1).toNat] do
              acc := acc.push (.vInt (lo + k))
          else
            for k in [0 : (lo - hi + 1).toNat] do
              acc := acc.push (.vInt (lo - k))
          pure (.vArr acc)
      | _ => err "rangeImpl: bad args"
  | "Data.Array", "replicateImpl" =>
      match args with
      | [.vInt count, v] => pure (.vArr (Array.replicate count.toNat v))
      | _ => err "replicateImpl: bad args"
  | "Data.Array", "unconsImpl" =>
      match args with
      | [empty, next, .vArr es] =>
          if es.isEmpty then apply ctx empty (.vObj [])
          else do
            let hd := es[0]!
            let tl := Value.vArr (es.extract 1 es.size)
            apply ctx next hd >>= fun f => apply ctx f tl
      | _ => err "unconsImpl: bad args"
  | "Data.Semiring", "intAdd" => int2 (fun a b => .vInt (a + b))
  | "Data.Semiring", "intMul" => int2 (fun a b => .vInt (a * b))
  | "Data.Ring", "intSub" => int2 (fun a b => .vInt (a - b))
  | "Data.HeytingAlgebra", "boolConj" =>
      match args with
      | [.vBool a, .vBool b] => pure (.vBool (a && b))
      | _ => err "boolConj: bad args"
  | "Data.HeytingAlgebra", "boolDisj" =>
      match args with
      | [.vBool a, .vBool b] => pure (.vBool (a || b))
      | _ => err "boolDisj: bad args"
  | "Data.HeytingAlgebra", "boolNot" =>
      match args with
      | [.vBool a] => pure (.vBool !a)
      | _ => err "boolNot: bad args"
  | "Data.Eq", "eqIntImpl" => int2 (fun a b => .vBool (a == b))
  | "Data.Eq", "eqStringImpl" =>
      match args with
      | [.vStr a, .vStr b] => pure (.vBool (a == b))
      | _ => err "eqStringImpl: bad args"
  | "Data.Eq", "eqBooleanImpl" =>
      match args with
      | [.vBool a, .vBool b] => pure (.vBool (a == b))
      | _ => err "eqBooleanImpl: bad args"
  | "Data.Eq", "eqArrayImpl" =>
      match args with
      | [eq, .vArr a, .vArr b] => do
          if a.size != b.size then pure (.vBool false)
          else do
            let mut ok := true
            for i in [0:a.size] do
              if ok then
                match ← apply ctx eq a[i]! >>= fun f => apply ctx f b[i]! with
                | .vBool r => ok := r
                | v => err s!"eqArrayImpl: {v.describe}"
            pure (.vBool ok)
      | _ => err "eqArrayImpl: bad args"
  | "Data.Ord", "ordIntImpl" =>
      match args with
      | [lt, eq, gt, .vInt a, .vInt b] =>
          pure (if a < b then lt else if a == b then eq else gt)
      | _ => err "ordIntImpl: bad args"
  | "Data.Ord", "ordStringImpl" =>
      match args with
      | [lt, eq, gt, .vStr a, .vStr b] =>
          pure (if a < b then lt else if a == b then eq else gt)
      | _ => err "ordStringImpl: bad args"
  | "Data.Semigroup", "concatArray" =>
      match args with
      | [.vArr a, .vArr b] => pure (.vArr (a ++ b))
      | _ => err "concatArray: bad args"
  | "Data.Semigroup", "concatString" =>
      match args with
      | [.vStr a, .vStr b] => pure (.vStr (a ++ b))
      | _ => err "concatString: bad args"
  | "Data.FunctorWithIndex", "mapWithIndexArray" =>
      match args with
      | [f, .vArr es] => do
          let mut acc : Array Value := #[]
          for i in [0:es.size] do
            acc := acc.push (← apply ctx f (.vInt i) >>= fun g => apply ctx g es[i]!)
          pure (.vArr acc)
      | _ => err "mapWithIndexArray: bad args"
  | "Control.Bind", "arrayBind" =>
      match args with
      | [.vArr es, f] => do
          let mut acc : Array Value := #[]
          for e in es do
            match ← apply ctx f e with
            | .vArr inner => acc := acc ++ inner
            | v => err s!"arrayBind: non-array {v.describe}"
          pure (.vArr acc)
      | _ => err s!"arrayBind: bad args {args.map (·.describe)}"
  | "Control.Apply", "arrayApply" =>
      match args with
      | [.vArr fs, .vArr es] => do
          let mut acc : Array Value := #[]
          for f in fs do
            for e in es do
              acc := acc.push (← apply ctx f e)
          pure (.vArr acc)
      | _ => err s!"arrayApply: bad args {args.map (·.describe)}"
  | "Data.Functor", "arrayMap" =>
      match args with
      | [f, .vArr es] => do
          let mut acc : Array Value := #[]
          for e in es do
            acc := acc.push (← apply ctx f e)
          pure (.vArr acc)
      | _ => err s!"arrayMap: bad args {args.map (·.describe)}"
  | "Data.Array", "filterImpl" =>
      match args with
      | [f, .vArr es] => do
          let mut acc : Array Value := #[]
          for e in es do
            match ← apply ctx f e with
            | .vBool true => acc := acc.push e
            | .vBool false => pure ()
            | v => err s!"filterImpl: {v.describe}"
          pure (.vArr acc)
      | _ => err "filterImpl: bad args"
  | "Data.Array", "reverse" =>
      match args with
      | [.vArr es] => pure (.vArr es.reverse)
      | _ => err "reverse: bad args"
  | "Data.Array", "sliceImpl" =>
      match args with
      | [.vInt lo, .vInt hi, .vArr es] =>
          pure (.vArr (es.extract lo.toNat hi.toNat))
      | _ => err "sliceImpl: bad args"
  | "Data.Array", "zipWithImpl" =>
      match args with
      | [f, .vArr a, .vArr b] => do
          let mut acc : Array Value := #[]
          for i in [0:min a.size b.size] do
            acc := acc.push (← apply ctx f a[i]! >>= fun g => apply ctx g b[i]!)
          pure (.vArr acc)
      | _ => err "zipWithImpl: bad args"
  | "Data.Foldable", "foldrArray" =>
      match args with
      | [f, z, .vArr es] => do
          let mut acc := z
          for i in [0:es.size] do
            acc ← apply ctx f es[es.size - 1 - i]! >>= fun g => apply ctx g acc
          pure acc
      | _ => err "foldrArray: bad args"
  | "Data.Foldable", "foldlArray" =>
      match args with
      | [f, z, .vArr es] => do
          let mut acc := z
          for e in es do
            acc ← apply ctx f acc >>= fun g => apply ctx g e
          pure acc
      | _ => err "foldlArray: bad args"
  | "Data.Function.Uncurried", "mkFn2" | "Data.Function.Uncurried", "mkFn3"
  | "Data.Function.Uncurried", "mkFn4" =>
      match args with
      | [f] => pure f
      | _ => err "mkFn: bad args"
  | "Data.Function.Uncurried", "runFn2" | "Data.Function.Uncurried", "runFn3"
  | "Data.Function.Uncurried", "runFn4" =>
      match args with
      | f :: rest => rest.foldlM (apply ctx) f
      | _ => err "runFn: bad args"
  | "Partial.Unsafe", "_unsafePartial" =>
      match args with
      | [f] => apply ctx f (.vObj [])
      | _ => err "_unsafePartial: bad args"
  | "Control.Monad.ST.Internal", "run" =>
      match args with
      | [m] => runST ctx m
      | _ => err "ST.run: bad args"
  | "Control.Monad.ST.Internal", _ =>
      -- defunctionalized: build an ST node, interpreted by `runST`
      pure (.vCtor "$ST" n args.length args)
  | "Control.Monad.ST.Uncurried", _ =>
      -- runSTFnN fn a₁ … aN — package the primitive with its arguments
      pure (.vCtor "$ST" "STFn" args.length args)
  | "Data.Array.ST", _ =>
      -- the primitives are only ever packaged via runSTFn; keep them symbolic
      err s!"Data.Array.ST.{n} applied directly (expected via runSTFn)"
  | "Data.Unit", "unit" => pure (.vObj [])
  | "Data.Show", "showIntImpl" =>
      match args with
      | [.vInt a] => pure (.vStr (toString a))
      | _ => err "showIntImpl: bad args"
  | "Effect", "pureE" => pure (.vCtor "$ST" "pure_" args.length args)
  | "Effect", "bindE" => pure (.vCtor "$ST" "bind_" args.length args)
  | "Effect", "untilE" => pure (.vCtor "$ST" "untilE" args.length args)
  | "Effect", "whileE" => pure (.vCtor "$ST" "whileE" args.length args)
  | "Effect", "forE" => pure (.vCtor "$ST" "forE" args.length args)
  | "Effect", "foreachE" => pure (.vCtor "$ST" "foreach" args.length args)
  | "Effect.Ref", "_new" => pure (.vCtor "$ST" "new" args.length args)
  | "Effect.Ref", "read" => pure (.vCtor "$ST" "read" args.length args)
  | "Effect.Ref", "write" => pure (.vCtor "$ST" "write" args.length args)
  | "Effect.Ref", "modifyImpl" => pure (.vCtor "$ST" "modifyImpl" args.length args)
  | "Effect.Unsafe", "unsafePerformEffect" =>
      match args with
      | [m'] => runST ctx m'
      | _ => err "unsafePerformEffect: bad args"
  | "Unsafe.Coerce", "unsafeCoerce" | "Data.Reflectable", "unsafeCoerce" =>
      match args with
      | [v] => pure v
      | _ => err "unsafeCoerce: bad args"
  | "Record.Unsafe", "unsafeHas" =>
      match args with
      | [.vStr k, .vObj fs] => pure (.vBool (fs.any (·.1 == k)))
      | _ => err "unsafeHas: bad args"
  | "Record.Unsafe", "unsafeGet" =>
      match args with
      | [.vStr k, .vObj fs] =>
          match fs.find? (·.1 == k) with
          | some (_, v) => pure v
          | none => err s!"unsafeGet: no field {k}"
      | _ => err s!"unsafeGet: bad args {args.map (·.describe)}"
  | "Record.Unsafe", "unsafeSet" =>
      match args with
      | [.vStr k, v, .vObj fs] =>
          pure (.vObj ((k, v) :: fs.filter (·.1 != k)))
      | _ => err s!"unsafeSet: bad args {args.map (·.describe)}"
  | "Record.Unsafe", "unsafeDelete" =>
      match args with
      | [.vStr k, .vObj fs] => pure (.vObj (fs.filter (·.1 != k)))
      | _ => err s!"unsafeDelete: bad args {args.map (·.describe)}"
  | "Data.Int", "quot" => int2 (fun a b => .vInt (a.tdiv b))
  | "Data.Int", "rem" => int2 (fun a b => .vInt (a.tmod b))
  | "Data.Int", "pow" => int2 (fun a b => .vInt (a ^ b.toNat))
  | "Snarky.Curves.Pasta", _ => pasta ctx n args
  | "$builtin", "arrPush" =>
      match args with
      | [.vArr xs, x] => pure (.vArr (xs.push x))
      | _ => err s!"arrPush: bad args {args.map (·.describe)}"
  | "$builtin", "array1" =>
      match args with
      | [a] => pure (.vArr #[a])
      | _ => err "array1: bad args"
  | "$builtin", "concat2" =>
      match args with
      | [.vArr xs, .vArr ys] => pure (.vArr (xs ++ ys))
      | _ => err s!"concat2: bad args {args.map (·.describe)}"
  | "Data.Traversable", "traverseArrayImpl" =>
      -- (apply, map, pure, f, array): faithful divide-and-conquer, effects left-to-right —
      -- singleton leaves via `array1`, merged with `apply (map concat2 left) right`
      match args with
      | [applyF, mapF, pureF, f, .vArr es] => do
          let arr1 := Value.vForeign "$builtin" "array1" 1 []
          let cat2 := Value.vForeign "$builtin" "concat2" 2 []
          let rec go (bot top : Nat) : IO Value := do
            if bot == top then do
              let fe ← apply ctx f es[bot]!
              apply ctx (← apply ctx mapF arr1) fe
            else do
              let mid := (bot + top) / 2
              let left ← go bot mid
              let right ← go (mid + 1) top
              let merged ← apply ctx (← apply ctx mapF cat2) left
              apply ctx (← apply ctx applyF merged) right
          if es.isEmpty then apply ctx pureF (.vArr #[])
          else go 0 (es.size - 1)
      | _ => err s!"traverseArrayImpl: bad args {args.map (·.describe)}"
  | _, _ => err s!"foreign {m}.{n} not implemented ({args.length} args)"

/-- The napi field boundary, realized in Lean: `Fp = Vesta.ScalarField` as `Int` mod
    `vestaScalarModulus` (the Pallas base-field cardinality). Inversion and `pow` use
    binary exponentiation mod `p`. -/
partial def pasta (_ctx : Ctx) (n : String) (args : List Value) : IO Value := do
  let P := vestaScalarModulus
  let norm (a : Int) : Int := a.emod P
  match n, args with
  | "_vestaScalarFieldZero", [_] => pure (.vBig 0)
  | "_vestaScalarFieldOne", [_] => pure (.vBig 1)
  | "_vestaScalarFieldModulus", [_] => pure (.vBig P)
  | "_vestaScalarFieldAdd", [.vBig a, .vBig b] => pure (.vBig (norm (a + b)))
  | "_vestaScalarFieldSub", [.vBig a, .vBig b] => pure (.vBig (norm (a - b)))
  | "_vestaScalarFieldMul", [.vBig a, .vBig b] => pure (.vBig (norm (a * b)))
  | "_vestaScalarFieldEq", [.vBig a, .vBig b] => pure (.vBool (norm a == norm b))
  | "_vestaScalarFieldInvert", [.vBig a] =>
      pure (.vBig (Int.ofNat (powMod (norm a).toNat (P.toNat - 2) P.toNat)))
  | "_vestaScalarFieldDiv", [.vBig a, .vBig b] =>
      pure (.vBig (norm (a * Int.ofNat (powMod (norm b).toNat (P.toNat - 2) P.toNat))))
  | "_vestaScalarFieldPow", [.vBig a, .vBig e] =>
      pure (.vBig (Int.ofNat (powMod (norm a).toNat e.toNat P.toNat)))
  | "_vestaScalarFieldFromBigInt", [.vBig a] => pure (.vBig (norm a))
  | "_vestaScalarFieldToBigInt", [.vBig a] => pure (.vBig (norm a))
  | "_vestaScalarFieldToString", [.vBig a] => pure (.vStr (toString (norm a)))
  | _, _ => err s!"Snarky.Curves.Pasta.{n}/{args.length} not implemented"

end

/-! ## Entry point -/

/-- Evaluate `module.ident` applied to the given arguments. -/
def run (ctx : Ctx) (m ident : String) (args : List Value) : IO Value := do
  let f ← globalValue ctx m ident
  args.foldlM (apply ctx) f

end Kimchi.CoreFn
