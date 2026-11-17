import Catcat.JS.Syntax
namespace Catcat.JS

inductive Value where
  | undef
  | bool (b : Bool)
  | big (n : Int)
  | str (s : String)
  /-- An array, by its location in the heap. -/
  | ref (loc : Nat)
  /-- `self` is the function's own name, bound again at each call. -/
  | closure (self : Option String) (params : List String) (body : List Stmt)
      (env : List (String × Value))

structure State where
  heap : Array (Array Value) := #[]
  out : String := ""

/-- Errors keep the state, so output written before a failure is not lost. -/
abbrev M := ExceptT String (StateM State)
abbrev Env := List (String × Value)
abbrev Funcs := List (String × List String × List Stmt)

def array (v : Value) : M (Nat × Array Value) := do
  let .ref loc := v | throw "not an array"
  let some a := (← get).heap[loc]? | throw "no such array"
  pure (loc, a)

def store (loc : Nat) (a : Array Value) : M Unit :=
  modify fun s => { s with heap := s.heap.setIfInBounds loc a }

def binop : BinOp → Value → Value → Except String Value
  | .add, .big a, .big b => pure (.big (a + b))
  | .sub, .big a, .big b => pure (.big (a - b))
  | .mul, .big a, .big b => pure (.big (a * b))
  | .div, .big a, .big b => if b == 0 then throw "division by zero" else pure (.big (a.tdiv b))
  | .mod, .big a, .big b => if b == 0 then throw "division by zero" else pure (.big (a.tmod b))
  | .lt, .big a, .big b => pure (.bool (a < b))
  | .concat, .str a, .str b => pure (.str (a ++ b))
  | .eq, .big a, .big b => pure (.bool (a == b))
  | .eq, .str a, .str b => pure (.bool (a == b))
  | .eq, .bool a, .bool b => pure (.bool (a == b))
  | .eq, .undef, .undef => pure (.bool true)
  -- JS would compare identities here. The subset never relies on that, so it is an error.
  | .eq, .ref _, .ref _ | .eq, .closure .., .closure .. => throw "=== on two objects"
  | .eq, _, _ => pure (.bool false)
  | _, _, _ => throw "operands of the wrong type"

def scalar (n : Int) : Bool := (0 ≤ n && n < 0xD800) || (0xE000 ≤ n && n < 0x110000)

mutual
/-- `call` applies a function value. It is the only step that is not structural. -/
def eval (funcs : Funcs) (call : Value → List Value → M Value) (env : Env) : Expr → M Value
  | .undef => pure .undef
  | .bool b => pure (.bool b)
  | .big n => pure (.big n)
  | .str s => pure (.str s)
  | .var x =>
    match env.lookup x, funcs.lookup x with
    | some v, _ => pure v
    | none, some (params, body) => pure (.closure none params body [])
    | none, none => throw s!"{x} is not defined"
  | .arr items => do
    let vs ← evalAll funcs call env items
    modifyGet fun s => (.ref s.heap.size, { s with heap := s.heap.push vs.toArray })
  | .index a i => do
    let (_, arr) ← array (← eval funcs call env a)
    pure (arr[i]?.getD .undef)
  | .bin op a b => do
    let x ← eval funcs call env a
    let y ← eval funcs call env b
    liftExcept (binop op x y)
  | .cond c t e => do
    match ← eval funcs call env c with
    | .bool true => eval funcs call env t
    | .bool false => eval funcs call env e
    | _ => throw "condition is not a boolean"
  | .fn params body => pure (.closure none params body env)
  | .call f args => do
    let fv ← eval funcs call env f
    call fv (← evalAll funcs call env args)
  | .push a v => do
    let target ← eval funcs call env a
    let x ← eval funcs call env v
    -- Read the array only now: evaluating `v` may itself have changed it.
    let (loc, arr) ← array target
    store loc (arr.push x)
    pure .undef
  | .pop a => do
    let (loc, arr) ← array (← eval funcs call env a)
    store loc arr.pop
    pure (arr.back?.getD .undef)
  | .builtin b e => do
    match b, ← eval funcs call env e with
    | .str, .big n => pure (.str (toString n))
    | .chr, .big n =>
      if scalar n then pure (.str (Char.ofNat n.toNat).toString) else throw "invalid code point"
    | .write, .str s => do
      modify fun st => { st with out := st.out ++ s }
      pure .undef
    | _, _ => throw "builtin argument of the wrong type"

def evalAll (funcs : Funcs) (call : Value → List Value → M Value) (env : Env) :
    List Expr → M (List Value)
  | [] => pure []
  | e :: es => do
    let v ← eval funcs call env e
    (v :: ·) <$> evalAll funcs call env es

/-- `some v` when a `return` was reached. -/
def exec (funcs : Funcs) (call : Value → List Value → M Value) (env : Env) :
    List Stmt → M (Option Value)
  | [] => pure none
  | .const x e :: rest => do
    let v ← eval funcs call env e
    exec funcs call ((x, v) :: env) rest
  | .func name params body :: rest =>
    exec funcs call ((name, .closure (some name) params body env) :: env) rest
  | .setIndex a i v :: rest => do
    let target ← eval funcs call env a
    let x ← eval funcs call env v
    let (loc, arr) ← array target
    unless i < arr.size do throw "index out of range"
    store loc (arr.setIfInBounds i x)
    exec funcs call env rest
  | .expr e :: rest => do
    let _ ← eval funcs call env e
    exec funcs call env rest
  | .ite c thn els :: rest => do
    let returned ← match ← eval funcs call env c with
      | .bool true => exec funcs call env thn
      | .bool false => exec funcs call env els
      | _ => throw "condition is not a boolean"
    if returned.isSome then pure returned else exec funcs call env rest
  | .block body :: rest => do
    let returned ← exec funcs call env body
    if returned.isSome then pure returned else exec funcs call env rest
  | .ret e :: _ => some <$> eval funcs call env e
  | .throw msg :: _ => do
    match ← eval funcs call env msg with
    | .str s => throw s
    | _ => throw "thrown message is not a string"
end

/-- `fuel` bounds the depth of calls, as the native stack does in a real engine. -/
def callWith (funcs : Funcs) : Nat → Value → List Value → M Value
  | 0, _, _ => throw "out of fuel"
  | fuel + 1, .closure self params body env, args => do
    let me := match self with
      | some name => [(name, Value.closure self params body env)]
      | none => []
    return (← exec funcs (callWith funcs fuel) (params.zip args ++ me ++ env) body).getD .undef
  | _, _, _ => throw "not a function"

/-- What the program wrote, and the error if it threw. -/
def Program.run (p : Program) (fuel : Nat := 1000) : String × Option String :=
  match (exec p.funcs (callWith p.funcs fuel) [] p.main).run.run {} with
  | (.ok _, st) => (st.out, none)
  | (.error e, st) => (st.out, some e)

end Catcat.JS
