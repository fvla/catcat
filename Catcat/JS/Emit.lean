import Catcat.Layer1.Run
import Catcat.JS.Runtime
namespace Catcat.JS
open Catcat

/-- A handler around the point being emitted. `depth` names its JS variables. -/
structure Frame where
  depth : Nat
  ops : List (Op Ty Name)

structure Ctx where
  /-- Innermost first. -/
  frames : List Frame := []
  /-- Inside a code value: the handlers below `frames` arrive at run time, in `E`. -/
  dynamic : Bool := false

abbrev E := Except String

def stack : Expr := .var "S"
def pop : Expr := .pop stack
def push (e : Expr) : Stmt := .expr (.push stack e)
/-- Pops into the given names, top first. -/
def pops (names : List String) : List Stmt := names.map (.const · pop)

def stateName (depth : Nat) : String := s!"h{depth}"
def clauseName (depth j : Nat) : String := s!"c{depth}_{j}"

/-- Identifies an operation label at run time, signature included. -/
def key (x : String) (o : Op Ty Name) : String :=
  s!"{x} ( {showTys o.pre}-- {showTys (o.outs.headD [])})"

def Ctx.find (ctx : Ctx) (o : Op Ty Name) : Option String :=
  ctx.frames.findSome? fun f => (f.ops.findIdx? (· == o)).map (clauseName f.depth)

/-- The handlers in scope, as the list a code value searches: `[[key, clause], rest]`. -/
def Ctx.env (ctx : Ctx) : Expr :=
  let entry (f : Frame) (rest : Expr) : Expr :=
    f.ops.zipIdx.foldr (init := rest) fun (o, j) rest =>
      match o.name with
      | .user x => .arr [.arr [.str (key x o), .var (clauseName f.depth j)], rest]
      | _ => rest
  ctx.frames.foldr entry (if ctx.dynamic then .var "E" else .undef)

def perform (ctx : Ctx) (x : String) (o : Op Ty Name) : Stmt :=
  match ctx.find o with
  | some clause => .expr (app clause [])
  | none =>
    if ctx.dynamic then .expr (.call (app "find" [.var "E", .str (key x o), .str x]) [])
    else .throw (.str (unhandled x))

mutual
def itemExpr : Item → Expr
  | .int n => .arr [.big 0, .big n]
  | .word w => .arr [.big 1, .str w]
  | .group b items => .arr [.big 2, .str b.opening, .str b.closing, listExpr items]

def listExpr : List Item → Expr
  | [] => .undef
  | i :: is => .arr [itemExpr i, listExpr is]
end

private def a := Expr.var "a"
private def b := Expr.var "b"
/-- `a` and `b` are the two arguments, in source order. -/
def binary (e : Expr) : List Stmt := [.block [.const "b" pop, .const "a" pop, push e]]
def flag (c : Expr) : Expr := .cond c (.big 1) (.big 0)

/-- A primitive, followed by the code of each of its branches. -/
def prim (name : String) (n : Nat) (branches : List (List Stmt)) : E (List Stmt) :=
  let temps := (List.range (n + 1)).map (s!"t{·}")
  let restore (names : List String) := names.reverse.map (push ∘ .var)
  let s := Expr.var "s"
  let k := Expr.var "k"
  let one (code : List Stmt) : E (List Stmt) := pure (code ++ branches.headD [])
  match name, branches with
  | "pick", _ => one [.block (pops temps ++ restore temps ++ [push (.var s!"t{n}")])]
  | "roll", _ => one [.block (pops temps ++ restore temps.dropLast ++ [push (.var s!"t{n}")])]
  | "drop", _ => one [.expr pop]
  | "+", _ => one (binary (.bin .add a b))
  | "-", _ => one (binary (.bin .sub a b))
  | "*", _ => one (binary (.bin .mul a b))
  -- BigInt division throws on zero; catcat defines it.
  | "/", _ => one (binary (.cond (is b 0) (.big 0) (.bin .div a b)))
  | "%", _ => one (binary (.cond (is b 0) a (.bin .mod a b)))
  | "<", _ => one (binary (flag (.bin .lt a b)))
  | "=", _ => one (binary (flag (.bin .eq a b)))
  | "if", [thn, els] => pure [.block [.const "c" pop, .ite (is (.var "c") 0) els thn]]
  | "len", _ => one [push (app "len" [pop])]
  | "slice", _ =>
    let sliced := app "drop" [app "take" [s, .var "hi"], .var "lo"]
    one [.block (pops ["hi", "lo", "s"] ++ [push sliced])]
  | "cat", _ => one (binary (app "cat" [a, b]))
  | "wrap", _ => one [push (.arr [.arr [.big 2, .str "[", .str "]", pop], .undef])]
  | "int>syn", _ => one [push (.arr [.arr [.big 0, pop], .undef])]
  | "eq", _ => one (binary (flag (app "eqItems" [a, b])))
  | "view", [int, word, group, other] =>
    let item := Expr.index s 0
    pure [.block [.const "s" pop, .const "k" (app "kind" [s]),
      .ite (is k 0) (push (.index item 1) :: int) [
      .ite (is k 1) (push s :: word) [
      .ite (is k 2) (push (.index item 3) :: group) (push s :: other)]]]]
  | "emit", _ => one [.expr (.builtin .write (app "chr" [pop]))]
  | _, _ => throw s!"the JS emitter has no translation for `{name}`"

mutual
/-- `code` emits the body of a code value. It is the only call that is not structural. -/
def emit (code : Val → E (List Stmt)) (ctx : Ctx) : T → E (List Stmt)
  | .nil => pure []
  | .seq t u => do pure ((← emit code ctx t) ++ (← emit code ctx u))
  | .run _ => pure [.block [.const "k" pop, .expr (.call (.index (.var "k") 0) [ctx.env])]]
  | .op o us => do
    let branches ← emitAll code ctx us
    let one (s : Stmt) : E (List Stmt) := pure (s :: branches.headD [])
    match o.name with
    | .lit (.int n) => one (push (.big n))
    | .lit (.syn items) => one (push (listExpr items))
    | .lit (.code sig body env) => do
      let text := (Item.group .brace body).show
      one (push (.arr [.fn ["E"] (← code (.code sig body env)), .str text]))
    | .prim name n => prim name n branches
    | .user x => one (perform ctx x o)
    | .compile .. => throw "`compile` needs the interpreter at run time; it cannot be emitted"
  | .handle rec st cl b => do
    unless cl.all (fun (o, _) => o.name matches .user _) do
      throw "handling a primitive cannot be emitted yet"
    if rec && cl.length > 1 then
      throw "a recursive handler with several clauses cannot be emitted yet"
    let d := ctx.frames.length
    let n := st.length
    let inner := { ctx with frames := ⟨d, cl.map (·.1)⟩ :: ctx.frames }
    let clauses ← emitClauses code (if rec then inner else ctx) d n 0 cl
    let state := if n == 0 then [] else [.const (stateName d) (.arr (List.replicate n pop))]
    pure [.block (state ++ clauses ++ (← emit code inner b) ++ pushState d n)]

def emitAll (code : Val → E (List Stmt)) (ctx : Ctx) : List T → E (List (List Stmt))
  | [] => pure []
  | t :: ts => do
    let s ← emit code ctx t
    (s :: ·) <$> emitAll code ctx ts

/-- One function per clause. It runs the clause with the handler's state on top of the
arguments, then stores the state the clause leaves. -/
def emitClauses (code : Val → E (List Stmt)) (ctx : Ctx) (d n j : Nat) :
    List (Op Ty Name × T) → E (List Stmt)
  | [] => pure []
  | (_, c) :: cl => do
    let body ← emit code ctx c
    let f := Stmt.func (clauseName d j) [] (pushState d n ++ body ++ popState d n)
    (f :: ·) <$> emitClauses code ctx d n (j + 1) cl

/-- The state goes back on the stack with its first cell on top. -/
def pushState (d n : Nat) : List Stmt :=
  (List.range n).reverse.map fun i => push (.index (.var (stateName d)) i)

def popState (d n : Nat) : List Stmt :=
  (List.range n).map fun i => .setIndex (.var (stateName d)) i pop
end

/-- The body of a code value. Its handlers are whatever is in scope where it runs.
`nesting` bounds code values inside code values; `depth` is passed to lowering. -/
def codeBody (depth : Nat) : Nat → Val → E (List Stmt)
  | 0, _ => throw "code values are nested too deeply"
  | nesting + 1, c =>
    match c.term? depth with
    | some t => emit (codeBody depth nesting) { dynamic := true } t
    | none => throw "a code value does not lower"

/-- Writes the final stack, bottom first, as the interpreter prints it. -/
def printStack (final : List Ty) : List Stmt :=
  let names := (List.range final.length).map (s!"v{·}")
  let shown (x : String) : Ty → Expr
    | .int => .builtin .str (.var x)
    | .syn => cat3 (.str "[ ") (app "showItems" [.var x]) (.str "]")
    | .code .. => .index (.var x) 1
  match (names.zip final).reverse.map fun (x, t) => shown x t with
  | [] => []
  | e :: es =>
    let line := es.foldl (fun acc e => cat3 acc (.str " ") e) e
    [.block (pops names ++ [.expr (.builtin .write (.bin .concat line (.str "\n")))])]

def emitSource (src : String) (depth : Nat := 1000) : E Program := do
  let (t, final) ← prepare src depth
  let main ← emit (codeBody depth 100) {} t
  pure ⟨runtime, .const "S" (.arr []) :: main ++ printStack final⟩

end Catcat.JS
