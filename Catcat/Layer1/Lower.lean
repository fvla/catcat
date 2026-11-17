import Catcat.Layer1.Prim
namespace Catcat

/-- The stack type at a point in the code being lowered. -/
structure Shape where
  stack : List Ty := []
  /-- `some`: the bottom is open, and these inputs have been asked for so far, top-first. -/
  inputs : Option (List Ty) := none
deriving BEq

abbrev L := Except String
/-- Lowers a nested or spliced body. -/
abbrev Sub := Env → Shape → List Item → L (T × Shape)

def Shape.push (sh : Shape) (ts : List Ty) : Shape := { sh with stack := ts ++ sh.stack }

def Shape.pop (sh : Shape) (t : Ty) : L Shape :=
  match sh.stack, sh.inputs with
  | a :: stack, _ =>
    if a == t then pure { sh with stack } else throw s!"expected {t.show}, found {a.show}"
  | [], some inputs => pure { sh with inputs := some (inputs ++ [t]) }
  | [], none => throw s!"stack underflow: expected {t.show}"

def Shape.apply (sh : Shape) (pre post : List Ty) : L Shape := do
  pure ((← pre.foldlM Shape.pop sh).push post)

/-- The top `n` types, for operations whose signature depends on them. -/
def Shape.top (sh : Shape) (n : Nat) (what : String) : L (List Ty) :=
  if sh.stack.length ≥ n then pure (sh.stack.take n)
  else if sh.inputs.isSome then
    throw s!"{what}: needs a value from below this block; give the block a signature"
  else throw s!"{what}: stack underflow"

def call (name : Name) (pre : List Ty) (outs : List (List Ty)) (branches : List T := [.nil]) : T :=
  .op ⟨name, pre, outs⟩ branches

def lit (v : Val) (t : Ty) : T := call (.lit v) [] [[t]]
def dropT (t : Ty) : T := call (.prim "drop" 0) [t] [[]]
def codeTy (s : Sig Ty) : Ty := .code s.pre s.post
def wordOp (w : String) (sig : Sig Ty) : Op Ty Name := ⟨.user w, sig.pre, [sig.post]⟩
def readOp (x : String) (t : Ty) : Op Ty Name := ⟨.user x, [], [[t]]⟩
def writeOp (x : String) (t : Ty) : Op Ty Name := ⟨.user (x ++ "!"), [t], [[]]⟩

/-- The definition of `w` and the definitions older than it. -/
def findDef (w : String) : List (String × Def) → Option (Def × List (String × Def))
  | [] => none
  | (name, d) :: older => if name == w then some (d, older) else findDef w older

/-- Lowers a block from a closed stack and checks what it leaves. -/
def closed (sub : Sub) (env : Env) (sig : Sig Ty) (body : List Item) : L T := do
  let (t, out) ← sub env { stack := sig.pre } body
  unless out.stack == sig.post do
    throw s!"block leaves ( {showTys out.stack}), its signature says ( {showTys sig.post})"
  pure t

def lowerWord (sub : Sub) (env : Env) (sh : Shape) (w : String) : L (T × Shape) :=
  match env.vars.lookup w, findDef w env.defs with
  | some t, _ => pure (.op (readOp w t) [.nil], sh.push [t])
  | _, some (.plain body, older) => sub { env with defs := older } sh body
  | _, some (.label sig, _) => do
    pure (.op (wordOp w sig) [.nil], ← sh.apply sig.pre sig.post)
  | _, some (.recursive sig body, older) => do
    let c ← closed sub { env with defs := (w, .label sig) :: older } sig body
    -- The handler wraps this call only, so whatever else the body performs
    -- reaches the handlers around the call.
    let t := .handle true [] [(wordOp w sig, c)] (.op (wordOp w sig) [.nil])
    pure (t, ← sh.apply sig.pre sig.post)
  | none, none =>
    match w, fixedPrims.lookup w with
    | _, some (pre, post) => do
      pure (call (.prim w 0) pre.reverse [post.reverse], ← sh.apply pre.reverse post.reverse)
    | "drop", _ => do
      let [t] ← sh.top 1 "drop" | throw "drop: empty stack"
      pure (dropT t, ← sh.pop t)
    | "run", _ => do
      let [.code pre post] ← sh.top 1 "run" | throw "run: the top of the stack is not code"
      pure (.run ⟨pre, post⟩, ← (← sh.pop (.code pre post)).apply pre post)
    | _, _ => throw s!"unknown word `{w}`"

/-- Lowers each branch from its own entry shape. All must leave the same shape. -/
def branches (sub : Shape → List Item → L (T × Shape)) (what : String) :
    List (Shape × List Item) → L (List T × Shape)
  | [] => throw s!"{what}: no branches"
  | [(sh, b)] => do
    let (t, out) ← sub sh b
    pure ([t], out)
  | (sh, b) :: rest => do
    let (t, out) ← sub sh b
    let (ts, out') ← branches sub what rest
    unless out == out' do throw s!"{what}: branches leave different stacks"
    pure (t :: ts, out)

/-- `depth` bounds how far blocks and spliced words may nest. -/
def lower : Nat → Env → Shape → List Item → L (T × Shape)
  | _, _, sh, [] => pure (.nil, sh)
  | 0, _, _, _ => throw "definitions are nested too deeply"
  | d + 1, env, sh,
      .word "define" :: .word w :: .group .paren sig :: .group .brace body :: rest => do
    lower (d + 1) { env with defs := (w, .recursive (← parseSig sig) body) :: env.defs } sh rest
  | d + 1, env, sh, .word "define" :: .word w :: .group .brace body :: rest =>
    lower (d + 1) { env with defs := (w, .plain body) :: env.defs } sh rest
  | d + 1, env, sh, .word "let" :: .group .square [.word x] :: rest => do
    let [t] ← sh.top 1 "let" | throw "let: empty stack"
    let (body, out) ← lower (d + 1) { env with vars := (x, t) :: env.vars } (← sh.pop t) rest
    -- The cell is on top when a clause runs: reading copies it, writing drops the old value.
    let clauses := [(readOp x t, call (.prim "pick" 0) [t] [[t, t]]), (writeOp x t, dropT t)]
    pure (.seq (.handle false [t] clauses body) (dropT t), out)
  | d + 1, env, sh, item :: rest => do
    let block := lower d env
    -- `used` is how many items of `rest` the form at the head takes.
    let (t, sh, used) ← match item, rest with
      | .int n, _ => pure (lit (.int n) .int, sh.push [.int], 0)
      | .group .square items, _ => pure (lit (.syn items) .syn, sh.push [.syn], 0)
      | .group .brace body, _ => do
        let (_, out) ← lower d env { inputs := some [] } body
        let sig : Sig Ty := ⟨out.inputs.getD [], out.stack⟩
        pure (lit (.code sig body env) (codeTy sig), sh.push [codeTy sig], 0)
      | .group .paren sig, .group .brace body :: _ => do
        let sig ← parseSig sig
        let _ ← closed (lower d) env sig body
        pure (lit (.code sig body env) (codeTy sig), sh.push [codeTy sig], 1)
      | .word "pick", .group .square [.int n] :: _ => do
        let ts ← sh.top (n.toNat + 1) "pick"
        let t := ts.getLast?.getD .int
        pure (call (.prim "pick" n.toNat) ts [t :: ts], sh.push [t], 1)
      | .word "roll", .group .square [.int n] :: _ => do
        let ts ← sh.top (n.toNat + 1) "roll"
        let moved := ts.getLast?.getD .int :: ts.dropLast
        let stack := moved ++ sh.stack.drop ts.length
        pure (call (.prim "roll" n.toNat) ts [moved], { sh with stack }, 1)
      | .word "set", .group .square [.word x] :: _ => do
        let some t := env.vars.lookup x | throw s!"set: `{x}` is not a variable in scope"
        pure (.op (writeOp x t) [.nil], ← sh.pop t, 1)
      | .word "if", .group .brace a :: .group .brace b :: _ => do
        let sh ← sh.pop .int
        let (ts, out) ← branches block "if" [(sh, a), (sh, b)]
        pure (call (.prim "if" 0) [.int] [[], []] ts, out, 2)
      | .word "view",
          .group .brace a :: .group .brace b :: .group .brace c :: .group .brace e :: _ => do
        let sh ← sh.pop .syn
        let (ts, out) ← branches block "view" ((viewOuts.map sh.push).zip [a, b, c, e])
        pure (call (.prim "view" 0) [.syn] viewOuts ts, out, 4)
      | .word "compile", .group .paren sig :: .group .brace a :: .group .brace b :: _ => do
        let sig ← parseSig sig
        let sh ← sh.pop .syn
        let (ts, out) ← branches block "compile" [(sh.push [codeTy sig], a), (sh, b)]
        pure (call (.compile sig env) [.syn] [[codeTy sig], []] ts, out, 3)
      | .word w, _ => do
        let (t, sh) ← lowerWord (lower d) env sh w
        pure (t, sh, 0)
      | item, _ => throw s!"unexpected `{item.show}`"
    let (u, out) ← lower (d + 1) env sh (rest.drop used)
    pure (.seq t u, out)
termination_by d _ _ items => (d, items.length)

end Catcat
