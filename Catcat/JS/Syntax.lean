namespace Catcat.JS

/-! A subset of strict-mode JavaScript: `const` bindings only, `BigInt` for integers,
arrays as the one mutable object, and no loops. -/

inductive BinOp where
  | add | sub | mul | div | mod | lt
  /-- `===`, used only where neither side is an array. -/
  | eq
  /-- `+` on strings. -/
  | concat
deriving BEq

inductive Builtin where
  /-- `String(n)` for a BigInt. -/
  | str
  /-- `String.fromCodePoint(Number(n))` for a valid scalar value. -/
  | chr
  /-- `process.stdout.write(s)`. -/
  | write
deriving BEq

mutual
inductive Expr where
  | undef
  | bool (b : Bool)
  | big (n : Int)
  | str (s : String)
  | var (x : String)
  | arr (items : List Expr)
  /-- `a[i]` with a literal index. -/
  | index (a : Expr) (i : Nat)
  | bin (op : BinOp) (a b : Expr)
  | cond (c t e : Expr)
  | fn (params : List String) (body : List Stmt)
  | call (f : Expr) (args : List Expr)
  | push (a v : Expr)
  | pop (a : Expr)
  | builtin (b : Builtin) (arg : Expr)

inductive Stmt where
  | const (x : String) (e : Expr)
  /-- A function declaration. Its body may call it by name. -/
  | func (name : String) (params : List String) (body : List Stmt)
  /-- `a[i] = v;` with a literal index that is already in range. -/
  | setIndex (a : Expr) (i : Nat) (v : Expr)
  | expr (e : Expr)
  | ite (c : Expr) (thn els : List Stmt)
  | block (body : List Stmt)
  | ret (e : Expr)
  /-- `throw new Error(msg);` -/
  | throw (msg : Expr)
end

/-- Top-level functions may call one another; `main` runs after them. -/
structure Program where
  funcs : List (String × List String × List Stmt)
  main : List Stmt

end Catcat.JS
