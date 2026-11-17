import Catcat.JS.Syntax
namespace Catcat.JS

def BinOp.symbol : BinOp → String
  | .add | .concat => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .lt => "<" | .eq => "==="

def quote (s : String) : String :=
  let esc (c : Char) : String :=
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    -- Control characters and the two line separators JS treats as newlines.
    else if c.toNat < 32 || c.toNat == 127 || c.toNat == 0x2028 || c.toNat == 0x2029 then
      "\\u{" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "}"
    else c.toString
  "\"" ++ String.join (s.toList.map esc) ++ "\""

def commas (xs : List String) : String := ", ".intercalate xs

mutual
/-- Every compound expression is parenthesized, so precedence never matters. -/
def Expr.print (ind : String) : Expr → String
  | .undef => "undefined"
  | .bool b => toString b
  | .big n => if n < 0 then s!"({n}n)" else s!"{n}n"
  | .str s => quote s
  | .var x => x
  | .arr items => s!"[{commas (printAll ind items)}]"
  | .index a i => s!"{a.print ind}[{i}]"
  | .bin op a b => s!"({a.print ind} {op.symbol} {b.print ind})"
  | .cond c t e => s!"({c.print ind} ? {t.print ind} : {e.print ind})"
  | .fn params body => s!"(({commas params}) => {printBlock ind body})"
  | .call f args => s!"{f.print ind}({commas (printAll ind args)})"
  | .push a v => s!"{a.print ind}.push({v.print ind})"
  | .pop a => s!"{a.print ind}.pop()"
  | .builtin .str e => s!"String({e.print ind})"
  | .builtin .chr e => s!"String.fromCodePoint(Number({e.print ind}))"
  | .builtin .write e => s!"process.stdout.write({e.print ind})"

def printAll (ind : String) : List Expr → List String
  | [] => []
  | e :: es => e.print ind :: printAll ind es

def Stmt.print (ind : String) : Stmt → String
  | .const x e => s!"{ind}const {x} = {e.print ind};\n"
  | .func name params body => s!"{ind}function {name}({commas params}) {printBlock ind body}\n"
  | .setIndex a i v => s!"{ind}{a.print ind}[{i}] = {v.print ind};\n"
  | .expr e => s!"{ind}{e.print ind};\n"
  | .ite c thn els => s!"{ind}if ({c.print ind}) {printBlock ind thn} else {printBlock ind els}\n"
  | .block body => s!"{ind}{printBlock ind body}\n"
  | .ret e => s!"{ind}return {e.print ind};\n"
  | .throw msg => s!"{ind}throw new Error({msg.print ind});\n"

def printStmts (ind : String) : List Stmt → String
  | [] => ""
  | s :: ss => s.print ind ++ printStmts ind ss

/-- `{ … }` with the body one level deeper than `ind`; the closing brace sits at `ind`. -/
def printBlock (ind : String) (body : List Stmt) : String :=
  "{\n" ++ printStmts (ind ++ "  ") body ++ ind ++ "}"
end

def Program.print (p : Program) : String :=
  "\"use strict\";\n" ++
  String.join (p.funcs.map fun (name, params, body) => (Stmt.func name params body).print "") ++
  printStmts "" p.main

end Catcat.JS
