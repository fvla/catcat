import Catcat.Kernel.Term
import Catcat.Layer1.Syntax
namespace Catcat

inductive Ty where
  | int
  | syn
  | code (pre post : List Ty)
deriving BEq, Repr

inductive Def where
  /-- Spliced at each call site. -/
  | plain (body : List Item)
  | recursive (sig : Sig Ty) (body : List Item)
  /-- A recursive word seen from inside its own body: an operation, not a splice. -/
  | label (sig : Sig Ty)
deriving BEq

structure Env where
  /-- Newest first. A body is lowered against the definitions older than it. -/
  defs : List (String × Def) := []
  /-- Dynamic variables in scope where lowering is happening. -/
  vars : List (String × Ty) := []
deriving BEq

inductive Val where
  | int (n : Int)
  | syn (items : List Item)
  /-- Code is its syntax plus what is needed to lower it again. Nothing reads it back out. -/
  | code (sig : Sig Ty) (body : List Item) (env : Env)
deriving BEq

inductive Name where
  | lit (v : Val)
  /-- `n` is the index argument of `pick` and `roll`. -/
  | prim (name : String) (n : Nat)
  | user (name : String)
  | compile (sig : Sig Ty) (env : Env)
deriving BEq

abbrev T := Term Ty Name

mutual
def Ty.show : Ty → String
  | .int => "int"
  | .syn => "Syn"
  | .code pre post => s!"Code ( {showTys pre}-- {showTys post})"

/-- Rendered bottom to top, as signatures are written. -/
def showTys : List Ty → String
  | [] => ""
  | t :: ts => showTys ts ++ t.show ++ " "
end

def Val.show : Val → String
  | .int n => toString n
  | .syn items => (Item.group .square items).show
  | .code _ body _ => (Item.group .brace body).show

/-- `( a b -- c )` reads bottom to top; a `Sig` is stored top-first. -/
def sigOf (ts : List (Option Ty)) : Except String (Sig Ty) :=
  match ts.span Option.isSome with
  | (pre, none :: post) =>
    if post.all Option.isSome then
      pure ⟨(pre.filterMap id).reverse, (post.filterMap id).reverse⟩
    else throw "signature: more than one `--`"
  | _ => throw "signature: missing `--`"

/-- One entry per type, `none` for `--`. -/
def parseTys : List Item → Except String (List (Option Ty))
  | [] => pure []
  | .word "--" :: rest => (none :: ·) <$> parseTys rest
  | .word "int" :: rest => (some .int :: ·) <$> parseTys rest
  | .word "Syn" :: rest => (some .syn :: ·) <$> parseTys rest
  | .word "Code" :: .group .paren sig :: rest => do
    let s ← sigOf (← parseTys sig)
    (some (.code s.pre s.post) :: ·) <$> parseTys rest
  | item :: _ => throw s!"signature: `{item.show}` is not a type"

def parseSig (items : List Item) : Except String (Sig Ty) := do sigOf (← parseTys items)

end Catcat
