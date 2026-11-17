import Catcat.Kernel.Typing
import Catcat.Kernel.Eval
import Catcat.Layer1.Lower
namespace Catcat

/-- Decoding a code value is lowering its syntax again. -/
def Val.term? (depth : Nat) : Val → Option T
  | .code sig body env => (closed (lower depth) env sig body).toOption
  | _ => none

def root (depth : Nat) (o : Op Ty Name) (args : List Val) (w : World) :
    Except String (Nat × List Val × World) :=
  match o.name, args with
  | .lit v, _ => pure (0, [v], w)
  | .prim name n, _ =>
    match prim name n args w with
    | some r => pure r
    | none => throw s!"`{name}` cannot take these arguments"
  | .compile sig env, [.syn body] =>
    let c := Val.code sig body env
    pure (if (c.term? depth).isSome then (0, [c], w) else (1, [], w))
  | .compile .., _ => throw "compile: not a syntax object"
  | .user x, _ => throw s!"`{x}` is performed but nothing handles it"

structure Outcome where
  out : String
  /-- The final stack, top first. -/
  result : Except String (List Val)

/-- `depth` bounds how far blocks and spliced words may nest during lowering. -/
def runSource (src : String) (fuel : Nat := 10000000) (depth : Nat := 1000) : Outcome :=
  let prepared : Except String T := do
    let (t, sh) ← lower depth {} {} (← read src)
    -- Lowering tracks types on its own; the kernel's checker must reach the same answer.
    unless t.infer codeTy == some ⟨[], sh.stack⟩ do
      throw "internal: lowering and the kernel disagree about the program's type"
    match t.free.filterMap fun o => match o.name with | .user x => some x | _ => none with
    | [] => pure t
    | x :: _ => throw s!"`{x}` is performed but nothing handles it"
  match prepared with
  | .error e => ⟨"", .error e⟩
  | .ok t =>
    let (result, w) := (den (Val.term? depth) fuel t [] .pure).exec (root depth) {}
    ⟨w.out, result⟩

/-- The output, then the final stack bottom first, or the error. -/
def Outcome.render (o : Outcome) : String :=
  o.out ++ match o.result with
    | .ok [] => ""
    | .ok stack => " ".intercalate (stack.reverse.map Val.show) ++ "\n"
    | .error e => s!"error: {e}\n"

end Catcat
