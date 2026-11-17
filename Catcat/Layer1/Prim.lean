import Catcat.Layer1.Types
namespace Catcat

/-- What the host keeps between operations. -/
structure World where
  out : String := ""

/-- Primitives with one fixed signature, written bottom to top as in source. -/
def fixedPrims : List (String × List Ty × List Ty) := [
  ("+", [.int, .int], [.int]), ("-", [.int, .int], [.int]), ("*", [.int, .int], [.int]),
  ("/", [.int, .int], [.int]), ("%", [.int, .int], [.int]),
  ("<", [.int, .int], [.int]), ("=", [.int, .int], [.int]),
  ("len", [.syn], [.int]), ("slice", [.syn, .int, .int], [.syn]), ("cat", [.syn, .syn], [.syn]),
  ("wrap", [.syn], [.syn]), ("int>syn", [.int], [.syn]), ("eq", [.syn, .syn], [.int]),
  ("emit", [.int], [])]

/-- Result segments of `view`, one per outcome: integer token, word token, single group, other. -/
def viewOuts : List (List Ty) := [[.int], [.syn], [.syn], [.syn]]

def truth (b : Bool) : Val := .int (if b then 1 else 0)

/-- Arguments arrive top-first, so `[b, a]` is source order `a b`.
Returns the outcome chosen and its results. -/
def prim (name : String) (n : Nat) (args : List Val) (w : World) :
    Option (Nat × List Val × World) :=
  let ok v := some (0, [v], w)
  match name, args with
  | "pick", _ => do some (0, (← args[n]?) :: args, w)
  | "roll", _ => do some (0, (← args[n]?) :: args.eraseIdx n, w)
  | "drop", [_] => some (0, [], w)
  | "+", [.int b, .int a] => ok (.int (a + b))
  | "-", [.int b, .int a] => ok (.int (a - b))
  | "*", [.int b, .int a] => ok (.int (a * b))
  -- Truncating, as in C and JS: `a / 0 = 0` and `a % 0 = a`.
  | "/", [.int b, .int a] => ok (.int (a.tdiv b))
  | "%", [.int b, .int a] => ok (.int (a.tmod b))
  | "<", [.int b, .int a] => ok (truth (a < b))
  | "=", [.int b, .int a] => ok (truth (a == b))
  | "if", [.int c] => some (if c != 0 then 0 else 1, [], w)
  | "len", [.syn s] => ok (.int s.length)
  | "slice", [.int hi, .int lo, .syn s] => ok (.syn ((s.take hi.toNat).drop lo.toNat))
  | "cat", [.syn b, .syn a] => ok (.syn (a ++ b))
  | "wrap", [.syn s] => ok (.syn [.group .square s])
  | "int>syn", [.int n] => ok (.syn [.int n])
  | "eq", [.syn b, .syn a] => ok (truth (a == b))
  | "view", [.syn s] =>
    match s with
    | [.int n] => some (0, [.int n], w)
    | [.word _] => some (1, [.syn s], w)
    | [.group _ items] => some (2, [.syn items], w)
    | _ => some (3, [.syn s], w)
  | "emit", [.int c] => some (0, [], { w with out := w.out.push (Char.ofNat c.toNat) })
  | _, _ => none

end Catcat
