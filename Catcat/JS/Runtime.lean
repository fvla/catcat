import Catcat.JS.Eval
namespace Catcat.JS
open Expr Stmt

def app (f : String) (args : List Expr) : Expr := .call (.var f) args
def isUndef (e : Expr) : Expr := .bin .eq e .undef
def is (e : Expr) (n : Int) : Expr := .bin .eq e (.big n)
/-- `if (c) { return e; }` -/
def retIf (c e : Expr) : Stmt := .ite c [.ret e] []
def cat3 (a b c : Expr) : Expr := .bin .concat a (.bin .concat b c)

/-! How catcat values look in JS.

* An `int` is a BigInt.
* A syntax object is `undefined` when empty, otherwise `[item, rest]`.
* An item is `[0n, n]`, `[1n, word]` or `[2n, open, close, items]`.
* A code value is `[function, text]`; the text is only for printing. -/

private def l := var "l"
private def a := var "a"
private def b := var "b"
private def n := var "n"
private def i := var "i"
private def c := var "c"

/-- The functions every emitted program starts with. -/
def runtime : Funcs := [
  ("len", ["l"], [retIf (isUndef l) (big 0), ret (bin .add (big 1) (app "len" [index l 1]))]),
  ("cat", ["a", "b"], [retIf (isUndef a) b, ret (arr [index a 0, app "cat" [index a 1, b]])]),
  ("take", ["l", "n"], [
    retIf (isUndef l) undef, retIf (bin .lt n (big 1)) undef,
    ret (arr [index l 0, app "take" [index l 1, bin .sub n (big 1)]])]),
  ("drop", ["l", "n"], [
    retIf (isUndef l) undef, retIf (bin .lt n (big 1)) l,
    ret (app "drop" [index l 1, bin .sub n (big 1)])]),
  ("eqItems", ["a", "b"], [
    retIf (isUndef a) (isUndef b), retIf (isUndef b) (bool false),
    retIf (app "eqItem" [index a 0, index b 0]) (app "eqItems" [index a 1, index b 1]),
    ret (bool false)]),
  ("eqItem", ["a", "b"], [
    ite (bin .eq (index a 0) (index b 0)) [] [ret (bool false)],
    -- Two groups: same bracket, then the same contents.
    ite (is (index a 0) 2) [
      retIf (bin .eq (index a 1) (index b 1)) (app "eqItems" [index a 3, index b 3]),
      ret (bool false)] [],
    ret (bin .eq (index a 1) (index b 1))]),
  -- The outcome of `view`: the tag of a lone item, or 3 for anything else.
  ("kind", ["l"], [
    retIf (isUndef l) (big 3), retIf (isUndef (index l 1)) (index (index l 0) 0), ret (big 3)]),
  ("showItems", ["l"], [
    retIf (isUndef l) (str ""),
    ret (cat3 (app "showItem" [index l 0]) (str " ") (app "showItems" [index l 1]))]),
  ("showItem", ["i"], [
    retIf (is (index i 0) 0) (builtin .str (index i 1)), retIf (is (index i 0) 1) (index i 1),
    ret (cat3 (index i 1) (str " ") (bin .concat (app "showItems" [index i 3]) (index i 2)))]),
  -- Anything that is not a Unicode scalar value becomes U+0000, as `Char.ofNat` does.
  ("chr", ["c"], [
    retIf (bin .lt c (big 0)) (str "\x00"), retIf (bin .lt c (big 0xD800)) (builtin .chr c),
    retIf (bin .lt c (big 0xE000)) (str "\x00"), retIf (bin .lt c (big 0x110000)) (builtin .chr c),
    ret (str "\x00")]),
  -- `l` is the handlers in scope where a code value runs: `[[key, clause], rest]`.
  ("find", ["l", "key", "name"], [
    ite (isUndef l)
      [.throw (cat3 (str "`") (var "name") (str "` is performed but nothing handles it"))] [],
    retIf (bin .eq (index (index l 0) 0) (var "key")) (index (index l 0) 1),
    ret (app "find" [index l 1, var "key", var "name"])])]

end Catcat.JS
